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
% DateTime   : Thu Dec  3 11:41:34 EST 2020

% Result     : Theorem 3.24s
% Output     : CNFRefutation 3.24s
% Verified   : 
% Statistics : Number of formulae       :  172 ( 660 expanded)
%              Number of clauses        :   83 ( 143 expanded)
%              Number of leaves         :   25 ( 185 expanded)
%              Depth                    :   22
%              Number of atoms          :  571 (2856 expanded)
%              Number of equality atoms :  283 (1474 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal clause size      :   20 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f14,axiom,(
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

fof(f21,plain,(
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
    inference(ennf_transformation,[],[f14])).

fof(f40,plain,(
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
    inference(nnf_transformation,[],[f21])).

fof(f41,plain,(
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
    inference(rectify,[],[f40])).

fof(f44,plain,(
    ! [X5,X0] :
      ( ? [X6] :
          ( ~ r2_hidden(X5,X6)
          & r2_hidden(X6,X0) )
     => ( ~ r2_hidden(X5,sK4(X0,X5))
        & r2_hidden(sK4(X0,X5),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f43,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r2_hidden(X2,X3)
          & r2_hidden(X3,X0) )
     => ( ~ r2_hidden(X2,sK3(X0,X1))
        & r2_hidden(sK3(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f42,plain,(
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
              ( ~ r2_hidden(sK2(X0,X1),X3)
              & r2_hidden(X3,X0) )
          | ~ r2_hidden(sK2(X0,X1),X1) )
        & ( ! [X4] :
              ( r2_hidden(sK2(X0,X1),X4)
              | ~ r2_hidden(X4,X0) )
          | r2_hidden(sK2(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ( ( ( k1_setfam_1(X0) = X1
            | k1_xboole_0 != X1 )
          & ( k1_xboole_0 = X1
            | k1_setfam_1(X0) != X1 ) )
        | k1_xboole_0 != X0 )
      & ( ( ( k1_setfam_1(X0) = X1
            | ( ( ( ~ r2_hidden(sK2(X0,X1),sK3(X0,X1))
                  & r2_hidden(sK3(X0,X1),X0) )
                | ~ r2_hidden(sK2(X0,X1),X1) )
              & ( ! [X4] :
                    ( r2_hidden(sK2(X0,X1),X4)
                    | ~ r2_hidden(X4,X0) )
                | r2_hidden(sK2(X0,X1),X1) ) ) )
          & ( ! [X5] :
                ( ( r2_hidden(X5,X1)
                  | ( ~ r2_hidden(X5,sK4(X0,X5))
                    & r2_hidden(sK4(X0,X5),X0) ) )
                & ( ! [X7] :
                      ( r2_hidden(X5,X7)
                      | ~ r2_hidden(X7,X0) )
                  | ~ r2_hidden(X5,X1) ) )
            | k1_setfam_1(X0) != X1 ) )
        | k1_xboole_0 = X0 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f41,f44,f43,f42])).

fof(f81,plain,(
    ! [X4,X0,X1] :
      ( k1_setfam_1(X0) = X1
      | r2_hidden(sK2(X0,X1),X4)
      | ~ r2_hidden(X4,X0)
      | r2_hidden(sK2(X0,X1),X1)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f45])).

fof(f15,conjecture,(
    ! [X0] : k1_setfam_1(k1_tarski(X0)) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,negated_conjecture,(
    ~ ! [X0] : k1_setfam_1(k1_tarski(X0)) = X0 ),
    inference(negated_conjecture,[],[f15])).

fof(f22,plain,(
    ? [X0] : k1_setfam_1(k1_tarski(X0)) != X0 ),
    inference(ennf_transformation,[],[f16])).

fof(f46,plain,
    ( ? [X0] : k1_setfam_1(k1_tarski(X0)) != X0
   => k1_setfam_1(k1_tarski(sK5)) != sK5 ),
    introduced(choice_axiom,[])).

fof(f47,plain,(
    k1_setfam_1(k1_tarski(sK5)) != sK5 ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f22,f46])).

fof(f86,plain,(
    k1_setfam_1(k1_tarski(sK5)) != sK5 ),
    inference(cnf_transformation,[],[f47])).

fof(f7,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f66,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f7])).

fof(f8,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f67,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f8])).

fof(f9,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f68,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f9])).

fof(f87,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f67,f68])).

fof(f88,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f66,f87])).

fof(f106,plain,(
    k1_setfam_1(k2_enumset1(sK5,sK5,sK5,sK5)) != sK5 ),
    inference(definition_unfolding,[],[f86,f88])).

fof(f82,plain,(
    ! [X0,X1] :
      ( k1_setfam_1(X0) = X1
      | r2_hidden(sK3(X0,X1),X0)
      | ~ r2_hidden(sK2(X0,X1),X1)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f45])).

fof(f6,axiom,(
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
    inference(ennf_transformation,[],[f6])).

fof(f30,plain,(
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

fof(f31,plain,(
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
    inference(flattening,[],[f30])).

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
    inference(rectify,[],[f31])).

fof(f33,plain,(
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

fof(f34,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f32,f33])).

fof(f61,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X2 != X5
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f34])).

fof(f93,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X2 != X5
      | k2_enumset1(X0,X0,X1,X2) != X3 ) ),
    inference(definition_unfolding,[],[f61,f68])).

fof(f109,plain,(
    ! [X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | k2_enumset1(X0,X0,X1,X5) != X3 ) ),
    inference(equality_resolution,[],[f93])).

fof(f110,plain,(
    ! [X0,X5,X1] : r2_hidden(X5,k2_enumset1(X0,X0,X1,X5)) ),
    inference(equality_resolution,[],[f109])).

fof(f58,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( X2 = X5
      | X1 = X5
      | X0 = X5
      | ~ r2_hidden(X5,X3)
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f34])).

fof(f96,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( X2 = X5
      | X1 = X5
      | X0 = X5
      | ~ r2_hidden(X5,X3)
      | k2_enumset1(X0,X0,X1,X2) != X3 ) ),
    inference(definition_unfolding,[],[f58,f68])).

fof(f115,plain,(
    ! [X2,X0,X5,X1] :
      ( X2 = X5
      | X1 = X5
      | X0 = X5
      | ~ r2_hidden(X5,k2_enumset1(X0,X0,X1,X2)) ) ),
    inference(equality_resolution,[],[f96])).

fof(f5,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f57,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k4_xboole_0(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f54,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | k4_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f29])).

fof(f84,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = X1
      | k1_setfam_1(X0) != X1
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f45])).

fof(f120,plain,(
    ! [X0] :
      ( k1_xboole_0 = k1_setfam_1(X0)
      | k1_xboole_0 != X0 ) ),
    inference(equality_resolution,[],[f84])).

fof(f121,plain,(
    k1_xboole_0 = k1_setfam_1(k1_xboole_0) ),
    inference(equality_resolution,[],[f120])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
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
    inference(nnf_transformation,[],[f17])).

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

fof(f48,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f27])).

fof(f51,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f28])).

fof(f108,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f51])).

fof(f55,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))
    <=> ( X0 != X2
        & r2_hidden(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))
        | X0 = X2
        | ~ r2_hidden(X0,X1) )
      & ( ( X0 != X2
          & r2_hidden(X0,X1) )
        | ~ r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) ) ) ),
    inference(nnf_transformation,[],[f12])).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))
        | X0 = X2
        | ~ r2_hidden(X0,X1) )
      & ( ( X0 != X2
          & r2_hidden(X0,X1) )
        | ~ r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) ) ) ),
    inference(flattening,[],[f37])).

fof(f74,plain,(
    ! [X2,X0,X1] :
      ( X0 != X2
      | ~ r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f102,plain,(
    ! [X2,X0,X1] :
      ( X0 != X2
      | ~ r2_hidden(X0,k4_xboole_0(X1,k2_enumset1(X2,X2,X2,X2))) ) ),
    inference(definition_unfolding,[],[f74,f88])).

fof(f117,plain,(
    ! [X2,X1] : ~ r2_hidden(X2,k4_xboole_0(X1,k2_enumset1(X2,X2,X2,X2))) ),
    inference(equality_resolution,[],[f102])).

fof(f49,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK0(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f18])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f83,plain,(
    ! [X0,X1] :
      ( k1_setfam_1(X0) = X1
      | ~ r2_hidden(sK2(X0,X1),sK3(X0,X1))
      | ~ r2_hidden(sK2(X0,X1),X1)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f45])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k1_tarski(X1)) = X0
    <=> ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(X0,k1_tarski(X1)) = X0
        | r2_hidden(X1,X0) )
      & ( ~ r2_hidden(X1,X0)
        | k4_xboole_0(X0,k1_tarski(X1)) != X0 ) ) ),
    inference(nnf_transformation,[],[f13])).

fof(f77,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k1_tarski(X1)) = X0
      | r2_hidden(X1,X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f104,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k2_enumset1(X1,X1,X1,X1)) = X0
      | r2_hidden(X1,X0) ) ),
    inference(definition_unfolding,[],[f77,f88])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
    <=> r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(k1_tarski(X0),X1)
        | ~ r2_hidden(X0,X1) )
      & ( r2_hidden(X0,X1)
        | ~ r1_tarski(k1_tarski(X0),X1) ) ) ),
    inference(nnf_transformation,[],[f10])).

fof(f69,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | ~ r1_tarski(k1_tarski(X0),X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f98,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | ~ r1_tarski(k2_enumset1(X0,X0,X0,X0),X1) ) ),
    inference(definition_unfolding,[],[f69,f88])).

fof(f11,axiom,(
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
    inference(nnf_transformation,[],[f11])).

fof(f72,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f36])).

fof(f99,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(k2_enumset1(X0,X0,X0,X0),k2_enumset1(X1,X1,X1,X1)) = k2_enumset1(X0,X0,X0,X0)
      | X0 = X1 ) ),
    inference(definition_unfolding,[],[f72,f88,f88,f88])).

fof(f71,plain,(
    ! [X0,X1] :
      ( X0 != X1
      | k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) != k1_tarski(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f100,plain,(
    ! [X0,X1] :
      ( X0 != X1
      | k4_xboole_0(k2_enumset1(X0,X0,X0,X0),k2_enumset1(X1,X1,X1,X1)) != k2_enumset1(X0,X0,X0,X0) ) ),
    inference(definition_unfolding,[],[f71,f88,f88,f88])).

fof(f116,plain,(
    ! [X1] : k4_xboole_0(k2_enumset1(X1,X1,X1,X1),k2_enumset1(X1,X1,X1,X1)) != k2_enumset1(X1,X1,X1,X1) ),
    inference(equality_resolution,[],[f100])).

fof(f76,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | k4_xboole_0(X0,k1_tarski(X1)) != X0 ) ),
    inference(cnf_transformation,[],[f39])).

fof(f105,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | k4_xboole_0(X0,k2_enumset1(X1,X1,X1,X1)) != X0 ) ),
    inference(definition_unfolding,[],[f76,f88])).

cnf(c_31,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(sK2(X1,X2),X2)
    | r2_hidden(sK2(X1,X2),X0)
    | k1_setfam_1(X1) = X2
    | k1_xboole_0 = X1 ),
    inference(cnf_transformation,[],[f81])).

cnf(c_35,negated_conjecture,
    ( k1_setfam_1(k2_enumset1(sK5,sK5,sK5,sK5)) != sK5 ),
    inference(cnf_transformation,[],[f106])).

cnf(c_5912,plain,
    ( ~ r2_hidden(X0,k2_enumset1(sK5,sK5,sK5,sK5))
    | r2_hidden(sK2(k2_enumset1(sK5,sK5,sK5,sK5),sK5),X0)
    | r2_hidden(sK2(k2_enumset1(sK5,sK5,sK5,sK5),sK5),sK5)
    | k1_xboole_0 = k2_enumset1(sK5,sK5,sK5,sK5) ),
    inference(resolution,[status(thm)],[c_31,c_35])).

cnf(c_30,plain,
    ( r2_hidden(sK3(X0,X1),X0)
    | ~ r2_hidden(sK2(X0,X1),X1)
    | k1_setfam_1(X0) = X1
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f82])).

cnf(c_6144,plain,
    ( ~ r2_hidden(X0,k2_enumset1(sK5,sK5,sK5,sK5))
    | r2_hidden(sK3(k2_enumset1(sK5,sK5,sK5,sK5),sK5),k2_enumset1(sK5,sK5,sK5,sK5))
    | r2_hidden(sK2(k2_enumset1(sK5,sK5,sK5,sK5),sK5),X0)
    | k1_setfam_1(k2_enumset1(sK5,sK5,sK5,sK5)) = sK5
    | k1_xboole_0 = k2_enumset1(sK5,sK5,sK5,sK5) ),
    inference(resolution,[status(thm)],[c_5912,c_30])).

cnf(c_6169,plain,
    ( r2_hidden(sK2(k2_enumset1(sK5,sK5,sK5,sK5),sK5),sK5)
    | ~ r2_hidden(sK5,k2_enumset1(sK5,sK5,sK5,sK5))
    | k1_xboole_0 = k2_enumset1(sK5,sK5,sK5,sK5) ),
    inference(factoring,[status(thm)],[c_5912])).

cnf(c_14,plain,
    ( r2_hidden(X0,k2_enumset1(X1,X1,X2,X0)) ),
    inference(cnf_transformation,[],[f110])).

cnf(c_1821,plain,
    ( r2_hidden(sK5,k2_enumset1(X0,X0,X1,sK5)) ),
    inference(instantiation,[status(thm)],[c_14])).

cnf(c_4408,plain,
    ( r2_hidden(sK5,k2_enumset1(sK5,sK5,sK5,sK5)) ),
    inference(instantiation,[status(thm)],[c_1821])).

cnf(c_6172,plain,
    ( r2_hidden(sK2(k2_enumset1(sK5,sK5,sK5,sK5),sK5),sK5)
    | k1_xboole_0 = k2_enumset1(sK5,sK5,sK5,sK5) ),
    inference(global_propositional_subsumption,[status(thm)],[c_6169,c_4408])).

cnf(c_6370,plain,
    ( r2_hidden(sK3(k2_enumset1(sK5,sK5,sK5,sK5),sK5),k2_enumset1(sK5,sK5,sK5,sK5))
    | k1_setfam_1(k2_enumset1(sK5,sK5,sK5,sK5)) = sK5
    | k1_xboole_0 = k2_enumset1(sK5,sK5,sK5,sK5) ),
    inference(resolution,[status(thm)],[c_6172,c_30])).

cnf(c_6373,plain,
    ( r2_hidden(sK3(k2_enumset1(sK5,sK5,sK5,sK5),sK5),k2_enumset1(sK5,sK5,sK5,sK5))
    | k1_xboole_0 = k2_enumset1(sK5,sK5,sK5,sK5) ),
    inference(global_propositional_subsumption,[status(thm)],[c_6144,c_35,c_6370])).

cnf(c_17,plain,
    ( ~ r2_hidden(X0,k2_enumset1(X1,X1,X2,X3))
    | X0 = X1
    | X0 = X2
    | X0 = X3 ),
    inference(cnf_transformation,[],[f115])).

cnf(c_6389,plain,
    ( sK3(k2_enumset1(sK5,sK5,sK5,sK5),sK5) = sK5
    | k1_xboole_0 = k2_enumset1(sK5,sK5,sK5,sK5) ),
    inference(resolution,[status(thm)],[c_6373,c_17])).

cnf(c_674,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X1)
    | X2 != X0 ),
    theory(equality)).

cnf(c_6667,plain,
    ( r1_tarski(sK3(k2_enumset1(sK5,sK5,sK5,sK5),sK5),X0)
    | ~ r1_tarski(sK5,X0)
    | k1_xboole_0 = k2_enumset1(sK5,sK5,sK5,sK5) ),
    inference(resolution,[status(thm)],[c_6389,c_674])).

cnf(c_673,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_9,plain,
    ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f57])).

cnf(c_2825,plain,
    ( X0 != X1
    | k4_xboole_0(X1,k1_xboole_0) = X0 ),
    inference(resolution,[status(thm)],[c_673,c_9])).

cnf(c_7,plain,
    ( r1_tarski(X0,X1)
    | k4_xboole_0(X0,X1) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f54])).

cnf(c_3322,plain,
    ( r1_tarski(X0,k1_xboole_0)
    | k1_xboole_0 != X0 ),
    inference(resolution,[status(thm)],[c_2825,c_7])).

cnf(c_28,plain,
    ( k1_setfam_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f121])).

cnf(c_2829,plain,
    ( X0 != k1_xboole_0
    | k1_setfam_1(k1_xboole_0) = X0 ),
    inference(resolution,[status(thm)],[c_673,c_28])).

cnf(c_672,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_2830,plain,
    ( X0 != X1
    | X1 = X0 ),
    inference(resolution,[status(thm)],[c_673,c_672])).

cnf(c_3150,plain,
    ( X0 = k1_setfam_1(k1_xboole_0)
    | X0 != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_2829,c_2830])).

cnf(c_3544,plain,
    ( r1_tarski(k1_setfam_1(k1_xboole_0),k1_xboole_0)
    | k1_xboole_0 != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_3322,c_3150])).

cnf(c_3545,plain,
    ( r1_tarski(k1_setfam_1(k1_xboole_0),k1_xboole_0) ),
    inference(equality_resolution_simp,[status(thm)],[c_3544])).

cnf(c_2,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | ~ r1_tarski(X1,X2) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_3551,plain,
    ( ~ r2_hidden(X0,k1_setfam_1(k1_xboole_0))
    | r2_hidden(X0,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_3545,c_2])).

cnf(c_5,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f108])).

cnf(c_1368,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_6,plain,
    ( ~ r1_tarski(X0,X1)
    | k4_xboole_0(X0,X1) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f55])).

cnf(c_1367,plain,
    ( k4_xboole_0(X0,X1) = k1_xboole_0
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_2137,plain,
    ( k4_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1368,c_1367])).

cnf(c_23,plain,
    ( ~ r2_hidden(X0,k4_xboole_0(X1,k2_enumset1(X0,X0,X0,X0))) ),
    inference(cnf_transformation,[],[f117])).

cnf(c_1353,plain,
    ( r2_hidden(X0,k4_xboole_0(X1,k2_enumset1(X0,X0,X0,X0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_2328,plain,
    ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2137,c_1353])).

cnf(c_2331,plain,
    ( ~ r2_hidden(X0,k1_xboole_0) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_2328])).

cnf(c_3558,plain,
    ( ~ r2_hidden(X0,k1_setfam_1(k1_xboole_0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3551,c_2331])).

cnf(c_1,plain,
    ( r2_hidden(sK0(X0,X1),X0)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_3754,plain,
    ( r1_tarski(k1_setfam_1(k1_xboole_0),X0) ),
    inference(resolution,[status(thm)],[c_3558,c_1])).

cnf(c_8,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X2)
    | r1_tarski(X0,X2) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_3764,plain,
    ( r1_tarski(X0,X1)
    | ~ r1_tarski(X0,k1_setfam_1(k1_xboole_0)) ),
    inference(resolution,[status(thm)],[c_3754,c_8])).

cnf(c_7222,plain,
    ( r1_tarski(sK3(k2_enumset1(sK5,sK5,sK5,sK5),sK5),X0)
    | ~ r1_tarski(sK5,k1_setfam_1(k1_xboole_0))
    | k1_xboole_0 = k2_enumset1(sK5,sK5,sK5,sK5) ),
    inference(resolution,[status(thm)],[c_6667,c_3764])).

cnf(c_675,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_6678,plain,
    ( r2_hidden(X0,sK3(k2_enumset1(sK5,sK5,sK5,sK5),sK5))
    | ~ r2_hidden(X1,sK5)
    | X0 != X1
    | k1_xboole_0 = k2_enumset1(sK5,sK5,sK5,sK5) ),
    inference(resolution,[status(thm)],[c_6389,c_675])).

cnf(c_7502,plain,
    ( r2_hidden(X0,sK3(k2_enumset1(sK5,sK5,sK5,sK5),sK5))
    | ~ r2_hidden(X0,sK5)
    | k1_xboole_0 = k2_enumset1(sK5,sK5,sK5,sK5) ),
    inference(resolution,[status(thm)],[c_6678,c_672])).

cnf(c_29,plain,
    ( ~ r2_hidden(sK2(X0,X1),X1)
    | ~ r2_hidden(sK2(X0,X1),sK3(X0,X1))
    | k1_setfam_1(X0) = X1
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f83])).

cnf(c_8315,plain,
    ( ~ r2_hidden(sK2(k2_enumset1(sK5,sK5,sK5,sK5),sK5),sK5)
    | k1_setfam_1(k2_enumset1(sK5,sK5,sK5,sK5)) = sK5
    | k1_xboole_0 = k2_enumset1(sK5,sK5,sK5,sK5) ),
    inference(resolution,[status(thm)],[c_7502,c_29])).

cnf(c_8321,plain,
    ( k1_xboole_0 = k2_enumset1(sK5,sK5,sK5,sK5) ),
    inference(global_propositional_subsumption,[status(thm)],[c_7222,c_35,c_4408,c_6169,c_8315])).

cnf(c_8327,plain,
    ( r1_tarski(k2_enumset1(sK5,sK5,sK5,sK5),k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_8321,c_3322])).

cnf(c_6452,plain,
    ( X0 != X1
    | X0 = sK5
    | sK5 != X1 ),
    inference(instantiation,[status(thm)],[c_673])).

cnf(c_6453,plain,
    ( sK5 != k1_xboole_0
    | k1_xboole_0 = sK5
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_6452])).

cnf(c_2201,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,k1_setfam_1(X3))
    | X2 != X0
    | k1_setfam_1(X3) != X1 ),
    inference(instantiation,[status(thm)],[c_675])).

cnf(c_3433,plain,
    ( r2_hidden(X0,k1_setfam_1(X1))
    | ~ r2_hidden(sK5,X2)
    | X0 != sK5
    | k1_setfam_1(X1) != X2 ),
    inference(instantiation,[status(thm)],[c_2201])).

cnf(c_3435,plain,
    ( ~ r2_hidden(sK5,k1_xboole_0)
    | r2_hidden(k1_xboole_0,k1_setfam_1(k1_xboole_0))
    | k1_setfam_1(k1_xboole_0) != k1_xboole_0
    | k1_xboole_0 != sK5 ),
    inference(instantiation,[status(thm)],[c_3433])).

cnf(c_2386,plain,
    ( ~ r2_hidden(sK5,X0)
    | r2_hidden(sK5,X1)
    | ~ r1_tarski(X0,X1) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_3056,plain,
    ( ~ r2_hidden(sK5,X0)
    | r2_hidden(sK5,k2_enumset1(X1,X1,X2,X3))
    | ~ r1_tarski(X0,k2_enumset1(X1,X1,X2,X3)) ),
    inference(instantiation,[status(thm)],[c_2386])).

cnf(c_3058,plain,
    ( r2_hidden(sK5,k2_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0))
    | ~ r2_hidden(sK5,k1_xboole_0)
    | ~ r1_tarski(k1_xboole_0,k2_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0)) ),
    inference(instantiation,[status(thm)],[c_3056])).

cnf(c_25,plain,
    ( r2_hidden(X0,X1)
    | k4_xboole_0(X1,k2_enumset1(X0,X0,X0,X0)) = X1 ),
    inference(cnf_transformation,[],[f104])).

cnf(c_2553,plain,
    ( r2_hidden(X0,k1_xboole_0)
    | r1_tarski(k1_xboole_0,k2_enumset1(X0,X0,X0,X0)) ),
    inference(resolution,[status(thm)],[c_25,c_7])).

cnf(c_2555,plain,
    ( r2_hidden(k1_xboole_0,k1_xboole_0)
    | r1_tarski(k1_xboole_0,k2_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0)) ),
    inference(instantiation,[status(thm)],[c_2553])).

cnf(c_2172,plain,
    ( r1_tarski(k1_setfam_1(k1_xboole_0),X0)
    | ~ r1_tarski(k1_xboole_0,X0) ),
    inference(resolution,[status(thm)],[c_674,c_28])).

cnf(c_2342,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k1_setfam_1(k1_xboole_0))
    | ~ r1_tarski(k1_xboole_0,X1) ),
    inference(resolution,[status(thm)],[c_2172,c_2])).

cnf(c_2344,plain,
    ( ~ r2_hidden(k1_xboole_0,k1_setfam_1(k1_xboole_0))
    | r2_hidden(k1_xboole_0,k1_xboole_0)
    | ~ r1_tarski(k1_xboole_0,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_2342])).

cnf(c_2332,plain,
    ( r2_hidden(k1_xboole_0,k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_2328])).

cnf(c_19,plain,
    ( r2_hidden(X0,X1)
    | ~ r1_tarski(k2_enumset1(X0,X0,X0,X0),X1) ),
    inference(cnf_transformation,[],[f98])).

cnf(c_1958,plain,
    ( r2_hidden(sK5,X0)
    | ~ r1_tarski(k2_enumset1(sK5,sK5,sK5,sK5),X0) ),
    inference(instantiation,[status(thm)],[c_19])).

cnf(c_1960,plain,
    ( r2_hidden(sK5,k1_xboole_0)
    | ~ r1_tarski(k2_enumset1(sK5,sK5,sK5,sK5),k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_1958])).

cnf(c_1808,plain,
    ( ~ r2_hidden(sK5,k2_enumset1(X0,X0,X1,X2))
    | sK5 = X0
    | sK5 = X1
    | sK5 = X2 ),
    inference(instantiation,[status(thm)],[c_17])).

cnf(c_1810,plain,
    ( ~ r2_hidden(sK5,k2_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0))
    | sK5 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1808])).

cnf(c_94,plain,
    ( r1_tarski(k1_xboole_0,k1_xboole_0)
    | k4_xboole_0(k1_xboole_0,k1_xboole_0) != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_91,plain,
    ( k4_xboole_0(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_20,plain,
    ( X0 = X1
    | k4_xboole_0(k2_enumset1(X1,X1,X1,X1),k2_enumset1(X0,X0,X0,X0)) = k2_enumset1(X1,X1,X1,X1) ),
    inference(cnf_transformation,[],[f99])).

cnf(c_68,plain,
    ( k4_xboole_0(k2_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k2_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0)) = k2_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0)
    | k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_20])).

cnf(c_21,plain,
    ( k4_xboole_0(k2_enumset1(X0,X0,X0,X0),k2_enumset1(X0,X0,X0,X0)) != k2_enumset1(X0,X0,X0,X0) ),
    inference(cnf_transformation,[],[f116])).

cnf(c_67,plain,
    ( k4_xboole_0(k2_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k2_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0)) != k2_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_21])).

cnf(c_55,plain,
    ( k4_xboole_0(X0,k2_enumset1(X1,X1,X1,X1)) = X0
    | r2_hidden(X1,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_57,plain,
    ( k4_xboole_0(k1_xboole_0,k2_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0)) = k1_xboole_0
    | r2_hidden(k1_xboole_0,k1_xboole_0) = iProver_top ),
    inference(instantiation,[status(thm)],[c_55])).

cnf(c_26,plain,
    ( ~ r2_hidden(X0,X1)
    | k4_xboole_0(X1,k2_enumset1(X0,X0,X0,X0)) != X1 ),
    inference(cnf_transformation,[],[f105])).

cnf(c_53,plain,
    ( ~ r2_hidden(k1_xboole_0,k1_xboole_0)
    | k4_xboole_0(k1_xboole_0,k2_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0)) != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_26])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_8327,c_6453,c_3435,c_3058,c_2555,c_2344,c_2332,c_1960,c_1810,c_94,c_91,c_68,c_67,c_57,c_53,c_28])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : iproveropt_run.sh %d %s
% 0.13/0.33  % Computer   : n005.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 16:23:02 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 3.24/1.00  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.24/1.00  
% 3.24/1.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.24/1.00  
% 3.24/1.00  ------  iProver source info
% 3.24/1.00  
% 3.24/1.00  git: date: 2020-06-30 10:37:57 +0100
% 3.24/1.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.24/1.00  git: non_committed_changes: false
% 3.24/1.00  git: last_make_outside_of_git: false
% 3.24/1.00  
% 3.24/1.00  ------ 
% 3.24/1.00  ------ Parsing...
% 3.24/1.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.24/1.00  
% 3.24/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e  sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 3.24/1.00  
% 3.24/1.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.24/1.00  
% 3.24/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.24/1.00  ------ Proving...
% 3.24/1.00  ------ Problem Properties 
% 3.24/1.00  
% 3.24/1.00  
% 3.24/1.00  clauses                                 34
% 3.24/1.00  conjectures                             1
% 3.24/1.00  EPR                                     4
% 3.24/1.00  Horn                                    22
% 3.24/1.00  unary                                   9
% 3.24/1.00  binary                                  10
% 3.24/1.00  lits                                    82
% 3.24/1.00  lits eq                                 34
% 3.24/1.00  fd_pure                                 0
% 3.24/1.00  fd_pseudo                               0
% 3.24/1.00  fd_cond                                 3
% 3.24/1.00  fd_pseudo_cond                          10
% 3.24/1.00  AC symbols                              0
% 3.24/1.00  
% 3.24/1.00  ------ Input Options Time Limit: Unbounded
% 3.24/1.00  
% 3.24/1.00  
% 3.24/1.00  ------ 
% 3.24/1.00  Current options:
% 3.24/1.00  ------ 
% 3.24/1.00  
% 3.24/1.00  
% 3.24/1.00  
% 3.24/1.00  
% 3.24/1.00  ------ Proving...
% 3.24/1.00  
% 3.24/1.00  
% 3.24/1.00  % SZS status Theorem for theBenchmark.p
% 3.24/1.00  
% 3.24/1.00  % SZS output start CNFRefutation for theBenchmark.p
% 3.24/1.00  
% 3.24/1.00  fof(f14,axiom,(
% 3.24/1.00    ! [X0,X1] : ((k1_xboole_0 = X0 => (k1_setfam_1(X0) = X1 <=> k1_xboole_0 = X1)) & (k1_xboole_0 != X0 => (k1_setfam_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ! [X3] : (r2_hidden(X3,X0) => r2_hidden(X2,X3))))))),
% 3.24/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.24/1.00  
% 3.24/1.00  fof(f21,plain,(
% 3.24/1.00    ! [X0,X1] : (((k1_setfam_1(X0) = X1 <=> k1_xboole_0 = X1) | k1_xboole_0 != X0) & ((k1_setfam_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ! [X3] : (r2_hidden(X2,X3) | ~r2_hidden(X3,X0)))) | k1_xboole_0 = X0))),
% 3.24/1.00    inference(ennf_transformation,[],[f14])).
% 3.24/1.00  
% 3.24/1.00  fof(f40,plain,(
% 3.24/1.00    ! [X0,X1] : ((((k1_setfam_1(X0) = X1 | k1_xboole_0 != X1) & (k1_xboole_0 = X1 | k1_setfam_1(X0) != X1)) | k1_xboole_0 != X0) & (((k1_setfam_1(X0) = X1 | ? [X2] : ((? [X3] : (~r2_hidden(X2,X3) & r2_hidden(X3,X0)) | ~r2_hidden(X2,X1)) & (! [X3] : (r2_hidden(X2,X3) | ~r2_hidden(X3,X0)) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ? [X3] : (~r2_hidden(X2,X3) & r2_hidden(X3,X0))) & (! [X3] : (r2_hidden(X2,X3) | ~r2_hidden(X3,X0)) | ~r2_hidden(X2,X1))) | k1_setfam_1(X0) != X1)) | k1_xboole_0 = X0))),
% 3.24/1.00    inference(nnf_transformation,[],[f21])).
% 3.24/1.00  
% 3.24/1.00  fof(f41,plain,(
% 3.24/1.00    ! [X0,X1] : ((((k1_setfam_1(X0) = X1 | k1_xboole_0 != X1) & (k1_xboole_0 = X1 | k1_setfam_1(X0) != X1)) | k1_xboole_0 != X0) & (((k1_setfam_1(X0) = X1 | ? [X2] : ((? [X3] : (~r2_hidden(X2,X3) & r2_hidden(X3,X0)) | ~r2_hidden(X2,X1)) & (! [X4] : (r2_hidden(X2,X4) | ~r2_hidden(X4,X0)) | r2_hidden(X2,X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ? [X6] : (~r2_hidden(X5,X6) & r2_hidden(X6,X0))) & (! [X7] : (r2_hidden(X5,X7) | ~r2_hidden(X7,X0)) | ~r2_hidden(X5,X1))) | k1_setfam_1(X0) != X1)) | k1_xboole_0 = X0))),
% 3.24/1.00    inference(rectify,[],[f40])).
% 3.24/1.00  
% 3.24/1.00  fof(f44,plain,(
% 3.24/1.00    ! [X5,X0] : (? [X6] : (~r2_hidden(X5,X6) & r2_hidden(X6,X0)) => (~r2_hidden(X5,sK4(X0,X5)) & r2_hidden(sK4(X0,X5),X0)))),
% 3.24/1.00    introduced(choice_axiom,[])).
% 3.24/1.00  
% 3.24/1.00  fof(f43,plain,(
% 3.24/1.00    ( ! [X2] : (! [X1,X0] : (? [X3] : (~r2_hidden(X2,X3) & r2_hidden(X3,X0)) => (~r2_hidden(X2,sK3(X0,X1)) & r2_hidden(sK3(X0,X1),X0)))) )),
% 3.24/1.00    introduced(choice_axiom,[])).
% 3.24/1.00  
% 3.24/1.00  fof(f42,plain,(
% 3.24/1.00    ! [X1,X0] : (? [X2] : ((? [X3] : (~r2_hidden(X2,X3) & r2_hidden(X3,X0)) | ~r2_hidden(X2,X1)) & (! [X4] : (r2_hidden(X2,X4) | ~r2_hidden(X4,X0)) | r2_hidden(X2,X1))) => ((? [X3] : (~r2_hidden(sK2(X0,X1),X3) & r2_hidden(X3,X0)) | ~r2_hidden(sK2(X0,X1),X1)) & (! [X4] : (r2_hidden(sK2(X0,X1),X4) | ~r2_hidden(X4,X0)) | r2_hidden(sK2(X0,X1),X1))))),
% 3.24/1.00    introduced(choice_axiom,[])).
% 3.24/1.00  
% 3.24/1.00  fof(f45,plain,(
% 3.24/1.00    ! [X0,X1] : ((((k1_setfam_1(X0) = X1 | k1_xboole_0 != X1) & (k1_xboole_0 = X1 | k1_setfam_1(X0) != X1)) | k1_xboole_0 != X0) & (((k1_setfam_1(X0) = X1 | (((~r2_hidden(sK2(X0,X1),sK3(X0,X1)) & r2_hidden(sK3(X0,X1),X0)) | ~r2_hidden(sK2(X0,X1),X1)) & (! [X4] : (r2_hidden(sK2(X0,X1),X4) | ~r2_hidden(X4,X0)) | r2_hidden(sK2(X0,X1),X1)))) & (! [X5] : ((r2_hidden(X5,X1) | (~r2_hidden(X5,sK4(X0,X5)) & r2_hidden(sK4(X0,X5),X0))) & (! [X7] : (r2_hidden(X5,X7) | ~r2_hidden(X7,X0)) | ~r2_hidden(X5,X1))) | k1_setfam_1(X0) != X1)) | k1_xboole_0 = X0))),
% 3.24/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f41,f44,f43,f42])).
% 3.24/1.00  
% 3.24/1.00  fof(f81,plain,(
% 3.24/1.00    ( ! [X4,X0,X1] : (k1_setfam_1(X0) = X1 | r2_hidden(sK2(X0,X1),X4) | ~r2_hidden(X4,X0) | r2_hidden(sK2(X0,X1),X1) | k1_xboole_0 = X0) )),
% 3.24/1.00    inference(cnf_transformation,[],[f45])).
% 3.24/1.00  
% 3.24/1.00  fof(f15,conjecture,(
% 3.24/1.00    ! [X0] : k1_setfam_1(k1_tarski(X0)) = X0),
% 3.24/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.24/1.00  
% 3.24/1.00  fof(f16,negated_conjecture,(
% 3.24/1.00    ~! [X0] : k1_setfam_1(k1_tarski(X0)) = X0),
% 3.24/1.00    inference(negated_conjecture,[],[f15])).
% 3.24/1.00  
% 3.24/1.00  fof(f22,plain,(
% 3.24/1.00    ? [X0] : k1_setfam_1(k1_tarski(X0)) != X0),
% 3.24/1.00    inference(ennf_transformation,[],[f16])).
% 3.24/1.00  
% 3.24/1.00  fof(f46,plain,(
% 3.24/1.00    ? [X0] : k1_setfam_1(k1_tarski(X0)) != X0 => k1_setfam_1(k1_tarski(sK5)) != sK5),
% 3.24/1.00    introduced(choice_axiom,[])).
% 3.24/1.00  
% 3.24/1.00  fof(f47,plain,(
% 3.24/1.00    k1_setfam_1(k1_tarski(sK5)) != sK5),
% 3.24/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f22,f46])).
% 3.24/1.00  
% 3.24/1.00  fof(f86,plain,(
% 3.24/1.00    k1_setfam_1(k1_tarski(sK5)) != sK5),
% 3.24/1.00    inference(cnf_transformation,[],[f47])).
% 3.24/1.00  
% 3.24/1.00  fof(f7,axiom,(
% 3.24/1.00    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 3.24/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.24/1.00  
% 3.24/1.00  fof(f66,plain,(
% 3.24/1.00    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 3.24/1.00    inference(cnf_transformation,[],[f7])).
% 3.24/1.00  
% 3.24/1.00  fof(f8,axiom,(
% 3.24/1.00    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 3.24/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.24/1.00  
% 3.24/1.00  fof(f67,plain,(
% 3.24/1.00    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 3.24/1.00    inference(cnf_transformation,[],[f8])).
% 3.24/1.00  
% 3.24/1.00  fof(f9,axiom,(
% 3.24/1.00    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 3.24/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.24/1.00  
% 3.24/1.00  fof(f68,plain,(
% 3.24/1.00    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 3.24/1.00    inference(cnf_transformation,[],[f9])).
% 3.24/1.00  
% 3.24/1.00  fof(f87,plain,(
% 3.24/1.00    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 3.24/1.00    inference(definition_unfolding,[],[f67,f68])).
% 3.24/1.00  
% 3.24/1.00  fof(f88,plain,(
% 3.24/1.00    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 3.24/1.00    inference(definition_unfolding,[],[f66,f87])).
% 3.24/1.00  
% 3.24/1.00  fof(f106,plain,(
% 3.24/1.00    k1_setfam_1(k2_enumset1(sK5,sK5,sK5,sK5)) != sK5),
% 3.24/1.00    inference(definition_unfolding,[],[f86,f88])).
% 3.24/1.00  
% 3.24/1.00  fof(f82,plain,(
% 3.24/1.00    ( ! [X0,X1] : (k1_setfam_1(X0) = X1 | r2_hidden(sK3(X0,X1),X0) | ~r2_hidden(sK2(X0,X1),X1) | k1_xboole_0 = X0) )),
% 3.24/1.00    inference(cnf_transformation,[],[f45])).
% 3.24/1.00  
% 3.24/1.00  fof(f6,axiom,(
% 3.24/1.00    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> ~(X2 != X4 & X1 != X4 & X0 != X4)))),
% 3.24/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.24/1.00  
% 3.24/1.00  fof(f20,plain,(
% 3.24/1.00    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> (X2 = X4 | X1 = X4 | X0 = X4)))),
% 3.24/1.00    inference(ennf_transformation,[],[f6])).
% 3.24/1.00  
% 3.24/1.00  fof(f30,plain,(
% 3.24/1.00    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & ((X2 = X4 | X1 = X4 | X0 = X4) | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & ((X2 = X4 | X1 = X4 | X0 = X4) | ~r2_hidden(X4,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 3.24/1.00    inference(nnf_transformation,[],[f20])).
% 3.24/1.00  
% 3.24/1.00  fof(f31,plain,(
% 3.24/1.00    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & (X2 = X4 | X1 = X4 | X0 = X4 | ~r2_hidden(X4,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 3.24/1.00    inference(flattening,[],[f30])).
% 3.24/1.00  
% 3.24/1.00  fof(f32,plain,(
% 3.24/1.00    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X2 != X5 & X1 != X5 & X0 != X5)) & (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 3.24/1.00    inference(rectify,[],[f31])).
% 3.24/1.00  
% 3.24/1.00  fof(f33,plain,(
% 3.24/1.00    ! [X3,X2,X1,X0] : (? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3))) => (((sK1(X0,X1,X2,X3) != X2 & sK1(X0,X1,X2,X3) != X1 & sK1(X0,X1,X2,X3) != X0) | ~r2_hidden(sK1(X0,X1,X2,X3),X3)) & (sK1(X0,X1,X2,X3) = X2 | sK1(X0,X1,X2,X3) = X1 | sK1(X0,X1,X2,X3) = X0 | r2_hidden(sK1(X0,X1,X2,X3),X3))))),
% 3.24/1.00    introduced(choice_axiom,[])).
% 3.24/1.00  
% 3.24/1.00  fof(f34,plain,(
% 3.24/1.00    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | (((sK1(X0,X1,X2,X3) != X2 & sK1(X0,X1,X2,X3) != X1 & sK1(X0,X1,X2,X3) != X0) | ~r2_hidden(sK1(X0,X1,X2,X3),X3)) & (sK1(X0,X1,X2,X3) = X2 | sK1(X0,X1,X2,X3) = X1 | sK1(X0,X1,X2,X3) = X0 | r2_hidden(sK1(X0,X1,X2,X3),X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X2 != X5 & X1 != X5 & X0 != X5)) & (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 3.24/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f32,f33])).
% 3.24/1.00  
% 3.24/1.00  fof(f61,plain,(
% 3.24/1.00    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X2 != X5 | k1_enumset1(X0,X1,X2) != X3) )),
% 3.24/1.00    inference(cnf_transformation,[],[f34])).
% 3.24/1.00  
% 3.24/1.00  fof(f93,plain,(
% 3.24/1.00    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X2 != X5 | k2_enumset1(X0,X0,X1,X2) != X3) )),
% 3.24/1.00    inference(definition_unfolding,[],[f61,f68])).
% 3.24/1.00  
% 3.24/1.00  fof(f109,plain,(
% 3.24/1.00    ( ! [X0,X5,X3,X1] : (r2_hidden(X5,X3) | k2_enumset1(X0,X0,X1,X5) != X3) )),
% 3.24/1.00    inference(equality_resolution,[],[f93])).
% 3.24/1.00  
% 3.24/1.00  fof(f110,plain,(
% 3.24/1.00    ( ! [X0,X5,X1] : (r2_hidden(X5,k2_enumset1(X0,X0,X1,X5))) )),
% 3.24/1.00    inference(equality_resolution,[],[f109])).
% 3.24/1.00  
% 3.24/1.00  fof(f58,plain,(
% 3.24/1.00    ( ! [X2,X0,X5,X3,X1] : (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3) | k1_enumset1(X0,X1,X2) != X3) )),
% 3.24/1.00    inference(cnf_transformation,[],[f34])).
% 3.24/1.00  
% 3.24/1.00  fof(f96,plain,(
% 3.24/1.00    ( ! [X2,X0,X5,X3,X1] : (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3) | k2_enumset1(X0,X0,X1,X2) != X3) )),
% 3.24/1.00    inference(definition_unfolding,[],[f58,f68])).
% 3.24/1.00  
% 3.24/1.00  fof(f115,plain,(
% 3.24/1.00    ( ! [X2,X0,X5,X1] : (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,k2_enumset1(X0,X0,X1,X2))) )),
% 3.24/1.00    inference(equality_resolution,[],[f96])).
% 3.24/1.00  
% 3.24/1.00  fof(f5,axiom,(
% 3.24/1.00    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 3.24/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.24/1.00  
% 3.24/1.00  fof(f57,plain,(
% 3.24/1.00    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 3.24/1.00    inference(cnf_transformation,[],[f5])).
% 3.24/1.00  
% 3.24/1.00  fof(f3,axiom,(
% 3.24/1.00    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 3.24/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.24/1.00  
% 3.24/1.00  fof(f29,plain,(
% 3.24/1.00    ! [X0,X1] : ((k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0))),
% 3.24/1.00    inference(nnf_transformation,[],[f3])).
% 3.24/1.00  
% 3.24/1.00  fof(f54,plain,(
% 3.24/1.00    ( ! [X0,X1] : (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0) )),
% 3.24/1.00    inference(cnf_transformation,[],[f29])).
% 3.24/1.00  
% 3.24/1.00  fof(f84,plain,(
% 3.24/1.00    ( ! [X0,X1] : (k1_xboole_0 = X1 | k1_setfam_1(X0) != X1 | k1_xboole_0 != X0) )),
% 3.24/1.00    inference(cnf_transformation,[],[f45])).
% 3.24/1.00  
% 3.24/1.00  fof(f120,plain,(
% 3.24/1.00    ( ! [X0] : (k1_xboole_0 = k1_setfam_1(X0) | k1_xboole_0 != X0) )),
% 3.24/1.00    inference(equality_resolution,[],[f84])).
% 3.24/1.00  
% 3.24/1.00  fof(f121,plain,(
% 3.24/1.00    k1_xboole_0 = k1_setfam_1(k1_xboole_0)),
% 3.24/1.00    inference(equality_resolution,[],[f120])).
% 3.24/1.00  
% 3.24/1.00  fof(f1,axiom,(
% 3.24/1.00    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 3.24/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.24/1.00  
% 3.24/1.00  fof(f17,plain,(
% 3.24/1.00    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 3.24/1.00    inference(ennf_transformation,[],[f1])).
% 3.24/1.00  
% 3.24/1.00  fof(f23,plain,(
% 3.24/1.00    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 3.24/1.00    inference(nnf_transformation,[],[f17])).
% 3.24/1.00  
% 3.24/1.00  fof(f24,plain,(
% 3.24/1.00    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 3.24/1.00    inference(rectify,[],[f23])).
% 3.24/1.00  
% 3.24/1.00  fof(f25,plain,(
% 3.24/1.00    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 3.24/1.00    introduced(choice_axiom,[])).
% 3.24/1.00  
% 3.24/1.00  fof(f26,plain,(
% 3.24/1.00    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 3.24/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f24,f25])).
% 3.24/1.00  
% 3.24/1.00  fof(f48,plain,(
% 3.24/1.00    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,X1)) )),
% 3.24/1.00    inference(cnf_transformation,[],[f26])).
% 3.24/1.00  
% 3.24/1.00  fof(f2,axiom,(
% 3.24/1.00    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 3.24/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.24/1.00  
% 3.24/1.00  fof(f27,plain,(
% 3.24/1.00    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.24/1.00    inference(nnf_transformation,[],[f2])).
% 3.24/1.00  
% 3.24/1.00  fof(f28,plain,(
% 3.24/1.00    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.24/1.00    inference(flattening,[],[f27])).
% 3.24/1.00  
% 3.24/1.00  fof(f51,plain,(
% 3.24/1.00    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 3.24/1.00    inference(cnf_transformation,[],[f28])).
% 3.24/1.00  
% 3.24/1.00  fof(f108,plain,(
% 3.24/1.00    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 3.24/1.00    inference(equality_resolution,[],[f51])).
% 3.24/1.00  
% 3.24/1.00  fof(f55,plain,(
% 3.24/1.00    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) )),
% 3.24/1.00    inference(cnf_transformation,[],[f29])).
% 3.24/1.00  
% 3.24/1.00  fof(f12,axiom,(
% 3.24/1.00    ! [X0,X1,X2] : (r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) <=> (X0 != X2 & r2_hidden(X0,X1)))),
% 3.24/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.24/1.00  
% 3.24/1.00  fof(f37,plain,(
% 3.24/1.00    ! [X0,X1,X2] : ((r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) | (X0 = X2 | ~r2_hidden(X0,X1))) & ((X0 != X2 & r2_hidden(X0,X1)) | ~r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))))),
% 3.24/1.00    inference(nnf_transformation,[],[f12])).
% 3.24/1.00  
% 3.24/1.00  fof(f38,plain,(
% 3.24/1.00    ! [X0,X1,X2] : ((r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) | X0 = X2 | ~r2_hidden(X0,X1)) & ((X0 != X2 & r2_hidden(X0,X1)) | ~r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))))),
% 3.24/1.00    inference(flattening,[],[f37])).
% 3.24/1.00  
% 3.24/1.00  fof(f74,plain,(
% 3.24/1.00    ( ! [X2,X0,X1] : (X0 != X2 | ~r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))) )),
% 3.24/1.00    inference(cnf_transformation,[],[f38])).
% 3.24/1.00  
% 3.24/1.00  fof(f102,plain,(
% 3.24/1.00    ( ! [X2,X0,X1] : (X0 != X2 | ~r2_hidden(X0,k4_xboole_0(X1,k2_enumset1(X2,X2,X2,X2)))) )),
% 3.24/1.00    inference(definition_unfolding,[],[f74,f88])).
% 3.24/1.00  
% 3.24/1.00  fof(f117,plain,(
% 3.24/1.00    ( ! [X2,X1] : (~r2_hidden(X2,k4_xboole_0(X1,k2_enumset1(X2,X2,X2,X2)))) )),
% 3.24/1.00    inference(equality_resolution,[],[f102])).
% 3.24/1.00  
% 3.24/1.00  fof(f49,plain,(
% 3.24/1.00    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK0(X0,X1),X0)) )),
% 3.24/1.00    inference(cnf_transformation,[],[f26])).
% 3.24/1.00  
% 3.24/1.00  fof(f4,axiom,(
% 3.24/1.00    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 3.24/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.24/1.00  
% 3.24/1.00  fof(f18,plain,(
% 3.24/1.00    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 3.24/1.00    inference(ennf_transformation,[],[f4])).
% 3.24/1.00  
% 3.24/1.00  fof(f19,plain,(
% 3.24/1.00    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 3.24/1.00    inference(flattening,[],[f18])).
% 3.24/1.00  
% 3.24/1.00  fof(f56,plain,(
% 3.24/1.00    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)) )),
% 3.24/1.00    inference(cnf_transformation,[],[f19])).
% 3.24/1.00  
% 3.24/1.00  fof(f83,plain,(
% 3.24/1.00    ( ! [X0,X1] : (k1_setfam_1(X0) = X1 | ~r2_hidden(sK2(X0,X1),sK3(X0,X1)) | ~r2_hidden(sK2(X0,X1),X1) | k1_xboole_0 = X0) )),
% 3.24/1.00    inference(cnf_transformation,[],[f45])).
% 3.24/1.00  
% 3.24/1.00  fof(f13,axiom,(
% 3.24/1.00    ! [X0,X1] : (k4_xboole_0(X0,k1_tarski(X1)) = X0 <=> ~r2_hidden(X1,X0))),
% 3.24/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.24/1.00  
% 3.24/1.00  fof(f39,plain,(
% 3.24/1.00    ! [X0,X1] : ((k4_xboole_0(X0,k1_tarski(X1)) = X0 | r2_hidden(X1,X0)) & (~r2_hidden(X1,X0) | k4_xboole_0(X0,k1_tarski(X1)) != X0))),
% 3.24/1.00    inference(nnf_transformation,[],[f13])).
% 3.24/1.00  
% 3.24/1.00  fof(f77,plain,(
% 3.24/1.00    ( ! [X0,X1] : (k4_xboole_0(X0,k1_tarski(X1)) = X0 | r2_hidden(X1,X0)) )),
% 3.24/1.00    inference(cnf_transformation,[],[f39])).
% 3.24/1.00  
% 3.24/1.00  fof(f104,plain,(
% 3.24/1.00    ( ! [X0,X1] : (k4_xboole_0(X0,k2_enumset1(X1,X1,X1,X1)) = X0 | r2_hidden(X1,X0)) )),
% 3.24/1.00    inference(definition_unfolding,[],[f77,f88])).
% 3.24/1.00  
% 3.24/1.00  fof(f10,axiom,(
% 3.24/1.00    ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) <=> r2_hidden(X0,X1))),
% 3.24/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.24/1.00  
% 3.24/1.00  fof(f35,plain,(
% 3.24/1.00    ! [X0,X1] : ((r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) & (r2_hidden(X0,X1) | ~r1_tarski(k1_tarski(X0),X1)))),
% 3.24/1.00    inference(nnf_transformation,[],[f10])).
% 3.24/1.00  
% 3.24/1.00  fof(f69,plain,(
% 3.24/1.00    ( ! [X0,X1] : (r2_hidden(X0,X1) | ~r1_tarski(k1_tarski(X0),X1)) )),
% 3.24/1.00    inference(cnf_transformation,[],[f35])).
% 3.24/1.00  
% 3.24/1.00  fof(f98,plain,(
% 3.24/1.00    ( ! [X0,X1] : (r2_hidden(X0,X1) | ~r1_tarski(k2_enumset1(X0,X0,X0,X0),X1)) )),
% 3.24/1.00    inference(definition_unfolding,[],[f69,f88])).
% 3.24/1.00  
% 3.24/1.00  fof(f11,axiom,(
% 3.24/1.00    ! [X0,X1] : (k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0) <=> X0 != X1)),
% 3.24/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.24/1.00  
% 3.24/1.00  fof(f36,plain,(
% 3.24/1.00    ! [X0,X1] : ((k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0) | X0 = X1) & (X0 != X1 | k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) != k1_tarski(X0)))),
% 3.24/1.00    inference(nnf_transformation,[],[f11])).
% 3.24/1.00  
% 3.24/1.00  fof(f72,plain,(
% 3.24/1.00    ( ! [X0,X1] : (k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0) | X0 = X1) )),
% 3.24/1.00    inference(cnf_transformation,[],[f36])).
% 3.24/1.00  
% 3.24/1.00  fof(f99,plain,(
% 3.24/1.00    ( ! [X0,X1] : (k4_xboole_0(k2_enumset1(X0,X0,X0,X0),k2_enumset1(X1,X1,X1,X1)) = k2_enumset1(X0,X0,X0,X0) | X0 = X1) )),
% 3.24/1.00    inference(definition_unfolding,[],[f72,f88,f88,f88])).
% 3.24/1.00  
% 3.24/1.00  fof(f71,plain,(
% 3.24/1.00    ( ! [X0,X1] : (X0 != X1 | k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) != k1_tarski(X0)) )),
% 3.24/1.00    inference(cnf_transformation,[],[f36])).
% 3.24/1.00  
% 3.24/1.00  fof(f100,plain,(
% 3.24/1.00    ( ! [X0,X1] : (X0 != X1 | k4_xboole_0(k2_enumset1(X0,X0,X0,X0),k2_enumset1(X1,X1,X1,X1)) != k2_enumset1(X0,X0,X0,X0)) )),
% 3.24/1.00    inference(definition_unfolding,[],[f71,f88,f88,f88])).
% 3.24/1.00  
% 3.24/1.00  fof(f116,plain,(
% 3.24/1.00    ( ! [X1] : (k4_xboole_0(k2_enumset1(X1,X1,X1,X1),k2_enumset1(X1,X1,X1,X1)) != k2_enumset1(X1,X1,X1,X1)) )),
% 3.24/1.00    inference(equality_resolution,[],[f100])).
% 3.24/1.00  
% 3.24/1.00  fof(f76,plain,(
% 3.24/1.00    ( ! [X0,X1] : (~r2_hidden(X1,X0) | k4_xboole_0(X0,k1_tarski(X1)) != X0) )),
% 3.24/1.00    inference(cnf_transformation,[],[f39])).
% 3.24/1.00  
% 3.24/1.00  fof(f105,plain,(
% 3.24/1.00    ( ! [X0,X1] : (~r2_hidden(X1,X0) | k4_xboole_0(X0,k2_enumset1(X1,X1,X1,X1)) != X0) )),
% 3.24/1.00    inference(definition_unfolding,[],[f76,f88])).
% 3.24/1.00  
% 3.24/1.00  cnf(c_31,plain,
% 3.24/1.00      ( ~ r2_hidden(X0,X1)
% 3.24/1.00      | r2_hidden(sK2(X1,X2),X2)
% 3.24/1.00      | r2_hidden(sK2(X1,X2),X0)
% 3.24/1.00      | k1_setfam_1(X1) = X2
% 3.24/1.00      | k1_xboole_0 = X1 ),
% 3.24/1.00      inference(cnf_transformation,[],[f81]) ).
% 3.24/1.00  
% 3.24/1.00  cnf(c_35,negated_conjecture,
% 3.24/1.00      ( k1_setfam_1(k2_enumset1(sK5,sK5,sK5,sK5)) != sK5 ),
% 3.24/1.00      inference(cnf_transformation,[],[f106]) ).
% 3.24/1.00  
% 3.24/1.00  cnf(c_5912,plain,
% 3.24/1.00      ( ~ r2_hidden(X0,k2_enumset1(sK5,sK5,sK5,sK5))
% 3.24/1.00      | r2_hidden(sK2(k2_enumset1(sK5,sK5,sK5,sK5),sK5),X0)
% 3.24/1.00      | r2_hidden(sK2(k2_enumset1(sK5,sK5,sK5,sK5),sK5),sK5)
% 3.24/1.00      | k1_xboole_0 = k2_enumset1(sK5,sK5,sK5,sK5) ),
% 3.24/1.00      inference(resolution,[status(thm)],[c_31,c_35]) ).
% 3.24/1.00  
% 3.24/1.00  cnf(c_30,plain,
% 3.24/1.00      ( r2_hidden(sK3(X0,X1),X0)
% 3.24/1.00      | ~ r2_hidden(sK2(X0,X1),X1)
% 3.24/1.00      | k1_setfam_1(X0) = X1
% 3.24/1.00      | k1_xboole_0 = X0 ),
% 3.24/1.00      inference(cnf_transformation,[],[f82]) ).
% 3.24/1.00  
% 3.24/1.00  cnf(c_6144,plain,
% 3.24/1.00      ( ~ r2_hidden(X0,k2_enumset1(sK5,sK5,sK5,sK5))
% 3.24/1.00      | r2_hidden(sK3(k2_enumset1(sK5,sK5,sK5,sK5),sK5),k2_enumset1(sK5,sK5,sK5,sK5))
% 3.24/1.00      | r2_hidden(sK2(k2_enumset1(sK5,sK5,sK5,sK5),sK5),X0)
% 3.24/1.00      | k1_setfam_1(k2_enumset1(sK5,sK5,sK5,sK5)) = sK5
% 3.24/1.00      | k1_xboole_0 = k2_enumset1(sK5,sK5,sK5,sK5) ),
% 3.24/1.00      inference(resolution,[status(thm)],[c_5912,c_30]) ).
% 3.24/1.00  
% 3.24/1.00  cnf(c_6169,plain,
% 3.24/1.00      ( r2_hidden(sK2(k2_enumset1(sK5,sK5,sK5,sK5),sK5),sK5)
% 3.24/1.00      | ~ r2_hidden(sK5,k2_enumset1(sK5,sK5,sK5,sK5))
% 3.24/1.00      | k1_xboole_0 = k2_enumset1(sK5,sK5,sK5,sK5) ),
% 3.24/1.00      inference(factoring,[status(thm)],[c_5912]) ).
% 3.24/1.00  
% 3.24/1.00  cnf(c_14,plain,
% 3.24/1.00      ( r2_hidden(X0,k2_enumset1(X1,X1,X2,X0)) ),
% 3.24/1.00      inference(cnf_transformation,[],[f110]) ).
% 3.24/1.00  
% 3.24/1.00  cnf(c_1821,plain,
% 3.24/1.00      ( r2_hidden(sK5,k2_enumset1(X0,X0,X1,sK5)) ),
% 3.24/1.00      inference(instantiation,[status(thm)],[c_14]) ).
% 3.24/1.00  
% 3.24/1.00  cnf(c_4408,plain,
% 3.24/1.00      ( r2_hidden(sK5,k2_enumset1(sK5,sK5,sK5,sK5)) ),
% 3.24/1.00      inference(instantiation,[status(thm)],[c_1821]) ).
% 3.24/1.00  
% 3.24/1.00  cnf(c_6172,plain,
% 3.24/1.00      ( r2_hidden(sK2(k2_enumset1(sK5,sK5,sK5,sK5),sK5),sK5)
% 3.24/1.00      | k1_xboole_0 = k2_enumset1(sK5,sK5,sK5,sK5) ),
% 3.24/1.00      inference(global_propositional_subsumption,
% 3.24/1.00                [status(thm)],
% 3.24/1.00                [c_6169,c_4408]) ).
% 3.24/1.00  
% 3.24/1.00  cnf(c_6370,plain,
% 3.24/1.00      ( r2_hidden(sK3(k2_enumset1(sK5,sK5,sK5,sK5),sK5),k2_enumset1(sK5,sK5,sK5,sK5))
% 3.24/1.00      | k1_setfam_1(k2_enumset1(sK5,sK5,sK5,sK5)) = sK5
% 3.24/1.00      | k1_xboole_0 = k2_enumset1(sK5,sK5,sK5,sK5) ),
% 3.24/1.00      inference(resolution,[status(thm)],[c_6172,c_30]) ).
% 3.24/1.00  
% 3.24/1.00  cnf(c_6373,plain,
% 3.24/1.00      ( r2_hidden(sK3(k2_enumset1(sK5,sK5,sK5,sK5),sK5),k2_enumset1(sK5,sK5,sK5,sK5))
% 3.24/1.00      | k1_xboole_0 = k2_enumset1(sK5,sK5,sK5,sK5) ),
% 3.24/1.00      inference(global_propositional_subsumption,
% 3.24/1.00                [status(thm)],
% 3.24/1.00                [c_6144,c_35,c_6370]) ).
% 3.24/1.00  
% 3.24/1.00  cnf(c_17,plain,
% 3.24/1.00      ( ~ r2_hidden(X0,k2_enumset1(X1,X1,X2,X3))
% 3.24/1.00      | X0 = X1
% 3.24/1.00      | X0 = X2
% 3.24/1.00      | X0 = X3 ),
% 3.24/1.00      inference(cnf_transformation,[],[f115]) ).
% 3.24/1.00  
% 3.24/1.00  cnf(c_6389,plain,
% 3.24/1.00      ( sK3(k2_enumset1(sK5,sK5,sK5,sK5),sK5) = sK5
% 3.24/1.00      | k1_xboole_0 = k2_enumset1(sK5,sK5,sK5,sK5) ),
% 3.24/1.00      inference(resolution,[status(thm)],[c_6373,c_17]) ).
% 3.24/1.00  
% 3.24/1.00  cnf(c_674,plain,
% 3.24/1.00      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,X1) | X2 != X0 ),
% 3.24/1.00      theory(equality) ).
% 3.24/1.00  
% 3.24/1.00  cnf(c_6667,plain,
% 3.24/1.00      ( r1_tarski(sK3(k2_enumset1(sK5,sK5,sK5,sK5),sK5),X0)
% 3.24/1.00      | ~ r1_tarski(sK5,X0)
% 3.24/1.00      | k1_xboole_0 = k2_enumset1(sK5,sK5,sK5,sK5) ),
% 3.24/1.00      inference(resolution,[status(thm)],[c_6389,c_674]) ).
% 3.24/1.00  
% 3.24/1.00  cnf(c_673,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 3.24/1.00  
% 3.24/1.00  cnf(c_9,plain,
% 3.24/1.00      ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
% 3.24/1.00      inference(cnf_transformation,[],[f57]) ).
% 3.24/1.00  
% 3.24/1.00  cnf(c_2825,plain,
% 3.24/1.00      ( X0 != X1 | k4_xboole_0(X1,k1_xboole_0) = X0 ),
% 3.24/1.00      inference(resolution,[status(thm)],[c_673,c_9]) ).
% 3.24/1.00  
% 3.24/1.00  cnf(c_7,plain,
% 3.24/1.00      ( r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0 ),
% 3.24/1.00      inference(cnf_transformation,[],[f54]) ).
% 3.24/1.00  
% 3.24/1.00  cnf(c_3322,plain,
% 3.24/1.00      ( r1_tarski(X0,k1_xboole_0) | k1_xboole_0 != X0 ),
% 3.24/1.00      inference(resolution,[status(thm)],[c_2825,c_7]) ).
% 3.24/1.00  
% 3.24/1.00  cnf(c_28,plain,
% 3.24/1.00      ( k1_setfam_1(k1_xboole_0) = k1_xboole_0 ),
% 3.24/1.00      inference(cnf_transformation,[],[f121]) ).
% 3.24/1.00  
% 3.24/1.00  cnf(c_2829,plain,
% 3.24/1.00      ( X0 != k1_xboole_0 | k1_setfam_1(k1_xboole_0) = X0 ),
% 3.24/1.00      inference(resolution,[status(thm)],[c_673,c_28]) ).
% 3.24/1.00  
% 3.24/1.00  cnf(c_672,plain,( X0 = X0 ),theory(equality) ).
% 3.24/1.00  
% 3.24/1.00  cnf(c_2830,plain,
% 3.24/1.00      ( X0 != X1 | X1 = X0 ),
% 3.24/1.00      inference(resolution,[status(thm)],[c_673,c_672]) ).
% 3.24/1.00  
% 3.24/1.00  cnf(c_3150,plain,
% 3.24/1.00      ( X0 = k1_setfam_1(k1_xboole_0) | X0 != k1_xboole_0 ),
% 3.24/1.00      inference(resolution,[status(thm)],[c_2829,c_2830]) ).
% 3.24/1.00  
% 3.24/1.00  cnf(c_3544,plain,
% 3.24/1.00      ( r1_tarski(k1_setfam_1(k1_xboole_0),k1_xboole_0)
% 3.24/1.00      | k1_xboole_0 != k1_xboole_0 ),
% 3.24/1.00      inference(resolution,[status(thm)],[c_3322,c_3150]) ).
% 3.24/1.00  
% 3.24/1.00  cnf(c_3545,plain,
% 3.24/1.00      ( r1_tarski(k1_setfam_1(k1_xboole_0),k1_xboole_0) ),
% 3.24/1.00      inference(equality_resolution_simp,[status(thm)],[c_3544]) ).
% 3.24/1.00  
% 3.24/1.00  cnf(c_2,plain,
% 3.24/1.00      ( ~ r2_hidden(X0,X1) | r2_hidden(X0,X2) | ~ r1_tarski(X1,X2) ),
% 3.24/1.00      inference(cnf_transformation,[],[f48]) ).
% 3.24/1.00  
% 3.24/1.00  cnf(c_3551,plain,
% 3.24/1.00      ( ~ r2_hidden(X0,k1_setfam_1(k1_xboole_0))
% 3.24/1.00      | r2_hidden(X0,k1_xboole_0) ),
% 3.24/1.00      inference(resolution,[status(thm)],[c_3545,c_2]) ).
% 3.24/1.00  
% 3.24/1.00  cnf(c_5,plain,
% 3.24/1.00      ( r1_tarski(X0,X0) ),
% 3.24/1.00      inference(cnf_transformation,[],[f108]) ).
% 3.24/1.00  
% 3.24/1.00  cnf(c_1368,plain,
% 3.24/1.00      ( r1_tarski(X0,X0) = iProver_top ),
% 3.24/1.00      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 3.24/1.00  
% 3.24/1.00  cnf(c_6,plain,
% 3.24/1.00      ( ~ r1_tarski(X0,X1) | k4_xboole_0(X0,X1) = k1_xboole_0 ),
% 3.24/1.00      inference(cnf_transformation,[],[f55]) ).
% 3.24/1.00  
% 3.24/1.00  cnf(c_1367,plain,
% 3.24/1.00      ( k4_xboole_0(X0,X1) = k1_xboole_0
% 3.24/1.00      | r1_tarski(X0,X1) != iProver_top ),
% 3.24/1.00      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 3.24/1.00  
% 3.24/1.00  cnf(c_2137,plain,
% 3.24/1.00      ( k4_xboole_0(X0,X0) = k1_xboole_0 ),
% 3.24/1.00      inference(superposition,[status(thm)],[c_1368,c_1367]) ).
% 3.24/1.00  
% 3.24/1.00  cnf(c_23,plain,
% 3.24/1.00      ( ~ r2_hidden(X0,k4_xboole_0(X1,k2_enumset1(X0,X0,X0,X0))) ),
% 3.24/1.00      inference(cnf_transformation,[],[f117]) ).
% 3.24/1.00  
% 3.24/1.00  cnf(c_1353,plain,
% 3.24/1.00      ( r2_hidden(X0,k4_xboole_0(X1,k2_enumset1(X0,X0,X0,X0))) != iProver_top ),
% 3.24/1.00      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 3.24/1.00  
% 3.24/1.00  cnf(c_2328,plain,
% 3.24/1.00      ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
% 3.24/1.00      inference(superposition,[status(thm)],[c_2137,c_1353]) ).
% 3.24/1.00  
% 3.24/1.00  cnf(c_2331,plain,
% 3.24/1.00      ( ~ r2_hidden(X0,k1_xboole_0) ),
% 3.24/1.00      inference(predicate_to_equality_rev,[status(thm)],[c_2328]) ).
% 3.24/1.00  
% 3.24/1.00  cnf(c_3558,plain,
% 3.24/1.00      ( ~ r2_hidden(X0,k1_setfam_1(k1_xboole_0)) ),
% 3.24/1.00      inference(global_propositional_subsumption,
% 3.24/1.00                [status(thm)],
% 3.24/1.00                [c_3551,c_2331]) ).
% 3.24/1.00  
% 3.24/1.00  cnf(c_1,plain,
% 3.24/1.00      ( r2_hidden(sK0(X0,X1),X0) | r1_tarski(X0,X1) ),
% 3.24/1.00      inference(cnf_transformation,[],[f49]) ).
% 3.24/1.00  
% 3.24/1.00  cnf(c_3754,plain,
% 3.24/1.00      ( r1_tarski(k1_setfam_1(k1_xboole_0),X0) ),
% 3.24/1.00      inference(resolution,[status(thm)],[c_3558,c_1]) ).
% 3.24/1.00  
% 3.24/1.00  cnf(c_8,plain,
% 3.24/1.00      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X2) | r1_tarski(X0,X2) ),
% 3.24/1.00      inference(cnf_transformation,[],[f56]) ).
% 3.24/1.00  
% 3.24/1.00  cnf(c_3764,plain,
% 3.24/1.00      ( r1_tarski(X0,X1) | ~ r1_tarski(X0,k1_setfam_1(k1_xboole_0)) ),
% 3.24/1.00      inference(resolution,[status(thm)],[c_3754,c_8]) ).
% 3.24/1.00  
% 3.24/1.00  cnf(c_7222,plain,
% 3.24/1.00      ( r1_tarski(sK3(k2_enumset1(sK5,sK5,sK5,sK5),sK5),X0)
% 3.24/1.00      | ~ r1_tarski(sK5,k1_setfam_1(k1_xboole_0))
% 3.24/1.00      | k1_xboole_0 = k2_enumset1(sK5,sK5,sK5,sK5) ),
% 3.24/1.00      inference(resolution,[status(thm)],[c_6667,c_3764]) ).
% 3.24/1.00  
% 3.24/1.00  cnf(c_675,plain,
% 3.24/1.00      ( ~ r2_hidden(X0,X1) | r2_hidden(X2,X3) | X2 != X0 | X3 != X1 ),
% 3.24/1.00      theory(equality) ).
% 3.24/1.00  
% 3.24/1.00  cnf(c_6678,plain,
% 3.24/1.00      ( r2_hidden(X0,sK3(k2_enumset1(sK5,sK5,sK5,sK5),sK5))
% 3.24/1.00      | ~ r2_hidden(X1,sK5)
% 3.24/1.00      | X0 != X1
% 3.24/1.00      | k1_xboole_0 = k2_enumset1(sK5,sK5,sK5,sK5) ),
% 3.24/1.00      inference(resolution,[status(thm)],[c_6389,c_675]) ).
% 3.24/1.00  
% 3.24/1.00  cnf(c_7502,plain,
% 3.24/1.00      ( r2_hidden(X0,sK3(k2_enumset1(sK5,sK5,sK5,sK5),sK5))
% 3.24/1.00      | ~ r2_hidden(X0,sK5)
% 3.24/1.00      | k1_xboole_0 = k2_enumset1(sK5,sK5,sK5,sK5) ),
% 3.24/1.00      inference(resolution,[status(thm)],[c_6678,c_672]) ).
% 3.24/1.00  
% 3.24/1.00  cnf(c_29,plain,
% 3.24/1.00      ( ~ r2_hidden(sK2(X0,X1),X1)
% 3.24/1.00      | ~ r2_hidden(sK2(X0,X1),sK3(X0,X1))
% 3.24/1.00      | k1_setfam_1(X0) = X1
% 3.24/1.00      | k1_xboole_0 = X0 ),
% 3.24/1.00      inference(cnf_transformation,[],[f83]) ).
% 3.24/1.00  
% 3.24/1.00  cnf(c_8315,plain,
% 3.24/1.00      ( ~ r2_hidden(sK2(k2_enumset1(sK5,sK5,sK5,sK5),sK5),sK5)
% 3.24/1.00      | k1_setfam_1(k2_enumset1(sK5,sK5,sK5,sK5)) = sK5
% 3.24/1.00      | k1_xboole_0 = k2_enumset1(sK5,sK5,sK5,sK5) ),
% 3.24/1.00      inference(resolution,[status(thm)],[c_7502,c_29]) ).
% 3.24/1.00  
% 3.24/1.00  cnf(c_8321,plain,
% 3.24/1.00      ( k1_xboole_0 = k2_enumset1(sK5,sK5,sK5,sK5) ),
% 3.24/1.00      inference(global_propositional_subsumption,
% 3.24/1.00                [status(thm)],
% 3.24/1.00                [c_7222,c_35,c_4408,c_6169,c_8315]) ).
% 3.24/1.00  
% 3.24/1.00  cnf(c_8327,plain,
% 3.24/1.00      ( r1_tarski(k2_enumset1(sK5,sK5,sK5,sK5),k1_xboole_0) ),
% 3.24/1.00      inference(resolution,[status(thm)],[c_8321,c_3322]) ).
% 3.24/1.00  
% 3.24/1.00  cnf(c_6452,plain,
% 3.24/1.00      ( X0 != X1 | X0 = sK5 | sK5 != X1 ),
% 3.24/1.00      inference(instantiation,[status(thm)],[c_673]) ).
% 3.24/1.00  
% 3.24/1.00  cnf(c_6453,plain,
% 3.24/1.00      ( sK5 != k1_xboole_0
% 3.24/1.00      | k1_xboole_0 = sK5
% 3.24/1.00      | k1_xboole_0 != k1_xboole_0 ),
% 3.24/1.00      inference(instantiation,[status(thm)],[c_6452]) ).
% 3.24/1.00  
% 3.24/1.00  cnf(c_2201,plain,
% 3.24/1.00      ( ~ r2_hidden(X0,X1)
% 3.24/1.00      | r2_hidden(X2,k1_setfam_1(X3))
% 3.24/1.00      | X2 != X0
% 3.24/1.00      | k1_setfam_1(X3) != X1 ),
% 3.24/1.00      inference(instantiation,[status(thm)],[c_675]) ).
% 3.24/1.00  
% 3.24/1.00  cnf(c_3433,plain,
% 3.24/1.00      ( r2_hidden(X0,k1_setfam_1(X1))
% 3.24/1.00      | ~ r2_hidden(sK5,X2)
% 3.24/1.00      | X0 != sK5
% 3.24/1.00      | k1_setfam_1(X1) != X2 ),
% 3.24/1.00      inference(instantiation,[status(thm)],[c_2201]) ).
% 3.24/1.00  
% 3.24/1.00  cnf(c_3435,plain,
% 3.24/1.00      ( ~ r2_hidden(sK5,k1_xboole_0)
% 3.24/1.00      | r2_hidden(k1_xboole_0,k1_setfam_1(k1_xboole_0))
% 3.24/1.00      | k1_setfam_1(k1_xboole_0) != k1_xboole_0
% 3.24/1.00      | k1_xboole_0 != sK5 ),
% 3.24/1.00      inference(instantiation,[status(thm)],[c_3433]) ).
% 3.24/1.00  
% 3.24/1.00  cnf(c_2386,plain,
% 3.24/1.00      ( ~ r2_hidden(sK5,X0) | r2_hidden(sK5,X1) | ~ r1_tarski(X0,X1) ),
% 3.24/1.00      inference(instantiation,[status(thm)],[c_2]) ).
% 3.24/1.00  
% 3.24/1.00  cnf(c_3056,plain,
% 3.24/1.00      ( ~ r2_hidden(sK5,X0)
% 3.24/1.00      | r2_hidden(sK5,k2_enumset1(X1,X1,X2,X3))
% 3.24/1.00      | ~ r1_tarski(X0,k2_enumset1(X1,X1,X2,X3)) ),
% 3.24/1.00      inference(instantiation,[status(thm)],[c_2386]) ).
% 3.24/1.00  
% 3.24/1.00  cnf(c_3058,plain,
% 3.24/1.00      ( r2_hidden(sK5,k2_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0))
% 3.24/1.00      | ~ r2_hidden(sK5,k1_xboole_0)
% 3.24/1.00      | ~ r1_tarski(k1_xboole_0,k2_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0)) ),
% 3.24/1.00      inference(instantiation,[status(thm)],[c_3056]) ).
% 3.24/1.00  
% 3.24/1.00  cnf(c_25,plain,
% 3.24/1.00      ( r2_hidden(X0,X1)
% 3.24/1.00      | k4_xboole_0(X1,k2_enumset1(X0,X0,X0,X0)) = X1 ),
% 3.24/1.00      inference(cnf_transformation,[],[f104]) ).
% 3.24/1.00  
% 3.24/1.00  cnf(c_2553,plain,
% 3.24/1.00      ( r2_hidden(X0,k1_xboole_0)
% 3.24/1.00      | r1_tarski(k1_xboole_0,k2_enumset1(X0,X0,X0,X0)) ),
% 3.24/1.00      inference(resolution,[status(thm)],[c_25,c_7]) ).
% 3.24/1.00  
% 3.24/1.00  cnf(c_2555,plain,
% 3.24/1.00      ( r2_hidden(k1_xboole_0,k1_xboole_0)
% 3.24/1.00      | r1_tarski(k1_xboole_0,k2_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0)) ),
% 3.24/1.00      inference(instantiation,[status(thm)],[c_2553]) ).
% 3.24/1.00  
% 3.24/1.00  cnf(c_2172,plain,
% 3.24/1.00      ( r1_tarski(k1_setfam_1(k1_xboole_0),X0)
% 3.24/1.00      | ~ r1_tarski(k1_xboole_0,X0) ),
% 3.24/1.00      inference(resolution,[status(thm)],[c_674,c_28]) ).
% 3.24/1.00  
% 3.24/1.00  cnf(c_2342,plain,
% 3.24/1.00      ( r2_hidden(X0,X1)
% 3.24/1.00      | ~ r2_hidden(X0,k1_setfam_1(k1_xboole_0))
% 3.24/1.00      | ~ r1_tarski(k1_xboole_0,X1) ),
% 3.24/1.00      inference(resolution,[status(thm)],[c_2172,c_2]) ).
% 3.24/1.00  
% 3.24/1.00  cnf(c_2344,plain,
% 3.24/1.00      ( ~ r2_hidden(k1_xboole_0,k1_setfam_1(k1_xboole_0))
% 3.24/1.00      | r2_hidden(k1_xboole_0,k1_xboole_0)
% 3.24/1.00      | ~ r1_tarski(k1_xboole_0,k1_xboole_0) ),
% 3.24/1.00      inference(instantiation,[status(thm)],[c_2342]) ).
% 3.24/1.00  
% 3.24/1.00  cnf(c_2332,plain,
% 3.24/1.00      ( r2_hidden(k1_xboole_0,k1_xboole_0) != iProver_top ),
% 3.24/1.00      inference(instantiation,[status(thm)],[c_2328]) ).
% 3.24/1.00  
% 3.24/1.00  cnf(c_19,plain,
% 3.24/1.00      ( r2_hidden(X0,X1) | ~ r1_tarski(k2_enumset1(X0,X0,X0,X0),X1) ),
% 3.24/1.00      inference(cnf_transformation,[],[f98]) ).
% 3.24/1.00  
% 3.24/1.00  cnf(c_1958,plain,
% 3.24/1.00      ( r2_hidden(sK5,X0)
% 3.24/1.00      | ~ r1_tarski(k2_enumset1(sK5,sK5,sK5,sK5),X0) ),
% 3.24/1.00      inference(instantiation,[status(thm)],[c_19]) ).
% 3.24/1.00  
% 3.24/1.00  cnf(c_1960,plain,
% 3.24/1.00      ( r2_hidden(sK5,k1_xboole_0)
% 3.24/1.00      | ~ r1_tarski(k2_enumset1(sK5,sK5,sK5,sK5),k1_xboole_0) ),
% 3.24/1.00      inference(instantiation,[status(thm)],[c_1958]) ).
% 3.24/1.00  
% 3.24/1.00  cnf(c_1808,plain,
% 3.24/1.00      ( ~ r2_hidden(sK5,k2_enumset1(X0,X0,X1,X2))
% 3.24/1.00      | sK5 = X0
% 3.24/1.00      | sK5 = X1
% 3.24/1.00      | sK5 = X2 ),
% 3.24/1.00      inference(instantiation,[status(thm)],[c_17]) ).
% 3.24/1.00  
% 3.24/1.00  cnf(c_1810,plain,
% 3.24/1.00      ( ~ r2_hidden(sK5,k2_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0))
% 3.24/1.00      | sK5 = k1_xboole_0 ),
% 3.24/1.00      inference(instantiation,[status(thm)],[c_1808]) ).
% 3.24/1.00  
% 3.24/1.00  cnf(c_94,plain,
% 3.24/1.00      ( r1_tarski(k1_xboole_0,k1_xboole_0)
% 3.24/1.00      | k4_xboole_0(k1_xboole_0,k1_xboole_0) != k1_xboole_0 ),
% 3.24/1.00      inference(instantiation,[status(thm)],[c_7]) ).
% 3.24/1.00  
% 3.24/1.00  cnf(c_91,plain,
% 3.24/1.00      ( k4_xboole_0(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
% 3.24/1.00      inference(instantiation,[status(thm)],[c_9]) ).
% 3.24/1.00  
% 3.24/1.00  cnf(c_20,plain,
% 3.24/1.00      ( X0 = X1
% 3.24/1.00      | k4_xboole_0(k2_enumset1(X1,X1,X1,X1),k2_enumset1(X0,X0,X0,X0)) = k2_enumset1(X1,X1,X1,X1) ),
% 3.24/1.00      inference(cnf_transformation,[],[f99]) ).
% 3.24/1.00  
% 3.24/1.00  cnf(c_68,plain,
% 3.24/1.00      ( k4_xboole_0(k2_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k2_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0)) = k2_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0)
% 3.24/1.00      | k1_xboole_0 = k1_xboole_0 ),
% 3.24/1.00      inference(instantiation,[status(thm)],[c_20]) ).
% 3.24/1.00  
% 3.24/1.00  cnf(c_21,plain,
% 3.24/1.00      ( k4_xboole_0(k2_enumset1(X0,X0,X0,X0),k2_enumset1(X0,X0,X0,X0)) != k2_enumset1(X0,X0,X0,X0) ),
% 3.24/1.00      inference(cnf_transformation,[],[f116]) ).
% 3.24/1.00  
% 3.24/1.00  cnf(c_67,plain,
% 3.24/1.00      ( k4_xboole_0(k2_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k2_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0)) != k2_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0) ),
% 3.24/1.00      inference(instantiation,[status(thm)],[c_21]) ).
% 3.24/1.00  
% 3.24/1.00  cnf(c_55,plain,
% 3.24/1.00      ( k4_xboole_0(X0,k2_enumset1(X1,X1,X1,X1)) = X0
% 3.24/1.00      | r2_hidden(X1,X0) = iProver_top ),
% 3.24/1.00      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 3.24/1.00  
% 3.24/1.00  cnf(c_57,plain,
% 3.24/1.00      ( k4_xboole_0(k1_xboole_0,k2_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0)) = k1_xboole_0
% 3.24/1.00      | r2_hidden(k1_xboole_0,k1_xboole_0) = iProver_top ),
% 3.24/1.00      inference(instantiation,[status(thm)],[c_55]) ).
% 3.24/1.00  
% 3.24/1.00  cnf(c_26,plain,
% 3.24/1.00      ( ~ r2_hidden(X0,X1)
% 3.24/1.00      | k4_xboole_0(X1,k2_enumset1(X0,X0,X0,X0)) != X1 ),
% 3.24/1.00      inference(cnf_transformation,[],[f105]) ).
% 3.24/1.00  
% 3.24/1.00  cnf(c_53,plain,
% 3.24/1.00      ( ~ r2_hidden(k1_xboole_0,k1_xboole_0)
% 3.24/1.00      | k4_xboole_0(k1_xboole_0,k2_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0)) != k1_xboole_0 ),
% 3.24/1.00      inference(instantiation,[status(thm)],[c_26]) ).
% 3.24/1.00  
% 3.24/1.00  cnf(contradiction,plain,
% 3.24/1.00      ( $false ),
% 3.24/1.00      inference(minisat,
% 3.24/1.00                [status(thm)],
% 3.24/1.00                [c_8327,c_6453,c_3435,c_3058,c_2555,c_2344,c_2332,c_1960,
% 3.24/1.00                 c_1810,c_94,c_91,c_68,c_67,c_57,c_53,c_28]) ).
% 3.24/1.00  
% 3.24/1.00  
% 3.24/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 3.24/1.00  
% 3.24/1.00  ------                               Statistics
% 3.24/1.00  
% 3.24/1.00  ------ Selected
% 3.24/1.00  
% 3.24/1.00  total_time:                             0.242
% 3.24/1.00  
%------------------------------------------------------------------------------
