%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:41:38 EST 2020

% Result     : Theorem 3.18s
% Output     : CNFRefutation 3.18s
% Verified   : 
% Statistics : Number of formulae       :  106 ( 625 expanded)
%              Number of clauses        :   43 ( 115 expanded)
%              Number of leaves         :   17 ( 185 expanded)
%              Depth                    :   19
%              Number of atoms          :  385 (3106 expanded)
%              Number of equality atoms :  249 (1617 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal clause size      :   20 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f9,axiom,(
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

fof(f13,plain,(
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
    inference(ennf_transformation,[],[f9])).

fof(f25,plain,(
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
    inference(nnf_transformation,[],[f13])).

fof(f26,plain,(
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
    inference(rectify,[],[f25])).

fof(f29,plain,(
    ! [X5,X0] :
      ( ? [X6] :
          ( ~ r2_hidden(X5,X6)
          & r2_hidden(X6,X0) )
     => ( ~ r2_hidden(X5,sK3(X0,X5))
        & r2_hidden(sK3(X0,X5),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r2_hidden(X2,X3)
          & r2_hidden(X3,X0) )
     => ( ~ r2_hidden(X2,sK2(X0,X1))
        & r2_hidden(sK2(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,(
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
              ( ~ r2_hidden(sK1(X0,X1),X3)
              & r2_hidden(X3,X0) )
          | ~ r2_hidden(sK1(X0,X1),X1) )
        & ( ! [X4] :
              ( r2_hidden(sK1(X0,X1),X4)
              | ~ r2_hidden(X4,X0) )
          | r2_hidden(sK1(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( ( ( k1_setfam_1(X0) = X1
            | k1_xboole_0 != X1 )
          & ( k1_xboole_0 = X1
            | k1_setfam_1(X0) != X1 ) )
        | k1_xboole_0 != X0 )
      & ( ( ( k1_setfam_1(X0) = X1
            | ( ( ( ~ r2_hidden(sK1(X0,X1),sK2(X0,X1))
                  & r2_hidden(sK2(X0,X1),X0) )
                | ~ r2_hidden(sK1(X0,X1),X1) )
              & ( ! [X4] :
                    ( r2_hidden(sK1(X0,X1),X4)
                    | ~ r2_hidden(X4,X0) )
                | r2_hidden(sK1(X0,X1),X1) ) ) )
          & ( ! [X5] :
                ( ( r2_hidden(X5,X1)
                  | ( ~ r2_hidden(X5,sK3(X0,X5))
                    & r2_hidden(sK3(X0,X5),X0) ) )
                & ( ! [X7] :
                      ( r2_hidden(X5,X7)
                      | ~ r2_hidden(X7,X0) )
                  | ~ r2_hidden(X5,X1) ) )
            | k1_setfam_1(X0) != X1 ) )
        | k1_xboole_0 = X0 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f26,f29,f28,f27])).

fof(f54,plain,(
    ! [X4,X0,X1] :
      ( k1_setfam_1(X0) = X1
      | r2_hidden(sK1(X0,X1),X4)
      | ~ r2_hidden(X4,X0)
      | r2_hidden(sK1(X0,X1),X1)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f30])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( k2_tarski(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( X1 = X3
            | X0 = X3 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
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
    inference(nnf_transformation,[],[f1])).

fof(f16,plain,(
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
    inference(flattening,[],[f15])).

fof(f17,plain,(
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
    inference(rectify,[],[f16])).

fof(f18,plain,(
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

fof(f19,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f17,f18])).

fof(f35,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | X1 != X4
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f19])).

fof(f3,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f3])).

fof(f4,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f4])).

fof(f60,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f40,f41])).

fof(f65,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | X1 != X4
      | k2_enumset1(X0,X0,X0,X1) != X2 ) ),
    inference(definition_unfolding,[],[f35,f60])).

fof(f78,plain,(
    ! [X4,X2,X0] :
      ( r2_hidden(X4,X2)
      | k2_enumset1(X0,X0,X0,X4) != X2 ) ),
    inference(equality_resolution,[],[f65])).

fof(f79,plain,(
    ! [X4,X0] : r2_hidden(X4,k2_enumset1(X0,X0,X0,X4)) ),
    inference(equality_resolution,[],[f78])).

fof(f55,plain,(
    ! [X0,X1] :
      ( k1_setfam_1(X0) = X1
      | r2_hidden(sK2(X0,X1),X0)
      | ~ r2_hidden(sK1(X0,X1),X1)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f30])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1))
    <=> X0 != X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1))
        | X0 = X1 )
      & ( X0 != X1
        | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) ) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f46,plain,(
    ! [X0,X1] :
      ( k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1))
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f22])).

fof(f2,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f61,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f39,f60])).

fof(f71,plain,(
    ! [X0,X1] :
      ( k2_enumset1(X0,X0,X0,X0) = k4_xboole_0(k2_enumset1(X0,X0,X0,X0),k2_enumset1(X1,X1,X1,X1))
      | X0 = X1 ) ),
    inference(definition_unfolding,[],[f46,f61,f61,f61])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))
    <=> ( X0 != X2
        & r2_hidden(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))
        | X0 = X2
        | ~ r2_hidden(X0,X1) )
      & ( ( X0 != X2
          & r2_hidden(X0,X1) )
        | ~ r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) ) ) ),
    inference(nnf_transformation,[],[f7])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))
        | X0 = X2
        | ~ r2_hidden(X0,X1) )
      & ( ( X0 != X2
          & r2_hidden(X0,X1) )
        | ~ r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) ) ) ),
    inference(flattening,[],[f23])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( X0 != X2
      | ~ r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f74,plain,(
    ! [X2,X0,X1] :
      ( X0 != X2
      | ~ r2_hidden(X0,k4_xboole_0(X1,k2_enumset1(X2,X2,X2,X2))) ) ),
    inference(definition_unfolding,[],[f48,f61])).

fof(f86,plain,(
    ! [X2,X1] : ~ r2_hidden(X2,k4_xboole_0(X1,k2_enumset1(X2,X2,X2,X2))) ),
    inference(equality_resolution,[],[f74])).

fof(f56,plain,(
    ! [X0,X1] :
      ( k1_setfam_1(X0) = X1
      | ~ r2_hidden(sK1(X0,X1),sK2(X0,X1))
      | ~ r2_hidden(sK1(X0,X1),X1)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f30])).

fof(f34,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | X0 != X4
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f19])).

fof(f66,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | X0 != X4
      | k2_enumset1(X0,X0,X0,X1) != X2 ) ),
    inference(definition_unfolding,[],[f34,f60])).

fof(f80,plain,(
    ! [X4,X2,X1] :
      ( r2_hidden(X4,X2)
      | k2_enumset1(X4,X4,X4,X1) != X2 ) ),
    inference(equality_resolution,[],[f66])).

fof(f81,plain,(
    ! [X4,X1] : r2_hidden(X4,k2_enumset1(X4,X4,X4,X1)) ),
    inference(equality_resolution,[],[f80])).

fof(f10,conjecture,(
    ! [X0] : k1_setfam_1(k1_tarski(X0)) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f11,negated_conjecture,(
    ~ ! [X0] : k1_setfam_1(k1_tarski(X0)) = X0 ),
    inference(negated_conjecture,[],[f10])).

fof(f14,plain,(
    ? [X0] : k1_setfam_1(k1_tarski(X0)) != X0 ),
    inference(ennf_transformation,[],[f11])).

fof(f31,plain,
    ( ? [X0] : k1_setfam_1(k1_tarski(X0)) != X0
   => k1_setfam_1(k1_tarski(sK4)) != sK4 ),
    introduced(choice_axiom,[])).

fof(f32,plain,(
    k1_setfam_1(k1_tarski(sK4)) != sK4 ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f14,f31])).

fof(f59,plain,(
    k1_setfam_1(k1_tarski(sK4)) != sK4 ),
    inference(cnf_transformation,[],[f32])).

fof(f77,plain,(
    k1_setfam_1(k2_enumset1(sK4,sK4,sK4,sK4)) != sK4 ),
    inference(definition_unfolding,[],[f59,f61])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),k1_tarski(X1))
     => X0 = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(k1_tarski(X0),k1_tarski(X1)) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f50,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(k1_tarski(X0),k1_tarski(X1)) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f76,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(k2_enumset1(X0,X0,X0,X0),k2_enumset1(X1,X1,X1,X1)) ) ),
    inference(definition_unfolding,[],[f50,f61,f61])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,k1_tarski(X1))
    <=> ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,k1_tarski(X1))
        | ( k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k1_tarski(X1)) ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,k1_tarski(X1))
        | ( k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k1_tarski(X1)) ) ) ),
    inference(flattening,[],[f20])).

fof(f43,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k1_tarski(X1))
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f21])).

fof(f69,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k2_enumset1(X1,X1,X1,X1))
      | k1_xboole_0 != X0 ) ),
    inference(definition_unfolding,[],[f43,f61])).

fof(f84,plain,(
    ! [X1] : r1_tarski(k1_xboole_0,k2_enumset1(X1,X1,X1,X1)) ),
    inference(equality_resolution,[],[f69])).

fof(f57,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = X1
      | k1_setfam_1(X0) != X1
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f30])).

fof(f89,plain,(
    ! [X0] :
      ( k1_xboole_0 = k1_setfam_1(X0)
      | k1_xboole_0 != X0 ) ),
    inference(equality_resolution,[],[f57])).

fof(f90,plain,(
    k1_xboole_0 = k1_setfam_1(k1_xboole_0) ),
    inference(equality_resolution,[],[f89])).

cnf(c_19,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(sK1(X1,X2),X2)
    | r2_hidden(sK1(X1,X2),X0)
    | k1_setfam_1(X1) = X2
    | k1_xboole_0 = X1 ),
    inference(cnf_transformation,[],[f54])).

cnf(c_720,plain,
    ( k1_setfam_1(X0) = X1
    | k1_xboole_0 = X0
    | r2_hidden(X2,X0) != iProver_top
    | r2_hidden(sK1(X0,X1),X1) = iProver_top
    | r2_hidden(sK1(X0,X1),X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_3,plain,
    ( r2_hidden(X0,k2_enumset1(X1,X1,X1,X0)) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_732,plain,
    ( r2_hidden(X0,k2_enumset1(X1,X1,X1,X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_18,plain,
    ( r2_hidden(sK2(X0,X1),X0)
    | ~ r2_hidden(sK1(X0,X1),X1)
    | k1_setfam_1(X0) = X1
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f55])).

cnf(c_721,plain,
    ( k1_setfam_1(X0) = X1
    | k1_xboole_0 = X0
    | r2_hidden(sK2(X0,X1),X0) = iProver_top
    | r2_hidden(sK1(X0,X1),X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_1993,plain,
    ( k1_setfam_1(X0) = X1
    | k1_xboole_0 = X0
    | r2_hidden(X1,X0) != iProver_top
    | r2_hidden(sK2(X0,X1),X0) = iProver_top
    | r2_hidden(sK1(X0,X1),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_720,c_721])).

cnf(c_2010,plain,
    ( k1_setfam_1(X0) = X1
    | k1_xboole_0 = X0
    | r2_hidden(X1,X0) != iProver_top
    | r2_hidden(sK2(X0,X1),X0) = iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_1993,c_721])).

cnf(c_9,plain,
    ( X0 = X1
    | k4_xboole_0(k2_enumset1(X1,X1,X1,X1),k2_enumset1(X0,X0,X0,X0)) = k2_enumset1(X1,X1,X1,X1) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_12,plain,
    ( ~ r2_hidden(X0,k4_xboole_0(X1,k2_enumset1(X0,X0,X0,X0))) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_725,plain,
    ( r2_hidden(X0,k4_xboole_0(X1,k2_enumset1(X0,X0,X0,X0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_1135,plain,
    ( X0 = X1
    | r2_hidden(X1,k2_enumset1(X0,X0,X0,X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_9,c_725])).

cnf(c_2451,plain,
    ( k2_enumset1(X0,X0,X0,X0) = k1_xboole_0
    | sK2(k2_enumset1(X0,X0,X0,X0),X1) = X0
    | k1_setfam_1(k2_enumset1(X0,X0,X0,X0)) = X1
    | r2_hidden(X1,k2_enumset1(X0,X0,X0,X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2010,c_1135])).

cnf(c_5647,plain,
    ( k2_enumset1(X0,X0,X0,X0) = k1_xboole_0
    | sK2(k2_enumset1(X0,X0,X0,X0),X0) = X0
    | k1_setfam_1(k2_enumset1(X0,X0,X0,X0)) = X0 ),
    inference(superposition,[status(thm)],[c_732,c_2451])).

cnf(c_17,plain,
    ( ~ r2_hidden(sK1(X0,X1),X1)
    | ~ r2_hidden(sK1(X0,X1),sK2(X0,X1))
    | k1_setfam_1(X0) = X1
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f56])).

cnf(c_722,plain,
    ( k1_setfam_1(X0) = X1
    | k1_xboole_0 = X0
    | r2_hidden(sK1(X0,X1),X1) != iProver_top
    | r2_hidden(sK1(X0,X1),sK2(X0,X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_5878,plain,
    ( k2_enumset1(X0,X0,X0,X0) = k1_xboole_0
    | k1_setfam_1(k2_enumset1(X0,X0,X0,X0)) = X0
    | r2_hidden(sK1(k2_enumset1(X0,X0,X0,X0),X0),X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_5647,c_722])).

cnf(c_6108,plain,
    ( k2_enumset1(X0,X0,X0,X0) = k1_xboole_0
    | k1_setfam_1(k2_enumset1(X0,X0,X0,X0)) = X0
    | r2_hidden(X0,k2_enumset1(X0,X0,X0,X0)) != iProver_top
    | r2_hidden(sK1(k2_enumset1(X0,X0,X0,X0),X0),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_720,c_5878])).

cnf(c_6164,plain,
    ( k2_enumset1(X0,X0,X0,X0) = k1_xboole_0
    | k1_setfam_1(k2_enumset1(X0,X0,X0,X0)) = X0
    | r2_hidden(X0,k2_enumset1(X0,X0,X0,X0)) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_6108,c_5878])).

cnf(c_4,plain,
    ( r2_hidden(X0,k2_enumset1(X0,X0,X0,X1)) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_731,plain,
    ( r2_hidden(X0,k2_enumset1(X0,X0,X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_6750,plain,
    ( k2_enumset1(X0,X0,X0,X0) = k1_xboole_0
    | k1_setfam_1(k2_enumset1(X0,X0,X0,X0)) = X0 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_6164,c_731])).

cnf(c_23,negated_conjecture,
    ( k1_setfam_1(k2_enumset1(sK4,sK4,sK4,sK4)) != sK4 ),
    inference(cnf_transformation,[],[f77])).

cnf(c_6756,plain,
    ( k2_enumset1(sK4,sK4,sK4,sK4) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_6750,c_23])).

cnf(c_14,plain,
    ( ~ r1_tarski(k2_enumset1(X0,X0,X0,X0),k2_enumset1(X1,X1,X1,X1))
    | X1 = X0 ),
    inference(cnf_transformation,[],[f76])).

cnf(c_723,plain,
    ( X0 = X1
    | r1_tarski(k2_enumset1(X1,X1,X1,X1),k2_enumset1(X0,X0,X0,X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_6962,plain,
    ( sK4 = X0
    | r1_tarski(k1_xboole_0,k2_enumset1(X0,X0,X0,X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_6756,c_723])).

cnf(c_7116,plain,
    ( sK4 = k1_xboole_0
    | r1_tarski(k1_xboole_0,k2_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_6962])).

cnf(c_408,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_964,plain,
    ( X0 != X1
    | sK4 != X1
    | sK4 = X0 ),
    inference(instantiation,[status(thm)],[c_408])).

cnf(c_3188,plain,
    ( k1_setfam_1(X0) != X1
    | sK4 != X1
    | sK4 = k1_setfam_1(X0) ),
    inference(instantiation,[status(thm)],[c_964])).

cnf(c_3189,plain,
    ( k1_setfam_1(k1_xboole_0) != k1_xboole_0
    | sK4 = k1_setfam_1(k1_xboole_0)
    | sK4 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_3188])).

cnf(c_413,plain,
    ( X0 != X1
    | k1_setfam_1(X0) = k1_setfam_1(X1) ),
    theory(equality)).

cnf(c_1115,plain,
    ( k2_enumset1(sK4,sK4,sK4,sK4) != X0
    | k1_setfam_1(k2_enumset1(sK4,sK4,sK4,sK4)) = k1_setfam_1(X0) ),
    inference(instantiation,[status(thm)],[c_413])).

cnf(c_1117,plain,
    ( k2_enumset1(sK4,sK4,sK4,sK4) != k1_xboole_0
    | k1_setfam_1(k2_enumset1(sK4,sK4,sK4,sK4)) = k1_setfam_1(k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_1115])).

cnf(c_890,plain,
    ( k1_setfam_1(k2_enumset1(sK4,sK4,sK4,sK4)) != X0
    | k1_setfam_1(k2_enumset1(sK4,sK4,sK4,sK4)) = sK4
    | sK4 != X0 ),
    inference(instantiation,[status(thm)],[c_408])).

cnf(c_1114,plain,
    ( k1_setfam_1(k2_enumset1(sK4,sK4,sK4,sK4)) != k1_setfam_1(X0)
    | k1_setfam_1(k2_enumset1(sK4,sK4,sK4,sK4)) = sK4
    | sK4 != k1_setfam_1(X0) ),
    inference(instantiation,[status(thm)],[c_890])).

cnf(c_1116,plain,
    ( k1_setfam_1(k2_enumset1(sK4,sK4,sK4,sK4)) != k1_setfam_1(k1_xboole_0)
    | k1_setfam_1(k2_enumset1(sK4,sK4,sK4,sK4)) = sK4
    | sK4 != k1_setfam_1(k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_1114])).

cnf(c_7,plain,
    ( r1_tarski(k1_xboole_0,k2_enumset1(X0,X0,X0,X0)) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_57,plain,
    ( r1_tarski(k1_xboole_0,k2_enumset1(X0,X0,X0,X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_59,plain,
    ( r1_tarski(k1_xboole_0,k2_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_57])).

cnf(c_16,plain,
    ( k1_setfam_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f90])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_7116,c_6756,c_3189,c_1117,c_1116,c_59,c_16,c_23])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.14/0.35  % Computer   : n023.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 14:30:36 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running in FOF mode
% 3.18/1.01  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.18/1.01  
% 3.18/1.01  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.18/1.01  
% 3.18/1.01  ------  iProver source info
% 3.18/1.01  
% 3.18/1.01  git: date: 2020-06-30 10:37:57 +0100
% 3.18/1.01  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.18/1.01  git: non_committed_changes: false
% 3.18/1.01  git: last_make_outside_of_git: false
% 3.18/1.01  
% 3.18/1.01  ------ 
% 3.18/1.01  
% 3.18/1.01  ------ Input Options
% 3.18/1.01  
% 3.18/1.01  --out_options                           all
% 3.18/1.01  --tptp_safe_out                         true
% 3.18/1.01  --problem_path                          ""
% 3.18/1.01  --include_path                          ""
% 3.18/1.01  --clausifier                            res/vclausify_rel
% 3.18/1.01  --clausifier_options                    --mode clausify
% 3.18/1.01  --stdin                                 false
% 3.18/1.01  --stats_out                             all
% 3.18/1.01  
% 3.18/1.01  ------ General Options
% 3.18/1.01  
% 3.18/1.01  --fof                                   false
% 3.18/1.01  --time_out_real                         305.
% 3.18/1.01  --time_out_virtual                      -1.
% 3.18/1.01  --symbol_type_check                     false
% 3.18/1.01  --clausify_out                          false
% 3.18/1.01  --sig_cnt_out                           false
% 3.18/1.01  --trig_cnt_out                          false
% 3.18/1.01  --trig_cnt_out_tolerance                1.
% 3.18/1.01  --trig_cnt_out_sk_spl                   false
% 3.18/1.01  --abstr_cl_out                          false
% 3.18/1.01  
% 3.18/1.01  ------ Global Options
% 3.18/1.01  
% 3.18/1.01  --schedule                              default
% 3.18/1.01  --add_important_lit                     false
% 3.18/1.01  --prop_solver_per_cl                    1000
% 3.18/1.01  --min_unsat_core                        false
% 3.18/1.01  --soft_assumptions                      false
% 3.18/1.01  --soft_lemma_size                       3
% 3.18/1.01  --prop_impl_unit_size                   0
% 3.18/1.01  --prop_impl_unit                        []
% 3.18/1.01  --share_sel_clauses                     true
% 3.18/1.01  --reset_solvers                         false
% 3.18/1.01  --bc_imp_inh                            [conj_cone]
% 3.18/1.01  --conj_cone_tolerance                   3.
% 3.18/1.01  --extra_neg_conj                        none
% 3.18/1.01  --large_theory_mode                     true
% 3.18/1.01  --prolific_symb_bound                   200
% 3.18/1.01  --lt_threshold                          2000
% 3.18/1.01  --clause_weak_htbl                      true
% 3.18/1.01  --gc_record_bc_elim                     false
% 3.18/1.01  
% 3.18/1.01  ------ Preprocessing Options
% 3.18/1.01  
% 3.18/1.01  --preprocessing_flag                    true
% 3.18/1.01  --time_out_prep_mult                    0.1
% 3.18/1.01  --splitting_mode                        input
% 3.18/1.01  --splitting_grd                         true
% 3.18/1.01  --splitting_cvd                         false
% 3.18/1.01  --splitting_cvd_svl                     false
% 3.18/1.01  --splitting_nvd                         32
% 3.18/1.01  --sub_typing                            true
% 3.18/1.01  --prep_gs_sim                           true
% 3.18/1.01  --prep_unflatten                        true
% 3.18/1.01  --prep_res_sim                          true
% 3.18/1.01  --prep_upred                            true
% 3.18/1.01  --prep_sem_filter                       exhaustive
% 3.18/1.01  --prep_sem_filter_out                   false
% 3.18/1.01  --pred_elim                             true
% 3.18/1.01  --res_sim_input                         true
% 3.18/1.01  --eq_ax_congr_red                       true
% 3.18/1.01  --pure_diseq_elim                       true
% 3.18/1.01  --brand_transform                       false
% 3.18/1.01  --non_eq_to_eq                          false
% 3.18/1.01  --prep_def_merge                        true
% 3.18/1.01  --prep_def_merge_prop_impl              false
% 3.18/1.01  --prep_def_merge_mbd                    true
% 3.18/1.01  --prep_def_merge_tr_red                 false
% 3.18/1.01  --prep_def_merge_tr_cl                  false
% 3.18/1.01  --smt_preprocessing                     true
% 3.18/1.01  --smt_ac_axioms                         fast
% 3.18/1.01  --preprocessed_out                      false
% 3.18/1.01  --preprocessed_stats                    false
% 3.18/1.01  
% 3.18/1.01  ------ Abstraction refinement Options
% 3.18/1.01  
% 3.18/1.01  --abstr_ref                             []
% 3.18/1.01  --abstr_ref_prep                        false
% 3.18/1.01  --abstr_ref_until_sat                   false
% 3.18/1.01  --abstr_ref_sig_restrict                funpre
% 3.18/1.01  --abstr_ref_af_restrict_to_split_sk     false
% 3.18/1.01  --abstr_ref_under                       []
% 3.18/1.01  
% 3.18/1.01  ------ SAT Options
% 3.18/1.01  
% 3.18/1.01  --sat_mode                              false
% 3.18/1.01  --sat_fm_restart_options                ""
% 3.18/1.01  --sat_gr_def                            false
% 3.18/1.01  --sat_epr_types                         true
% 3.18/1.01  --sat_non_cyclic_types                  false
% 3.18/1.01  --sat_finite_models                     false
% 3.18/1.01  --sat_fm_lemmas                         false
% 3.18/1.01  --sat_fm_prep                           false
% 3.18/1.01  --sat_fm_uc_incr                        true
% 3.18/1.01  --sat_out_model                         small
% 3.18/1.01  --sat_out_clauses                       false
% 3.18/1.01  
% 3.18/1.01  ------ QBF Options
% 3.18/1.01  
% 3.18/1.01  --qbf_mode                              false
% 3.18/1.01  --qbf_elim_univ                         false
% 3.18/1.01  --qbf_dom_inst                          none
% 3.18/1.01  --qbf_dom_pre_inst                      false
% 3.18/1.01  --qbf_sk_in                             false
% 3.18/1.01  --qbf_pred_elim                         true
% 3.18/1.01  --qbf_split                             512
% 3.18/1.01  
% 3.18/1.01  ------ BMC1 Options
% 3.18/1.01  
% 3.18/1.01  --bmc1_incremental                      false
% 3.18/1.01  --bmc1_axioms                           reachable_all
% 3.18/1.01  --bmc1_min_bound                        0
% 3.18/1.01  --bmc1_max_bound                        -1
% 3.18/1.01  --bmc1_max_bound_default                -1
% 3.18/1.01  --bmc1_symbol_reachability              true
% 3.18/1.01  --bmc1_property_lemmas                  false
% 3.18/1.01  --bmc1_k_induction                      false
% 3.18/1.01  --bmc1_non_equiv_states                 false
% 3.18/1.01  --bmc1_deadlock                         false
% 3.18/1.01  --bmc1_ucm                              false
% 3.18/1.01  --bmc1_add_unsat_core                   none
% 3.18/1.01  --bmc1_unsat_core_children              false
% 3.18/1.01  --bmc1_unsat_core_extrapolate_axioms    false
% 3.18/1.01  --bmc1_out_stat                         full
% 3.18/1.01  --bmc1_ground_init                      false
% 3.18/1.01  --bmc1_pre_inst_next_state              false
% 3.18/1.01  --bmc1_pre_inst_state                   false
% 3.18/1.01  --bmc1_pre_inst_reach_state             false
% 3.18/1.01  --bmc1_out_unsat_core                   false
% 3.18/1.01  --bmc1_aig_witness_out                  false
% 3.18/1.01  --bmc1_verbose                          false
% 3.18/1.01  --bmc1_dump_clauses_tptp                false
% 3.18/1.01  --bmc1_dump_unsat_core_tptp             false
% 3.18/1.01  --bmc1_dump_file                        -
% 3.18/1.01  --bmc1_ucm_expand_uc_limit              128
% 3.18/1.01  --bmc1_ucm_n_expand_iterations          6
% 3.18/1.01  --bmc1_ucm_extend_mode                  1
% 3.18/1.01  --bmc1_ucm_init_mode                    2
% 3.18/1.01  --bmc1_ucm_cone_mode                    none
% 3.18/1.01  --bmc1_ucm_reduced_relation_type        0
% 3.18/1.01  --bmc1_ucm_relax_model                  4
% 3.18/1.01  --bmc1_ucm_full_tr_after_sat            true
% 3.18/1.01  --bmc1_ucm_expand_neg_assumptions       false
% 3.18/1.01  --bmc1_ucm_layered_model                none
% 3.18/1.01  --bmc1_ucm_max_lemma_size               10
% 3.18/1.01  
% 3.18/1.01  ------ AIG Options
% 3.18/1.01  
% 3.18/1.01  --aig_mode                              false
% 3.18/1.01  
% 3.18/1.01  ------ Instantiation Options
% 3.18/1.01  
% 3.18/1.01  --instantiation_flag                    true
% 3.18/1.01  --inst_sos_flag                         false
% 3.18/1.01  --inst_sos_phase                        true
% 3.18/1.01  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.18/1.01  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.18/1.01  --inst_lit_sel_side                     num_symb
% 3.18/1.01  --inst_solver_per_active                1400
% 3.18/1.01  --inst_solver_calls_frac                1.
% 3.18/1.01  --inst_passive_queue_type               priority_queues
% 3.18/1.01  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.18/1.01  --inst_passive_queues_freq              [25;2]
% 3.18/1.01  --inst_dismatching                      true
% 3.18/1.01  --inst_eager_unprocessed_to_passive     true
% 3.18/1.01  --inst_prop_sim_given                   true
% 3.18/1.01  --inst_prop_sim_new                     false
% 3.18/1.01  --inst_subs_new                         false
% 3.18/1.01  --inst_eq_res_simp                      false
% 3.18/1.01  --inst_subs_given                       false
% 3.18/1.01  --inst_orphan_elimination               true
% 3.18/1.01  --inst_learning_loop_flag               true
% 3.18/1.01  --inst_learning_start                   3000
% 3.18/1.01  --inst_learning_factor                  2
% 3.18/1.01  --inst_start_prop_sim_after_learn       3
% 3.18/1.01  --inst_sel_renew                        solver
% 3.18/1.01  --inst_lit_activity_flag                true
% 3.18/1.01  --inst_restr_to_given                   false
% 3.18/1.01  --inst_activity_threshold               500
% 3.18/1.01  --inst_out_proof                        true
% 3.18/1.01  
% 3.18/1.01  ------ Resolution Options
% 3.18/1.01  
% 3.18/1.01  --resolution_flag                       true
% 3.18/1.01  --res_lit_sel                           adaptive
% 3.18/1.01  --res_lit_sel_side                      none
% 3.18/1.01  --res_ordering                          kbo
% 3.18/1.01  --res_to_prop_solver                    active
% 3.18/1.01  --res_prop_simpl_new                    false
% 3.18/1.01  --res_prop_simpl_given                  true
% 3.18/1.01  --res_passive_queue_type                priority_queues
% 3.18/1.01  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.18/1.01  --res_passive_queues_freq               [15;5]
% 3.18/1.01  --res_forward_subs                      full
% 3.18/1.01  --res_backward_subs                     full
% 3.18/1.01  --res_forward_subs_resolution           true
% 3.18/1.01  --res_backward_subs_resolution          true
% 3.18/1.01  --res_orphan_elimination                true
% 3.18/1.01  --res_time_limit                        2.
% 3.18/1.01  --res_out_proof                         true
% 3.18/1.01  
% 3.18/1.01  ------ Superposition Options
% 3.18/1.01  
% 3.18/1.01  --superposition_flag                    true
% 3.18/1.01  --sup_passive_queue_type                priority_queues
% 3.18/1.01  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.18/1.01  --sup_passive_queues_freq               [8;1;4]
% 3.18/1.01  --demod_completeness_check              fast
% 3.18/1.01  --demod_use_ground                      true
% 3.18/1.01  --sup_to_prop_solver                    passive
% 3.18/1.01  --sup_prop_simpl_new                    true
% 3.18/1.01  --sup_prop_simpl_given                  true
% 3.18/1.01  --sup_fun_splitting                     false
% 3.18/1.01  --sup_smt_interval                      50000
% 3.18/1.01  
% 3.18/1.01  ------ Superposition Simplification Setup
% 3.18/1.01  
% 3.18/1.01  --sup_indices_passive                   []
% 3.18/1.01  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.18/1.01  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.18/1.01  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.18/1.01  --sup_full_triv                         [TrivRules;PropSubs]
% 3.18/1.01  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.18/1.01  --sup_full_bw                           [BwDemod]
% 3.18/1.01  --sup_immed_triv                        [TrivRules]
% 3.18/1.01  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.18/1.01  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.18/1.01  --sup_immed_bw_main                     []
% 3.18/1.01  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.18/1.01  --sup_input_triv                        [Unflattening;TrivRules]
% 3.18/1.01  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.18/1.01  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.18/1.01  
% 3.18/1.01  ------ Combination Options
% 3.18/1.01  
% 3.18/1.01  --comb_res_mult                         3
% 3.18/1.01  --comb_sup_mult                         2
% 3.18/1.01  --comb_inst_mult                        10
% 3.18/1.01  
% 3.18/1.01  ------ Debug Options
% 3.18/1.01  
% 3.18/1.01  --dbg_backtrace                         false
% 3.18/1.01  --dbg_dump_prop_clauses                 false
% 3.18/1.01  --dbg_dump_prop_clauses_file            -
% 3.18/1.01  --dbg_out_stat                          false
% 3.18/1.01  ------ Parsing...
% 3.18/1.01  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.18/1.01  
% 3.18/1.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e  sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 3.18/1.01  
% 3.18/1.01  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.18/1.01  
% 3.18/1.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.18/1.01  ------ Proving...
% 3.18/1.01  ------ Problem Properties 
% 3.18/1.01  
% 3.18/1.01  
% 3.18/1.01  clauses                                 23
% 3.18/1.01  conjectures                             1
% 3.18/1.01  EPR                                     0
% 3.18/1.01  Horn                                    12
% 3.18/1.01  unary                                   8
% 3.18/1.01  binary                                  3
% 3.18/1.01  lits                                    56
% 3.18/1.01  lits eq                                 27
% 3.18/1.01  fd_pure                                 0
% 3.18/1.01  fd_pseudo                               0
% 3.18/1.01  fd_cond                                 3
% 3.18/1.01  fd_pseudo_cond                          10
% 3.18/1.01  AC symbols                              0
% 3.18/1.01  
% 3.18/1.01  ------ Schedule dynamic 5 is on 
% 3.18/1.01  
% 3.18/1.01  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.18/1.01  
% 3.18/1.01  
% 3.18/1.01  ------ 
% 3.18/1.01  Current options:
% 3.18/1.01  ------ 
% 3.18/1.01  
% 3.18/1.01  ------ Input Options
% 3.18/1.01  
% 3.18/1.01  --out_options                           all
% 3.18/1.01  --tptp_safe_out                         true
% 3.18/1.01  --problem_path                          ""
% 3.18/1.01  --include_path                          ""
% 3.18/1.01  --clausifier                            res/vclausify_rel
% 3.18/1.01  --clausifier_options                    --mode clausify
% 3.18/1.01  --stdin                                 false
% 3.18/1.01  --stats_out                             all
% 3.18/1.01  
% 3.18/1.01  ------ General Options
% 3.18/1.01  
% 3.18/1.01  --fof                                   false
% 3.18/1.01  --time_out_real                         305.
% 3.18/1.01  --time_out_virtual                      -1.
% 3.18/1.01  --symbol_type_check                     false
% 3.18/1.01  --clausify_out                          false
% 3.18/1.01  --sig_cnt_out                           false
% 3.18/1.01  --trig_cnt_out                          false
% 3.18/1.01  --trig_cnt_out_tolerance                1.
% 3.18/1.01  --trig_cnt_out_sk_spl                   false
% 3.18/1.01  --abstr_cl_out                          false
% 3.18/1.01  
% 3.18/1.01  ------ Global Options
% 3.18/1.01  
% 3.18/1.01  --schedule                              default
% 3.18/1.01  --add_important_lit                     false
% 3.18/1.01  --prop_solver_per_cl                    1000
% 3.18/1.01  --min_unsat_core                        false
% 3.18/1.01  --soft_assumptions                      false
% 3.18/1.01  --soft_lemma_size                       3
% 3.18/1.01  --prop_impl_unit_size                   0
% 3.18/1.01  --prop_impl_unit                        []
% 3.18/1.01  --share_sel_clauses                     true
% 3.18/1.01  --reset_solvers                         false
% 3.18/1.01  --bc_imp_inh                            [conj_cone]
% 3.18/1.01  --conj_cone_tolerance                   3.
% 3.18/1.01  --extra_neg_conj                        none
% 3.18/1.01  --large_theory_mode                     true
% 3.18/1.01  --prolific_symb_bound                   200
% 3.18/1.01  --lt_threshold                          2000
% 3.18/1.01  --clause_weak_htbl                      true
% 3.18/1.01  --gc_record_bc_elim                     false
% 3.18/1.01  
% 3.18/1.01  ------ Preprocessing Options
% 3.18/1.01  
% 3.18/1.01  --preprocessing_flag                    true
% 3.18/1.01  --time_out_prep_mult                    0.1
% 3.18/1.01  --splitting_mode                        input
% 3.18/1.01  --splitting_grd                         true
% 3.18/1.01  --splitting_cvd                         false
% 3.18/1.01  --splitting_cvd_svl                     false
% 3.18/1.01  --splitting_nvd                         32
% 3.18/1.01  --sub_typing                            true
% 3.18/1.01  --prep_gs_sim                           true
% 3.18/1.01  --prep_unflatten                        true
% 3.18/1.01  --prep_res_sim                          true
% 3.18/1.01  --prep_upred                            true
% 3.18/1.01  --prep_sem_filter                       exhaustive
% 3.18/1.01  --prep_sem_filter_out                   false
% 3.18/1.01  --pred_elim                             true
% 3.18/1.01  --res_sim_input                         true
% 3.18/1.01  --eq_ax_congr_red                       true
% 3.18/1.01  --pure_diseq_elim                       true
% 3.18/1.01  --brand_transform                       false
% 3.18/1.01  --non_eq_to_eq                          false
% 3.18/1.01  --prep_def_merge                        true
% 3.18/1.01  --prep_def_merge_prop_impl              false
% 3.18/1.01  --prep_def_merge_mbd                    true
% 3.18/1.01  --prep_def_merge_tr_red                 false
% 3.18/1.01  --prep_def_merge_tr_cl                  false
% 3.18/1.01  --smt_preprocessing                     true
% 3.18/1.01  --smt_ac_axioms                         fast
% 3.18/1.01  --preprocessed_out                      false
% 3.18/1.01  --preprocessed_stats                    false
% 3.18/1.01  
% 3.18/1.01  ------ Abstraction refinement Options
% 3.18/1.01  
% 3.18/1.01  --abstr_ref                             []
% 3.18/1.01  --abstr_ref_prep                        false
% 3.18/1.01  --abstr_ref_until_sat                   false
% 3.18/1.01  --abstr_ref_sig_restrict                funpre
% 3.18/1.01  --abstr_ref_af_restrict_to_split_sk     false
% 3.18/1.01  --abstr_ref_under                       []
% 3.18/1.01  
% 3.18/1.01  ------ SAT Options
% 3.18/1.01  
% 3.18/1.01  --sat_mode                              false
% 3.18/1.01  --sat_fm_restart_options                ""
% 3.18/1.01  --sat_gr_def                            false
% 3.18/1.01  --sat_epr_types                         true
% 3.18/1.01  --sat_non_cyclic_types                  false
% 3.18/1.01  --sat_finite_models                     false
% 3.18/1.01  --sat_fm_lemmas                         false
% 3.18/1.01  --sat_fm_prep                           false
% 3.18/1.01  --sat_fm_uc_incr                        true
% 3.18/1.01  --sat_out_model                         small
% 3.18/1.01  --sat_out_clauses                       false
% 3.18/1.01  
% 3.18/1.01  ------ QBF Options
% 3.18/1.01  
% 3.18/1.01  --qbf_mode                              false
% 3.18/1.01  --qbf_elim_univ                         false
% 3.18/1.01  --qbf_dom_inst                          none
% 3.18/1.01  --qbf_dom_pre_inst                      false
% 3.18/1.01  --qbf_sk_in                             false
% 3.18/1.01  --qbf_pred_elim                         true
% 3.18/1.01  --qbf_split                             512
% 3.18/1.01  
% 3.18/1.01  ------ BMC1 Options
% 3.18/1.01  
% 3.18/1.01  --bmc1_incremental                      false
% 3.18/1.01  --bmc1_axioms                           reachable_all
% 3.18/1.01  --bmc1_min_bound                        0
% 3.18/1.01  --bmc1_max_bound                        -1
% 3.18/1.01  --bmc1_max_bound_default                -1
% 3.18/1.01  --bmc1_symbol_reachability              true
% 3.18/1.01  --bmc1_property_lemmas                  false
% 3.18/1.01  --bmc1_k_induction                      false
% 3.18/1.01  --bmc1_non_equiv_states                 false
% 3.18/1.01  --bmc1_deadlock                         false
% 3.18/1.01  --bmc1_ucm                              false
% 3.18/1.01  --bmc1_add_unsat_core                   none
% 3.18/1.01  --bmc1_unsat_core_children              false
% 3.18/1.01  --bmc1_unsat_core_extrapolate_axioms    false
% 3.18/1.01  --bmc1_out_stat                         full
% 3.18/1.01  --bmc1_ground_init                      false
% 3.18/1.01  --bmc1_pre_inst_next_state              false
% 3.18/1.01  --bmc1_pre_inst_state                   false
% 3.18/1.01  --bmc1_pre_inst_reach_state             false
% 3.18/1.01  --bmc1_out_unsat_core                   false
% 3.18/1.01  --bmc1_aig_witness_out                  false
% 3.18/1.01  --bmc1_verbose                          false
% 3.18/1.01  --bmc1_dump_clauses_tptp                false
% 3.18/1.01  --bmc1_dump_unsat_core_tptp             false
% 3.18/1.01  --bmc1_dump_file                        -
% 3.18/1.01  --bmc1_ucm_expand_uc_limit              128
% 3.18/1.01  --bmc1_ucm_n_expand_iterations          6
% 3.18/1.01  --bmc1_ucm_extend_mode                  1
% 3.18/1.01  --bmc1_ucm_init_mode                    2
% 3.18/1.01  --bmc1_ucm_cone_mode                    none
% 3.18/1.01  --bmc1_ucm_reduced_relation_type        0
% 3.18/1.01  --bmc1_ucm_relax_model                  4
% 3.18/1.01  --bmc1_ucm_full_tr_after_sat            true
% 3.18/1.01  --bmc1_ucm_expand_neg_assumptions       false
% 3.18/1.01  --bmc1_ucm_layered_model                none
% 3.18/1.01  --bmc1_ucm_max_lemma_size               10
% 3.18/1.01  
% 3.18/1.01  ------ AIG Options
% 3.18/1.01  
% 3.18/1.01  --aig_mode                              false
% 3.18/1.01  
% 3.18/1.01  ------ Instantiation Options
% 3.18/1.01  
% 3.18/1.01  --instantiation_flag                    true
% 3.18/1.01  --inst_sos_flag                         false
% 3.18/1.01  --inst_sos_phase                        true
% 3.18/1.01  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.18/1.01  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.18/1.01  --inst_lit_sel_side                     none
% 3.18/1.01  --inst_solver_per_active                1400
% 3.18/1.01  --inst_solver_calls_frac                1.
% 3.18/1.01  --inst_passive_queue_type               priority_queues
% 3.18/1.01  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.18/1.01  --inst_passive_queues_freq              [25;2]
% 3.18/1.01  --inst_dismatching                      true
% 3.18/1.01  --inst_eager_unprocessed_to_passive     true
% 3.18/1.01  --inst_prop_sim_given                   true
% 3.18/1.01  --inst_prop_sim_new                     false
% 3.18/1.01  --inst_subs_new                         false
% 3.18/1.01  --inst_eq_res_simp                      false
% 3.18/1.01  --inst_subs_given                       false
% 3.18/1.01  --inst_orphan_elimination               true
% 3.18/1.01  --inst_learning_loop_flag               true
% 3.18/1.01  --inst_learning_start                   3000
% 3.18/1.01  --inst_learning_factor                  2
% 3.18/1.01  --inst_start_prop_sim_after_learn       3
% 3.18/1.01  --inst_sel_renew                        solver
% 3.18/1.01  --inst_lit_activity_flag                true
% 3.18/1.01  --inst_restr_to_given                   false
% 3.18/1.01  --inst_activity_threshold               500
% 3.18/1.01  --inst_out_proof                        true
% 3.18/1.01  
% 3.18/1.01  ------ Resolution Options
% 3.18/1.01  
% 3.18/1.01  --resolution_flag                       false
% 3.18/1.01  --res_lit_sel                           adaptive
% 3.18/1.01  --res_lit_sel_side                      none
% 3.18/1.01  --res_ordering                          kbo
% 3.18/1.01  --res_to_prop_solver                    active
% 3.18/1.01  --res_prop_simpl_new                    false
% 3.18/1.01  --res_prop_simpl_given                  true
% 3.18/1.01  --res_passive_queue_type                priority_queues
% 3.18/1.01  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.18/1.01  --res_passive_queues_freq               [15;5]
% 3.18/1.01  --res_forward_subs                      full
% 3.18/1.01  --res_backward_subs                     full
% 3.18/1.01  --res_forward_subs_resolution           true
% 3.18/1.01  --res_backward_subs_resolution          true
% 3.18/1.01  --res_orphan_elimination                true
% 3.18/1.01  --res_time_limit                        2.
% 3.18/1.01  --res_out_proof                         true
% 3.18/1.01  
% 3.18/1.01  ------ Superposition Options
% 3.18/1.01  
% 3.18/1.01  --superposition_flag                    true
% 3.18/1.01  --sup_passive_queue_type                priority_queues
% 3.18/1.01  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.18/1.01  --sup_passive_queues_freq               [8;1;4]
% 3.18/1.01  --demod_completeness_check              fast
% 3.18/1.01  --demod_use_ground                      true
% 3.18/1.01  --sup_to_prop_solver                    passive
% 3.18/1.01  --sup_prop_simpl_new                    true
% 3.18/1.01  --sup_prop_simpl_given                  true
% 3.18/1.01  --sup_fun_splitting                     false
% 3.18/1.01  --sup_smt_interval                      50000
% 3.18/1.01  
% 3.18/1.01  ------ Superposition Simplification Setup
% 3.18/1.01  
% 3.18/1.01  --sup_indices_passive                   []
% 3.18/1.01  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.18/1.01  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.18/1.01  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.18/1.01  --sup_full_triv                         [TrivRules;PropSubs]
% 3.18/1.01  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.18/1.01  --sup_full_bw                           [BwDemod]
% 3.18/1.01  --sup_immed_triv                        [TrivRules]
% 3.18/1.01  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.18/1.01  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.18/1.01  --sup_immed_bw_main                     []
% 3.18/1.01  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.18/1.01  --sup_input_triv                        [Unflattening;TrivRules]
% 3.18/1.01  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.18/1.01  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.18/1.01  
% 3.18/1.01  ------ Combination Options
% 3.18/1.01  
% 3.18/1.01  --comb_res_mult                         3
% 3.18/1.01  --comb_sup_mult                         2
% 3.18/1.01  --comb_inst_mult                        10
% 3.18/1.01  
% 3.18/1.01  ------ Debug Options
% 3.18/1.01  
% 3.18/1.01  --dbg_backtrace                         false
% 3.18/1.01  --dbg_dump_prop_clauses                 false
% 3.18/1.01  --dbg_dump_prop_clauses_file            -
% 3.18/1.01  --dbg_out_stat                          false
% 3.18/1.01  
% 3.18/1.01  
% 3.18/1.01  
% 3.18/1.01  
% 3.18/1.01  ------ Proving...
% 3.18/1.01  
% 3.18/1.01  
% 3.18/1.01  % SZS status Theorem for theBenchmark.p
% 3.18/1.01  
% 3.18/1.01  % SZS output start CNFRefutation for theBenchmark.p
% 3.18/1.01  
% 3.18/1.01  fof(f9,axiom,(
% 3.18/1.01    ! [X0,X1] : ((k1_xboole_0 = X0 => (k1_setfam_1(X0) = X1 <=> k1_xboole_0 = X1)) & (k1_xboole_0 != X0 => (k1_setfam_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ! [X3] : (r2_hidden(X3,X0) => r2_hidden(X2,X3))))))),
% 3.18/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.18/1.01  
% 3.18/1.01  fof(f13,plain,(
% 3.18/1.01    ! [X0,X1] : (((k1_setfam_1(X0) = X1 <=> k1_xboole_0 = X1) | k1_xboole_0 != X0) & ((k1_setfam_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ! [X3] : (r2_hidden(X2,X3) | ~r2_hidden(X3,X0)))) | k1_xboole_0 = X0))),
% 3.18/1.01    inference(ennf_transformation,[],[f9])).
% 3.18/1.01  
% 3.18/1.01  fof(f25,plain,(
% 3.18/1.01    ! [X0,X1] : ((((k1_setfam_1(X0) = X1 | k1_xboole_0 != X1) & (k1_xboole_0 = X1 | k1_setfam_1(X0) != X1)) | k1_xboole_0 != X0) & (((k1_setfam_1(X0) = X1 | ? [X2] : ((? [X3] : (~r2_hidden(X2,X3) & r2_hidden(X3,X0)) | ~r2_hidden(X2,X1)) & (! [X3] : (r2_hidden(X2,X3) | ~r2_hidden(X3,X0)) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ? [X3] : (~r2_hidden(X2,X3) & r2_hidden(X3,X0))) & (! [X3] : (r2_hidden(X2,X3) | ~r2_hidden(X3,X0)) | ~r2_hidden(X2,X1))) | k1_setfam_1(X0) != X1)) | k1_xboole_0 = X0))),
% 3.18/1.01    inference(nnf_transformation,[],[f13])).
% 3.18/1.01  
% 3.18/1.01  fof(f26,plain,(
% 3.18/1.01    ! [X0,X1] : ((((k1_setfam_1(X0) = X1 | k1_xboole_0 != X1) & (k1_xboole_0 = X1 | k1_setfam_1(X0) != X1)) | k1_xboole_0 != X0) & (((k1_setfam_1(X0) = X1 | ? [X2] : ((? [X3] : (~r2_hidden(X2,X3) & r2_hidden(X3,X0)) | ~r2_hidden(X2,X1)) & (! [X4] : (r2_hidden(X2,X4) | ~r2_hidden(X4,X0)) | r2_hidden(X2,X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ? [X6] : (~r2_hidden(X5,X6) & r2_hidden(X6,X0))) & (! [X7] : (r2_hidden(X5,X7) | ~r2_hidden(X7,X0)) | ~r2_hidden(X5,X1))) | k1_setfam_1(X0) != X1)) | k1_xboole_0 = X0))),
% 3.18/1.01    inference(rectify,[],[f25])).
% 3.18/1.01  
% 3.18/1.01  fof(f29,plain,(
% 3.18/1.01    ! [X5,X0] : (? [X6] : (~r2_hidden(X5,X6) & r2_hidden(X6,X0)) => (~r2_hidden(X5,sK3(X0,X5)) & r2_hidden(sK3(X0,X5),X0)))),
% 3.18/1.01    introduced(choice_axiom,[])).
% 3.18/1.01  
% 3.18/1.01  fof(f28,plain,(
% 3.18/1.01    ( ! [X2] : (! [X1,X0] : (? [X3] : (~r2_hidden(X2,X3) & r2_hidden(X3,X0)) => (~r2_hidden(X2,sK2(X0,X1)) & r2_hidden(sK2(X0,X1),X0)))) )),
% 3.18/1.01    introduced(choice_axiom,[])).
% 3.18/1.01  
% 3.18/1.01  fof(f27,plain,(
% 3.18/1.01    ! [X1,X0] : (? [X2] : ((? [X3] : (~r2_hidden(X2,X3) & r2_hidden(X3,X0)) | ~r2_hidden(X2,X1)) & (! [X4] : (r2_hidden(X2,X4) | ~r2_hidden(X4,X0)) | r2_hidden(X2,X1))) => ((? [X3] : (~r2_hidden(sK1(X0,X1),X3) & r2_hidden(X3,X0)) | ~r2_hidden(sK1(X0,X1),X1)) & (! [X4] : (r2_hidden(sK1(X0,X1),X4) | ~r2_hidden(X4,X0)) | r2_hidden(sK1(X0,X1),X1))))),
% 3.18/1.01    introduced(choice_axiom,[])).
% 3.18/1.01  
% 3.18/1.01  fof(f30,plain,(
% 3.18/1.01    ! [X0,X1] : ((((k1_setfam_1(X0) = X1 | k1_xboole_0 != X1) & (k1_xboole_0 = X1 | k1_setfam_1(X0) != X1)) | k1_xboole_0 != X0) & (((k1_setfam_1(X0) = X1 | (((~r2_hidden(sK1(X0,X1),sK2(X0,X1)) & r2_hidden(sK2(X0,X1),X0)) | ~r2_hidden(sK1(X0,X1),X1)) & (! [X4] : (r2_hidden(sK1(X0,X1),X4) | ~r2_hidden(X4,X0)) | r2_hidden(sK1(X0,X1),X1)))) & (! [X5] : ((r2_hidden(X5,X1) | (~r2_hidden(X5,sK3(X0,X5)) & r2_hidden(sK3(X0,X5),X0))) & (! [X7] : (r2_hidden(X5,X7) | ~r2_hidden(X7,X0)) | ~r2_hidden(X5,X1))) | k1_setfam_1(X0) != X1)) | k1_xboole_0 = X0))),
% 3.18/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f26,f29,f28,f27])).
% 3.18/1.01  
% 3.18/1.01  fof(f54,plain,(
% 3.18/1.01    ( ! [X4,X0,X1] : (k1_setfam_1(X0) = X1 | r2_hidden(sK1(X0,X1),X4) | ~r2_hidden(X4,X0) | r2_hidden(sK1(X0,X1),X1) | k1_xboole_0 = X0) )),
% 3.18/1.01    inference(cnf_transformation,[],[f30])).
% 3.18/1.01  
% 3.18/1.01  fof(f1,axiom,(
% 3.18/1.01    ! [X0,X1,X2] : (k2_tarski(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (X1 = X3 | X0 = X3)))),
% 3.18/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.18/1.01  
% 3.18/1.01  fof(f15,plain,(
% 3.18/1.01    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & ((X1 = X3 | X0 = X3) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (X1 != X3 & X0 != X3)) & ((X1 = X3 | X0 = X3) | ~r2_hidden(X3,X2))) | k2_tarski(X0,X1) != X2))),
% 3.18/1.01    inference(nnf_transformation,[],[f1])).
% 3.18/1.01  
% 3.18/1.01  fof(f16,plain,(
% 3.18/1.01    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (X1 != X3 & X0 != X3)) & (X1 = X3 | X0 = X3 | ~r2_hidden(X3,X2))) | k2_tarski(X0,X1) != X2))),
% 3.18/1.01    inference(flattening,[],[f15])).
% 3.18/1.01  
% 3.18/1.01  fof(f17,plain,(
% 3.18/1.01    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (X1 != X4 & X0 != X4)) & (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2))) | k2_tarski(X0,X1) != X2))),
% 3.18/1.01    inference(rectify,[],[f16])).
% 3.18/1.01  
% 3.18/1.01  fof(f18,plain,(
% 3.18/1.01    ! [X2,X1,X0] : (? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2))) => (((sK0(X0,X1,X2) != X1 & sK0(X0,X1,X2) != X0) | ~r2_hidden(sK0(X0,X1,X2),X2)) & (sK0(X0,X1,X2) = X1 | sK0(X0,X1,X2) = X0 | r2_hidden(sK0(X0,X1,X2),X2))))),
% 3.18/1.01    introduced(choice_axiom,[])).
% 3.18/1.01  
% 3.18/1.01  fof(f19,plain,(
% 3.18/1.01    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | (((sK0(X0,X1,X2) != X1 & sK0(X0,X1,X2) != X0) | ~r2_hidden(sK0(X0,X1,X2),X2)) & (sK0(X0,X1,X2) = X1 | sK0(X0,X1,X2) = X0 | r2_hidden(sK0(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (X1 != X4 & X0 != X4)) & (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2))) | k2_tarski(X0,X1) != X2))),
% 3.18/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f17,f18])).
% 3.18/1.01  
% 3.18/1.01  fof(f35,plain,(
% 3.18/1.01    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | X1 != X4 | k2_tarski(X0,X1) != X2) )),
% 3.18/1.01    inference(cnf_transformation,[],[f19])).
% 3.18/1.01  
% 3.18/1.01  fof(f3,axiom,(
% 3.18/1.01    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 3.18/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.18/1.01  
% 3.18/1.01  fof(f40,plain,(
% 3.18/1.01    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 3.18/1.01    inference(cnf_transformation,[],[f3])).
% 3.18/1.01  
% 3.18/1.01  fof(f4,axiom,(
% 3.18/1.01    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 3.18/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.18/1.01  
% 3.18/1.01  fof(f41,plain,(
% 3.18/1.01    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 3.18/1.01    inference(cnf_transformation,[],[f4])).
% 3.18/1.01  
% 3.18/1.01  fof(f60,plain,(
% 3.18/1.01    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 3.18/1.01    inference(definition_unfolding,[],[f40,f41])).
% 3.18/1.01  
% 3.18/1.01  fof(f65,plain,(
% 3.18/1.01    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | X1 != X4 | k2_enumset1(X0,X0,X0,X1) != X2) )),
% 3.18/1.01    inference(definition_unfolding,[],[f35,f60])).
% 3.18/1.01  
% 3.18/1.01  fof(f78,plain,(
% 3.18/1.01    ( ! [X4,X2,X0] : (r2_hidden(X4,X2) | k2_enumset1(X0,X0,X0,X4) != X2) )),
% 3.18/1.01    inference(equality_resolution,[],[f65])).
% 3.18/1.01  
% 3.18/1.01  fof(f79,plain,(
% 3.18/1.01    ( ! [X4,X0] : (r2_hidden(X4,k2_enumset1(X0,X0,X0,X4))) )),
% 3.18/1.01    inference(equality_resolution,[],[f78])).
% 3.18/1.01  
% 3.18/1.01  fof(f55,plain,(
% 3.18/1.01    ( ! [X0,X1] : (k1_setfam_1(X0) = X1 | r2_hidden(sK2(X0,X1),X0) | ~r2_hidden(sK1(X0,X1),X1) | k1_xboole_0 = X0) )),
% 3.18/1.01    inference(cnf_transformation,[],[f30])).
% 3.18/1.01  
% 3.18/1.01  fof(f6,axiom,(
% 3.18/1.01    ! [X0,X1] : (k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) <=> X0 != X1)),
% 3.18/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.18/1.01  
% 3.18/1.01  fof(f22,plain,(
% 3.18/1.01    ! [X0,X1] : ((k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) | X0 = X1) & (X0 != X1 | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),k1_tarski(X1))))),
% 3.18/1.01    inference(nnf_transformation,[],[f6])).
% 3.18/1.01  
% 3.18/1.01  fof(f46,plain,(
% 3.18/1.01    ( ! [X0,X1] : (k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) | X0 = X1) )),
% 3.18/1.01    inference(cnf_transformation,[],[f22])).
% 3.18/1.01  
% 3.18/1.01  fof(f2,axiom,(
% 3.18/1.01    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 3.18/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.18/1.01  
% 3.18/1.01  fof(f39,plain,(
% 3.18/1.01    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 3.18/1.01    inference(cnf_transformation,[],[f2])).
% 3.18/1.01  
% 3.18/1.01  fof(f61,plain,(
% 3.18/1.01    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 3.18/1.01    inference(definition_unfolding,[],[f39,f60])).
% 3.18/1.01  
% 3.18/1.01  fof(f71,plain,(
% 3.18/1.01    ( ! [X0,X1] : (k2_enumset1(X0,X0,X0,X0) = k4_xboole_0(k2_enumset1(X0,X0,X0,X0),k2_enumset1(X1,X1,X1,X1)) | X0 = X1) )),
% 3.18/1.01    inference(definition_unfolding,[],[f46,f61,f61,f61])).
% 3.18/1.01  
% 3.18/1.01  fof(f7,axiom,(
% 3.18/1.01    ! [X0,X1,X2] : (r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) <=> (X0 != X2 & r2_hidden(X0,X1)))),
% 3.18/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.18/1.01  
% 3.18/1.01  fof(f23,plain,(
% 3.18/1.01    ! [X0,X1,X2] : ((r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) | (X0 = X2 | ~r2_hidden(X0,X1))) & ((X0 != X2 & r2_hidden(X0,X1)) | ~r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))))),
% 3.18/1.01    inference(nnf_transformation,[],[f7])).
% 3.18/1.01  
% 3.18/1.01  fof(f24,plain,(
% 3.18/1.01    ! [X0,X1,X2] : ((r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) | X0 = X2 | ~r2_hidden(X0,X1)) & ((X0 != X2 & r2_hidden(X0,X1)) | ~r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))))),
% 3.18/1.01    inference(flattening,[],[f23])).
% 3.18/1.01  
% 3.18/1.01  fof(f48,plain,(
% 3.18/1.01    ( ! [X2,X0,X1] : (X0 != X2 | ~r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))) )),
% 3.18/1.01    inference(cnf_transformation,[],[f24])).
% 3.18/1.01  
% 3.18/1.01  fof(f74,plain,(
% 3.18/1.01    ( ! [X2,X0,X1] : (X0 != X2 | ~r2_hidden(X0,k4_xboole_0(X1,k2_enumset1(X2,X2,X2,X2)))) )),
% 3.18/1.01    inference(definition_unfolding,[],[f48,f61])).
% 3.18/1.01  
% 3.18/1.01  fof(f86,plain,(
% 3.18/1.01    ( ! [X2,X1] : (~r2_hidden(X2,k4_xboole_0(X1,k2_enumset1(X2,X2,X2,X2)))) )),
% 3.18/1.01    inference(equality_resolution,[],[f74])).
% 3.18/1.01  
% 3.18/1.01  fof(f56,plain,(
% 3.18/1.01    ( ! [X0,X1] : (k1_setfam_1(X0) = X1 | ~r2_hidden(sK1(X0,X1),sK2(X0,X1)) | ~r2_hidden(sK1(X0,X1),X1) | k1_xboole_0 = X0) )),
% 3.18/1.01    inference(cnf_transformation,[],[f30])).
% 3.18/1.01  
% 3.18/1.01  fof(f34,plain,(
% 3.18/1.01    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | X0 != X4 | k2_tarski(X0,X1) != X2) )),
% 3.18/1.01    inference(cnf_transformation,[],[f19])).
% 3.18/1.01  
% 3.18/1.01  fof(f66,plain,(
% 3.18/1.01    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | X0 != X4 | k2_enumset1(X0,X0,X0,X1) != X2) )),
% 3.18/1.01    inference(definition_unfolding,[],[f34,f60])).
% 3.18/1.01  
% 3.18/1.01  fof(f80,plain,(
% 3.18/1.01    ( ! [X4,X2,X1] : (r2_hidden(X4,X2) | k2_enumset1(X4,X4,X4,X1) != X2) )),
% 3.18/1.01    inference(equality_resolution,[],[f66])).
% 3.18/1.01  
% 3.18/1.01  fof(f81,plain,(
% 3.18/1.01    ( ! [X4,X1] : (r2_hidden(X4,k2_enumset1(X4,X4,X4,X1))) )),
% 3.18/1.01    inference(equality_resolution,[],[f80])).
% 3.18/1.01  
% 3.18/1.01  fof(f10,conjecture,(
% 3.18/1.01    ! [X0] : k1_setfam_1(k1_tarski(X0)) = X0),
% 3.18/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.18/1.01  
% 3.18/1.01  fof(f11,negated_conjecture,(
% 3.18/1.01    ~! [X0] : k1_setfam_1(k1_tarski(X0)) = X0),
% 3.18/1.01    inference(negated_conjecture,[],[f10])).
% 3.18/1.01  
% 3.18/1.01  fof(f14,plain,(
% 3.18/1.01    ? [X0] : k1_setfam_1(k1_tarski(X0)) != X0),
% 3.18/1.01    inference(ennf_transformation,[],[f11])).
% 3.18/1.01  
% 3.18/1.01  fof(f31,plain,(
% 3.18/1.01    ? [X0] : k1_setfam_1(k1_tarski(X0)) != X0 => k1_setfam_1(k1_tarski(sK4)) != sK4),
% 3.18/1.01    introduced(choice_axiom,[])).
% 3.18/1.01  
% 3.18/1.01  fof(f32,plain,(
% 3.18/1.01    k1_setfam_1(k1_tarski(sK4)) != sK4),
% 3.18/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f14,f31])).
% 3.18/1.01  
% 3.18/1.01  fof(f59,plain,(
% 3.18/1.01    k1_setfam_1(k1_tarski(sK4)) != sK4),
% 3.18/1.01    inference(cnf_transformation,[],[f32])).
% 3.18/1.01  
% 3.18/1.01  fof(f77,plain,(
% 3.18/1.01    k1_setfam_1(k2_enumset1(sK4,sK4,sK4,sK4)) != sK4),
% 3.18/1.01    inference(definition_unfolding,[],[f59,f61])).
% 3.18/1.01  
% 3.18/1.01  fof(f8,axiom,(
% 3.18/1.01    ! [X0,X1] : (r1_tarski(k1_tarski(X0),k1_tarski(X1)) => X0 = X1)),
% 3.18/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.18/1.01  
% 3.18/1.01  fof(f12,plain,(
% 3.18/1.01    ! [X0,X1] : (X0 = X1 | ~r1_tarski(k1_tarski(X0),k1_tarski(X1)))),
% 3.18/1.01    inference(ennf_transformation,[],[f8])).
% 3.18/1.01  
% 3.18/1.01  fof(f50,plain,(
% 3.18/1.01    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(k1_tarski(X0),k1_tarski(X1))) )),
% 3.18/1.01    inference(cnf_transformation,[],[f12])).
% 3.18/1.01  
% 3.18/1.01  fof(f76,plain,(
% 3.18/1.01    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(k2_enumset1(X0,X0,X0,X0),k2_enumset1(X1,X1,X1,X1))) )),
% 3.18/1.01    inference(definition_unfolding,[],[f50,f61,f61])).
% 3.18/1.01  
% 3.18/1.01  fof(f5,axiom,(
% 3.18/1.01    ! [X0,X1] : (r1_tarski(X0,k1_tarski(X1)) <=> (k1_tarski(X1) = X0 | k1_xboole_0 = X0))),
% 3.18/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.18/1.01  
% 3.18/1.01  fof(f20,plain,(
% 3.18/1.01    ! [X0,X1] : ((r1_tarski(X0,k1_tarski(X1)) | (k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & ((k1_tarski(X1) = X0 | k1_xboole_0 = X0) | ~r1_tarski(X0,k1_tarski(X1))))),
% 3.18/1.01    inference(nnf_transformation,[],[f5])).
% 3.18/1.01  
% 3.18/1.01  fof(f21,plain,(
% 3.18/1.01    ! [X0,X1] : ((r1_tarski(X0,k1_tarski(X1)) | (k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & (k1_tarski(X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k1_tarski(X1))))),
% 3.18/1.01    inference(flattening,[],[f20])).
% 3.18/1.01  
% 3.18/1.01  fof(f43,plain,(
% 3.18/1.01    ( ! [X0,X1] : (r1_tarski(X0,k1_tarski(X1)) | k1_xboole_0 != X0) )),
% 3.18/1.01    inference(cnf_transformation,[],[f21])).
% 3.18/1.01  
% 3.18/1.01  fof(f69,plain,(
% 3.18/1.01    ( ! [X0,X1] : (r1_tarski(X0,k2_enumset1(X1,X1,X1,X1)) | k1_xboole_0 != X0) )),
% 3.18/1.01    inference(definition_unfolding,[],[f43,f61])).
% 3.18/1.01  
% 3.18/1.01  fof(f84,plain,(
% 3.18/1.01    ( ! [X1] : (r1_tarski(k1_xboole_0,k2_enumset1(X1,X1,X1,X1))) )),
% 3.18/1.01    inference(equality_resolution,[],[f69])).
% 3.18/1.01  
% 3.18/1.01  fof(f57,plain,(
% 3.18/1.01    ( ! [X0,X1] : (k1_xboole_0 = X1 | k1_setfam_1(X0) != X1 | k1_xboole_0 != X0) )),
% 3.18/1.01    inference(cnf_transformation,[],[f30])).
% 3.18/1.01  
% 3.18/1.01  fof(f89,plain,(
% 3.18/1.01    ( ! [X0] : (k1_xboole_0 = k1_setfam_1(X0) | k1_xboole_0 != X0) )),
% 3.18/1.01    inference(equality_resolution,[],[f57])).
% 3.18/1.01  
% 3.18/1.01  fof(f90,plain,(
% 3.18/1.01    k1_xboole_0 = k1_setfam_1(k1_xboole_0)),
% 3.18/1.01    inference(equality_resolution,[],[f89])).
% 3.18/1.01  
% 3.18/1.01  cnf(c_19,plain,
% 3.18/1.01      ( ~ r2_hidden(X0,X1)
% 3.18/1.01      | r2_hidden(sK1(X1,X2),X2)
% 3.18/1.01      | r2_hidden(sK1(X1,X2),X0)
% 3.18/1.01      | k1_setfam_1(X1) = X2
% 3.18/1.01      | k1_xboole_0 = X1 ),
% 3.18/1.01      inference(cnf_transformation,[],[f54]) ).
% 3.18/1.01  
% 3.18/1.01  cnf(c_720,plain,
% 3.18/1.01      ( k1_setfam_1(X0) = X1
% 3.18/1.01      | k1_xboole_0 = X0
% 3.18/1.01      | r2_hidden(X2,X0) != iProver_top
% 3.18/1.01      | r2_hidden(sK1(X0,X1),X1) = iProver_top
% 3.18/1.01      | r2_hidden(sK1(X0,X1),X2) = iProver_top ),
% 3.18/1.01      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 3.18/1.01  
% 3.18/1.01  cnf(c_3,plain,
% 3.18/1.01      ( r2_hidden(X0,k2_enumset1(X1,X1,X1,X0)) ),
% 3.18/1.01      inference(cnf_transformation,[],[f79]) ).
% 3.18/1.01  
% 3.18/1.01  cnf(c_732,plain,
% 3.18/1.01      ( r2_hidden(X0,k2_enumset1(X1,X1,X1,X0)) = iProver_top ),
% 3.18/1.01      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 3.18/1.01  
% 3.18/1.01  cnf(c_18,plain,
% 3.18/1.01      ( r2_hidden(sK2(X0,X1),X0)
% 3.18/1.01      | ~ r2_hidden(sK1(X0,X1),X1)
% 3.18/1.01      | k1_setfam_1(X0) = X1
% 3.18/1.01      | k1_xboole_0 = X0 ),
% 3.18/1.01      inference(cnf_transformation,[],[f55]) ).
% 3.18/1.01  
% 3.18/1.01  cnf(c_721,plain,
% 3.18/1.01      ( k1_setfam_1(X0) = X1
% 3.18/1.01      | k1_xboole_0 = X0
% 3.18/1.01      | r2_hidden(sK2(X0,X1),X0) = iProver_top
% 3.18/1.01      | r2_hidden(sK1(X0,X1),X1) != iProver_top ),
% 3.18/1.01      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 3.18/1.01  
% 3.18/1.01  cnf(c_1993,plain,
% 3.18/1.01      ( k1_setfam_1(X0) = X1
% 3.18/1.01      | k1_xboole_0 = X0
% 3.18/1.01      | r2_hidden(X1,X0) != iProver_top
% 3.18/1.01      | r2_hidden(sK2(X0,X1),X0) = iProver_top
% 3.18/1.01      | r2_hidden(sK1(X0,X1),X1) = iProver_top ),
% 3.18/1.01      inference(superposition,[status(thm)],[c_720,c_721]) ).
% 3.18/1.01  
% 3.18/1.01  cnf(c_2010,plain,
% 3.18/1.01      ( k1_setfam_1(X0) = X1
% 3.18/1.01      | k1_xboole_0 = X0
% 3.18/1.01      | r2_hidden(X1,X0) != iProver_top
% 3.18/1.01      | r2_hidden(sK2(X0,X1),X0) = iProver_top ),
% 3.18/1.01      inference(forward_subsumption_resolution,
% 3.18/1.01                [status(thm)],
% 3.18/1.01                [c_1993,c_721]) ).
% 3.18/1.01  
% 3.18/1.01  cnf(c_9,plain,
% 3.18/1.01      ( X0 = X1
% 3.18/1.01      | k4_xboole_0(k2_enumset1(X1,X1,X1,X1),k2_enumset1(X0,X0,X0,X0)) = k2_enumset1(X1,X1,X1,X1) ),
% 3.18/1.01      inference(cnf_transformation,[],[f71]) ).
% 3.18/1.01  
% 3.18/1.01  cnf(c_12,plain,
% 3.18/1.01      ( ~ r2_hidden(X0,k4_xboole_0(X1,k2_enumset1(X0,X0,X0,X0))) ),
% 3.18/1.01      inference(cnf_transformation,[],[f86]) ).
% 3.18/1.01  
% 3.18/1.01  cnf(c_725,plain,
% 3.18/1.01      ( r2_hidden(X0,k4_xboole_0(X1,k2_enumset1(X0,X0,X0,X0))) != iProver_top ),
% 3.18/1.01      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 3.18/1.01  
% 3.18/1.01  cnf(c_1135,plain,
% 3.18/1.01      ( X0 = X1 | r2_hidden(X1,k2_enumset1(X0,X0,X0,X0)) != iProver_top ),
% 3.18/1.01      inference(superposition,[status(thm)],[c_9,c_725]) ).
% 3.18/1.01  
% 3.18/1.01  cnf(c_2451,plain,
% 3.18/1.01      ( k2_enumset1(X0,X0,X0,X0) = k1_xboole_0
% 3.18/1.01      | sK2(k2_enumset1(X0,X0,X0,X0),X1) = X0
% 3.18/1.01      | k1_setfam_1(k2_enumset1(X0,X0,X0,X0)) = X1
% 3.18/1.01      | r2_hidden(X1,k2_enumset1(X0,X0,X0,X0)) != iProver_top ),
% 3.18/1.01      inference(superposition,[status(thm)],[c_2010,c_1135]) ).
% 3.18/1.01  
% 3.18/1.01  cnf(c_5647,plain,
% 3.18/1.01      ( k2_enumset1(X0,X0,X0,X0) = k1_xboole_0
% 3.18/1.01      | sK2(k2_enumset1(X0,X0,X0,X0),X0) = X0
% 3.18/1.01      | k1_setfam_1(k2_enumset1(X0,X0,X0,X0)) = X0 ),
% 3.18/1.01      inference(superposition,[status(thm)],[c_732,c_2451]) ).
% 3.18/1.01  
% 3.18/1.01  cnf(c_17,plain,
% 3.18/1.01      ( ~ r2_hidden(sK1(X0,X1),X1)
% 3.18/1.01      | ~ r2_hidden(sK1(X0,X1),sK2(X0,X1))
% 3.18/1.01      | k1_setfam_1(X0) = X1
% 3.18/1.01      | k1_xboole_0 = X0 ),
% 3.18/1.01      inference(cnf_transformation,[],[f56]) ).
% 3.18/1.01  
% 3.18/1.01  cnf(c_722,plain,
% 3.18/1.01      ( k1_setfam_1(X0) = X1
% 3.18/1.01      | k1_xboole_0 = X0
% 3.18/1.01      | r2_hidden(sK1(X0,X1),X1) != iProver_top
% 3.18/1.01      | r2_hidden(sK1(X0,X1),sK2(X0,X1)) != iProver_top ),
% 3.18/1.01      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 3.18/1.01  
% 3.18/1.01  cnf(c_5878,plain,
% 3.18/1.01      ( k2_enumset1(X0,X0,X0,X0) = k1_xboole_0
% 3.18/1.01      | k1_setfam_1(k2_enumset1(X0,X0,X0,X0)) = X0
% 3.18/1.01      | r2_hidden(sK1(k2_enumset1(X0,X0,X0,X0),X0),X0) != iProver_top ),
% 3.18/1.01      inference(superposition,[status(thm)],[c_5647,c_722]) ).
% 3.18/1.01  
% 3.18/1.01  cnf(c_6108,plain,
% 3.18/1.01      ( k2_enumset1(X0,X0,X0,X0) = k1_xboole_0
% 3.18/1.01      | k1_setfam_1(k2_enumset1(X0,X0,X0,X0)) = X0
% 3.18/1.01      | r2_hidden(X0,k2_enumset1(X0,X0,X0,X0)) != iProver_top
% 3.18/1.01      | r2_hidden(sK1(k2_enumset1(X0,X0,X0,X0),X0),X0) = iProver_top ),
% 3.18/1.01      inference(superposition,[status(thm)],[c_720,c_5878]) ).
% 3.18/1.01  
% 3.18/1.01  cnf(c_6164,plain,
% 3.18/1.01      ( k2_enumset1(X0,X0,X0,X0) = k1_xboole_0
% 3.18/1.01      | k1_setfam_1(k2_enumset1(X0,X0,X0,X0)) = X0
% 3.18/1.01      | r2_hidden(X0,k2_enumset1(X0,X0,X0,X0)) != iProver_top ),
% 3.18/1.01      inference(forward_subsumption_resolution,
% 3.18/1.01                [status(thm)],
% 3.18/1.01                [c_6108,c_5878]) ).
% 3.18/1.01  
% 3.18/1.01  cnf(c_4,plain,
% 3.18/1.01      ( r2_hidden(X0,k2_enumset1(X0,X0,X0,X1)) ),
% 3.18/1.01      inference(cnf_transformation,[],[f81]) ).
% 3.18/1.01  
% 3.18/1.01  cnf(c_731,plain,
% 3.18/1.01      ( r2_hidden(X0,k2_enumset1(X0,X0,X0,X1)) = iProver_top ),
% 3.18/1.01      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 3.18/1.01  
% 3.18/1.01  cnf(c_6750,plain,
% 3.18/1.01      ( k2_enumset1(X0,X0,X0,X0) = k1_xboole_0
% 3.18/1.01      | k1_setfam_1(k2_enumset1(X0,X0,X0,X0)) = X0 ),
% 3.18/1.01      inference(forward_subsumption_resolution,
% 3.18/1.01                [status(thm)],
% 3.18/1.01                [c_6164,c_731]) ).
% 3.18/1.01  
% 3.18/1.01  cnf(c_23,negated_conjecture,
% 3.18/1.01      ( k1_setfam_1(k2_enumset1(sK4,sK4,sK4,sK4)) != sK4 ),
% 3.18/1.01      inference(cnf_transformation,[],[f77]) ).
% 3.18/1.01  
% 3.18/1.01  cnf(c_6756,plain,
% 3.18/1.01      ( k2_enumset1(sK4,sK4,sK4,sK4) = k1_xboole_0 ),
% 3.18/1.01      inference(superposition,[status(thm)],[c_6750,c_23]) ).
% 3.18/1.01  
% 3.18/1.01  cnf(c_14,plain,
% 3.18/1.01      ( ~ r1_tarski(k2_enumset1(X0,X0,X0,X0),k2_enumset1(X1,X1,X1,X1))
% 3.18/1.01      | X1 = X0 ),
% 3.18/1.01      inference(cnf_transformation,[],[f76]) ).
% 3.18/1.01  
% 3.18/1.01  cnf(c_723,plain,
% 3.18/1.01      ( X0 = X1
% 3.18/1.01      | r1_tarski(k2_enumset1(X1,X1,X1,X1),k2_enumset1(X0,X0,X0,X0)) != iProver_top ),
% 3.18/1.01      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 3.18/1.01  
% 3.18/1.01  cnf(c_6962,plain,
% 3.18/1.01      ( sK4 = X0
% 3.18/1.01      | r1_tarski(k1_xboole_0,k2_enumset1(X0,X0,X0,X0)) != iProver_top ),
% 3.18/1.01      inference(superposition,[status(thm)],[c_6756,c_723]) ).
% 3.18/1.01  
% 3.18/1.01  cnf(c_7116,plain,
% 3.18/1.01      ( sK4 = k1_xboole_0
% 3.18/1.01      | r1_tarski(k1_xboole_0,k2_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0)) != iProver_top ),
% 3.18/1.01      inference(instantiation,[status(thm)],[c_6962]) ).
% 3.18/1.01  
% 3.18/1.01  cnf(c_408,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 3.18/1.01  
% 3.18/1.01  cnf(c_964,plain,
% 3.18/1.01      ( X0 != X1 | sK4 != X1 | sK4 = X0 ),
% 3.18/1.01      inference(instantiation,[status(thm)],[c_408]) ).
% 3.18/1.01  
% 3.18/1.01  cnf(c_3188,plain,
% 3.18/1.01      ( k1_setfam_1(X0) != X1 | sK4 != X1 | sK4 = k1_setfam_1(X0) ),
% 3.18/1.01      inference(instantiation,[status(thm)],[c_964]) ).
% 3.18/1.01  
% 3.18/1.01  cnf(c_3189,plain,
% 3.18/1.01      ( k1_setfam_1(k1_xboole_0) != k1_xboole_0
% 3.18/1.01      | sK4 = k1_setfam_1(k1_xboole_0)
% 3.18/1.01      | sK4 != k1_xboole_0 ),
% 3.18/1.01      inference(instantiation,[status(thm)],[c_3188]) ).
% 3.18/1.01  
% 3.18/1.01  cnf(c_413,plain,
% 3.18/1.01      ( X0 != X1 | k1_setfam_1(X0) = k1_setfam_1(X1) ),
% 3.18/1.01      theory(equality) ).
% 3.18/1.01  
% 3.18/1.01  cnf(c_1115,plain,
% 3.18/1.01      ( k2_enumset1(sK4,sK4,sK4,sK4) != X0
% 3.18/1.01      | k1_setfam_1(k2_enumset1(sK4,sK4,sK4,sK4)) = k1_setfam_1(X0) ),
% 3.18/1.01      inference(instantiation,[status(thm)],[c_413]) ).
% 3.18/1.01  
% 3.18/1.01  cnf(c_1117,plain,
% 3.18/1.01      ( k2_enumset1(sK4,sK4,sK4,sK4) != k1_xboole_0
% 3.18/1.01      | k1_setfam_1(k2_enumset1(sK4,sK4,sK4,sK4)) = k1_setfam_1(k1_xboole_0) ),
% 3.18/1.01      inference(instantiation,[status(thm)],[c_1115]) ).
% 3.18/1.01  
% 3.18/1.01  cnf(c_890,plain,
% 3.18/1.01      ( k1_setfam_1(k2_enumset1(sK4,sK4,sK4,sK4)) != X0
% 3.18/1.01      | k1_setfam_1(k2_enumset1(sK4,sK4,sK4,sK4)) = sK4
% 3.18/1.01      | sK4 != X0 ),
% 3.18/1.01      inference(instantiation,[status(thm)],[c_408]) ).
% 3.18/1.01  
% 3.18/1.01  cnf(c_1114,plain,
% 3.18/1.01      ( k1_setfam_1(k2_enumset1(sK4,sK4,sK4,sK4)) != k1_setfam_1(X0)
% 3.18/1.01      | k1_setfam_1(k2_enumset1(sK4,sK4,sK4,sK4)) = sK4
% 3.18/1.01      | sK4 != k1_setfam_1(X0) ),
% 3.18/1.01      inference(instantiation,[status(thm)],[c_890]) ).
% 3.18/1.01  
% 3.18/1.01  cnf(c_1116,plain,
% 3.18/1.01      ( k1_setfam_1(k2_enumset1(sK4,sK4,sK4,sK4)) != k1_setfam_1(k1_xboole_0)
% 3.18/1.01      | k1_setfam_1(k2_enumset1(sK4,sK4,sK4,sK4)) = sK4
% 3.18/1.01      | sK4 != k1_setfam_1(k1_xboole_0) ),
% 3.18/1.01      inference(instantiation,[status(thm)],[c_1114]) ).
% 3.18/1.01  
% 3.18/1.01  cnf(c_7,plain,
% 3.18/1.01      ( r1_tarski(k1_xboole_0,k2_enumset1(X0,X0,X0,X0)) ),
% 3.18/1.01      inference(cnf_transformation,[],[f84]) ).
% 3.18/1.01  
% 3.18/1.01  cnf(c_57,plain,
% 3.18/1.01      ( r1_tarski(k1_xboole_0,k2_enumset1(X0,X0,X0,X0)) = iProver_top ),
% 3.18/1.01      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 3.18/1.01  
% 3.18/1.01  cnf(c_59,plain,
% 3.18/1.01      ( r1_tarski(k1_xboole_0,k2_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0)) = iProver_top ),
% 3.18/1.01      inference(instantiation,[status(thm)],[c_57]) ).
% 3.18/1.01  
% 3.18/1.01  cnf(c_16,plain,
% 3.18/1.01      ( k1_setfam_1(k1_xboole_0) = k1_xboole_0 ),
% 3.18/1.01      inference(cnf_transformation,[],[f90]) ).
% 3.18/1.01  
% 3.18/1.01  cnf(contradiction,plain,
% 3.18/1.01      ( $false ),
% 3.18/1.01      inference(minisat,
% 3.18/1.01                [status(thm)],
% 3.18/1.01                [c_7116,c_6756,c_3189,c_1117,c_1116,c_59,c_16,c_23]) ).
% 3.18/1.01  
% 3.18/1.01  
% 3.18/1.01  % SZS output end CNFRefutation for theBenchmark.p
% 3.18/1.01  
% 3.18/1.01  ------                               Statistics
% 3.18/1.01  
% 3.18/1.01  ------ General
% 3.18/1.01  
% 3.18/1.01  abstr_ref_over_cycles:                  0
% 3.18/1.01  abstr_ref_under_cycles:                 0
% 3.18/1.01  gc_basic_clause_elim:                   0
% 3.18/1.01  forced_gc_time:                         0
% 3.18/1.01  parsing_time:                           0.012
% 3.18/1.01  unif_index_cands_time:                  0.
% 3.18/1.01  unif_index_add_time:                    0.
% 3.18/1.01  orderings_time:                         0.
% 3.18/1.01  out_proof_time:                         0.009
% 3.18/1.01  total_time:                             0.24
% 3.18/1.01  num_of_symbols:                         42
% 3.18/1.01  num_of_terms:                           8022
% 3.18/1.01  
% 3.18/1.01  ------ Preprocessing
% 3.18/1.01  
% 3.18/1.01  num_of_splits:                          0
% 3.18/1.01  num_of_split_atoms:                     0
% 3.18/1.01  num_of_reused_defs:                     0
% 3.18/1.01  num_eq_ax_congr_red:                    27
% 3.18/1.01  num_of_sem_filtered_clauses:            1
% 3.18/1.01  num_of_subtypes:                        0
% 3.18/1.01  monotx_restored_types:                  0
% 3.18/1.01  sat_num_of_epr_types:                   0
% 3.18/1.01  sat_num_of_non_cyclic_types:            0
% 3.18/1.01  sat_guarded_non_collapsed_types:        0
% 3.18/1.01  num_pure_diseq_elim:                    0
% 3.18/1.01  simp_replaced_by:                       0
% 3.18/1.01  res_preprocessed:                       107
% 3.18/1.01  prep_upred:                             0
% 3.18/1.01  prep_unflattend:                        4
% 3.18/1.01  smt_new_axioms:                         0
% 3.18/1.01  pred_elim_cands:                        2
% 3.18/1.01  pred_elim:                              0
% 3.18/1.01  pred_elim_cl:                           0
% 3.18/1.01  pred_elim_cycles:                       2
% 3.18/1.01  merged_defs:                            0
% 3.18/1.01  merged_defs_ncl:                        0
% 3.18/1.01  bin_hyper_res:                          0
% 3.18/1.01  prep_cycles:                            4
% 3.18/1.01  pred_elim_time:                         0.001
% 3.18/1.01  splitting_time:                         0.
% 3.18/1.01  sem_filter_time:                        0.
% 3.18/1.01  monotx_time:                            0.
% 3.18/1.01  subtype_inf_time:                       0.
% 3.18/1.01  
% 3.18/1.01  ------ Problem properties
% 3.18/1.01  
% 3.18/1.01  clauses:                                23
% 3.18/1.01  conjectures:                            1
% 3.18/1.01  epr:                                    0
% 3.18/1.01  horn:                                   12
% 3.18/1.01  ground:                                 2
% 3.18/1.01  unary:                                  8
% 3.18/1.01  binary:                                 3
% 3.18/1.01  lits:                                   56
% 3.18/1.01  lits_eq:                                27
% 3.18/1.01  fd_pure:                                0
% 3.18/1.01  fd_pseudo:                              0
% 3.18/1.01  fd_cond:                                3
% 3.18/1.01  fd_pseudo_cond:                         10
% 3.18/1.01  ac_symbols:                             0
% 3.18/1.01  
% 3.18/1.01  ------ Propositional Solver
% 3.18/1.01  
% 3.18/1.01  prop_solver_calls:                      27
% 3.18/1.01  prop_fast_solver_calls:                 722
% 3.18/1.01  smt_solver_calls:                       0
% 3.18/1.01  smt_fast_solver_calls:                  0
% 3.18/1.01  prop_num_of_clauses:                    2128
% 3.18/1.01  prop_preprocess_simplified:             5753
% 3.18/1.01  prop_fo_subsumed:                       0
% 3.18/1.01  prop_solver_time:                       0.
% 3.18/1.01  smt_solver_time:                        0.
% 3.18/1.01  smt_fast_solver_time:                   0.
% 3.18/1.01  prop_fast_solver_time:                  0.
% 3.18/1.01  prop_unsat_core_time:                   0.
% 3.18/1.01  
% 3.18/1.01  ------ QBF
% 3.18/1.01  
% 3.18/1.01  qbf_q_res:                              0
% 3.18/1.01  qbf_num_tautologies:                    0
% 3.18/1.01  qbf_prep_cycles:                        0
% 3.18/1.01  
% 3.18/1.01  ------ BMC1
% 3.18/1.01  
% 3.18/1.01  bmc1_current_bound:                     -1
% 3.18/1.01  bmc1_last_solved_bound:                 -1
% 3.18/1.01  bmc1_unsat_core_size:                   -1
% 3.18/1.01  bmc1_unsat_core_parents_size:           -1
% 3.18/1.01  bmc1_merge_next_fun:                    0
% 3.18/1.01  bmc1_unsat_core_clauses_time:           0.
% 3.18/1.01  
% 3.18/1.01  ------ Instantiation
% 3.18/1.01  
% 3.18/1.01  inst_num_of_clauses:                    528
% 3.18/1.01  inst_num_in_passive:                    102
% 3.18/1.01  inst_num_in_active:                     191
% 3.18/1.01  inst_num_in_unprocessed:                235
% 3.18/1.01  inst_num_of_loops:                      260
% 3.18/1.01  inst_num_of_learning_restarts:          0
% 3.18/1.01  inst_num_moves_active_passive:          67
% 3.18/1.01  inst_lit_activity:                      0
% 3.18/1.01  inst_lit_activity_moves:                0
% 3.18/1.01  inst_num_tautologies:                   0
% 3.18/1.01  inst_num_prop_implied:                  0
% 3.18/1.01  inst_num_existing_simplified:           0
% 3.18/1.01  inst_num_eq_res_simplified:             0
% 3.18/1.01  inst_num_child_elim:                    0
% 3.18/1.01  inst_num_of_dismatching_blockings:      440
% 3.18/1.01  inst_num_of_non_proper_insts:           568
% 3.18/1.01  inst_num_of_duplicates:                 0
% 3.18/1.01  inst_inst_num_from_inst_to_res:         0
% 3.18/1.01  inst_dismatching_checking_time:         0.
% 3.18/1.01  
% 3.18/1.01  ------ Resolution
% 3.18/1.01  
% 3.18/1.01  res_num_of_clauses:                     0
% 3.18/1.01  res_num_in_passive:                     0
% 3.18/1.01  res_num_in_active:                      0
% 3.18/1.01  res_num_of_loops:                       111
% 3.18/1.01  res_forward_subset_subsumed:            88
% 3.18/1.01  res_backward_subset_subsumed:           0
% 3.18/1.01  res_forward_subsumed:                   0
% 3.18/1.01  res_backward_subsumed:                  0
% 3.18/1.01  res_forward_subsumption_resolution:     0
% 3.18/1.01  res_backward_subsumption_resolution:    0
% 3.18/1.01  res_clause_to_clause_subsumption:       1591
% 3.18/1.01  res_orphan_elimination:                 0
% 3.18/1.01  res_tautology_del:                      18
% 3.18/1.01  res_num_eq_res_simplified:              0
% 3.18/1.01  res_num_sel_changes:                    0
% 3.18/1.01  res_moves_from_active_to_pass:          0
% 3.18/1.01  
% 3.18/1.01  ------ Superposition
% 3.18/1.01  
% 3.18/1.01  sup_time_total:                         0.
% 3.18/1.01  sup_time_generating:                    0.
% 3.18/1.01  sup_time_sim_full:                      0.
% 3.18/1.01  sup_time_sim_immed:                     0.
% 3.18/1.01  
% 3.18/1.01  sup_num_of_clauses:                     210
% 3.18/1.01  sup_num_in_active:                      49
% 3.18/1.01  sup_num_in_passive:                     161
% 3.18/1.01  sup_num_of_loops:                       50
% 3.18/1.01  sup_fw_superposition:                   106
% 3.18/1.01  sup_bw_superposition:                   151
% 3.18/1.01  sup_immediate_simplified:               17
% 3.18/1.01  sup_given_eliminated:                   0
% 3.18/1.01  comparisons_done:                       0
% 3.18/1.01  comparisons_avoided:                    54
% 3.18/1.01  
% 3.18/1.01  ------ Simplifications
% 3.18/1.01  
% 3.18/1.01  
% 3.18/1.01  sim_fw_subset_subsumed:                 6
% 3.18/1.01  sim_bw_subset_subsumed:                 2
% 3.18/1.01  sim_fw_subsumed:                        8
% 3.18/1.01  sim_bw_subsumed:                        3
% 3.18/1.01  sim_fw_subsumption_res:                 3
% 3.18/1.01  sim_bw_subsumption_res:                 0
% 3.18/1.01  sim_tautology_del:                      6
% 3.18/1.01  sim_eq_tautology_del:                   10
% 3.18/1.01  sim_eq_res_simp:                        1
% 3.18/1.01  sim_fw_demodulated:                     1
% 3.18/1.01  sim_bw_demodulated:                     1
% 3.18/1.01  sim_light_normalised:                   9
% 3.18/1.01  sim_joinable_taut:                      0
% 3.18/1.01  sim_joinable_simp:                      0
% 3.18/1.01  sim_ac_normalised:                      0
% 3.18/1.01  sim_smt_subsumption:                    0
% 3.18/1.01  
%------------------------------------------------------------------------------
