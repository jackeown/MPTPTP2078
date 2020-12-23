%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:41:33 EST 2020

% Result     : Theorem 11.49s
% Output     : CNFRefutation 11.49s
% Verified   : 
% Statistics : Number of formulae       :  204 (2328 expanded)
%              Number of clauses        :  109 ( 524 expanded)
%              Number of leaves         :   27 ( 658 expanded)
%              Depth                    :   22
%              Number of atoms          :  688 (10906 expanded)
%              Number of equality atoms :  297 (5334 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal clause size      :   20 (   2 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f21,plain,(
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

fof(f22,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f21])).

fof(f23,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK0(X0,X1),X1)
          & r2_hidden(sK0(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f22,f23])).

fof(f50,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK0(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( k3_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] :
              ( r2_hidden(X3,X0)
              & r2_hidden(X2,X3) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( k3_tarski(X0) = X1
        | ? [X2] :
            ( ( ! [X3] :
                  ( ~ r2_hidden(X3,X0)
                  | ~ r2_hidden(X2,X3) )
              | ~ r2_hidden(X2,X1) )
            & ( ? [X3] :
                  ( r2_hidden(X3,X0)
                  & r2_hidden(X2,X3) )
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | ! [X3] :
                  ( ~ r2_hidden(X3,X0)
                  | ~ r2_hidden(X2,X3) ) )
            & ( ? [X3] :
                  ( r2_hidden(X3,X0)
                  & r2_hidden(X2,X3) )
              | ~ r2_hidden(X2,X1) ) )
        | k3_tarski(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f7])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( k3_tarski(X0) = X1
        | ? [X2] :
            ( ( ! [X3] :
                  ( ~ r2_hidden(X3,X0)
                  | ~ r2_hidden(X2,X3) )
              | ~ r2_hidden(X2,X1) )
            & ( ? [X4] :
                  ( r2_hidden(X4,X0)
                  & r2_hidden(X2,X4) )
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] :
                  ( ~ r2_hidden(X6,X0)
                  | ~ r2_hidden(X5,X6) ) )
            & ( ? [X7] :
                  ( r2_hidden(X7,X0)
                  & r2_hidden(X5,X7) )
              | ~ r2_hidden(X5,X1) ) )
        | k3_tarski(X0) != X1 ) ) ),
    inference(rectify,[],[f32])).

fof(f36,plain,(
    ! [X5,X0] :
      ( ? [X7] :
          ( r2_hidden(X7,X0)
          & r2_hidden(X5,X7) )
     => ( r2_hidden(sK4(X0,X5),X0)
        & r2_hidden(X5,sK4(X0,X5)) ) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( r2_hidden(X4,X0)
          & r2_hidden(X2,X4) )
     => ( r2_hidden(sK3(X0,X1),X0)
        & r2_hidden(X2,sK3(X0,X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ! [X3] :
                ( ~ r2_hidden(X3,X0)
                | ~ r2_hidden(X2,X3) )
            | ~ r2_hidden(X2,X1) )
          & ( ? [X4] :
                ( r2_hidden(X4,X0)
                & r2_hidden(X2,X4) )
            | r2_hidden(X2,X1) ) )
     => ( ( ! [X3] :
              ( ~ r2_hidden(X3,X0)
              | ~ r2_hidden(sK2(X0,X1),X3) )
          | ~ r2_hidden(sK2(X0,X1),X1) )
        & ( ? [X4] :
              ( r2_hidden(X4,X0)
              & r2_hidden(sK2(X0,X1),X4) )
          | r2_hidden(sK2(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( k3_tarski(X0) = X1
        | ( ( ! [X3] :
                ( ~ r2_hidden(X3,X0)
                | ~ r2_hidden(sK2(X0,X1),X3) )
            | ~ r2_hidden(sK2(X0,X1),X1) )
          & ( ( r2_hidden(sK3(X0,X1),X0)
              & r2_hidden(sK2(X0,X1),sK3(X0,X1)) )
            | r2_hidden(sK2(X0,X1),X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] :
                  ( ~ r2_hidden(X6,X0)
                  | ~ r2_hidden(X5,X6) ) )
            & ( ( r2_hidden(sK4(X0,X5),X0)
                & r2_hidden(X5,sK4(X0,X5)) )
              | ~ r2_hidden(X5,X1) ) )
        | k3_tarski(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f33,f36,f35,f34])).

fof(f67,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(sK4(X0,X5),X0)
      | ~ r2_hidden(X5,X1)
      | k3_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f37])).

fof(f114,plain,(
    ! [X0,X5] :
      ( r2_hidden(sK4(X0,X5),X0)
      | ~ r2_hidden(X5,k3_tarski(X0)) ) ),
    inference(equality_resolution,[],[f67])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))
    <=> ( X0 != X2
        & r2_hidden(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))
        | X0 = X2
        | ~ r2_hidden(X0,X1) )
      & ( ( X0 != X2
          & r2_hidden(X0,X1) )
        | ~ r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) ) ) ),
    inference(nnf_transformation,[],[f9])).

fof(f40,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))
        | X0 = X2
        | ~ r2_hidden(X0,X1) )
      & ( ( X0 != X2
          & r2_hidden(X0,X1) )
        | ~ r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) ) ) ),
    inference(flattening,[],[f39])).

fof(f74,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,X1)
      | ~ r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f4,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f63,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f5,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f64,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f5])).

fof(f6,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f65,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f6])).

fof(f88,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f64,f65])).

fof(f89,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f63,f88])).

fof(f102,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,X1)
      | ~ r2_hidden(X0,k4_xboole_0(X1,k2_enumset1(X2,X2,X2,X2))) ) ),
    inference(definition_unfolding,[],[f74,f89])).

fof(f51,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK0(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f3,axiom,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ~ ( X2 != X4
              & X1 != X4
              & X0 != X4 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( X2 = X4
            | X1 = X4
            | X0 = X4 ) ) ) ),
    inference(ennf_transformation,[],[f3])).

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
    inference(nnf_transformation,[],[f16])).

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

fof(f57,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X1 != X5
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f31])).

fof(f95,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X1 != X5
      | k2_enumset1(X0,X0,X1,X2) != X3 ) ),
    inference(definition_unfolding,[],[f57,f65])).

fof(f108,plain,(
    ! [X2,X0,X5,X3] :
      ( r2_hidden(X5,X3)
      | k2_enumset1(X0,X0,X5,X2) != X3 ) ),
    inference(equality_resolution,[],[f95])).

fof(f109,plain,(
    ! [X2,X0,X5] : r2_hidden(X5,k2_enumset1(X0,X0,X5,X2)) ),
    inference(equality_resolution,[],[f108])).

fof(f58,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X2 != X5
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f31])).

fof(f94,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X2 != X5
      | k2_enumset1(X0,X0,X1,X2) != X3 ) ),
    inference(definition_unfolding,[],[f58,f65])).

fof(f106,plain,(
    ! [X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | k2_enumset1(X0,X0,X1,X5) != X3 ) ),
    inference(equality_resolution,[],[f94])).

fof(f107,plain,(
    ! [X0,X5,X1] : r2_hidden(X5,k2_enumset1(X0,X0,X1,X5)) ),
    inference(equality_resolution,[],[f106])).

fof(f12,axiom,(
    ! [X0] :
      ( r2_hidden(k1_xboole_0,X0)
     => k1_xboole_0 = k1_setfam_1(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0] :
      ( k1_xboole_0 = k1_setfam_1(X0)
      | ~ r2_hidden(k1_xboole_0,X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f86,plain,(
    ! [X0] :
      ( k1_xboole_0 = k1_setfam_1(X0)
      | ~ r2_hidden(k1_xboole_0,X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => r1_tarski(k1_setfam_1(X1),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_setfam_1(X1),X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f85,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_setfam_1(X1),X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

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

fof(f54,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( X0 != X2
      | ~ r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f101,plain,(
    ! [X2,X0,X1] :
      ( X0 != X2
      | ~ r2_hidden(X0,k4_xboole_0(X1,k2_enumset1(X2,X2,X2,X2))) ) ),
    inference(definition_unfolding,[],[f75,f89])).

fof(f116,plain,(
    ! [X2,X1] : ~ r2_hidden(X2,k4_xboole_0(X1,k2_enumset1(X2,X2,X2,X2))) ),
    inference(equality_resolution,[],[f101])).

fof(f49,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

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

fof(f17,plain,(
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
    inference(nnf_transformation,[],[f17])).

fof(f42,plain,(
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
    inference(rectify,[],[f41])).

fof(f45,plain,(
    ! [X5,X0] :
      ( ? [X6] :
          ( ~ r2_hidden(X5,X6)
          & r2_hidden(X6,X0) )
     => ( ~ r2_hidden(X5,sK7(X0,X5))
        & r2_hidden(sK7(X0,X5),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f44,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r2_hidden(X2,X3)
          & r2_hidden(X3,X0) )
     => ( ~ r2_hidden(X2,sK6(X0,X1))
        & r2_hidden(sK6(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f43,plain,(
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
              ( ~ r2_hidden(sK5(X0,X1),X3)
              & r2_hidden(X3,X0) )
          | ~ r2_hidden(sK5(X0,X1),X1) )
        & ( ! [X4] :
              ( r2_hidden(sK5(X0,X1),X4)
              | ~ r2_hidden(X4,X0) )
          | r2_hidden(sK5(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ( ( ( k1_setfam_1(X0) = X1
            | k1_xboole_0 != X1 )
          & ( k1_xboole_0 = X1
            | k1_setfam_1(X0) != X1 ) )
        | k1_xboole_0 != X0 )
      & ( ( ( k1_setfam_1(X0) = X1
            | ( ( ( ~ r2_hidden(sK5(X0,X1),sK6(X0,X1))
                  & r2_hidden(sK6(X0,X1),X0) )
                | ~ r2_hidden(sK5(X0,X1),X1) )
              & ( ! [X4] :
                    ( r2_hidden(sK5(X0,X1),X4)
                    | ~ r2_hidden(X4,X0) )
                | r2_hidden(sK5(X0,X1),X1) ) ) )
          & ( ! [X5] :
                ( ( r2_hidden(X5,X1)
                  | ( ~ r2_hidden(X5,sK7(X0,X5))
                    & r2_hidden(sK7(X0,X5),X0) ) )
                & ( ! [X7] :
                      ( r2_hidden(X5,X7)
                      | ~ r2_hidden(X7,X0) )
                  | ~ r2_hidden(X5,X1) ) )
            | k1_setfam_1(X0) != X1 ) )
        | k1_xboole_0 = X0 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6,sK7])],[f42,f45,f44,f43])).

fof(f80,plain,(
    ! [X4,X0,X1] :
      ( k1_setfam_1(X0) = X1
      | r2_hidden(sK5(X0,X1),X4)
      | ~ r2_hidden(X4,X0)
      | r2_hidden(sK5(X0,X1),X1)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f46])).

fof(f13,conjecture,(
    ! [X0] : k1_setfam_1(k1_tarski(X0)) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,negated_conjecture,(
    ~ ! [X0] : k1_setfam_1(k1_tarski(X0)) = X0 ),
    inference(negated_conjecture,[],[f13])).

fof(f20,plain,(
    ? [X0] : k1_setfam_1(k1_tarski(X0)) != X0 ),
    inference(ennf_transformation,[],[f14])).

fof(f47,plain,
    ( ? [X0] : k1_setfam_1(k1_tarski(X0)) != X0
   => k1_setfam_1(k1_tarski(sK8)) != sK8 ),
    introduced(choice_axiom,[])).

fof(f48,plain,(
    k1_setfam_1(k1_tarski(sK8)) != sK8 ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8])],[f20,f47])).

fof(f87,plain,(
    k1_setfam_1(k1_tarski(sK8)) != sK8 ),
    inference(cnf_transformation,[],[f48])).

fof(f103,plain,(
    k1_setfam_1(k2_enumset1(sK8,sK8,sK8,sK8)) != sK8 ),
    inference(definition_unfolding,[],[f87,f89])).

fof(f81,plain,(
    ! [X0,X1] :
      ( k1_setfam_1(X0) = X1
      | r2_hidden(sK6(X0,X1),X0)
      | ~ r2_hidden(sK5(X0,X1),X1)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f46])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
    <=> r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(k1_tarski(X0),X1)
        | ~ r2_hidden(X0,X1) )
      & ( r2_hidden(X0,X1)
        | ~ r1_tarski(k1_tarski(X0),X1) ) ) ),
    inference(nnf_transformation,[],[f8])).

fof(f72,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | ~ r1_tarski(k1_tarski(X0),X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f99,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | ~ r1_tarski(k2_enumset1(X0,X0,X0,X0),X1) ) ),
    inference(definition_unfolding,[],[f72,f89])).

fof(f52,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f105,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f52])).

fof(f55,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( X2 = X5
      | X1 = X5
      | X0 = X5
      | ~ r2_hidden(X5,X3)
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f31])).

fof(f97,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( X2 = X5
      | X1 = X5
      | X0 = X5
      | ~ r2_hidden(X5,X3)
      | k2_enumset1(X0,X0,X1,X2) != X3 ) ),
    inference(definition_unfolding,[],[f55,f65])).

fof(f112,plain,(
    ! [X2,X0,X5,X1] :
      ( X2 = X5
      | X1 = X5
      | X0 = X5
      | ~ r2_hidden(X5,k2_enumset1(X0,X0,X1,X2)) ) ),
    inference(equality_resolution,[],[f97])).

fof(f83,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = X1
      | k1_setfam_1(X0) != X1
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f46])).

fof(f119,plain,(
    ! [X0] :
      ( k1_xboole_0 = k1_setfam_1(X0)
      | k1_xboole_0 != X0 ) ),
    inference(equality_resolution,[],[f83])).

fof(f120,plain,(
    k1_xboole_0 = k1_setfam_1(k1_xboole_0) ),
    inference(equality_resolution,[],[f119])).

fof(f82,plain,(
    ! [X0,X1] :
      ( k1_setfam_1(X0) = X1
      | ~ r2_hidden(sK5(X0,X1),sK6(X0,X1))
      | ~ r2_hidden(sK5(X0,X1),X1)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f46])).

fof(f68,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | ~ r2_hidden(X6,X0)
      | ~ r2_hidden(X5,X6)
      | k3_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f37])).

fof(f113,plain,(
    ! [X6,X0,X5] :
      ( r2_hidden(X5,k3_tarski(X0))
      | ~ r2_hidden(X6,X0)
      | ~ r2_hidden(X5,X6) ) ),
    inference(equality_resolution,[],[f68])).

fof(f56,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X0 != X5
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f31])).

fof(f96,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X0 != X5
      | k2_enumset1(X0,X0,X1,X2) != X3 ) ),
    inference(definition_unfolding,[],[f56,f65])).

fof(f110,plain,(
    ! [X2,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | k2_enumset1(X5,X5,X1,X2) != X3 ) ),
    inference(equality_resolution,[],[f96])).

fof(f111,plain,(
    ! [X2,X5,X1] : r2_hidden(X5,k2_enumset1(X5,X5,X1,X2)) ),
    inference(equality_resolution,[],[f110])).

cnf(c_1,plain,
    ( r2_hidden(sK0(X0,X1),X0)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_1249,plain,
    ( r2_hidden(sK0(X0,X1),X0) = iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_18,plain,
    ( ~ r2_hidden(X0,k3_tarski(X1))
    | r2_hidden(sK4(X1,X0),X1) ),
    inference(cnf_transformation,[],[f114])).

cnf(c_1233,plain,
    ( r2_hidden(X0,k3_tarski(X1)) != iProver_top
    | r2_hidden(sK4(X1,X0),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_24,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k4_xboole_0(X1,k2_enumset1(X2,X2,X2,X2))) ),
    inference(cnf_transformation,[],[f102])).

cnf(c_1227,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r2_hidden(X0,k4_xboole_0(X1,k2_enumset1(X2,X2,X2,X2))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_3172,plain,
    ( r2_hidden(sK0(k4_xboole_0(X0,k2_enumset1(X1,X1,X1,X1)),X2),X0) = iProver_top
    | r1_tarski(k4_xboole_0(X0,k2_enumset1(X1,X1,X1,X1)),X2) = iProver_top ),
    inference(superposition,[status(thm)],[c_1249,c_1227])).

cnf(c_0,plain,
    ( ~ r2_hidden(sK0(X0,X1),X1)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_1250,plain,
    ( r2_hidden(sK0(X0,X1),X1) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_33825,plain,
    ( r1_tarski(k4_xboole_0(X0,k2_enumset1(X1,X1,X1,X1)),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_3172,c_1250])).

cnf(c_11,plain,
    ( r2_hidden(X0,k2_enumset1(X1,X1,X0,X2)) ),
    inference(cnf_transformation,[],[f109])).

cnf(c_1240,plain,
    ( r2_hidden(X0,k2_enumset1(X1,X1,X0,X2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_10,plain,
    ( r2_hidden(X0,k2_enumset1(X1,X1,X2,X0)) ),
    inference(cnf_transformation,[],[f107])).

cnf(c_1241,plain,
    ( r2_hidden(X0,k2_enumset1(X1,X1,X2,X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_34,plain,
    ( ~ r2_hidden(k1_xboole_0,X0)
    | k1_setfam_1(X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f86])).

cnf(c_1219,plain,
    ( k1_setfam_1(X0) = k1_xboole_0
    | r2_hidden(k1_xboole_0,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_1635,plain,
    ( k1_setfam_1(k2_enumset1(X0,X0,X1,k1_xboole_0)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1241,c_1219])).

cnf(c_33,plain,
    ( ~ r2_hidden(X0,X1)
    | r1_tarski(k1_setfam_1(X1),X0) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_1220,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r1_tarski(k1_setfam_1(X1),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_1821,plain,
    ( r2_hidden(X0,k2_enumset1(X1,X1,X2,k1_xboole_0)) != iProver_top
    | r1_tarski(k1_xboole_0,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1635,c_1220])).

cnf(c_3459,plain,
    ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1240,c_1821])).

cnf(c_3,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f54])).

cnf(c_1247,plain,
    ( X0 = X1
    | r1_tarski(X1,X0) != iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_3481,plain,
    ( k1_xboole_0 = X0
    | r1_tarski(X0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_3459,c_1247])).

cnf(c_33971,plain,
    ( k4_xboole_0(k1_xboole_0,k2_enumset1(X0,X0,X0,X0)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_33825,c_3481])).

cnf(c_23,plain,
    ( ~ r2_hidden(X0,k4_xboole_0(X1,k2_enumset1(X0,X0,X0,X0))) ),
    inference(cnf_transformation,[],[f116])).

cnf(c_1228,plain,
    ( r2_hidden(X0,k4_xboole_0(X1,k2_enumset1(X0,X0,X0,X0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_35358,plain,
    ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_33971,c_1228])).

cnf(c_36198,plain,
    ( r2_hidden(X0,k3_tarski(k1_xboole_0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1233,c_35358])).

cnf(c_36286,plain,
    ( r1_tarski(k3_tarski(k1_xboole_0),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1249,c_36198])).

cnf(c_36816,plain,
    ( k3_tarski(k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_36286,c_3481])).

cnf(c_582,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X1)
    | X2 != X0 ),
    theory(equality)).

cnf(c_2699,plain,
    ( ~ r1_tarski(X0,k1_setfam_1(k2_enumset1(sK8,sK8,sK8,sK8)))
    | r1_tarski(X1,k1_setfam_1(k2_enumset1(sK8,sK8,sK8,sK8)))
    | X1 != X0 ),
    inference(instantiation,[status(thm)],[c_582])).

cnf(c_26407,plain,
    ( ~ r1_tarski(X0,k1_setfam_1(k2_enumset1(sK8,sK8,sK8,sK8)))
    | r1_tarski(k3_tarski(X1),k1_setfam_1(k2_enumset1(sK8,sK8,sK8,sK8)))
    | k3_tarski(X1) != X0 ),
    inference(instantiation,[status(thm)],[c_2699])).

cnf(c_26413,plain,
    ( r1_tarski(k3_tarski(k1_xboole_0),k1_setfam_1(k2_enumset1(sK8,sK8,sK8,sK8)))
    | ~ r1_tarski(k1_xboole_0,k1_setfam_1(k2_enumset1(sK8,sK8,sK8,sK8)))
    | k3_tarski(k1_xboole_0) != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_26407])).

cnf(c_2,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | ~ r1_tarski(X1,X2) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_2727,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,k1_setfam_1(X2))
    | ~ r1_tarski(X1,k1_setfam_1(X2)) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_16934,plain,
    ( ~ r2_hidden(sK0(sK8,k1_setfam_1(k2_enumset1(sK8,sK8,sK8,sK8))),X0)
    | r2_hidden(sK0(sK8,k1_setfam_1(k2_enumset1(sK8,sK8,sK8,sK8))),k1_setfam_1(k2_enumset1(sK8,sK8,sK8,sK8)))
    | ~ r1_tarski(X0,k1_setfam_1(k2_enumset1(sK8,sK8,sK8,sK8))) ),
    inference(instantiation,[status(thm)],[c_2727])).

cnf(c_24903,plain,
    ( r2_hidden(sK0(sK8,k1_setfam_1(k2_enumset1(sK8,sK8,sK8,sK8))),k1_setfam_1(k2_enumset1(sK8,sK8,sK8,sK8)))
    | ~ r2_hidden(sK0(sK8,k1_setfam_1(k2_enumset1(sK8,sK8,sK8,sK8))),k3_tarski(X0))
    | ~ r1_tarski(k3_tarski(X0),k1_setfam_1(k2_enumset1(sK8,sK8,sK8,sK8))) ),
    inference(instantiation,[status(thm)],[c_16934])).

cnf(c_24906,plain,
    ( r2_hidden(sK0(sK8,k1_setfam_1(k2_enumset1(sK8,sK8,sK8,sK8))),k1_setfam_1(k2_enumset1(sK8,sK8,sK8,sK8)))
    | ~ r2_hidden(sK0(sK8,k1_setfam_1(k2_enumset1(sK8,sK8,sK8,sK8))),k3_tarski(k1_xboole_0))
    | ~ r1_tarski(k3_tarski(k1_xboole_0),k1_setfam_1(k2_enumset1(sK8,sK8,sK8,sK8))) ),
    inference(instantiation,[status(thm)],[c_24903])).

cnf(c_29,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(sK5(X1,X2),X2)
    | r2_hidden(sK5(X1,X2),X0)
    | k1_setfam_1(X1) = X2
    | k1_xboole_0 = X1 ),
    inference(cnf_transformation,[],[f80])).

cnf(c_35,negated_conjecture,
    ( k1_setfam_1(k2_enumset1(sK8,sK8,sK8,sK8)) != sK8 ),
    inference(cnf_transformation,[],[f103])).

cnf(c_7025,plain,
    ( ~ r2_hidden(X0,k2_enumset1(sK8,sK8,sK8,sK8))
    | r2_hidden(sK5(k2_enumset1(sK8,sK8,sK8,sK8),sK8),X0)
    | r2_hidden(sK5(k2_enumset1(sK8,sK8,sK8,sK8),sK8),sK8)
    | k1_xboole_0 = k2_enumset1(sK8,sK8,sK8,sK8) ),
    inference(resolution,[status(thm)],[c_29,c_35])).

cnf(c_28,plain,
    ( r2_hidden(sK6(X0,X1),X0)
    | ~ r2_hidden(sK5(X0,X1),X1)
    | k1_setfam_1(X0) = X1
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f81])).

cnf(c_7398,plain,
    ( ~ r2_hidden(X0,k2_enumset1(sK8,sK8,sK8,sK8))
    | r2_hidden(sK6(k2_enumset1(sK8,sK8,sK8,sK8),sK8),k2_enumset1(sK8,sK8,sK8,sK8))
    | r2_hidden(sK5(k2_enumset1(sK8,sK8,sK8,sK8),sK8),X0)
    | k1_setfam_1(k2_enumset1(sK8,sK8,sK8,sK8)) = sK8
    | k1_xboole_0 = k2_enumset1(sK8,sK8,sK8,sK8) ),
    inference(resolution,[status(thm)],[c_7025,c_28])).

cnf(c_7431,plain,
    ( r2_hidden(sK5(k2_enumset1(sK8,sK8,sK8,sK8),sK8),sK8)
    | ~ r2_hidden(sK8,k2_enumset1(sK8,sK8,sK8,sK8))
    | k1_xboole_0 = k2_enumset1(sK8,sK8,sK8,sK8) ),
    inference(factoring,[status(thm)],[c_7025])).

cnf(c_21,plain,
    ( r2_hidden(X0,X1)
    | ~ r1_tarski(k2_enumset1(X0,X0,X0,X0),X1) ),
    inference(cnf_transformation,[],[f99])).

cnf(c_1783,plain,
    ( r2_hidden(sK8,X0)
    | ~ r1_tarski(k2_enumset1(sK8,sK8,sK8,sK8),X0) ),
    inference(instantiation,[status(thm)],[c_21])).

cnf(c_1894,plain,
    ( r2_hidden(sK8,k2_enumset1(sK8,sK8,sK8,sK8))
    | ~ r1_tarski(k2_enumset1(sK8,sK8,sK8,sK8),k2_enumset1(sK8,sK8,sK8,sK8)) ),
    inference(instantiation,[status(thm)],[c_1783])).

cnf(c_5,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f105])).

cnf(c_1574,plain,
    ( r1_tarski(k2_enumset1(X0,X0,X0,X0),k2_enumset1(X0,X0,X0,X0)) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_1895,plain,
    ( r1_tarski(k2_enumset1(sK8,sK8,sK8,sK8),k2_enumset1(sK8,sK8,sK8,sK8)) ),
    inference(instantiation,[status(thm)],[c_1574])).

cnf(c_7434,plain,
    ( r2_hidden(sK5(k2_enumset1(sK8,sK8,sK8,sK8),sK8),sK8)
    | k1_xboole_0 = k2_enumset1(sK8,sK8,sK8,sK8) ),
    inference(global_propositional_subsumption,[status(thm)],[c_7431,c_1894,c_1895])).

cnf(c_7673,plain,
    ( r2_hidden(sK6(k2_enumset1(sK8,sK8,sK8,sK8),sK8),k2_enumset1(sK8,sK8,sK8,sK8))
    | k1_setfam_1(k2_enumset1(sK8,sK8,sK8,sK8)) = sK8
    | k1_xboole_0 = k2_enumset1(sK8,sK8,sK8,sK8) ),
    inference(resolution,[status(thm)],[c_7434,c_28])).

cnf(c_7677,plain,
    ( r2_hidden(sK6(k2_enumset1(sK8,sK8,sK8,sK8),sK8),k2_enumset1(sK8,sK8,sK8,sK8))
    | k1_xboole_0 = k2_enumset1(sK8,sK8,sK8,sK8) ),
    inference(global_propositional_subsumption,[status(thm)],[c_7398,c_35,c_7673])).

cnf(c_13,plain,
    ( ~ r2_hidden(X0,k2_enumset1(X1,X1,X2,X3))
    | X0 = X1
    | X0 = X2
    | X0 = X3 ),
    inference(cnf_transformation,[],[f112])).

cnf(c_7955,plain,
    ( sK6(k2_enumset1(sK8,sK8,sK8,sK8),sK8) = sK8
    | k1_xboole_0 = k2_enumset1(sK8,sK8,sK8,sK8) ),
    inference(resolution,[status(thm)],[c_7677,c_13])).

cnf(c_581,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_580,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_2666,plain,
    ( X0 != X1
    | X1 = X0 ),
    inference(resolution,[status(thm)],[c_581,c_580])).

cnf(c_7968,plain,
    ( sK8 = sK6(k2_enumset1(sK8,sK8,sK8,sK8),sK8)
    | k1_xboole_0 = k2_enumset1(sK8,sK8,sK8,sK8) ),
    inference(resolution,[status(thm)],[c_7955,c_2666])).

cnf(c_583,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_26,plain,
    ( k1_setfam_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f120])).

cnf(c_5252,plain,
    ( r2_hidden(X0,k1_setfam_1(k1_xboole_0))
    | ~ r2_hidden(X1,k1_xboole_0)
    | X0 != X1 ),
    inference(resolution,[status(thm)],[c_583,c_26])).

cnf(c_9111,plain,
    ( ~ r2_hidden(sK6(k2_enumset1(sK8,sK8,sK8,sK8),sK8),k1_xboole_0)
    | r2_hidden(sK8,k1_setfam_1(k1_xboole_0))
    | k1_xboole_0 = k2_enumset1(sK8,sK8,sK8,sK8) ),
    inference(resolution,[status(thm)],[c_7968,c_5252])).

cnf(c_1896,plain,
    ( r2_hidden(sK8,k2_enumset1(sK8,sK8,sK8,sK8)) = iProver_top
    | r1_tarski(k2_enumset1(sK8,sK8,sK8,sK8),k2_enumset1(sK8,sK8,sK8,sK8)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1894])).

cnf(c_1898,plain,
    ( r1_tarski(k2_enumset1(sK8,sK8,sK8,sK8),k2_enumset1(sK8,sK8,sK8,sK8)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1895])).

cnf(c_7432,plain,
    ( k1_xboole_0 = k2_enumset1(sK8,sK8,sK8,sK8)
    | r2_hidden(sK5(k2_enumset1(sK8,sK8,sK8,sK8),sK8),sK8) = iProver_top
    | r2_hidden(sK8,k2_enumset1(sK8,sK8,sK8,sK8)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7431])).

cnf(c_7973,plain,
    ( r2_hidden(X0,sK6(k2_enumset1(sK8,sK8,sK8,sK8),sK8))
    | ~ r2_hidden(X1,sK8)
    | X0 != X1
    | k1_xboole_0 = k2_enumset1(sK8,sK8,sK8,sK8) ),
    inference(resolution,[status(thm)],[c_7955,c_583])).

cnf(c_10096,plain,
    ( r2_hidden(X0,sK6(k2_enumset1(sK8,sK8,sK8,sK8),sK8))
    | ~ r2_hidden(X0,sK8)
    | k1_xboole_0 = k2_enumset1(sK8,sK8,sK8,sK8) ),
    inference(resolution,[status(thm)],[c_7973,c_580])).

cnf(c_27,plain,
    ( ~ r2_hidden(sK5(X0,X1),X1)
    | ~ r2_hidden(sK5(X0,X1),sK6(X0,X1))
    | k1_setfam_1(X0) = X1
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f82])).

cnf(c_11616,plain,
    ( ~ r2_hidden(sK5(k2_enumset1(sK8,sK8,sK8,sK8),sK8),sK8)
    | k1_setfam_1(k2_enumset1(sK8,sK8,sK8,sK8)) = sK8
    | k1_xboole_0 = k2_enumset1(sK8,sK8,sK8,sK8) ),
    inference(resolution,[status(thm)],[c_10096,c_27])).

cnf(c_11617,plain,
    ( k1_setfam_1(k2_enumset1(sK8,sK8,sK8,sK8)) = sK8
    | k1_xboole_0 = k2_enumset1(sK8,sK8,sK8,sK8)
    | r2_hidden(sK5(k2_enumset1(sK8,sK8,sK8,sK8),sK8),sK8) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11616])).

cnf(c_11952,plain,
    ( k1_xboole_0 = k2_enumset1(sK8,sK8,sK8,sK8) ),
    inference(global_propositional_subsumption,[status(thm)],[c_9111,c_35,c_1896,c_1898,c_7432,c_11617])).

cnf(c_586,plain,
    ( X0 != X1
    | k1_setfam_1(X0) = k1_setfam_1(X1) ),
    theory(equality)).

cnf(c_2168,plain,
    ( ~ r1_tarski(k1_setfam_1(X0),X1)
    | r1_tarski(k1_setfam_1(X2),X1)
    | X2 != X0 ),
    inference(resolution,[status(thm)],[c_582,c_586])).

cnf(c_11960,plain,
    ( ~ r1_tarski(k1_setfam_1(k2_enumset1(sK8,sK8,sK8,sK8)),X0)
    | r1_tarski(k1_setfam_1(k1_xboole_0),X0) ),
    inference(resolution,[status(thm)],[c_11952,c_2168])).

cnf(c_2161,plain,
    ( r1_tarski(k1_setfam_1(k1_xboole_0),X0)
    | ~ r1_tarski(k1_xboole_0,X0) ),
    inference(resolution,[status(thm)],[c_582,c_26])).

cnf(c_3478,plain,
    ( r1_tarski(k1_xboole_0,X0) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_3459])).

cnf(c_16020,plain,
    ( r1_tarski(k1_setfam_1(k1_xboole_0),X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_11960,c_2161,c_3478])).

cnf(c_11967,plain,
    ( k2_enumset1(sK8,sK8,sK8,sK8) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_11952,c_2666])).

cnf(c_15775,plain,
    ( r1_tarski(k1_setfam_1(k2_enumset1(sK8,sK8,sK8,sK8)),X0)
    | ~ r1_tarski(k1_setfam_1(k1_xboole_0),X0) ),
    inference(resolution,[status(thm)],[c_11967,c_2168])).

cnf(c_16696,plain,
    ( r1_tarski(k1_setfam_1(k2_enumset1(sK8,sK8,sK8,sK8)),X0) ),
    inference(backward_subsumption_resolution,[status(thm)],[c_16020,c_15775])).

cnf(c_2661,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X2 != X0
    | X1 = X2 ),
    inference(resolution,[status(thm)],[c_581,c_3])).

cnf(c_12387,plain,
    ( ~ r1_tarski(X0,k2_enumset1(sK8,sK8,sK8,sK8))
    | ~ r1_tarski(k2_enumset1(sK8,sK8,sK8,sK8),X0)
    | X0 = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_2661,c_11952])).

cnf(c_15773,plain,
    ( r1_tarski(k2_enumset1(sK8,sK8,sK8,sK8),X0)
    | ~ r1_tarski(k1_xboole_0,X0) ),
    inference(resolution,[status(thm)],[c_11967,c_582])).

cnf(c_18703,plain,
    ( ~ r1_tarski(X0,k2_enumset1(sK8,sK8,sK8,sK8))
    | X0 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_12387,c_3478,c_15773])).

cnf(c_22970,plain,
    ( k1_setfam_1(k2_enumset1(sK8,sK8,sK8,sK8)) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_16696,c_18703])).

cnf(c_9607,plain,
    ( X0 != X1
    | X0 = k1_setfam_1(k2_enumset1(sK8,sK8,sK8,sK8))
    | k1_setfam_1(k2_enumset1(sK8,sK8,sK8,sK8)) != X1 ),
    inference(instantiation,[status(thm)],[c_581])).

cnf(c_9608,plain,
    ( k1_setfam_1(k2_enumset1(sK8,sK8,sK8,sK8)) != k1_xboole_0
    | k1_xboole_0 = k1_setfam_1(k2_enumset1(sK8,sK8,sK8,sK8))
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_9607])).

cnf(c_17,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X2,X0)
    | r2_hidden(X2,k3_tarski(X1)) ),
    inference(cnf_transformation,[],[f113])).

cnf(c_6864,plain,
    ( r2_hidden(sK0(sK8,k1_setfam_1(k2_enumset1(sK8,sK8,sK8,sK8))),k3_tarski(X0))
    | ~ r2_hidden(sK0(sK8,k1_setfam_1(k2_enumset1(sK8,sK8,sK8,sK8))),sK8)
    | ~ r2_hidden(sK8,X0) ),
    inference(instantiation,[status(thm)],[c_17])).

cnf(c_6866,plain,
    ( r2_hidden(sK0(sK8,k1_setfam_1(k2_enumset1(sK8,sK8,sK8,sK8))),k3_tarski(k1_xboole_0))
    | ~ r2_hidden(sK0(sK8,k1_setfam_1(k2_enumset1(sK8,sK8,sK8,sK8))),sK8)
    | ~ r2_hidden(sK8,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_6864])).

cnf(c_5835,plain,
    ( r1_tarski(X0,k1_setfam_1(k2_enumset1(sK8,sK8,sK8,sK8)))
    | ~ r1_tarski(k1_setfam_1(k2_enumset1(sK8,sK8,sK8,sK8)),k1_setfam_1(k2_enumset1(sK8,sK8,sK8,sK8)))
    | X0 != k1_setfam_1(k2_enumset1(sK8,sK8,sK8,sK8)) ),
    inference(instantiation,[status(thm)],[c_2699])).

cnf(c_5837,plain,
    ( ~ r1_tarski(k1_setfam_1(k2_enumset1(sK8,sK8,sK8,sK8)),k1_setfam_1(k2_enumset1(sK8,sK8,sK8,sK8)))
    | r1_tarski(k1_xboole_0,k1_setfam_1(k2_enumset1(sK8,sK8,sK8,sK8)))
    | k1_xboole_0 != k1_setfam_1(k2_enumset1(sK8,sK8,sK8,sK8)) ),
    inference(instantiation,[status(thm)],[c_5835])).

cnf(c_1538,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k2_enumset1(X2,X2,X2,X2),X1)
    | k2_enumset1(X2,X2,X2,X2) != X0 ),
    inference(instantiation,[status(thm)],[c_582])).

cnf(c_4011,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k2_enumset1(sK8,sK8,sK8,sK8),X1)
    | k2_enumset1(sK8,sK8,sK8,sK8) != X0 ),
    inference(instantiation,[status(thm)],[c_1538])).

cnf(c_4013,plain,
    ( r1_tarski(k2_enumset1(sK8,sK8,sK8,sK8),k1_xboole_0)
    | ~ r1_tarski(k1_xboole_0,k1_xboole_0)
    | k2_enumset1(sK8,sK8,sK8,sK8) != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_4011])).

cnf(c_2684,plain,
    ( r1_tarski(k1_setfam_1(k2_enumset1(sK8,sK8,sK8,sK8)),k1_setfam_1(k2_enumset1(sK8,sK8,sK8,sK8))) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_1658,plain,
    ( ~ r1_tarski(k1_setfam_1(k2_enumset1(sK8,sK8,sK8,sK8)),sK8)
    | ~ r1_tarski(sK8,k1_setfam_1(k2_enumset1(sK8,sK8,sK8,sK8))) ),
    inference(resolution,[status(thm)],[c_3,c_35])).

cnf(c_1954,plain,
    ( ~ r2_hidden(sK8,k2_enumset1(sK8,sK8,sK8,sK8))
    | ~ r1_tarski(sK8,k1_setfam_1(k2_enumset1(sK8,sK8,sK8,sK8))) ),
    inference(resolution,[status(thm)],[c_1658,c_33])).

cnf(c_1785,plain,
    ( r2_hidden(sK8,k1_xboole_0)
    | ~ r1_tarski(k2_enumset1(sK8,sK8,sK8,sK8),k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_1783])).

cnf(c_1677,plain,
    ( ~ r2_hidden(sK0(sK8,k1_setfam_1(k2_enumset1(sK8,sK8,sK8,sK8))),k1_setfam_1(k2_enumset1(sK8,sK8,sK8,sK8)))
    | r1_tarski(sK8,k1_setfam_1(k2_enumset1(sK8,sK8,sK8,sK8))) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_1678,plain,
    ( r2_hidden(sK0(sK8,k1_setfam_1(k2_enumset1(sK8,sK8,sK8,sK8))),sK8)
    | r1_tarski(sK8,k1_setfam_1(k2_enumset1(sK8,sK8,sK8,sK8))) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_106,plain,
    ( r1_tarski(k1_xboole_0,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_12,plain,
    ( r2_hidden(X0,k2_enumset1(X0,X0,X1,X2)) ),
    inference(cnf_transformation,[],[f111])).

cnf(c_93,plain,
    ( r2_hidden(k1_xboole_0,k2_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0)) ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_90,plain,
    ( ~ r2_hidden(k1_xboole_0,k2_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0))
    | k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_13])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_36816,c_26413,c_24906,c_22970,c_11967,c_9608,c_6866,c_5837,c_4013,c_2684,c_1954,c_1895,c_1894,c_1785,c_1677,c_1678,c_106,c_93,c_90])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n018.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 12:12:26 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  % Running in FOF mode
% 11.49/1.99  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 11.49/1.99  
% 11.49/1.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 11.49/1.99  
% 11.49/1.99  ------  iProver source info
% 11.49/1.99  
% 11.49/1.99  git: date: 2020-06-30 10:37:57 +0100
% 11.49/1.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 11.49/1.99  git: non_committed_changes: false
% 11.49/1.99  git: last_make_outside_of_git: false
% 11.49/1.99  
% 11.49/1.99  ------ 
% 11.49/1.99  ------ Parsing...
% 11.49/1.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 11.49/1.99  
% 11.49/1.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 1 0s  sf_e 
% 11.49/1.99  
% 11.49/1.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 11.49/1.99  
% 11.49/1.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 11.49/1.99  ------ Proving...
% 11.49/1.99  ------ Problem Properties 
% 11.49/1.99  
% 11.49/1.99  
% 11.49/1.99  clauses                                 34
% 11.49/1.99  conjectures                             1
% 11.49/1.99  EPR                                     3
% 11.49/1.99  Horn                                    22
% 11.49/1.99  unary                                   7
% 11.49/1.99  binary                                  9
% 11.49/1.99  lits                                    88
% 11.49/1.99  lits eq                                 30
% 11.49/1.99  fd_pure                                 0
% 11.49/1.99  fd_pseudo                               0
% 11.49/1.99  fd_cond                                 3
% 11.49/1.99  fd_pseudo_cond                          12
% 11.49/1.99  AC symbols                              0
% 11.49/1.99  
% 11.49/1.99  ------ Input Options Time Limit: Unbounded
% 11.49/1.99  
% 11.49/1.99  
% 11.49/1.99  ------ 
% 11.49/1.99  Current options:
% 11.49/1.99  ------ 
% 11.49/1.99  
% 11.49/1.99  
% 11.49/1.99  
% 11.49/1.99  
% 11.49/1.99  ------ Proving...
% 11.49/1.99  
% 11.49/1.99  
% 11.49/1.99  % SZS status Theorem for theBenchmark.p
% 11.49/1.99  
% 11.49/1.99  % SZS output start CNFRefutation for theBenchmark.p
% 11.49/1.99  
% 11.49/1.99  fof(f1,axiom,(
% 11.49/1.99    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 11.49/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.49/1.99  
% 11.49/1.99  fof(f15,plain,(
% 11.49/1.99    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 11.49/1.99    inference(ennf_transformation,[],[f1])).
% 11.49/1.99  
% 11.49/1.99  fof(f21,plain,(
% 11.49/1.99    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 11.49/1.99    inference(nnf_transformation,[],[f15])).
% 11.49/1.99  
% 11.49/1.99  fof(f22,plain,(
% 11.49/1.99    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 11.49/1.99    inference(rectify,[],[f21])).
% 11.49/1.99  
% 11.49/1.99  fof(f23,plain,(
% 11.49/1.99    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 11.49/1.99    introduced(choice_axiom,[])).
% 11.49/1.99  
% 11.49/1.99  fof(f24,plain,(
% 11.49/1.99    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 11.49/1.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f22,f23])).
% 11.49/1.99  
% 11.49/1.99  fof(f50,plain,(
% 11.49/1.99    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK0(X0,X1),X0)) )),
% 11.49/1.99    inference(cnf_transformation,[],[f24])).
% 11.49/1.99  
% 11.49/1.99  fof(f7,axiom,(
% 11.49/1.99    ! [X0,X1] : (k3_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (r2_hidden(X3,X0) & r2_hidden(X2,X3))))),
% 11.49/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.49/1.99  
% 11.49/1.99  fof(f32,plain,(
% 11.49/1.99    ! [X0,X1] : ((k3_tarski(X0) = X1 | ? [X2] : ((! [X3] : (~r2_hidden(X3,X0) | ~r2_hidden(X2,X3)) | ~r2_hidden(X2,X1)) & (? [X3] : (r2_hidden(X3,X0) & r2_hidden(X2,X3)) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ! [X3] : (~r2_hidden(X3,X0) | ~r2_hidden(X2,X3))) & (? [X3] : (r2_hidden(X3,X0) & r2_hidden(X2,X3)) | ~r2_hidden(X2,X1))) | k3_tarski(X0) != X1))),
% 11.49/1.99    inference(nnf_transformation,[],[f7])).
% 11.49/1.99  
% 11.49/1.99  fof(f33,plain,(
% 11.49/1.99    ! [X0,X1] : ((k3_tarski(X0) = X1 | ? [X2] : ((! [X3] : (~r2_hidden(X3,X0) | ~r2_hidden(X2,X3)) | ~r2_hidden(X2,X1)) & (? [X4] : (r2_hidden(X4,X0) & r2_hidden(X2,X4)) | r2_hidden(X2,X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : (~r2_hidden(X6,X0) | ~r2_hidden(X5,X6))) & (? [X7] : (r2_hidden(X7,X0) & r2_hidden(X5,X7)) | ~r2_hidden(X5,X1))) | k3_tarski(X0) != X1))),
% 11.49/1.99    inference(rectify,[],[f32])).
% 11.49/1.99  
% 11.49/1.99  fof(f36,plain,(
% 11.49/1.99    ! [X5,X0] : (? [X7] : (r2_hidden(X7,X0) & r2_hidden(X5,X7)) => (r2_hidden(sK4(X0,X5),X0) & r2_hidden(X5,sK4(X0,X5))))),
% 11.49/1.99    introduced(choice_axiom,[])).
% 11.49/1.99  
% 11.49/1.99  fof(f35,plain,(
% 11.49/1.99    ( ! [X2] : (! [X1,X0] : (? [X4] : (r2_hidden(X4,X0) & r2_hidden(X2,X4)) => (r2_hidden(sK3(X0,X1),X0) & r2_hidden(X2,sK3(X0,X1))))) )),
% 11.49/1.99    introduced(choice_axiom,[])).
% 11.49/1.99  
% 11.49/1.99  fof(f34,plain,(
% 11.49/1.99    ! [X1,X0] : (? [X2] : ((! [X3] : (~r2_hidden(X3,X0) | ~r2_hidden(X2,X3)) | ~r2_hidden(X2,X1)) & (? [X4] : (r2_hidden(X4,X0) & r2_hidden(X2,X4)) | r2_hidden(X2,X1))) => ((! [X3] : (~r2_hidden(X3,X0) | ~r2_hidden(sK2(X0,X1),X3)) | ~r2_hidden(sK2(X0,X1),X1)) & (? [X4] : (r2_hidden(X4,X0) & r2_hidden(sK2(X0,X1),X4)) | r2_hidden(sK2(X0,X1),X1))))),
% 11.49/1.99    introduced(choice_axiom,[])).
% 11.49/1.99  
% 11.49/1.99  fof(f37,plain,(
% 11.49/1.99    ! [X0,X1] : ((k3_tarski(X0) = X1 | ((! [X3] : (~r2_hidden(X3,X0) | ~r2_hidden(sK2(X0,X1),X3)) | ~r2_hidden(sK2(X0,X1),X1)) & ((r2_hidden(sK3(X0,X1),X0) & r2_hidden(sK2(X0,X1),sK3(X0,X1))) | r2_hidden(sK2(X0,X1),X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : (~r2_hidden(X6,X0) | ~r2_hidden(X5,X6))) & ((r2_hidden(sK4(X0,X5),X0) & r2_hidden(X5,sK4(X0,X5))) | ~r2_hidden(X5,X1))) | k3_tarski(X0) != X1))),
% 11.49/1.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f33,f36,f35,f34])).
% 11.49/1.99  
% 11.49/1.99  fof(f67,plain,(
% 11.49/1.99    ( ! [X0,X5,X1] : (r2_hidden(sK4(X0,X5),X0) | ~r2_hidden(X5,X1) | k3_tarski(X0) != X1) )),
% 11.49/1.99    inference(cnf_transformation,[],[f37])).
% 11.49/1.99  
% 11.49/1.99  fof(f114,plain,(
% 11.49/1.99    ( ! [X0,X5] : (r2_hidden(sK4(X0,X5),X0) | ~r2_hidden(X5,k3_tarski(X0))) )),
% 11.49/1.99    inference(equality_resolution,[],[f67])).
% 11.49/1.99  
% 11.49/1.99  fof(f9,axiom,(
% 11.49/1.99    ! [X0,X1,X2] : (r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) <=> (X0 != X2 & r2_hidden(X0,X1)))),
% 11.49/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.49/1.99  
% 11.49/1.99  fof(f39,plain,(
% 11.49/1.99    ! [X0,X1,X2] : ((r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) | (X0 = X2 | ~r2_hidden(X0,X1))) & ((X0 != X2 & r2_hidden(X0,X1)) | ~r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))))),
% 11.49/1.99    inference(nnf_transformation,[],[f9])).
% 11.49/1.99  
% 11.49/1.99  fof(f40,plain,(
% 11.49/1.99    ! [X0,X1,X2] : ((r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) | X0 = X2 | ~r2_hidden(X0,X1)) & ((X0 != X2 & r2_hidden(X0,X1)) | ~r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))))),
% 11.49/1.99    inference(flattening,[],[f39])).
% 11.49/1.99  
% 11.49/1.99  fof(f74,plain,(
% 11.49/1.99    ( ! [X2,X0,X1] : (r2_hidden(X0,X1) | ~r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))) )),
% 11.49/1.99    inference(cnf_transformation,[],[f40])).
% 11.49/1.99  
% 11.49/1.99  fof(f4,axiom,(
% 11.49/1.99    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 11.49/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.49/1.99  
% 11.49/1.99  fof(f63,plain,(
% 11.49/1.99    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 11.49/1.99    inference(cnf_transformation,[],[f4])).
% 11.49/1.99  
% 11.49/1.99  fof(f5,axiom,(
% 11.49/1.99    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 11.49/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.49/1.99  
% 11.49/1.99  fof(f64,plain,(
% 11.49/1.99    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 11.49/1.99    inference(cnf_transformation,[],[f5])).
% 11.49/1.99  
% 11.49/1.99  fof(f6,axiom,(
% 11.49/1.99    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 11.49/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.49/1.99  
% 11.49/1.99  fof(f65,plain,(
% 11.49/1.99    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 11.49/1.99    inference(cnf_transformation,[],[f6])).
% 11.49/1.99  
% 11.49/1.99  fof(f88,plain,(
% 11.49/1.99    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 11.49/1.99    inference(definition_unfolding,[],[f64,f65])).
% 11.49/1.99  
% 11.49/1.99  fof(f89,plain,(
% 11.49/1.99    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 11.49/1.99    inference(definition_unfolding,[],[f63,f88])).
% 11.49/1.99  
% 11.49/1.99  fof(f102,plain,(
% 11.49/1.99    ( ! [X2,X0,X1] : (r2_hidden(X0,X1) | ~r2_hidden(X0,k4_xboole_0(X1,k2_enumset1(X2,X2,X2,X2)))) )),
% 11.49/1.99    inference(definition_unfolding,[],[f74,f89])).
% 11.49/1.99  
% 11.49/1.99  fof(f51,plain,(
% 11.49/1.99    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r2_hidden(sK0(X0,X1),X1)) )),
% 11.49/1.99    inference(cnf_transformation,[],[f24])).
% 11.49/1.99  
% 11.49/1.99  fof(f3,axiom,(
% 11.49/1.99    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> ~(X2 != X4 & X1 != X4 & X0 != X4)))),
% 11.49/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.49/1.99  
% 11.49/1.99  fof(f16,plain,(
% 11.49/1.99    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> (X2 = X4 | X1 = X4 | X0 = X4)))),
% 11.49/1.99    inference(ennf_transformation,[],[f3])).
% 11.49/1.99  
% 11.49/1.99  fof(f27,plain,(
% 11.49/1.99    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & ((X2 = X4 | X1 = X4 | X0 = X4) | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & ((X2 = X4 | X1 = X4 | X0 = X4) | ~r2_hidden(X4,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 11.49/1.99    inference(nnf_transformation,[],[f16])).
% 11.49/1.99  
% 11.49/1.99  fof(f28,plain,(
% 11.49/1.99    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & (X2 = X4 | X1 = X4 | X0 = X4 | ~r2_hidden(X4,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 11.49/1.99    inference(flattening,[],[f27])).
% 11.49/1.99  
% 11.49/1.99  fof(f29,plain,(
% 11.49/1.99    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X2 != X5 & X1 != X5 & X0 != X5)) & (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 11.49/1.99    inference(rectify,[],[f28])).
% 11.49/1.99  
% 11.49/1.99  fof(f30,plain,(
% 11.49/1.99    ! [X3,X2,X1,X0] : (? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3))) => (((sK1(X0,X1,X2,X3) != X2 & sK1(X0,X1,X2,X3) != X1 & sK1(X0,X1,X2,X3) != X0) | ~r2_hidden(sK1(X0,X1,X2,X3),X3)) & (sK1(X0,X1,X2,X3) = X2 | sK1(X0,X1,X2,X3) = X1 | sK1(X0,X1,X2,X3) = X0 | r2_hidden(sK1(X0,X1,X2,X3),X3))))),
% 11.49/1.99    introduced(choice_axiom,[])).
% 11.49/1.99  
% 11.49/1.99  fof(f31,plain,(
% 11.49/1.99    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | (((sK1(X0,X1,X2,X3) != X2 & sK1(X0,X1,X2,X3) != X1 & sK1(X0,X1,X2,X3) != X0) | ~r2_hidden(sK1(X0,X1,X2,X3),X3)) & (sK1(X0,X1,X2,X3) = X2 | sK1(X0,X1,X2,X3) = X1 | sK1(X0,X1,X2,X3) = X0 | r2_hidden(sK1(X0,X1,X2,X3),X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X2 != X5 & X1 != X5 & X0 != X5)) & (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 11.49/1.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f29,f30])).
% 11.49/1.99  
% 11.49/1.99  fof(f57,plain,(
% 11.49/1.99    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X1 != X5 | k1_enumset1(X0,X1,X2) != X3) )),
% 11.49/1.99    inference(cnf_transformation,[],[f31])).
% 11.49/1.99  
% 11.49/1.99  fof(f95,plain,(
% 11.49/1.99    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X1 != X5 | k2_enumset1(X0,X0,X1,X2) != X3) )),
% 11.49/1.99    inference(definition_unfolding,[],[f57,f65])).
% 11.49/1.99  
% 11.49/1.99  fof(f108,plain,(
% 11.49/1.99    ( ! [X2,X0,X5,X3] : (r2_hidden(X5,X3) | k2_enumset1(X0,X0,X5,X2) != X3) )),
% 11.49/1.99    inference(equality_resolution,[],[f95])).
% 11.49/1.99  
% 11.49/1.99  fof(f109,plain,(
% 11.49/1.99    ( ! [X2,X0,X5] : (r2_hidden(X5,k2_enumset1(X0,X0,X5,X2))) )),
% 11.49/1.99    inference(equality_resolution,[],[f108])).
% 11.49/1.99  
% 11.49/1.99  fof(f58,plain,(
% 11.49/1.99    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X2 != X5 | k1_enumset1(X0,X1,X2) != X3) )),
% 11.49/1.99    inference(cnf_transformation,[],[f31])).
% 11.49/1.99  
% 11.49/1.99  fof(f94,plain,(
% 11.49/1.99    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X2 != X5 | k2_enumset1(X0,X0,X1,X2) != X3) )),
% 11.49/1.99    inference(definition_unfolding,[],[f58,f65])).
% 11.49/1.99  
% 11.49/1.99  fof(f106,plain,(
% 11.49/1.99    ( ! [X0,X5,X3,X1] : (r2_hidden(X5,X3) | k2_enumset1(X0,X0,X1,X5) != X3) )),
% 11.49/1.99    inference(equality_resolution,[],[f94])).
% 11.49/1.99  
% 11.49/1.99  fof(f107,plain,(
% 11.49/1.99    ( ! [X0,X5,X1] : (r2_hidden(X5,k2_enumset1(X0,X0,X1,X5))) )),
% 11.49/1.99    inference(equality_resolution,[],[f106])).
% 11.49/1.99  
% 11.49/1.99  fof(f12,axiom,(
% 11.49/1.99    ! [X0] : (r2_hidden(k1_xboole_0,X0) => k1_xboole_0 = k1_setfam_1(X0))),
% 11.49/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.49/1.99  
% 11.49/1.99  fof(f19,plain,(
% 11.49/1.99    ! [X0] : (k1_xboole_0 = k1_setfam_1(X0) | ~r2_hidden(k1_xboole_0,X0))),
% 11.49/1.99    inference(ennf_transformation,[],[f12])).
% 11.49/1.99  
% 11.49/1.99  fof(f86,plain,(
% 11.49/1.99    ( ! [X0] : (k1_xboole_0 = k1_setfam_1(X0) | ~r2_hidden(k1_xboole_0,X0)) )),
% 11.49/1.99    inference(cnf_transformation,[],[f19])).
% 11.49/1.99  
% 11.49/1.99  fof(f11,axiom,(
% 11.49/1.99    ! [X0,X1] : (r2_hidden(X0,X1) => r1_tarski(k1_setfam_1(X1),X0))),
% 11.49/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.49/1.99  
% 11.49/1.99  fof(f18,plain,(
% 11.49/1.99    ! [X0,X1] : (r1_tarski(k1_setfam_1(X1),X0) | ~r2_hidden(X0,X1))),
% 11.49/1.99    inference(ennf_transformation,[],[f11])).
% 11.49/1.99  
% 11.49/1.99  fof(f85,plain,(
% 11.49/1.99    ( ! [X0,X1] : (r1_tarski(k1_setfam_1(X1),X0) | ~r2_hidden(X0,X1)) )),
% 11.49/1.99    inference(cnf_transformation,[],[f18])).
% 11.49/1.99  
% 11.49/1.99  fof(f2,axiom,(
% 11.49/1.99    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 11.49/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.49/1.99  
% 11.49/1.99  fof(f25,plain,(
% 11.49/1.99    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 11.49/1.99    inference(nnf_transformation,[],[f2])).
% 11.49/1.99  
% 11.49/1.99  fof(f26,plain,(
% 11.49/1.99    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 11.49/1.99    inference(flattening,[],[f25])).
% 11.49/1.99  
% 11.49/1.99  fof(f54,plain,(
% 11.49/1.99    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 11.49/1.99    inference(cnf_transformation,[],[f26])).
% 11.49/1.99  
% 11.49/1.99  fof(f75,plain,(
% 11.49/1.99    ( ! [X2,X0,X1] : (X0 != X2 | ~r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))) )),
% 11.49/1.99    inference(cnf_transformation,[],[f40])).
% 11.49/1.99  
% 11.49/1.99  fof(f101,plain,(
% 11.49/1.99    ( ! [X2,X0,X1] : (X0 != X2 | ~r2_hidden(X0,k4_xboole_0(X1,k2_enumset1(X2,X2,X2,X2)))) )),
% 11.49/1.99    inference(definition_unfolding,[],[f75,f89])).
% 11.49/1.99  
% 11.49/1.99  fof(f116,plain,(
% 11.49/1.99    ( ! [X2,X1] : (~r2_hidden(X2,k4_xboole_0(X1,k2_enumset1(X2,X2,X2,X2)))) )),
% 11.49/1.99    inference(equality_resolution,[],[f101])).
% 11.49/1.99  
% 11.49/1.99  fof(f49,plain,(
% 11.49/1.99    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,X1)) )),
% 11.49/1.99    inference(cnf_transformation,[],[f24])).
% 11.49/1.99  
% 11.49/1.99  fof(f10,axiom,(
% 11.49/1.99    ! [X0,X1] : ((k1_xboole_0 = X0 => (k1_setfam_1(X0) = X1 <=> k1_xboole_0 = X1)) & (k1_xboole_0 != X0 => (k1_setfam_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ! [X3] : (r2_hidden(X3,X0) => r2_hidden(X2,X3))))))),
% 11.49/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.49/1.99  
% 11.49/1.99  fof(f17,plain,(
% 11.49/1.99    ! [X0,X1] : (((k1_setfam_1(X0) = X1 <=> k1_xboole_0 = X1) | k1_xboole_0 != X0) & ((k1_setfam_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ! [X3] : (r2_hidden(X2,X3) | ~r2_hidden(X3,X0)))) | k1_xboole_0 = X0))),
% 11.49/1.99    inference(ennf_transformation,[],[f10])).
% 11.49/1.99  
% 11.49/1.99  fof(f41,plain,(
% 11.49/1.99    ! [X0,X1] : ((((k1_setfam_1(X0) = X1 | k1_xboole_0 != X1) & (k1_xboole_0 = X1 | k1_setfam_1(X0) != X1)) | k1_xboole_0 != X0) & (((k1_setfam_1(X0) = X1 | ? [X2] : ((? [X3] : (~r2_hidden(X2,X3) & r2_hidden(X3,X0)) | ~r2_hidden(X2,X1)) & (! [X3] : (r2_hidden(X2,X3) | ~r2_hidden(X3,X0)) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ? [X3] : (~r2_hidden(X2,X3) & r2_hidden(X3,X0))) & (! [X3] : (r2_hidden(X2,X3) | ~r2_hidden(X3,X0)) | ~r2_hidden(X2,X1))) | k1_setfam_1(X0) != X1)) | k1_xboole_0 = X0))),
% 11.49/1.99    inference(nnf_transformation,[],[f17])).
% 11.49/1.99  
% 11.49/1.99  fof(f42,plain,(
% 11.49/1.99    ! [X0,X1] : ((((k1_setfam_1(X0) = X1 | k1_xboole_0 != X1) & (k1_xboole_0 = X1 | k1_setfam_1(X0) != X1)) | k1_xboole_0 != X0) & (((k1_setfam_1(X0) = X1 | ? [X2] : ((? [X3] : (~r2_hidden(X2,X3) & r2_hidden(X3,X0)) | ~r2_hidden(X2,X1)) & (! [X4] : (r2_hidden(X2,X4) | ~r2_hidden(X4,X0)) | r2_hidden(X2,X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ? [X6] : (~r2_hidden(X5,X6) & r2_hidden(X6,X0))) & (! [X7] : (r2_hidden(X5,X7) | ~r2_hidden(X7,X0)) | ~r2_hidden(X5,X1))) | k1_setfam_1(X0) != X1)) | k1_xboole_0 = X0))),
% 11.49/1.99    inference(rectify,[],[f41])).
% 11.49/1.99  
% 11.49/1.99  fof(f45,plain,(
% 11.49/1.99    ! [X5,X0] : (? [X6] : (~r2_hidden(X5,X6) & r2_hidden(X6,X0)) => (~r2_hidden(X5,sK7(X0,X5)) & r2_hidden(sK7(X0,X5),X0)))),
% 11.49/1.99    introduced(choice_axiom,[])).
% 11.49/1.99  
% 11.49/1.99  fof(f44,plain,(
% 11.49/1.99    ( ! [X2] : (! [X1,X0] : (? [X3] : (~r2_hidden(X2,X3) & r2_hidden(X3,X0)) => (~r2_hidden(X2,sK6(X0,X1)) & r2_hidden(sK6(X0,X1),X0)))) )),
% 11.49/1.99    introduced(choice_axiom,[])).
% 11.49/1.99  
% 11.49/1.99  fof(f43,plain,(
% 11.49/1.99    ! [X1,X0] : (? [X2] : ((? [X3] : (~r2_hidden(X2,X3) & r2_hidden(X3,X0)) | ~r2_hidden(X2,X1)) & (! [X4] : (r2_hidden(X2,X4) | ~r2_hidden(X4,X0)) | r2_hidden(X2,X1))) => ((? [X3] : (~r2_hidden(sK5(X0,X1),X3) & r2_hidden(X3,X0)) | ~r2_hidden(sK5(X0,X1),X1)) & (! [X4] : (r2_hidden(sK5(X0,X1),X4) | ~r2_hidden(X4,X0)) | r2_hidden(sK5(X0,X1),X1))))),
% 11.49/1.99    introduced(choice_axiom,[])).
% 11.49/1.99  
% 11.49/1.99  fof(f46,plain,(
% 11.49/1.99    ! [X0,X1] : ((((k1_setfam_1(X0) = X1 | k1_xboole_0 != X1) & (k1_xboole_0 = X1 | k1_setfam_1(X0) != X1)) | k1_xboole_0 != X0) & (((k1_setfam_1(X0) = X1 | (((~r2_hidden(sK5(X0,X1),sK6(X0,X1)) & r2_hidden(sK6(X0,X1),X0)) | ~r2_hidden(sK5(X0,X1),X1)) & (! [X4] : (r2_hidden(sK5(X0,X1),X4) | ~r2_hidden(X4,X0)) | r2_hidden(sK5(X0,X1),X1)))) & (! [X5] : ((r2_hidden(X5,X1) | (~r2_hidden(X5,sK7(X0,X5)) & r2_hidden(sK7(X0,X5),X0))) & (! [X7] : (r2_hidden(X5,X7) | ~r2_hidden(X7,X0)) | ~r2_hidden(X5,X1))) | k1_setfam_1(X0) != X1)) | k1_xboole_0 = X0))),
% 11.49/1.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6,sK7])],[f42,f45,f44,f43])).
% 11.49/1.99  
% 11.49/1.99  fof(f80,plain,(
% 11.49/1.99    ( ! [X4,X0,X1] : (k1_setfam_1(X0) = X1 | r2_hidden(sK5(X0,X1),X4) | ~r2_hidden(X4,X0) | r2_hidden(sK5(X0,X1),X1) | k1_xboole_0 = X0) )),
% 11.49/1.99    inference(cnf_transformation,[],[f46])).
% 11.49/1.99  
% 11.49/1.99  fof(f13,conjecture,(
% 11.49/1.99    ! [X0] : k1_setfam_1(k1_tarski(X0)) = X0),
% 11.49/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.49/1.99  
% 11.49/1.99  fof(f14,negated_conjecture,(
% 11.49/1.99    ~! [X0] : k1_setfam_1(k1_tarski(X0)) = X0),
% 11.49/1.99    inference(negated_conjecture,[],[f13])).
% 11.49/1.99  
% 11.49/1.99  fof(f20,plain,(
% 11.49/1.99    ? [X0] : k1_setfam_1(k1_tarski(X0)) != X0),
% 11.49/1.99    inference(ennf_transformation,[],[f14])).
% 11.49/1.99  
% 11.49/1.99  fof(f47,plain,(
% 11.49/1.99    ? [X0] : k1_setfam_1(k1_tarski(X0)) != X0 => k1_setfam_1(k1_tarski(sK8)) != sK8),
% 11.49/1.99    introduced(choice_axiom,[])).
% 11.49/1.99  
% 11.49/1.99  fof(f48,plain,(
% 11.49/1.99    k1_setfam_1(k1_tarski(sK8)) != sK8),
% 11.49/1.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8])],[f20,f47])).
% 11.49/1.99  
% 11.49/1.99  fof(f87,plain,(
% 11.49/1.99    k1_setfam_1(k1_tarski(sK8)) != sK8),
% 11.49/1.99    inference(cnf_transformation,[],[f48])).
% 11.49/1.99  
% 11.49/1.99  fof(f103,plain,(
% 11.49/1.99    k1_setfam_1(k2_enumset1(sK8,sK8,sK8,sK8)) != sK8),
% 11.49/1.99    inference(definition_unfolding,[],[f87,f89])).
% 11.49/1.99  
% 11.49/1.99  fof(f81,plain,(
% 11.49/1.99    ( ! [X0,X1] : (k1_setfam_1(X0) = X1 | r2_hidden(sK6(X0,X1),X0) | ~r2_hidden(sK5(X0,X1),X1) | k1_xboole_0 = X0) )),
% 11.49/1.99    inference(cnf_transformation,[],[f46])).
% 11.49/1.99  
% 11.49/1.99  fof(f8,axiom,(
% 11.49/1.99    ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) <=> r2_hidden(X0,X1))),
% 11.49/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.49/1.99  
% 11.49/1.99  fof(f38,plain,(
% 11.49/1.99    ! [X0,X1] : ((r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) & (r2_hidden(X0,X1) | ~r1_tarski(k1_tarski(X0),X1)))),
% 11.49/1.99    inference(nnf_transformation,[],[f8])).
% 11.49/1.99  
% 11.49/1.99  fof(f72,plain,(
% 11.49/1.99    ( ! [X0,X1] : (r2_hidden(X0,X1) | ~r1_tarski(k1_tarski(X0),X1)) )),
% 11.49/1.99    inference(cnf_transformation,[],[f38])).
% 11.49/1.99  
% 11.49/1.99  fof(f99,plain,(
% 11.49/1.99    ( ! [X0,X1] : (r2_hidden(X0,X1) | ~r1_tarski(k2_enumset1(X0,X0,X0,X0),X1)) )),
% 11.49/1.99    inference(definition_unfolding,[],[f72,f89])).
% 11.49/1.99  
% 11.49/1.99  fof(f52,plain,(
% 11.49/1.99    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 11.49/1.99    inference(cnf_transformation,[],[f26])).
% 11.49/1.99  
% 11.49/1.99  fof(f105,plain,(
% 11.49/1.99    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 11.49/1.99    inference(equality_resolution,[],[f52])).
% 11.49/1.99  
% 11.49/1.99  fof(f55,plain,(
% 11.49/1.99    ( ! [X2,X0,X5,X3,X1] : (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3) | k1_enumset1(X0,X1,X2) != X3) )),
% 11.49/1.99    inference(cnf_transformation,[],[f31])).
% 11.49/1.99  
% 11.49/1.99  fof(f97,plain,(
% 11.49/1.99    ( ! [X2,X0,X5,X3,X1] : (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3) | k2_enumset1(X0,X0,X1,X2) != X3) )),
% 11.49/1.99    inference(definition_unfolding,[],[f55,f65])).
% 11.49/1.99  
% 11.49/1.99  fof(f112,plain,(
% 11.49/1.99    ( ! [X2,X0,X5,X1] : (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,k2_enumset1(X0,X0,X1,X2))) )),
% 11.49/1.99    inference(equality_resolution,[],[f97])).
% 11.49/1.99  
% 11.49/1.99  fof(f83,plain,(
% 11.49/1.99    ( ! [X0,X1] : (k1_xboole_0 = X1 | k1_setfam_1(X0) != X1 | k1_xboole_0 != X0) )),
% 11.49/1.99    inference(cnf_transformation,[],[f46])).
% 11.49/1.99  
% 11.49/1.99  fof(f119,plain,(
% 11.49/1.99    ( ! [X0] : (k1_xboole_0 = k1_setfam_1(X0) | k1_xboole_0 != X0) )),
% 11.49/1.99    inference(equality_resolution,[],[f83])).
% 11.49/1.99  
% 11.49/1.99  fof(f120,plain,(
% 11.49/1.99    k1_xboole_0 = k1_setfam_1(k1_xboole_0)),
% 11.49/1.99    inference(equality_resolution,[],[f119])).
% 11.49/1.99  
% 11.49/1.99  fof(f82,plain,(
% 11.49/1.99    ( ! [X0,X1] : (k1_setfam_1(X0) = X1 | ~r2_hidden(sK5(X0,X1),sK6(X0,X1)) | ~r2_hidden(sK5(X0,X1),X1) | k1_xboole_0 = X0) )),
% 11.49/1.99    inference(cnf_transformation,[],[f46])).
% 11.49/1.99  
% 11.49/1.99  fof(f68,plain,(
% 11.49/1.99    ( ! [X6,X0,X5,X1] : (r2_hidden(X5,X1) | ~r2_hidden(X6,X0) | ~r2_hidden(X5,X6) | k3_tarski(X0) != X1) )),
% 11.49/1.99    inference(cnf_transformation,[],[f37])).
% 11.49/1.99  
% 11.49/1.99  fof(f113,plain,(
% 11.49/1.99    ( ! [X6,X0,X5] : (r2_hidden(X5,k3_tarski(X0)) | ~r2_hidden(X6,X0) | ~r2_hidden(X5,X6)) )),
% 11.49/1.99    inference(equality_resolution,[],[f68])).
% 11.49/1.99  
% 11.49/1.99  fof(f56,plain,(
% 11.49/1.99    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X0 != X5 | k1_enumset1(X0,X1,X2) != X3) )),
% 11.49/1.99    inference(cnf_transformation,[],[f31])).
% 11.49/1.99  
% 11.49/1.99  fof(f96,plain,(
% 11.49/1.99    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X0 != X5 | k2_enumset1(X0,X0,X1,X2) != X3) )),
% 11.49/1.99    inference(definition_unfolding,[],[f56,f65])).
% 11.49/1.99  
% 11.49/1.99  fof(f110,plain,(
% 11.49/1.99    ( ! [X2,X5,X3,X1] : (r2_hidden(X5,X3) | k2_enumset1(X5,X5,X1,X2) != X3) )),
% 11.49/1.99    inference(equality_resolution,[],[f96])).
% 11.49/1.99  
% 11.49/1.99  fof(f111,plain,(
% 11.49/1.99    ( ! [X2,X5,X1] : (r2_hidden(X5,k2_enumset1(X5,X5,X1,X2))) )),
% 11.49/1.99    inference(equality_resolution,[],[f110])).
% 11.49/1.99  
% 11.49/1.99  cnf(c_1,plain,
% 11.49/1.99      ( r2_hidden(sK0(X0,X1),X0) | r1_tarski(X0,X1) ),
% 11.49/1.99      inference(cnf_transformation,[],[f50]) ).
% 11.49/1.99  
% 11.49/1.99  cnf(c_1249,plain,
% 11.49/1.99      ( r2_hidden(sK0(X0,X1),X0) = iProver_top
% 11.49/1.99      | r1_tarski(X0,X1) = iProver_top ),
% 11.49/1.99      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 11.49/1.99  
% 11.49/1.99  cnf(c_18,plain,
% 11.49/1.99      ( ~ r2_hidden(X0,k3_tarski(X1)) | r2_hidden(sK4(X1,X0),X1) ),
% 11.49/1.99      inference(cnf_transformation,[],[f114]) ).
% 11.49/1.99  
% 11.49/1.99  cnf(c_1233,plain,
% 11.49/1.99      ( r2_hidden(X0,k3_tarski(X1)) != iProver_top
% 11.49/1.99      | r2_hidden(sK4(X1,X0),X1) = iProver_top ),
% 11.49/1.99      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 11.49/1.99  
% 11.49/1.99  cnf(c_24,plain,
% 11.49/1.99      ( r2_hidden(X0,X1)
% 11.49/1.99      | ~ r2_hidden(X0,k4_xboole_0(X1,k2_enumset1(X2,X2,X2,X2))) ),
% 11.49/1.99      inference(cnf_transformation,[],[f102]) ).
% 11.49/1.99  
% 11.49/1.99  cnf(c_1227,plain,
% 11.49/1.99      ( r2_hidden(X0,X1) = iProver_top
% 11.49/1.99      | r2_hidden(X0,k4_xboole_0(X1,k2_enumset1(X2,X2,X2,X2))) != iProver_top ),
% 11.49/1.99      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 11.49/1.99  
% 11.49/1.99  cnf(c_3172,plain,
% 11.49/1.99      ( r2_hidden(sK0(k4_xboole_0(X0,k2_enumset1(X1,X1,X1,X1)),X2),X0) = iProver_top
% 11.49/1.99      | r1_tarski(k4_xboole_0(X0,k2_enumset1(X1,X1,X1,X1)),X2) = iProver_top ),
% 11.49/1.99      inference(superposition,[status(thm)],[c_1249,c_1227]) ).
% 11.49/1.99  
% 11.49/1.99  cnf(c_0,plain,
% 11.49/1.99      ( ~ r2_hidden(sK0(X0,X1),X1) | r1_tarski(X0,X1) ),
% 11.49/1.99      inference(cnf_transformation,[],[f51]) ).
% 11.49/1.99  
% 11.49/1.99  cnf(c_1250,plain,
% 11.49/1.99      ( r2_hidden(sK0(X0,X1),X1) != iProver_top
% 11.49/1.99      | r1_tarski(X0,X1) = iProver_top ),
% 11.49/1.99      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 11.49/1.99  
% 11.49/1.99  cnf(c_33825,plain,
% 11.49/1.99      ( r1_tarski(k4_xboole_0(X0,k2_enumset1(X1,X1,X1,X1)),X0) = iProver_top ),
% 11.49/1.99      inference(superposition,[status(thm)],[c_3172,c_1250]) ).
% 11.49/1.99  
% 11.49/1.99  cnf(c_11,plain,
% 11.49/1.99      ( r2_hidden(X0,k2_enumset1(X1,X1,X0,X2)) ),
% 11.49/1.99      inference(cnf_transformation,[],[f109]) ).
% 11.49/1.99  
% 11.49/1.99  cnf(c_1240,plain,
% 11.49/1.99      ( r2_hidden(X0,k2_enumset1(X1,X1,X0,X2)) = iProver_top ),
% 11.49/1.99      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 11.49/1.99  
% 11.49/1.99  cnf(c_10,plain,
% 11.49/1.99      ( r2_hidden(X0,k2_enumset1(X1,X1,X2,X0)) ),
% 11.49/1.99      inference(cnf_transformation,[],[f107]) ).
% 11.49/1.99  
% 11.49/1.99  cnf(c_1241,plain,
% 11.49/1.99      ( r2_hidden(X0,k2_enumset1(X1,X1,X2,X0)) = iProver_top ),
% 11.49/1.99      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 11.49/1.99  
% 11.49/1.99  cnf(c_34,plain,
% 11.49/1.99      ( ~ r2_hidden(k1_xboole_0,X0) | k1_setfam_1(X0) = k1_xboole_0 ),
% 11.49/1.99      inference(cnf_transformation,[],[f86]) ).
% 11.49/1.99  
% 11.49/1.99  cnf(c_1219,plain,
% 11.49/1.99      ( k1_setfam_1(X0) = k1_xboole_0
% 11.49/1.99      | r2_hidden(k1_xboole_0,X0) != iProver_top ),
% 11.49/1.99      inference(predicate_to_equality,[status(thm)],[c_34]) ).
% 11.49/1.99  
% 11.49/1.99  cnf(c_1635,plain,
% 11.49/1.99      ( k1_setfam_1(k2_enumset1(X0,X0,X1,k1_xboole_0)) = k1_xboole_0 ),
% 11.49/1.99      inference(superposition,[status(thm)],[c_1241,c_1219]) ).
% 11.49/1.99  
% 11.49/1.99  cnf(c_33,plain,
% 11.49/1.99      ( ~ r2_hidden(X0,X1) | r1_tarski(k1_setfam_1(X1),X0) ),
% 11.49/1.99      inference(cnf_transformation,[],[f85]) ).
% 11.49/1.99  
% 11.49/1.99  cnf(c_1220,plain,
% 11.49/1.99      ( r2_hidden(X0,X1) != iProver_top
% 11.49/1.99      | r1_tarski(k1_setfam_1(X1),X0) = iProver_top ),
% 11.49/1.99      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 11.49/1.99  
% 11.49/1.99  cnf(c_1821,plain,
% 11.49/1.99      ( r2_hidden(X0,k2_enumset1(X1,X1,X2,k1_xboole_0)) != iProver_top
% 11.49/1.99      | r1_tarski(k1_xboole_0,X0) = iProver_top ),
% 11.49/1.99      inference(superposition,[status(thm)],[c_1635,c_1220]) ).
% 11.49/1.99  
% 11.49/1.99  cnf(c_3459,plain,
% 11.49/1.99      ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
% 11.49/1.99      inference(superposition,[status(thm)],[c_1240,c_1821]) ).
% 11.49/1.99  
% 11.49/1.99  cnf(c_3,plain,
% 11.49/1.99      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X1 = X0 ),
% 11.49/1.99      inference(cnf_transformation,[],[f54]) ).
% 11.49/1.99  
% 11.49/1.99  cnf(c_1247,plain,
% 11.49/1.99      ( X0 = X1
% 11.49/1.99      | r1_tarski(X1,X0) != iProver_top
% 11.49/1.99      | r1_tarski(X0,X1) != iProver_top ),
% 11.49/1.99      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 11.49/1.99  
% 11.49/1.99  cnf(c_3481,plain,
% 11.49/1.99      ( k1_xboole_0 = X0 | r1_tarski(X0,k1_xboole_0) != iProver_top ),
% 11.49/1.99      inference(superposition,[status(thm)],[c_3459,c_1247]) ).
% 11.49/1.99  
% 11.49/1.99  cnf(c_33971,plain,
% 11.49/1.99      ( k4_xboole_0(k1_xboole_0,k2_enumset1(X0,X0,X0,X0)) = k1_xboole_0 ),
% 11.49/1.99      inference(superposition,[status(thm)],[c_33825,c_3481]) ).
% 11.49/1.99  
% 11.49/1.99  cnf(c_23,plain,
% 11.49/1.99      ( ~ r2_hidden(X0,k4_xboole_0(X1,k2_enumset1(X0,X0,X0,X0))) ),
% 11.49/1.99      inference(cnf_transformation,[],[f116]) ).
% 11.49/1.99  
% 11.49/1.99  cnf(c_1228,plain,
% 11.49/1.99      ( r2_hidden(X0,k4_xboole_0(X1,k2_enumset1(X0,X0,X0,X0))) != iProver_top ),
% 11.49/1.99      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 11.49/1.99  
% 11.49/1.99  cnf(c_35358,plain,
% 11.49/1.99      ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
% 11.49/1.99      inference(superposition,[status(thm)],[c_33971,c_1228]) ).
% 11.49/1.99  
% 11.49/1.99  cnf(c_36198,plain,
% 11.49/1.99      ( r2_hidden(X0,k3_tarski(k1_xboole_0)) != iProver_top ),
% 11.49/1.99      inference(superposition,[status(thm)],[c_1233,c_35358]) ).
% 11.49/1.99  
% 11.49/1.99  cnf(c_36286,plain,
% 11.49/1.99      ( r1_tarski(k3_tarski(k1_xboole_0),X0) = iProver_top ),
% 11.49/1.99      inference(superposition,[status(thm)],[c_1249,c_36198]) ).
% 11.49/1.99  
% 11.49/1.99  cnf(c_36816,plain,
% 11.49/1.99      ( k3_tarski(k1_xboole_0) = k1_xboole_0 ),
% 11.49/1.99      inference(superposition,[status(thm)],[c_36286,c_3481]) ).
% 11.49/1.99  
% 11.49/1.99  cnf(c_582,plain,
% 11.49/1.99      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,X1) | X2 != X0 ),
% 11.49/1.99      theory(equality) ).
% 11.49/1.99  
% 11.49/1.99  cnf(c_2699,plain,
% 11.49/1.99      ( ~ r1_tarski(X0,k1_setfam_1(k2_enumset1(sK8,sK8,sK8,sK8)))
% 11.49/1.99      | r1_tarski(X1,k1_setfam_1(k2_enumset1(sK8,sK8,sK8,sK8)))
% 11.49/1.99      | X1 != X0 ),
% 11.49/1.99      inference(instantiation,[status(thm)],[c_582]) ).
% 11.49/1.99  
% 11.49/1.99  cnf(c_26407,plain,
% 11.49/1.99      ( ~ r1_tarski(X0,k1_setfam_1(k2_enumset1(sK8,sK8,sK8,sK8)))
% 11.49/1.99      | r1_tarski(k3_tarski(X1),k1_setfam_1(k2_enumset1(sK8,sK8,sK8,sK8)))
% 11.49/1.99      | k3_tarski(X1) != X0 ),
% 11.49/1.99      inference(instantiation,[status(thm)],[c_2699]) ).
% 11.49/1.99  
% 11.49/1.99  cnf(c_26413,plain,
% 11.49/1.99      ( r1_tarski(k3_tarski(k1_xboole_0),k1_setfam_1(k2_enumset1(sK8,sK8,sK8,sK8)))
% 11.49/1.99      | ~ r1_tarski(k1_xboole_0,k1_setfam_1(k2_enumset1(sK8,sK8,sK8,sK8)))
% 11.49/1.99      | k3_tarski(k1_xboole_0) != k1_xboole_0 ),
% 11.49/1.99      inference(instantiation,[status(thm)],[c_26407]) ).
% 11.49/1.99  
% 11.49/1.99  cnf(c_2,plain,
% 11.49/1.99      ( ~ r2_hidden(X0,X1) | r2_hidden(X0,X2) | ~ r1_tarski(X1,X2) ),
% 11.49/1.99      inference(cnf_transformation,[],[f49]) ).
% 11.49/1.99  
% 11.49/1.99  cnf(c_2727,plain,
% 11.49/1.99      ( ~ r2_hidden(X0,X1)
% 11.49/1.99      | r2_hidden(X0,k1_setfam_1(X2))
% 11.49/1.99      | ~ r1_tarski(X1,k1_setfam_1(X2)) ),
% 11.49/1.99      inference(instantiation,[status(thm)],[c_2]) ).
% 11.49/1.99  
% 11.49/1.99  cnf(c_16934,plain,
% 11.49/1.99      ( ~ r2_hidden(sK0(sK8,k1_setfam_1(k2_enumset1(sK8,sK8,sK8,sK8))),X0)
% 11.49/1.99      | r2_hidden(sK0(sK8,k1_setfam_1(k2_enumset1(sK8,sK8,sK8,sK8))),k1_setfam_1(k2_enumset1(sK8,sK8,sK8,sK8)))
% 11.49/1.99      | ~ r1_tarski(X0,k1_setfam_1(k2_enumset1(sK8,sK8,sK8,sK8))) ),
% 11.49/1.99      inference(instantiation,[status(thm)],[c_2727]) ).
% 11.49/1.99  
% 11.49/1.99  cnf(c_24903,plain,
% 11.49/1.99      ( r2_hidden(sK0(sK8,k1_setfam_1(k2_enumset1(sK8,sK8,sK8,sK8))),k1_setfam_1(k2_enumset1(sK8,sK8,sK8,sK8)))
% 11.49/1.99      | ~ r2_hidden(sK0(sK8,k1_setfam_1(k2_enumset1(sK8,sK8,sK8,sK8))),k3_tarski(X0))
% 11.49/1.99      | ~ r1_tarski(k3_tarski(X0),k1_setfam_1(k2_enumset1(sK8,sK8,sK8,sK8))) ),
% 11.49/1.99      inference(instantiation,[status(thm)],[c_16934]) ).
% 11.49/1.99  
% 11.49/1.99  cnf(c_24906,plain,
% 11.49/1.99      ( r2_hidden(sK0(sK8,k1_setfam_1(k2_enumset1(sK8,sK8,sK8,sK8))),k1_setfam_1(k2_enumset1(sK8,sK8,sK8,sK8)))
% 11.49/1.99      | ~ r2_hidden(sK0(sK8,k1_setfam_1(k2_enumset1(sK8,sK8,sK8,sK8))),k3_tarski(k1_xboole_0))
% 11.49/1.99      | ~ r1_tarski(k3_tarski(k1_xboole_0),k1_setfam_1(k2_enumset1(sK8,sK8,sK8,sK8))) ),
% 11.49/1.99      inference(instantiation,[status(thm)],[c_24903]) ).
% 11.49/1.99  
% 11.49/1.99  cnf(c_29,plain,
% 11.49/1.99      ( ~ r2_hidden(X0,X1)
% 11.49/1.99      | r2_hidden(sK5(X1,X2),X2)
% 11.49/1.99      | r2_hidden(sK5(X1,X2),X0)
% 11.49/1.99      | k1_setfam_1(X1) = X2
% 11.49/1.99      | k1_xboole_0 = X1 ),
% 11.49/1.99      inference(cnf_transformation,[],[f80]) ).
% 11.49/1.99  
% 11.49/1.99  cnf(c_35,negated_conjecture,
% 11.49/1.99      ( k1_setfam_1(k2_enumset1(sK8,sK8,sK8,sK8)) != sK8 ),
% 11.49/1.99      inference(cnf_transformation,[],[f103]) ).
% 11.49/1.99  
% 11.49/1.99  cnf(c_7025,plain,
% 11.49/1.99      ( ~ r2_hidden(X0,k2_enumset1(sK8,sK8,sK8,sK8))
% 11.49/1.99      | r2_hidden(sK5(k2_enumset1(sK8,sK8,sK8,sK8),sK8),X0)
% 11.49/1.99      | r2_hidden(sK5(k2_enumset1(sK8,sK8,sK8,sK8),sK8),sK8)
% 11.49/1.99      | k1_xboole_0 = k2_enumset1(sK8,sK8,sK8,sK8) ),
% 11.49/1.99      inference(resolution,[status(thm)],[c_29,c_35]) ).
% 11.49/1.99  
% 11.49/1.99  cnf(c_28,plain,
% 11.49/1.99      ( r2_hidden(sK6(X0,X1),X0)
% 11.49/1.99      | ~ r2_hidden(sK5(X0,X1),X1)
% 11.49/1.99      | k1_setfam_1(X0) = X1
% 11.49/1.99      | k1_xboole_0 = X0 ),
% 11.49/1.99      inference(cnf_transformation,[],[f81]) ).
% 11.49/1.99  
% 11.49/1.99  cnf(c_7398,plain,
% 11.49/1.99      ( ~ r2_hidden(X0,k2_enumset1(sK8,sK8,sK8,sK8))
% 11.49/1.99      | r2_hidden(sK6(k2_enumset1(sK8,sK8,sK8,sK8),sK8),k2_enumset1(sK8,sK8,sK8,sK8))
% 11.49/1.99      | r2_hidden(sK5(k2_enumset1(sK8,sK8,sK8,sK8),sK8),X0)
% 11.49/1.99      | k1_setfam_1(k2_enumset1(sK8,sK8,sK8,sK8)) = sK8
% 11.49/1.99      | k1_xboole_0 = k2_enumset1(sK8,sK8,sK8,sK8) ),
% 11.49/1.99      inference(resolution,[status(thm)],[c_7025,c_28]) ).
% 11.49/1.99  
% 11.49/1.99  cnf(c_7431,plain,
% 11.49/1.99      ( r2_hidden(sK5(k2_enumset1(sK8,sK8,sK8,sK8),sK8),sK8)
% 11.49/1.99      | ~ r2_hidden(sK8,k2_enumset1(sK8,sK8,sK8,sK8))
% 11.49/1.99      | k1_xboole_0 = k2_enumset1(sK8,sK8,sK8,sK8) ),
% 11.49/1.99      inference(factoring,[status(thm)],[c_7025]) ).
% 11.49/1.99  
% 11.49/1.99  cnf(c_21,plain,
% 11.49/1.99      ( r2_hidden(X0,X1) | ~ r1_tarski(k2_enumset1(X0,X0,X0,X0),X1) ),
% 11.49/1.99      inference(cnf_transformation,[],[f99]) ).
% 11.49/1.99  
% 11.49/1.99  cnf(c_1783,plain,
% 11.49/1.99      ( r2_hidden(sK8,X0)
% 11.49/1.99      | ~ r1_tarski(k2_enumset1(sK8,sK8,sK8,sK8),X0) ),
% 11.49/1.99      inference(instantiation,[status(thm)],[c_21]) ).
% 11.49/1.99  
% 11.49/1.99  cnf(c_1894,plain,
% 11.49/1.99      ( r2_hidden(sK8,k2_enumset1(sK8,sK8,sK8,sK8))
% 11.49/1.99      | ~ r1_tarski(k2_enumset1(sK8,sK8,sK8,sK8),k2_enumset1(sK8,sK8,sK8,sK8)) ),
% 11.49/1.99      inference(instantiation,[status(thm)],[c_1783]) ).
% 11.49/1.99  
% 11.49/1.99  cnf(c_5,plain,
% 11.49/1.99      ( r1_tarski(X0,X0) ),
% 11.49/1.99      inference(cnf_transformation,[],[f105]) ).
% 11.49/1.99  
% 11.49/1.99  cnf(c_1574,plain,
% 11.49/1.99      ( r1_tarski(k2_enumset1(X0,X0,X0,X0),k2_enumset1(X0,X0,X0,X0)) ),
% 11.49/1.99      inference(instantiation,[status(thm)],[c_5]) ).
% 11.49/1.99  
% 11.49/1.99  cnf(c_1895,plain,
% 11.49/1.99      ( r1_tarski(k2_enumset1(sK8,sK8,sK8,sK8),k2_enumset1(sK8,sK8,sK8,sK8)) ),
% 11.49/1.99      inference(instantiation,[status(thm)],[c_1574]) ).
% 11.49/1.99  
% 11.49/1.99  cnf(c_7434,plain,
% 11.49/1.99      ( r2_hidden(sK5(k2_enumset1(sK8,sK8,sK8,sK8),sK8),sK8)
% 11.49/1.99      | k1_xboole_0 = k2_enumset1(sK8,sK8,sK8,sK8) ),
% 11.49/1.99      inference(global_propositional_subsumption,
% 11.49/1.99                [status(thm)],
% 11.49/1.99                [c_7431,c_1894,c_1895]) ).
% 11.49/1.99  
% 11.49/1.99  cnf(c_7673,plain,
% 11.49/1.99      ( r2_hidden(sK6(k2_enumset1(sK8,sK8,sK8,sK8),sK8),k2_enumset1(sK8,sK8,sK8,sK8))
% 11.49/1.99      | k1_setfam_1(k2_enumset1(sK8,sK8,sK8,sK8)) = sK8
% 11.49/1.99      | k1_xboole_0 = k2_enumset1(sK8,sK8,sK8,sK8) ),
% 11.49/1.99      inference(resolution,[status(thm)],[c_7434,c_28]) ).
% 11.49/1.99  
% 11.49/1.99  cnf(c_7677,plain,
% 11.49/1.99      ( r2_hidden(sK6(k2_enumset1(sK8,sK8,sK8,sK8),sK8),k2_enumset1(sK8,sK8,sK8,sK8))
% 11.49/1.99      | k1_xboole_0 = k2_enumset1(sK8,sK8,sK8,sK8) ),
% 11.49/1.99      inference(global_propositional_subsumption,
% 11.49/1.99                [status(thm)],
% 11.49/1.99                [c_7398,c_35,c_7673]) ).
% 11.49/1.99  
% 11.49/1.99  cnf(c_13,plain,
% 11.49/1.99      ( ~ r2_hidden(X0,k2_enumset1(X1,X1,X2,X3))
% 11.49/1.99      | X0 = X1
% 11.49/1.99      | X0 = X2
% 11.49/1.99      | X0 = X3 ),
% 11.49/1.99      inference(cnf_transformation,[],[f112]) ).
% 11.49/1.99  
% 11.49/1.99  cnf(c_7955,plain,
% 11.49/1.99      ( sK6(k2_enumset1(sK8,sK8,sK8,sK8),sK8) = sK8
% 11.49/1.99      | k1_xboole_0 = k2_enumset1(sK8,sK8,sK8,sK8) ),
% 11.49/1.99      inference(resolution,[status(thm)],[c_7677,c_13]) ).
% 11.49/1.99  
% 11.49/1.99  cnf(c_581,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 11.49/1.99  
% 11.49/1.99  cnf(c_580,plain,( X0 = X0 ),theory(equality) ).
% 11.49/1.99  
% 11.49/1.99  cnf(c_2666,plain,
% 11.49/1.99      ( X0 != X1 | X1 = X0 ),
% 11.49/1.99      inference(resolution,[status(thm)],[c_581,c_580]) ).
% 11.49/1.99  
% 11.49/1.99  cnf(c_7968,plain,
% 11.49/1.99      ( sK8 = sK6(k2_enumset1(sK8,sK8,sK8,sK8),sK8)
% 11.49/1.99      | k1_xboole_0 = k2_enumset1(sK8,sK8,sK8,sK8) ),
% 11.49/1.99      inference(resolution,[status(thm)],[c_7955,c_2666]) ).
% 11.49/1.99  
% 11.49/1.99  cnf(c_583,plain,
% 11.49/1.99      ( ~ r2_hidden(X0,X1) | r2_hidden(X2,X3) | X2 != X0 | X3 != X1 ),
% 11.49/1.99      theory(equality) ).
% 11.49/1.99  
% 11.49/1.99  cnf(c_26,plain,
% 11.49/1.99      ( k1_setfam_1(k1_xboole_0) = k1_xboole_0 ),
% 11.49/1.99      inference(cnf_transformation,[],[f120]) ).
% 11.49/1.99  
% 11.49/1.99  cnf(c_5252,plain,
% 11.49/1.99      ( r2_hidden(X0,k1_setfam_1(k1_xboole_0))
% 11.49/1.99      | ~ r2_hidden(X1,k1_xboole_0)
% 11.49/1.99      | X0 != X1 ),
% 11.49/1.99      inference(resolution,[status(thm)],[c_583,c_26]) ).
% 11.49/1.99  
% 11.49/1.99  cnf(c_9111,plain,
% 11.49/1.99      ( ~ r2_hidden(sK6(k2_enumset1(sK8,sK8,sK8,sK8),sK8),k1_xboole_0)
% 11.49/1.99      | r2_hidden(sK8,k1_setfam_1(k1_xboole_0))
% 11.49/1.99      | k1_xboole_0 = k2_enumset1(sK8,sK8,sK8,sK8) ),
% 11.49/1.99      inference(resolution,[status(thm)],[c_7968,c_5252]) ).
% 11.49/1.99  
% 11.49/1.99  cnf(c_1896,plain,
% 11.49/1.99      ( r2_hidden(sK8,k2_enumset1(sK8,sK8,sK8,sK8)) = iProver_top
% 11.49/1.99      | r1_tarski(k2_enumset1(sK8,sK8,sK8,sK8),k2_enumset1(sK8,sK8,sK8,sK8)) != iProver_top ),
% 11.49/1.99      inference(predicate_to_equality,[status(thm)],[c_1894]) ).
% 11.49/1.99  
% 11.49/1.99  cnf(c_1898,plain,
% 11.49/1.99      ( r1_tarski(k2_enumset1(sK8,sK8,sK8,sK8),k2_enumset1(sK8,sK8,sK8,sK8)) = iProver_top ),
% 11.49/1.99      inference(predicate_to_equality,[status(thm)],[c_1895]) ).
% 11.49/1.99  
% 11.49/1.99  cnf(c_7432,plain,
% 11.49/1.99      ( k1_xboole_0 = k2_enumset1(sK8,sK8,sK8,sK8)
% 11.49/1.99      | r2_hidden(sK5(k2_enumset1(sK8,sK8,sK8,sK8),sK8),sK8) = iProver_top
% 11.49/1.99      | r2_hidden(sK8,k2_enumset1(sK8,sK8,sK8,sK8)) != iProver_top ),
% 11.49/1.99      inference(predicate_to_equality,[status(thm)],[c_7431]) ).
% 11.49/1.99  
% 11.49/1.99  cnf(c_7973,plain,
% 11.49/1.99      ( r2_hidden(X0,sK6(k2_enumset1(sK8,sK8,sK8,sK8),sK8))
% 11.49/1.99      | ~ r2_hidden(X1,sK8)
% 11.49/1.99      | X0 != X1
% 11.49/1.99      | k1_xboole_0 = k2_enumset1(sK8,sK8,sK8,sK8) ),
% 11.49/1.99      inference(resolution,[status(thm)],[c_7955,c_583]) ).
% 11.49/1.99  
% 11.49/1.99  cnf(c_10096,plain,
% 11.49/1.99      ( r2_hidden(X0,sK6(k2_enumset1(sK8,sK8,sK8,sK8),sK8))
% 11.49/1.99      | ~ r2_hidden(X0,sK8)
% 11.49/1.99      | k1_xboole_0 = k2_enumset1(sK8,sK8,sK8,sK8) ),
% 11.49/1.99      inference(resolution,[status(thm)],[c_7973,c_580]) ).
% 11.49/1.99  
% 11.49/1.99  cnf(c_27,plain,
% 11.49/1.99      ( ~ r2_hidden(sK5(X0,X1),X1)
% 11.49/1.99      | ~ r2_hidden(sK5(X0,X1),sK6(X0,X1))
% 11.49/1.99      | k1_setfam_1(X0) = X1
% 11.49/1.99      | k1_xboole_0 = X0 ),
% 11.49/1.99      inference(cnf_transformation,[],[f82]) ).
% 11.49/1.99  
% 11.49/1.99  cnf(c_11616,plain,
% 11.49/1.99      ( ~ r2_hidden(sK5(k2_enumset1(sK8,sK8,sK8,sK8),sK8),sK8)
% 11.49/1.99      | k1_setfam_1(k2_enumset1(sK8,sK8,sK8,sK8)) = sK8
% 11.49/1.99      | k1_xboole_0 = k2_enumset1(sK8,sK8,sK8,sK8) ),
% 11.49/1.99      inference(resolution,[status(thm)],[c_10096,c_27]) ).
% 11.49/1.99  
% 11.49/1.99  cnf(c_11617,plain,
% 11.49/1.99      ( k1_setfam_1(k2_enumset1(sK8,sK8,sK8,sK8)) = sK8
% 11.49/1.99      | k1_xboole_0 = k2_enumset1(sK8,sK8,sK8,sK8)
% 11.49/1.99      | r2_hidden(sK5(k2_enumset1(sK8,sK8,sK8,sK8),sK8),sK8) != iProver_top ),
% 11.49/1.99      inference(predicate_to_equality,[status(thm)],[c_11616]) ).
% 11.49/1.99  
% 11.49/1.99  cnf(c_11952,plain,
% 11.49/1.99      ( k1_xboole_0 = k2_enumset1(sK8,sK8,sK8,sK8) ),
% 11.49/1.99      inference(global_propositional_subsumption,
% 11.49/1.99                [status(thm)],
% 11.49/1.99                [c_9111,c_35,c_1896,c_1898,c_7432,c_11617]) ).
% 11.49/1.99  
% 11.49/1.99  cnf(c_586,plain,
% 11.49/1.99      ( X0 != X1 | k1_setfam_1(X0) = k1_setfam_1(X1) ),
% 11.49/1.99      theory(equality) ).
% 11.49/1.99  
% 11.49/1.99  cnf(c_2168,plain,
% 11.49/1.99      ( ~ r1_tarski(k1_setfam_1(X0),X1)
% 11.49/1.99      | r1_tarski(k1_setfam_1(X2),X1)
% 11.49/1.99      | X2 != X0 ),
% 11.49/1.99      inference(resolution,[status(thm)],[c_582,c_586]) ).
% 11.49/1.99  
% 11.49/1.99  cnf(c_11960,plain,
% 11.49/1.99      ( ~ r1_tarski(k1_setfam_1(k2_enumset1(sK8,sK8,sK8,sK8)),X0)
% 11.49/1.99      | r1_tarski(k1_setfam_1(k1_xboole_0),X0) ),
% 11.49/1.99      inference(resolution,[status(thm)],[c_11952,c_2168]) ).
% 11.49/1.99  
% 11.49/1.99  cnf(c_2161,plain,
% 11.49/1.99      ( r1_tarski(k1_setfam_1(k1_xboole_0),X0)
% 11.49/1.99      | ~ r1_tarski(k1_xboole_0,X0) ),
% 11.49/1.99      inference(resolution,[status(thm)],[c_582,c_26]) ).
% 11.49/1.99  
% 11.49/1.99  cnf(c_3478,plain,
% 11.49/1.99      ( r1_tarski(k1_xboole_0,X0) ),
% 11.49/1.99      inference(predicate_to_equality_rev,[status(thm)],[c_3459]) ).
% 11.49/1.99  
% 11.49/1.99  cnf(c_16020,plain,
% 11.49/1.99      ( r1_tarski(k1_setfam_1(k1_xboole_0),X0) ),
% 11.49/1.99      inference(global_propositional_subsumption,
% 11.49/1.99                [status(thm)],
% 11.49/1.99                [c_11960,c_2161,c_3478]) ).
% 11.49/1.99  
% 11.49/1.99  cnf(c_11967,plain,
% 11.49/1.99      ( k2_enumset1(sK8,sK8,sK8,sK8) = k1_xboole_0 ),
% 11.49/1.99      inference(resolution,[status(thm)],[c_11952,c_2666]) ).
% 11.49/1.99  
% 11.49/1.99  cnf(c_15775,plain,
% 11.49/1.99      ( r1_tarski(k1_setfam_1(k2_enumset1(sK8,sK8,sK8,sK8)),X0)
% 11.49/1.99      | ~ r1_tarski(k1_setfam_1(k1_xboole_0),X0) ),
% 11.49/1.99      inference(resolution,[status(thm)],[c_11967,c_2168]) ).
% 11.49/1.99  
% 11.49/1.99  cnf(c_16696,plain,
% 11.49/1.99      ( r1_tarski(k1_setfam_1(k2_enumset1(sK8,sK8,sK8,sK8)),X0) ),
% 11.49/1.99      inference(backward_subsumption_resolution,
% 11.49/1.99                [status(thm)],
% 11.49/1.99                [c_16020,c_15775]) ).
% 11.49/1.99  
% 11.49/1.99  cnf(c_2661,plain,
% 11.49/1.99      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X2 != X0 | X1 = X2 ),
% 11.49/1.99      inference(resolution,[status(thm)],[c_581,c_3]) ).
% 11.49/1.99  
% 11.49/1.99  cnf(c_12387,plain,
% 11.49/1.99      ( ~ r1_tarski(X0,k2_enumset1(sK8,sK8,sK8,sK8))
% 11.49/1.99      | ~ r1_tarski(k2_enumset1(sK8,sK8,sK8,sK8),X0)
% 11.49/1.99      | X0 = k1_xboole_0 ),
% 11.49/1.99      inference(resolution,[status(thm)],[c_2661,c_11952]) ).
% 11.49/1.99  
% 11.49/1.99  cnf(c_15773,plain,
% 11.49/1.99      ( r1_tarski(k2_enumset1(sK8,sK8,sK8,sK8),X0)
% 11.49/1.99      | ~ r1_tarski(k1_xboole_0,X0) ),
% 11.49/1.99      inference(resolution,[status(thm)],[c_11967,c_582]) ).
% 11.49/1.99  
% 11.49/1.99  cnf(c_18703,plain,
% 11.49/1.99      ( ~ r1_tarski(X0,k2_enumset1(sK8,sK8,sK8,sK8)) | X0 = k1_xboole_0 ),
% 11.49/1.99      inference(global_propositional_subsumption,
% 11.49/1.99                [status(thm)],
% 11.49/1.99                [c_12387,c_3478,c_15773]) ).
% 11.49/1.99  
% 11.49/1.99  cnf(c_22970,plain,
% 11.49/1.99      ( k1_setfam_1(k2_enumset1(sK8,sK8,sK8,sK8)) = k1_xboole_0 ),
% 11.49/1.99      inference(resolution,[status(thm)],[c_16696,c_18703]) ).
% 11.49/1.99  
% 11.49/1.99  cnf(c_9607,plain,
% 11.49/1.99      ( X0 != X1
% 11.49/1.99      | X0 = k1_setfam_1(k2_enumset1(sK8,sK8,sK8,sK8))
% 11.49/1.99      | k1_setfam_1(k2_enumset1(sK8,sK8,sK8,sK8)) != X1 ),
% 11.49/1.99      inference(instantiation,[status(thm)],[c_581]) ).
% 11.49/1.99  
% 11.49/1.99  cnf(c_9608,plain,
% 11.49/1.99      ( k1_setfam_1(k2_enumset1(sK8,sK8,sK8,sK8)) != k1_xboole_0
% 11.49/1.99      | k1_xboole_0 = k1_setfam_1(k2_enumset1(sK8,sK8,sK8,sK8))
% 11.49/1.99      | k1_xboole_0 != k1_xboole_0 ),
% 11.49/1.99      inference(instantiation,[status(thm)],[c_9607]) ).
% 11.49/1.99  
% 11.49/1.99  cnf(c_17,plain,
% 11.49/1.99      ( ~ r2_hidden(X0,X1)
% 11.49/1.99      | ~ r2_hidden(X2,X0)
% 11.49/1.99      | r2_hidden(X2,k3_tarski(X1)) ),
% 11.49/1.99      inference(cnf_transformation,[],[f113]) ).
% 11.49/1.99  
% 11.49/1.99  cnf(c_6864,plain,
% 11.49/1.99      ( r2_hidden(sK0(sK8,k1_setfam_1(k2_enumset1(sK8,sK8,sK8,sK8))),k3_tarski(X0))
% 11.49/1.99      | ~ r2_hidden(sK0(sK8,k1_setfam_1(k2_enumset1(sK8,sK8,sK8,sK8))),sK8)
% 11.49/1.99      | ~ r2_hidden(sK8,X0) ),
% 11.49/1.99      inference(instantiation,[status(thm)],[c_17]) ).
% 11.49/1.99  
% 11.49/1.99  cnf(c_6866,plain,
% 11.49/1.99      ( r2_hidden(sK0(sK8,k1_setfam_1(k2_enumset1(sK8,sK8,sK8,sK8))),k3_tarski(k1_xboole_0))
% 11.49/1.99      | ~ r2_hidden(sK0(sK8,k1_setfam_1(k2_enumset1(sK8,sK8,sK8,sK8))),sK8)
% 11.49/1.99      | ~ r2_hidden(sK8,k1_xboole_0) ),
% 11.49/1.99      inference(instantiation,[status(thm)],[c_6864]) ).
% 11.49/1.99  
% 11.49/1.99  cnf(c_5835,plain,
% 11.49/1.99      ( r1_tarski(X0,k1_setfam_1(k2_enumset1(sK8,sK8,sK8,sK8)))
% 11.49/1.99      | ~ r1_tarski(k1_setfam_1(k2_enumset1(sK8,sK8,sK8,sK8)),k1_setfam_1(k2_enumset1(sK8,sK8,sK8,sK8)))
% 11.49/1.99      | X0 != k1_setfam_1(k2_enumset1(sK8,sK8,sK8,sK8)) ),
% 11.49/1.99      inference(instantiation,[status(thm)],[c_2699]) ).
% 11.49/1.99  
% 11.49/1.99  cnf(c_5837,plain,
% 11.49/1.99      ( ~ r1_tarski(k1_setfam_1(k2_enumset1(sK8,sK8,sK8,sK8)),k1_setfam_1(k2_enumset1(sK8,sK8,sK8,sK8)))
% 11.49/1.99      | r1_tarski(k1_xboole_0,k1_setfam_1(k2_enumset1(sK8,sK8,sK8,sK8)))
% 11.49/1.99      | k1_xboole_0 != k1_setfam_1(k2_enumset1(sK8,sK8,sK8,sK8)) ),
% 11.49/1.99      inference(instantiation,[status(thm)],[c_5835]) ).
% 11.49/1.99  
% 11.49/1.99  cnf(c_1538,plain,
% 11.49/1.99      ( ~ r1_tarski(X0,X1)
% 11.49/1.99      | r1_tarski(k2_enumset1(X2,X2,X2,X2),X1)
% 11.49/1.99      | k2_enumset1(X2,X2,X2,X2) != X0 ),
% 11.49/1.99      inference(instantiation,[status(thm)],[c_582]) ).
% 11.49/1.99  
% 11.49/1.99  cnf(c_4011,plain,
% 11.49/1.99      ( ~ r1_tarski(X0,X1)
% 11.49/1.99      | r1_tarski(k2_enumset1(sK8,sK8,sK8,sK8),X1)
% 11.49/1.99      | k2_enumset1(sK8,sK8,sK8,sK8) != X0 ),
% 11.49/1.99      inference(instantiation,[status(thm)],[c_1538]) ).
% 11.49/1.99  
% 11.49/1.99  cnf(c_4013,plain,
% 11.49/1.99      ( r1_tarski(k2_enumset1(sK8,sK8,sK8,sK8),k1_xboole_0)
% 11.49/1.99      | ~ r1_tarski(k1_xboole_0,k1_xboole_0)
% 11.49/1.99      | k2_enumset1(sK8,sK8,sK8,sK8) != k1_xboole_0 ),
% 11.49/1.99      inference(instantiation,[status(thm)],[c_4011]) ).
% 11.49/1.99  
% 11.49/1.99  cnf(c_2684,plain,
% 11.49/1.99      ( r1_tarski(k1_setfam_1(k2_enumset1(sK8,sK8,sK8,sK8)),k1_setfam_1(k2_enumset1(sK8,sK8,sK8,sK8))) ),
% 11.49/1.99      inference(instantiation,[status(thm)],[c_5]) ).
% 11.49/1.99  
% 11.49/1.99  cnf(c_1658,plain,
% 11.49/1.99      ( ~ r1_tarski(k1_setfam_1(k2_enumset1(sK8,sK8,sK8,sK8)),sK8)
% 11.49/1.99      | ~ r1_tarski(sK8,k1_setfam_1(k2_enumset1(sK8,sK8,sK8,sK8))) ),
% 11.49/1.99      inference(resolution,[status(thm)],[c_3,c_35]) ).
% 11.49/1.99  
% 11.49/1.99  cnf(c_1954,plain,
% 11.49/1.99      ( ~ r2_hidden(sK8,k2_enumset1(sK8,sK8,sK8,sK8))
% 11.49/1.99      | ~ r1_tarski(sK8,k1_setfam_1(k2_enumset1(sK8,sK8,sK8,sK8))) ),
% 11.49/1.99      inference(resolution,[status(thm)],[c_1658,c_33]) ).
% 11.49/1.99  
% 11.49/1.99  cnf(c_1785,plain,
% 11.49/1.99      ( r2_hidden(sK8,k1_xboole_0)
% 11.49/1.99      | ~ r1_tarski(k2_enumset1(sK8,sK8,sK8,sK8),k1_xboole_0) ),
% 11.49/1.99      inference(instantiation,[status(thm)],[c_1783]) ).
% 11.49/1.99  
% 11.49/1.99  cnf(c_1677,plain,
% 11.49/1.99      ( ~ r2_hidden(sK0(sK8,k1_setfam_1(k2_enumset1(sK8,sK8,sK8,sK8))),k1_setfam_1(k2_enumset1(sK8,sK8,sK8,sK8)))
% 11.49/1.99      | r1_tarski(sK8,k1_setfam_1(k2_enumset1(sK8,sK8,sK8,sK8))) ),
% 11.49/1.99      inference(instantiation,[status(thm)],[c_0]) ).
% 11.49/1.99  
% 11.49/1.99  cnf(c_1678,plain,
% 11.49/1.99      ( r2_hidden(sK0(sK8,k1_setfam_1(k2_enumset1(sK8,sK8,sK8,sK8))),sK8)
% 11.49/1.99      | r1_tarski(sK8,k1_setfam_1(k2_enumset1(sK8,sK8,sK8,sK8))) ),
% 11.49/1.99      inference(instantiation,[status(thm)],[c_1]) ).
% 11.49/1.99  
% 11.49/1.99  cnf(c_106,plain,
% 11.49/1.99      ( r1_tarski(k1_xboole_0,k1_xboole_0) ),
% 11.49/1.99      inference(instantiation,[status(thm)],[c_5]) ).
% 11.49/1.99  
% 11.49/1.99  cnf(c_12,plain,
% 11.49/1.99      ( r2_hidden(X0,k2_enumset1(X0,X0,X1,X2)) ),
% 11.49/1.99      inference(cnf_transformation,[],[f111]) ).
% 11.49/1.99  
% 11.49/1.99  cnf(c_93,plain,
% 11.49/1.99      ( r2_hidden(k1_xboole_0,k2_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0)) ),
% 11.49/1.99      inference(instantiation,[status(thm)],[c_12]) ).
% 11.49/1.99  
% 11.49/1.99  cnf(c_90,plain,
% 11.49/1.99      ( ~ r2_hidden(k1_xboole_0,k2_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0))
% 11.49/1.99      | k1_xboole_0 = k1_xboole_0 ),
% 11.49/1.99      inference(instantiation,[status(thm)],[c_13]) ).
% 11.49/1.99  
% 11.49/1.99  cnf(contradiction,plain,
% 11.49/1.99      ( $false ),
% 11.49/1.99      inference(minisat,
% 11.49/1.99                [status(thm)],
% 11.49/1.99                [c_36816,c_26413,c_24906,c_22970,c_11967,c_9608,c_6866,
% 11.49/1.99                 c_5837,c_4013,c_2684,c_1954,c_1895,c_1894,c_1785,c_1677,
% 11.49/1.99                 c_1678,c_106,c_93,c_90]) ).
% 11.49/1.99  
% 11.49/1.99  
% 11.49/1.99  % SZS output end CNFRefutation for theBenchmark.p
% 11.49/1.99  
% 11.49/1.99  ------                               Statistics
% 11.49/1.99  
% 11.49/1.99  ------ Selected
% 11.49/1.99  
% 11.49/1.99  total_time:                             1.275
% 11.49/1.99  
%------------------------------------------------------------------------------
