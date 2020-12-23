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
% DateTime   : Thu Dec  3 11:36:51 EST 2020

% Result     : Theorem 23.24s
% Output     : CNFRefutation 23.24s
% Verified   : 
% Statistics : Number of formulae       :  119 ( 159 expanded)
%              Number of clauses        :   58 (  60 expanded)
%              Number of leaves         :   20 (  38 expanded)
%              Depth                    :   19
%              Number of atoms          :  403 ( 664 expanded)
%              Number of equality atoms :  147 ( 231 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal clause size      :   18 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f19,conjecture,(
    ! [X0,X1,X2,X3] :
      ~ ( ! [X4,X5] :
            ~ ( k4_tarski(X4,X5) = X3
              & r2_hidden(X5,X2)
              & r2_hidden(X4,X1) )
        & r2_hidden(X3,X0)
        & r1_tarski(X0,k2_zfmisc_1(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ~ ( ! [X4,X5] :
              ~ ( k4_tarski(X4,X5) = X3
                & r2_hidden(X5,X2)
                & r2_hidden(X4,X1) )
          & r2_hidden(X3,X0)
          & r1_tarski(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(negated_conjecture,[],[f19])).

fof(f27,plain,(
    ? [X0,X1,X2,X3] :
      ( ! [X4,X5] :
          ( k4_tarski(X4,X5) != X3
          | ~ r2_hidden(X5,X2)
          | ~ r2_hidden(X4,X1) )
      & r2_hidden(X3,X0)
      & r1_tarski(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f50,plain,
    ( ? [X0,X1,X2,X3] :
        ( ! [X4,X5] :
            ( k4_tarski(X4,X5) != X3
            | ~ r2_hidden(X5,X2)
            | ~ r2_hidden(X4,X1) )
        & r2_hidden(X3,X0)
        & r1_tarski(X0,k2_zfmisc_1(X1,X2)) )
   => ( ! [X5,X4] :
          ( k4_tarski(X4,X5) != sK11
          | ~ r2_hidden(X5,sK10)
          | ~ r2_hidden(X4,sK9) )
      & r2_hidden(sK11,sK8)
      & r1_tarski(sK8,k2_zfmisc_1(sK9,sK10)) ) ),
    introduced(choice_axiom,[])).

fof(f51,plain,
    ( ! [X4,X5] :
        ( k4_tarski(X4,X5) != sK11
        | ~ r2_hidden(X5,sK10)
        | ~ r2_hidden(X4,sK9) )
    & r2_hidden(sK11,sK8)
    & r1_tarski(sK8,k2_zfmisc_1(sK9,sK10)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8,sK9,sK10,sK11])],[f27,f50])).

fof(f91,plain,(
    r1_tarski(sK8,k2_zfmisc_1(sK9,sK10)) ),
    inference(cnf_transformation,[],[f51])).

fof(f18,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k1_tarski(X1)) = X0
    <=> ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f49,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(X0,k1_tarski(X1)) = X0
        | r2_hidden(X1,X0) )
      & ( ~ r2_hidden(X1,X0)
        | k4_xboole_0(X0,k1_tarski(X1)) != X0 ) ) ),
    inference(nnf_transformation,[],[f18])).

fof(f90,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k1_tarski(X1)) = X0
      | r2_hidden(X1,X0) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( k2_zfmisc_1(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ? [X4,X5] :
              ( k4_tarski(X4,X5) = X3
              & r2_hidden(X5,X1)
              & r2_hidden(X4,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X0,X1,X2] :
      ( ( k2_zfmisc_1(X0,X1) = X2
        | ? [X3] :
            ( ( ! [X4,X5] :
                  ( k4_tarski(X4,X5) != X3
                  | ~ r2_hidden(X5,X1)
                  | ~ r2_hidden(X4,X0) )
              | ~ r2_hidden(X3,X2) )
            & ( ? [X4,X5] :
                  ( k4_tarski(X4,X5) = X3
                  & r2_hidden(X5,X1)
                  & r2_hidden(X4,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ! [X4,X5] :
                  ( k4_tarski(X4,X5) != X3
                  | ~ r2_hidden(X5,X1)
                  | ~ r2_hidden(X4,X0) ) )
            & ( ? [X4,X5] :
                  ( k4_tarski(X4,X5) = X3
                  & r2_hidden(X5,X1)
                  & r2_hidden(X4,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k2_zfmisc_1(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f43,plain,(
    ! [X0,X1,X2] :
      ( ( k2_zfmisc_1(X0,X1) = X2
        | ? [X3] :
            ( ( ! [X4,X5] :
                  ( k4_tarski(X4,X5) != X3
                  | ~ r2_hidden(X5,X1)
                  | ~ r2_hidden(X4,X0) )
              | ~ r2_hidden(X3,X2) )
            & ( ? [X6,X7] :
                  ( k4_tarski(X6,X7) = X3
                  & r2_hidden(X7,X1)
                  & r2_hidden(X6,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X8] :
            ( ( r2_hidden(X8,X2)
              | ! [X9,X10] :
                  ( k4_tarski(X9,X10) != X8
                  | ~ r2_hidden(X10,X1)
                  | ~ r2_hidden(X9,X0) ) )
            & ( ? [X11,X12] :
                  ( k4_tarski(X11,X12) = X8
                  & r2_hidden(X12,X1)
                  & r2_hidden(X11,X0) )
              | ~ r2_hidden(X8,X2) ) )
        | k2_zfmisc_1(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f42])).

fof(f46,plain,(
    ! [X8,X1,X0] :
      ( ? [X11,X12] :
          ( k4_tarski(X11,X12) = X8
          & r2_hidden(X12,X1)
          & r2_hidden(X11,X0) )
     => ( k4_tarski(sK6(X0,X1,X8),sK7(X0,X1,X8)) = X8
        & r2_hidden(sK7(X0,X1,X8),X1)
        & r2_hidden(sK6(X0,X1,X8),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f45,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X6,X7] :
          ( k4_tarski(X6,X7) = X3
          & r2_hidden(X7,X1)
          & r2_hidden(X6,X0) )
     => ( k4_tarski(sK4(X0,X1,X2),sK5(X0,X1,X2)) = X3
        & r2_hidden(sK5(X0,X1,X2),X1)
        & r2_hidden(sK4(X0,X1,X2),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f44,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ! [X4,X5] :
                ( k4_tarski(X4,X5) != X3
                | ~ r2_hidden(X5,X1)
                | ~ r2_hidden(X4,X0) )
            | ~ r2_hidden(X3,X2) )
          & ( ? [X6,X7] :
                ( k4_tarski(X6,X7) = X3
                & r2_hidden(X7,X1)
                & r2_hidden(X6,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( ! [X5,X4] :
              ( k4_tarski(X4,X5) != sK3(X0,X1,X2)
              | ~ r2_hidden(X5,X1)
              | ~ r2_hidden(X4,X0) )
          | ~ r2_hidden(sK3(X0,X1,X2),X2) )
        & ( ? [X7,X6] :
              ( k4_tarski(X6,X7) = sK3(X0,X1,X2)
              & r2_hidden(X7,X1)
              & r2_hidden(X6,X0) )
          | r2_hidden(sK3(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f47,plain,(
    ! [X0,X1,X2] :
      ( ( k2_zfmisc_1(X0,X1) = X2
        | ( ( ! [X4,X5] :
                ( k4_tarski(X4,X5) != sK3(X0,X1,X2)
                | ~ r2_hidden(X5,X1)
                | ~ r2_hidden(X4,X0) )
            | ~ r2_hidden(sK3(X0,X1,X2),X2) )
          & ( ( k4_tarski(sK4(X0,X1,X2),sK5(X0,X1,X2)) = sK3(X0,X1,X2)
              & r2_hidden(sK5(X0,X1,X2),X1)
              & r2_hidden(sK4(X0,X1,X2),X0) )
            | r2_hidden(sK3(X0,X1,X2),X2) ) ) )
      & ( ! [X8] :
            ( ( r2_hidden(X8,X2)
              | ! [X9,X10] :
                  ( k4_tarski(X9,X10) != X8
                  | ~ r2_hidden(X10,X1)
                  | ~ r2_hidden(X9,X0) ) )
            & ( ( k4_tarski(sK6(X0,X1,X8),sK7(X0,X1,X8)) = X8
                & r2_hidden(sK7(X0,X1,X8),X1)
                & r2_hidden(sK6(X0,X1,X8),X0) )
              | ~ r2_hidden(X8,X2) ) )
        | k2_zfmisc_1(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5,sK6,sK7])],[f43,f46,f45,f44])).

fof(f78,plain,(
    ! [X2,X0,X8,X1] :
      ( r2_hidden(sK6(X0,X1,X8),X0)
      | ~ r2_hidden(X8,X2)
      | k2_zfmisc_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f47])).

fof(f116,plain,(
    ! [X0,X8,X1] :
      ( r2_hidden(sK6(X0,X1,X8),X0)
      | ~ r2_hidden(X8,k2_zfmisc_1(X0,X1)) ) ),
    inference(equality_resolution,[],[f78])).

fof(f79,plain,(
    ! [X2,X0,X8,X1] :
      ( r2_hidden(sK7(X0,X1,X8),X1)
      | ~ r2_hidden(X8,X2)
      | k2_zfmisc_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f47])).

fof(f115,plain,(
    ! [X0,X8,X1] :
      ( r2_hidden(sK7(X0,X1,X8),X1)
      | ~ r2_hidden(X8,k2_zfmisc_1(X0,X1)) ) ),
    inference(equality_resolution,[],[f79])).

fof(f80,plain,(
    ! [X2,X0,X8,X1] :
      ( k4_tarski(sK6(X0,X1,X8),sK7(X0,X1,X8)) = X8
      | ~ r2_hidden(X8,X2)
      | k2_zfmisc_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f47])).

fof(f114,plain,(
    ! [X0,X8,X1] :
      ( k4_tarski(sK6(X0,X1,X8),sK7(X0,X1,X8)) = X8
      | ~ r2_hidden(X8,k2_zfmisc_1(X0,X1)) ) ),
    inference(equality_resolution,[],[f80])).

fof(f93,plain,(
    ! [X4,X5] :
      ( k4_tarski(X4,X5) != sK11
      | ~ r2_hidden(X5,sK10)
      | ~ r2_hidden(X4,sK9) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k4_xboole_0(X1,X2))
     => ( r1_xboole_0(X0,X2)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X0,X2)
        & r1_tarski(X0,X1) )
      | ~ r1_tarski(X0,k4_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_tarski(X0,k4_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_xboole_0(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f23])).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f13,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f76,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f13])).

fof(f14,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f77,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f14])).

fof(f103,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k1_enumset1(X1,X1,X0) ),
    inference(definition_unfolding,[],[f76,f77,f77])).

fof(f12,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f75,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f12])).

fof(f17,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f88,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f17])).

fof(f94,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k1_enumset1(X0,X0,X1)) ),
    inference(definition_unfolding,[],[f88,f77])).

fof(f102,plain,(
    ! [X0,X1] : r1_tarski(X0,k3_tarski(k1_enumset1(X0,X0,X1))) ),
    inference(definition_unfolding,[],[f75,f94])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X0,X2)
        & r1_tarski(X0,k2_xboole_0(X1,X2)) )
     => r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
      | ~ r1_xboole_0(X0,X2)
      | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
      | ~ r1_xboole_0(X0,X2)
      | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(flattening,[],[f25])).

fof(f74,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r1_xboole_0(X0,X2)
      | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f101,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r1_xboole_0(X0,X2)
      | ~ r1_tarski(X0,k3_tarski(k1_enumset1(X1,X1,X2))) ) ),
    inference(definition_unfolding,[],[f74,f94])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
    <=> r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(k1_tarski(X0),X1)
        | ~ r2_hidden(X0,X1) )
      & ( r2_hidden(X0,X1)
        | ~ r1_tarski(k1_tarski(X0),X1) ) ) ),
    inference(nnf_transformation,[],[f16])).

fof(f86,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | ~ r1_tarski(k1_tarski(X0),X1) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
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
    inference(nnf_transformation,[],[f3])).

fof(f34,plain,(
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
    inference(flattening,[],[f33])).

fof(f35,plain,(
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
    inference(rectify,[],[f34])).

fof(f36,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( ~ r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( r2_hidden(sK1(X0,X1,X2),X1)
          | ~ r2_hidden(sK1(X0,X1,X2),X0)
          | ~ r2_hidden(sK1(X0,X1,X2),X2) )
        & ( ( ~ r2_hidden(sK1(X0,X1,X2),X1)
            & r2_hidden(sK1(X0,X1,X2),X0) )
          | r2_hidden(sK1(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ( ( r2_hidden(sK1(X0,X1,X2),X1)
            | ~ r2_hidden(sK1(X0,X1,X2),X0)
            | ~ r2_hidden(sK1(X0,X1,X2),X2) )
          & ( ( ~ r2_hidden(sK1(X0,X1,X2),X1)
              & r2_hidden(sK1(X0,X1,X2),X0) )
            | r2_hidden(sK1(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( ~ r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f35,f36])).

fof(f59,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f37])).

fof(f108,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,k4_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f59])).

fof(f87,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f8,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f71,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f8])).

fof(f92,plain,(
    r2_hidden(sK11,sK8) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_38,negated_conjecture,
    ( r1_tarski(sK8,k2_zfmisc_1(sK9,sK10)) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_1524,plain,
    ( r1_tarski(sK8,k2_zfmisc_1(sK9,sK10)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_38])).

cnf(c_34,plain,
    ( r2_hidden(X0,X1)
    | k4_xboole_0(X1,k1_tarski(X0)) = X1 ),
    inference(cnf_transformation,[],[f90])).

cnf(c_1528,plain,
    ( k4_xboole_0(X0,k1_tarski(X1)) = X0
    | r2_hidden(X1,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_31,plain,
    ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
    | r2_hidden(sK6(X1,X2,X0),X1) ),
    inference(cnf_transformation,[],[f116])).

cnf(c_1531,plain,
    ( r2_hidden(X0,k2_zfmisc_1(X1,X2)) != iProver_top
    | r2_hidden(sK6(X1,X2,X0),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_30,plain,
    ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
    | r2_hidden(sK7(X1,X2,X0),X2) ),
    inference(cnf_transformation,[],[f115])).

cnf(c_1532,plain,
    ( r2_hidden(X0,k2_zfmisc_1(X1,X2)) != iProver_top
    | r2_hidden(sK7(X1,X2,X0),X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_29,plain,
    ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
    | k4_tarski(sK6(X1,X2,X0),sK7(X1,X2,X0)) = X0 ),
    inference(cnf_transformation,[],[f114])).

cnf(c_1533,plain,
    ( k4_tarski(sK6(X0,X1,X2),sK7(X0,X1,X2)) = X2
    | r2_hidden(X2,k2_zfmisc_1(X0,X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_7485,plain,
    ( k4_tarski(sK6(X0,X1,X2),sK7(X0,X1,X2)) = X2
    | k4_xboole_0(k2_zfmisc_1(X0,X1),k1_tarski(X2)) = k2_zfmisc_1(X0,X1) ),
    inference(superposition,[status(thm)],[c_1528,c_1533])).

cnf(c_36,negated_conjecture,
    ( ~ r2_hidden(X0,sK9)
    | ~ r2_hidden(X1,sK10)
    | k4_tarski(X0,X1) != sK11 ),
    inference(cnf_transformation,[],[f93])).

cnf(c_1526,plain,
    ( k4_tarski(X0,X1) != sK11
    | r2_hidden(X0,sK9) != iProver_top
    | r2_hidden(X1,sK10) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_36])).

cnf(c_65246,plain,
    ( k4_xboole_0(k2_zfmisc_1(X0,X1),k1_tarski(X2)) = k2_zfmisc_1(X0,X1)
    | sK11 != X2
    | r2_hidden(sK7(X0,X1,X2),sK10) != iProver_top
    | r2_hidden(sK6(X0,X1,X2),sK9) != iProver_top ),
    inference(superposition,[status(thm)],[c_7485,c_1526])).

cnf(c_69728,plain,
    ( k4_xboole_0(k2_zfmisc_1(X0,X1),k1_tarski(sK11)) = k2_zfmisc_1(X0,X1)
    | r2_hidden(sK7(X0,X1,sK11),sK10) != iProver_top
    | r2_hidden(sK6(X0,X1,sK11),sK9) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_65246])).

cnf(c_69734,plain,
    ( k4_xboole_0(k2_zfmisc_1(X0,sK10),k1_tarski(sK11)) = k2_zfmisc_1(X0,sK10)
    | r2_hidden(sK6(X0,sK10,sK11),sK9) != iProver_top
    | r2_hidden(sK11,k2_zfmisc_1(X0,sK10)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1532,c_69728])).

cnf(c_70075,plain,
    ( k4_xboole_0(k2_zfmisc_1(sK9,sK10),k1_tarski(sK11)) = k2_zfmisc_1(sK9,sK10)
    | r2_hidden(sK11,k2_zfmisc_1(sK9,sK10)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1531,c_69734])).

cnf(c_96175,plain,
    ( k4_xboole_0(k2_zfmisc_1(sK9,sK10),k1_tarski(sK11)) = k2_zfmisc_1(sK9,sK10) ),
    inference(superposition,[status(thm)],[c_1528,c_70075])).

cnf(c_16,plain,
    ( r1_xboole_0(X0,X1)
    | ~ r1_tarski(X0,k4_xboole_0(X2,X1)) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_1544,plain,
    ( r1_xboole_0(X0,X1) = iProver_top
    | r1_tarski(X0,k4_xboole_0(X2,X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_100372,plain,
    ( r1_xboole_0(X0,k1_tarski(sK11)) = iProver_top
    | r1_tarski(X0,k2_zfmisc_1(sK9,sK10)) != iProver_top ),
    inference(superposition,[status(thm)],[c_96175,c_1544])).

cnf(c_102763,plain,
    ( r1_xboole_0(sK8,k1_tarski(sK11)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1524,c_100372])).

cnf(c_20,plain,
    ( ~ r1_xboole_0(X0,X1)
    | r1_xboole_0(X2,X1)
    | ~ r1_tarski(X2,X0) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_1541,plain,
    ( r1_xboole_0(X0,X1) != iProver_top
    | r1_xboole_0(X2,X1) = iProver_top
    | r1_tarski(X2,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_103287,plain,
    ( r1_xboole_0(X0,k1_tarski(sK11)) = iProver_top
    | r1_tarski(X0,sK8) != iProver_top ),
    inference(superposition,[status(thm)],[c_102763,c_1541])).

cnf(c_23,plain,
    ( k1_enumset1(X0,X0,X1) = k1_enumset1(X1,X1,X0) ),
    inference(cnf_transformation,[],[f103])).

cnf(c_22,plain,
    ( r1_tarski(X0,k3_tarski(k1_enumset1(X0,X0,X1))) ),
    inference(cnf_transformation,[],[f102])).

cnf(c_1539,plain,
    ( r1_tarski(X0,k3_tarski(k1_enumset1(X0,X0,X1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_2283,plain,
    ( r1_tarski(X0,k3_tarski(k1_enumset1(X1,X1,X0))) = iProver_top ),
    inference(superposition,[status(thm)],[c_23,c_1539])).

cnf(c_21,plain,
    ( ~ r1_xboole_0(X0,X1)
    | r1_tarski(X0,X2)
    | ~ r1_tarski(X0,k3_tarski(k1_enumset1(X2,X2,X1))) ),
    inference(cnf_transformation,[],[f101])).

cnf(c_1540,plain,
    ( r1_xboole_0(X0,X1) != iProver_top
    | r1_tarski(X0,X2) = iProver_top
    | r1_tarski(X0,k3_tarski(k1_enumset1(X2,X2,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_9599,plain,
    ( r1_xboole_0(X0,X0) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_2283,c_1540])).

cnf(c_103293,plain,
    ( r1_tarski(k1_tarski(sK11),X0) = iProver_top
    | r1_tarski(k1_tarski(sK11),sK8) != iProver_top ),
    inference(superposition,[status(thm)],[c_103287,c_9599])).

cnf(c_103296,plain,
    ( r1_tarski(k1_tarski(sK11),sK8) != iProver_top
    | r1_tarski(k1_tarski(sK11),k1_xboole_0) = iProver_top ),
    inference(instantiation,[status(thm)],[c_103293])).

cnf(c_805,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_5485,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(sK11,X2)
    | X1 != X2
    | X0 != sK11 ),
    inference(instantiation,[status(thm)],[c_805])).

cnf(c_10309,plain,
    ( ~ r2_hidden(sK11,X0)
    | r2_hidden(sK11,X1)
    | X1 != X0
    | sK11 != sK11 ),
    inference(instantiation,[status(thm)],[c_5485])).

cnf(c_21841,plain,
    ( ~ r2_hidden(sK11,X0)
    | r2_hidden(sK11,k4_xboole_0(X1,X2))
    | k4_xboole_0(X1,X2) != X0
    | sK11 != sK11 ),
    inference(instantiation,[status(thm)],[c_10309])).

cnf(c_21842,plain,
    ( k4_xboole_0(X0,X1) != X2
    | sK11 != sK11
    | r2_hidden(sK11,X2) != iProver_top
    | r2_hidden(sK11,k4_xboole_0(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21841])).

cnf(c_21844,plain,
    ( k4_xboole_0(k1_xboole_0,k1_xboole_0) != k1_xboole_0
    | sK11 != sK11
    | r2_hidden(sK11,k4_xboole_0(k1_xboole_0,k1_xboole_0)) = iProver_top
    | r2_hidden(sK11,k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_21842])).

cnf(c_802,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_7339,plain,
    ( sK11 = sK11 ),
    inference(instantiation,[status(thm)],[c_802])).

cnf(c_33,plain,
    ( ~ r1_tarski(k1_tarski(X0),X1)
    | r2_hidden(X0,X1) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_7156,plain,
    ( ~ r1_tarski(k1_tarski(sK11),X0)
    | r2_hidden(sK11,X0) ),
    inference(instantiation,[status(thm)],[c_33])).

cnf(c_7157,plain,
    ( r1_tarski(k1_tarski(sK11),X0) != iProver_top
    | r2_hidden(sK11,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7156])).

cnf(c_7159,plain,
    ( r1_tarski(k1_tarski(sK11),k1_xboole_0) != iProver_top
    | r2_hidden(sK11,k1_xboole_0) = iProver_top ),
    inference(instantiation,[status(thm)],[c_7157])).

cnf(c_10,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k4_xboole_0(X2,X1)) ),
    inference(cnf_transformation,[],[f108])).

cnf(c_3697,plain,
    ( ~ r2_hidden(sK11,X0)
    | ~ r2_hidden(sK11,k4_xboole_0(X1,X0)) ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_3698,plain,
    ( r2_hidden(sK11,X0) != iProver_top
    | r2_hidden(sK11,k4_xboole_0(X1,X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3697])).

cnf(c_3700,plain,
    ( r2_hidden(sK11,k4_xboole_0(k1_xboole_0,k1_xboole_0)) != iProver_top
    | r2_hidden(sK11,k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_3698])).

cnf(c_32,plain,
    ( r1_tarski(k1_tarski(X0),X1)
    | ~ r2_hidden(X0,X1) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_2592,plain,
    ( r1_tarski(k1_tarski(sK11),sK8)
    | ~ r2_hidden(sK11,sK8) ),
    inference(instantiation,[status(thm)],[c_32])).

cnf(c_2593,plain,
    ( r1_tarski(k1_tarski(sK11),sK8) = iProver_top
    | r2_hidden(sK11,sK8) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2592])).

cnf(c_19,plain,
    ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f71])).

cnf(c_88,plain,
    ( k4_xboole_0(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_19])).

cnf(c_37,negated_conjecture,
    ( r2_hidden(sK11,sK8) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_40,plain,
    ( r2_hidden(sK11,sK8) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_37])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_103296,c_21844,c_7339,c_7159,c_3700,c_2593,c_88,c_40])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n003.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 12:04:27 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  % Running in FOF mode
% 23.24/3.48  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 23.24/3.48  
% 23.24/3.48  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 23.24/3.48  
% 23.24/3.48  ------  iProver source info
% 23.24/3.48  
% 23.24/3.48  git: date: 2020-06-30 10:37:57 +0100
% 23.24/3.48  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 23.24/3.48  git: non_committed_changes: false
% 23.24/3.48  git: last_make_outside_of_git: false
% 23.24/3.48  
% 23.24/3.48  ------ 
% 23.24/3.48  
% 23.24/3.48  ------ Input Options
% 23.24/3.48  
% 23.24/3.48  --out_options                           all
% 23.24/3.48  --tptp_safe_out                         true
% 23.24/3.48  --problem_path                          ""
% 23.24/3.48  --include_path                          ""
% 23.24/3.48  --clausifier                            res/vclausify_rel
% 23.24/3.48  --clausifier_options                    ""
% 23.24/3.48  --stdin                                 false
% 23.24/3.48  --stats_out                             all
% 23.24/3.48  
% 23.24/3.48  ------ General Options
% 23.24/3.48  
% 23.24/3.48  --fof                                   false
% 23.24/3.48  --time_out_real                         305.
% 23.24/3.48  --time_out_virtual                      -1.
% 23.24/3.48  --symbol_type_check                     false
% 23.24/3.48  --clausify_out                          false
% 23.24/3.48  --sig_cnt_out                           false
% 23.24/3.48  --trig_cnt_out                          false
% 23.24/3.48  --trig_cnt_out_tolerance                1.
% 23.24/3.48  --trig_cnt_out_sk_spl                   false
% 23.24/3.48  --abstr_cl_out                          false
% 23.24/3.48  
% 23.24/3.48  ------ Global Options
% 23.24/3.48  
% 23.24/3.48  --schedule                              default
% 23.24/3.48  --add_important_lit                     false
% 23.24/3.48  --prop_solver_per_cl                    1000
% 23.24/3.48  --min_unsat_core                        false
% 23.24/3.48  --soft_assumptions                      false
% 23.24/3.48  --soft_lemma_size                       3
% 23.24/3.48  --prop_impl_unit_size                   0
% 23.24/3.48  --prop_impl_unit                        []
% 23.24/3.48  --share_sel_clauses                     true
% 23.24/3.48  --reset_solvers                         false
% 23.24/3.48  --bc_imp_inh                            [conj_cone]
% 23.24/3.48  --conj_cone_tolerance                   3.
% 23.24/3.48  --extra_neg_conj                        none
% 23.24/3.48  --large_theory_mode                     true
% 23.24/3.48  --prolific_symb_bound                   200
% 23.24/3.48  --lt_threshold                          2000
% 23.24/3.48  --clause_weak_htbl                      true
% 23.24/3.48  --gc_record_bc_elim                     false
% 23.24/3.48  
% 23.24/3.48  ------ Preprocessing Options
% 23.24/3.48  
% 23.24/3.48  --preprocessing_flag                    true
% 23.24/3.48  --time_out_prep_mult                    0.1
% 23.24/3.48  --splitting_mode                        input
% 23.24/3.48  --splitting_grd                         true
% 23.24/3.48  --splitting_cvd                         false
% 23.24/3.48  --splitting_cvd_svl                     false
% 23.24/3.48  --splitting_nvd                         32
% 23.24/3.48  --sub_typing                            true
% 23.24/3.48  --prep_gs_sim                           true
% 23.24/3.48  --prep_unflatten                        true
% 23.24/3.48  --prep_res_sim                          true
% 23.24/3.48  --prep_upred                            true
% 23.24/3.48  --prep_sem_filter                       exhaustive
% 23.24/3.48  --prep_sem_filter_out                   false
% 23.24/3.48  --pred_elim                             true
% 23.24/3.48  --res_sim_input                         true
% 23.24/3.48  --eq_ax_congr_red                       true
% 23.24/3.48  --pure_diseq_elim                       true
% 23.24/3.48  --brand_transform                       false
% 23.24/3.48  --non_eq_to_eq                          false
% 23.24/3.48  --prep_def_merge                        true
% 23.24/3.48  --prep_def_merge_prop_impl              false
% 23.24/3.48  --prep_def_merge_mbd                    true
% 23.24/3.48  --prep_def_merge_tr_red                 false
% 23.24/3.48  --prep_def_merge_tr_cl                  false
% 23.24/3.48  --smt_preprocessing                     true
% 23.24/3.48  --smt_ac_axioms                         fast
% 23.24/3.48  --preprocessed_out                      false
% 23.24/3.48  --preprocessed_stats                    false
% 23.24/3.48  
% 23.24/3.48  ------ Abstraction refinement Options
% 23.24/3.48  
% 23.24/3.48  --abstr_ref                             []
% 23.24/3.48  --abstr_ref_prep                        false
% 23.24/3.48  --abstr_ref_until_sat                   false
% 23.24/3.48  --abstr_ref_sig_restrict                funpre
% 23.24/3.48  --abstr_ref_af_restrict_to_split_sk     false
% 23.24/3.48  --abstr_ref_under                       []
% 23.24/3.48  
% 23.24/3.48  ------ SAT Options
% 23.24/3.48  
% 23.24/3.48  --sat_mode                              false
% 23.24/3.48  --sat_fm_restart_options                ""
% 23.24/3.48  --sat_gr_def                            false
% 23.24/3.48  --sat_epr_types                         true
% 23.24/3.48  --sat_non_cyclic_types                  false
% 23.24/3.48  --sat_finite_models                     false
% 23.24/3.48  --sat_fm_lemmas                         false
% 23.24/3.48  --sat_fm_prep                           false
% 23.24/3.48  --sat_fm_uc_incr                        true
% 23.24/3.48  --sat_out_model                         small
% 23.24/3.48  --sat_out_clauses                       false
% 23.24/3.48  
% 23.24/3.48  ------ QBF Options
% 23.24/3.48  
% 23.24/3.48  --qbf_mode                              false
% 23.24/3.48  --qbf_elim_univ                         false
% 23.24/3.48  --qbf_dom_inst                          none
% 23.24/3.48  --qbf_dom_pre_inst                      false
% 23.24/3.48  --qbf_sk_in                             false
% 23.24/3.48  --qbf_pred_elim                         true
% 23.24/3.48  --qbf_split                             512
% 23.24/3.48  
% 23.24/3.48  ------ BMC1 Options
% 23.24/3.48  
% 23.24/3.48  --bmc1_incremental                      false
% 23.24/3.48  --bmc1_axioms                           reachable_all
% 23.24/3.48  --bmc1_min_bound                        0
% 23.24/3.48  --bmc1_max_bound                        -1
% 23.24/3.48  --bmc1_max_bound_default                -1
% 23.24/3.48  --bmc1_symbol_reachability              true
% 23.24/3.48  --bmc1_property_lemmas                  false
% 23.24/3.48  --bmc1_k_induction                      false
% 23.24/3.48  --bmc1_non_equiv_states                 false
% 23.24/3.48  --bmc1_deadlock                         false
% 23.24/3.48  --bmc1_ucm                              false
% 23.24/3.48  --bmc1_add_unsat_core                   none
% 23.24/3.48  --bmc1_unsat_core_children              false
% 23.24/3.48  --bmc1_unsat_core_extrapolate_axioms    false
% 23.24/3.48  --bmc1_out_stat                         full
% 23.24/3.48  --bmc1_ground_init                      false
% 23.24/3.48  --bmc1_pre_inst_next_state              false
% 23.24/3.48  --bmc1_pre_inst_state                   false
% 23.24/3.48  --bmc1_pre_inst_reach_state             false
% 23.24/3.48  --bmc1_out_unsat_core                   false
% 23.24/3.48  --bmc1_aig_witness_out                  false
% 23.24/3.48  --bmc1_verbose                          false
% 23.24/3.48  --bmc1_dump_clauses_tptp                false
% 23.24/3.48  --bmc1_dump_unsat_core_tptp             false
% 23.24/3.48  --bmc1_dump_file                        -
% 23.24/3.48  --bmc1_ucm_expand_uc_limit              128
% 23.24/3.48  --bmc1_ucm_n_expand_iterations          6
% 23.24/3.48  --bmc1_ucm_extend_mode                  1
% 23.24/3.48  --bmc1_ucm_init_mode                    2
% 23.24/3.48  --bmc1_ucm_cone_mode                    none
% 23.24/3.48  --bmc1_ucm_reduced_relation_type        0
% 23.24/3.48  --bmc1_ucm_relax_model                  4
% 23.24/3.48  --bmc1_ucm_full_tr_after_sat            true
% 23.24/3.48  --bmc1_ucm_expand_neg_assumptions       false
% 23.24/3.48  --bmc1_ucm_layered_model                none
% 23.24/3.48  --bmc1_ucm_max_lemma_size               10
% 23.24/3.48  
% 23.24/3.48  ------ AIG Options
% 23.24/3.48  
% 23.24/3.48  --aig_mode                              false
% 23.24/3.48  
% 23.24/3.48  ------ Instantiation Options
% 23.24/3.48  
% 23.24/3.48  --instantiation_flag                    true
% 23.24/3.48  --inst_sos_flag                         true
% 23.24/3.48  --inst_sos_phase                        true
% 23.24/3.48  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 23.24/3.48  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 23.24/3.48  --inst_lit_sel_side                     num_symb
% 23.24/3.48  --inst_solver_per_active                1400
% 23.24/3.48  --inst_solver_calls_frac                1.
% 23.24/3.48  --inst_passive_queue_type               priority_queues
% 23.24/3.48  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 23.24/3.48  --inst_passive_queues_freq              [25;2]
% 23.24/3.48  --inst_dismatching                      true
% 23.24/3.48  --inst_eager_unprocessed_to_passive     true
% 23.24/3.48  --inst_prop_sim_given                   true
% 23.24/3.48  --inst_prop_sim_new                     false
% 23.24/3.48  --inst_subs_new                         false
% 23.24/3.48  --inst_eq_res_simp                      false
% 23.24/3.48  --inst_subs_given                       false
% 23.24/3.48  --inst_orphan_elimination               true
% 23.24/3.48  --inst_learning_loop_flag               true
% 23.24/3.48  --inst_learning_start                   3000
% 23.24/3.48  --inst_learning_factor                  2
% 23.24/3.48  --inst_start_prop_sim_after_learn       3
% 23.24/3.48  --inst_sel_renew                        solver
% 23.24/3.48  --inst_lit_activity_flag                true
% 23.24/3.48  --inst_restr_to_given                   false
% 23.24/3.48  --inst_activity_threshold               500
% 23.24/3.48  --inst_out_proof                        true
% 23.24/3.48  
% 23.24/3.48  ------ Resolution Options
% 23.24/3.48  
% 23.24/3.48  --resolution_flag                       true
% 23.24/3.48  --res_lit_sel                           adaptive
% 23.24/3.48  --res_lit_sel_side                      none
% 23.24/3.48  --res_ordering                          kbo
% 23.24/3.48  --res_to_prop_solver                    active
% 23.24/3.48  --res_prop_simpl_new                    false
% 23.24/3.48  --res_prop_simpl_given                  true
% 23.24/3.48  --res_passive_queue_type                priority_queues
% 23.24/3.48  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 23.24/3.48  --res_passive_queues_freq               [15;5]
% 23.24/3.48  --res_forward_subs                      full
% 23.24/3.48  --res_backward_subs                     full
% 23.24/3.48  --res_forward_subs_resolution           true
% 23.24/3.48  --res_backward_subs_resolution          true
% 23.24/3.48  --res_orphan_elimination                true
% 23.24/3.48  --res_time_limit                        2.
% 23.24/3.48  --res_out_proof                         true
% 23.24/3.48  
% 23.24/3.48  ------ Superposition Options
% 23.24/3.48  
% 23.24/3.48  --superposition_flag                    true
% 23.24/3.48  --sup_passive_queue_type                priority_queues
% 23.24/3.48  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 23.24/3.48  --sup_passive_queues_freq               [8;1;4]
% 23.24/3.48  --demod_completeness_check              fast
% 23.24/3.48  --demod_use_ground                      true
% 23.24/3.48  --sup_to_prop_solver                    passive
% 23.24/3.48  --sup_prop_simpl_new                    true
% 23.24/3.48  --sup_prop_simpl_given                  true
% 23.24/3.48  --sup_fun_splitting                     true
% 23.24/3.48  --sup_smt_interval                      50000
% 23.24/3.48  
% 23.24/3.48  ------ Superposition Simplification Setup
% 23.24/3.48  
% 23.24/3.48  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 23.24/3.48  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 23.24/3.48  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 23.24/3.48  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 23.24/3.48  --sup_full_triv                         [TrivRules;PropSubs]
% 23.24/3.48  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 23.24/3.48  --sup_full_bw                           [BwDemod;BwSubsumption]
% 23.24/3.48  --sup_immed_triv                        [TrivRules]
% 23.24/3.48  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 23.24/3.48  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 23.24/3.48  --sup_immed_bw_main                     []
% 23.24/3.48  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 23.24/3.48  --sup_input_triv                        [Unflattening;TrivRules]
% 23.24/3.48  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 23.24/3.48  --sup_input_bw                          []
% 23.24/3.48  
% 23.24/3.48  ------ Combination Options
% 23.24/3.48  
% 23.24/3.48  --comb_res_mult                         3
% 23.24/3.48  --comb_sup_mult                         2
% 23.24/3.48  --comb_inst_mult                        10
% 23.24/3.48  
% 23.24/3.48  ------ Debug Options
% 23.24/3.48  
% 23.24/3.48  --dbg_backtrace                         false
% 23.24/3.48  --dbg_dump_prop_clauses                 false
% 23.24/3.48  --dbg_dump_prop_clauses_file            -
% 23.24/3.48  --dbg_out_stat                          false
% 23.24/3.48  ------ Parsing...
% 23.24/3.48  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 23.24/3.48  
% 23.24/3.48  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e  sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 23.24/3.48  
% 23.24/3.48  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 23.24/3.48  
% 23.24/3.48  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 23.24/3.48  ------ Proving...
% 23.24/3.48  ------ Problem Properties 
% 23.24/3.48  
% 23.24/3.48  
% 23.24/3.48  clauses                                 38
% 23.24/3.48  conjectures                             3
% 23.24/3.48  EPR                                     5
% 23.24/3.48  Horn                                    27
% 23.24/3.48  unary                                   7
% 23.24/3.48  binary                                  14
% 23.24/3.48  lits                                    90
% 23.24/3.48  lits eq                                 20
% 23.24/3.48  fd_pure                                 0
% 23.24/3.48  fd_pseudo                               0
% 23.24/3.48  fd_cond                                 1
% 23.24/3.48  fd_pseudo_cond                          11
% 23.24/3.48  AC symbols                              0
% 23.24/3.48  
% 23.24/3.48  ------ Schedule dynamic 5 is on 
% 23.24/3.48  
% 23.24/3.48  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 23.24/3.48  
% 23.24/3.48  
% 23.24/3.48  ------ 
% 23.24/3.48  Current options:
% 23.24/3.48  ------ 
% 23.24/3.48  
% 23.24/3.48  ------ Input Options
% 23.24/3.48  
% 23.24/3.48  --out_options                           all
% 23.24/3.48  --tptp_safe_out                         true
% 23.24/3.48  --problem_path                          ""
% 23.24/3.48  --include_path                          ""
% 23.24/3.48  --clausifier                            res/vclausify_rel
% 23.24/3.48  --clausifier_options                    ""
% 23.24/3.48  --stdin                                 false
% 23.24/3.48  --stats_out                             all
% 23.24/3.48  
% 23.24/3.48  ------ General Options
% 23.24/3.48  
% 23.24/3.48  --fof                                   false
% 23.24/3.48  --time_out_real                         305.
% 23.24/3.48  --time_out_virtual                      -1.
% 23.24/3.48  --symbol_type_check                     false
% 23.24/3.48  --clausify_out                          false
% 23.24/3.48  --sig_cnt_out                           false
% 23.24/3.48  --trig_cnt_out                          false
% 23.24/3.48  --trig_cnt_out_tolerance                1.
% 23.24/3.48  --trig_cnt_out_sk_spl                   false
% 23.24/3.48  --abstr_cl_out                          false
% 23.24/3.48  
% 23.24/3.48  ------ Global Options
% 23.24/3.48  
% 23.24/3.48  --schedule                              default
% 23.24/3.48  --add_important_lit                     false
% 23.24/3.48  --prop_solver_per_cl                    1000
% 23.24/3.48  --min_unsat_core                        false
% 23.24/3.48  --soft_assumptions                      false
% 23.24/3.48  --soft_lemma_size                       3
% 23.24/3.48  --prop_impl_unit_size                   0
% 23.24/3.48  --prop_impl_unit                        []
% 23.24/3.48  --share_sel_clauses                     true
% 23.24/3.48  --reset_solvers                         false
% 23.24/3.48  --bc_imp_inh                            [conj_cone]
% 23.24/3.48  --conj_cone_tolerance                   3.
% 23.24/3.48  --extra_neg_conj                        none
% 23.24/3.48  --large_theory_mode                     true
% 23.24/3.48  --prolific_symb_bound                   200
% 23.24/3.48  --lt_threshold                          2000
% 23.24/3.48  --clause_weak_htbl                      true
% 23.24/3.48  --gc_record_bc_elim                     false
% 23.24/3.48  
% 23.24/3.48  ------ Preprocessing Options
% 23.24/3.48  
% 23.24/3.48  --preprocessing_flag                    true
% 23.24/3.48  --time_out_prep_mult                    0.1
% 23.24/3.48  --splitting_mode                        input
% 23.24/3.48  --splitting_grd                         true
% 23.24/3.48  --splitting_cvd                         false
% 23.24/3.48  --splitting_cvd_svl                     false
% 23.24/3.48  --splitting_nvd                         32
% 23.24/3.48  --sub_typing                            true
% 23.24/3.48  --prep_gs_sim                           true
% 23.24/3.48  --prep_unflatten                        true
% 23.24/3.48  --prep_res_sim                          true
% 23.24/3.48  --prep_upred                            true
% 23.24/3.48  --prep_sem_filter                       exhaustive
% 23.24/3.48  --prep_sem_filter_out                   false
% 23.24/3.48  --pred_elim                             true
% 23.24/3.48  --res_sim_input                         true
% 23.24/3.48  --eq_ax_congr_red                       true
% 23.24/3.48  --pure_diseq_elim                       true
% 23.24/3.48  --brand_transform                       false
% 23.24/3.48  --non_eq_to_eq                          false
% 23.24/3.48  --prep_def_merge                        true
% 23.24/3.48  --prep_def_merge_prop_impl              false
% 23.24/3.48  --prep_def_merge_mbd                    true
% 23.24/3.48  --prep_def_merge_tr_red                 false
% 23.24/3.48  --prep_def_merge_tr_cl                  false
% 23.24/3.48  --smt_preprocessing                     true
% 23.24/3.48  --smt_ac_axioms                         fast
% 23.24/3.48  --preprocessed_out                      false
% 23.24/3.48  --preprocessed_stats                    false
% 23.24/3.48  
% 23.24/3.48  ------ Abstraction refinement Options
% 23.24/3.48  
% 23.24/3.48  --abstr_ref                             []
% 23.24/3.48  --abstr_ref_prep                        false
% 23.24/3.48  --abstr_ref_until_sat                   false
% 23.24/3.48  --abstr_ref_sig_restrict                funpre
% 23.24/3.48  --abstr_ref_af_restrict_to_split_sk     false
% 23.24/3.48  --abstr_ref_under                       []
% 23.24/3.48  
% 23.24/3.48  ------ SAT Options
% 23.24/3.48  
% 23.24/3.48  --sat_mode                              false
% 23.24/3.48  --sat_fm_restart_options                ""
% 23.24/3.48  --sat_gr_def                            false
% 23.24/3.48  --sat_epr_types                         true
% 23.24/3.48  --sat_non_cyclic_types                  false
% 23.24/3.48  --sat_finite_models                     false
% 23.24/3.48  --sat_fm_lemmas                         false
% 23.24/3.48  --sat_fm_prep                           false
% 23.24/3.48  --sat_fm_uc_incr                        true
% 23.24/3.48  --sat_out_model                         small
% 23.24/3.48  --sat_out_clauses                       false
% 23.24/3.48  
% 23.24/3.48  ------ QBF Options
% 23.24/3.48  
% 23.24/3.48  --qbf_mode                              false
% 23.24/3.48  --qbf_elim_univ                         false
% 23.24/3.48  --qbf_dom_inst                          none
% 23.24/3.48  --qbf_dom_pre_inst                      false
% 23.24/3.48  --qbf_sk_in                             false
% 23.24/3.48  --qbf_pred_elim                         true
% 23.24/3.48  --qbf_split                             512
% 23.24/3.48  
% 23.24/3.48  ------ BMC1 Options
% 23.24/3.48  
% 23.24/3.48  --bmc1_incremental                      false
% 23.24/3.48  --bmc1_axioms                           reachable_all
% 23.24/3.48  --bmc1_min_bound                        0
% 23.24/3.48  --bmc1_max_bound                        -1
% 23.24/3.48  --bmc1_max_bound_default                -1
% 23.24/3.48  --bmc1_symbol_reachability              true
% 23.24/3.48  --bmc1_property_lemmas                  false
% 23.24/3.48  --bmc1_k_induction                      false
% 23.24/3.48  --bmc1_non_equiv_states                 false
% 23.24/3.48  --bmc1_deadlock                         false
% 23.24/3.48  --bmc1_ucm                              false
% 23.24/3.48  --bmc1_add_unsat_core                   none
% 23.24/3.48  --bmc1_unsat_core_children              false
% 23.24/3.48  --bmc1_unsat_core_extrapolate_axioms    false
% 23.24/3.48  --bmc1_out_stat                         full
% 23.24/3.48  --bmc1_ground_init                      false
% 23.24/3.48  --bmc1_pre_inst_next_state              false
% 23.24/3.48  --bmc1_pre_inst_state                   false
% 23.24/3.48  --bmc1_pre_inst_reach_state             false
% 23.24/3.48  --bmc1_out_unsat_core                   false
% 23.24/3.48  --bmc1_aig_witness_out                  false
% 23.24/3.48  --bmc1_verbose                          false
% 23.24/3.48  --bmc1_dump_clauses_tptp                false
% 23.24/3.48  --bmc1_dump_unsat_core_tptp             false
% 23.24/3.48  --bmc1_dump_file                        -
% 23.24/3.48  --bmc1_ucm_expand_uc_limit              128
% 23.24/3.48  --bmc1_ucm_n_expand_iterations          6
% 23.24/3.48  --bmc1_ucm_extend_mode                  1
% 23.24/3.48  --bmc1_ucm_init_mode                    2
% 23.24/3.48  --bmc1_ucm_cone_mode                    none
% 23.24/3.48  --bmc1_ucm_reduced_relation_type        0
% 23.24/3.48  --bmc1_ucm_relax_model                  4
% 23.24/3.48  --bmc1_ucm_full_tr_after_sat            true
% 23.24/3.48  --bmc1_ucm_expand_neg_assumptions       false
% 23.24/3.48  --bmc1_ucm_layered_model                none
% 23.24/3.48  --bmc1_ucm_max_lemma_size               10
% 23.24/3.48  
% 23.24/3.48  ------ AIG Options
% 23.24/3.48  
% 23.24/3.48  --aig_mode                              false
% 23.24/3.48  
% 23.24/3.48  ------ Instantiation Options
% 23.24/3.48  
% 23.24/3.48  --instantiation_flag                    true
% 23.24/3.48  --inst_sos_flag                         true
% 23.24/3.48  --inst_sos_phase                        true
% 23.24/3.48  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 23.24/3.48  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 23.24/3.48  --inst_lit_sel_side                     none
% 23.24/3.48  --inst_solver_per_active                1400
% 23.24/3.48  --inst_solver_calls_frac                1.
% 23.24/3.48  --inst_passive_queue_type               priority_queues
% 23.24/3.48  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 23.24/3.48  --inst_passive_queues_freq              [25;2]
% 23.24/3.48  --inst_dismatching                      true
% 23.24/3.48  --inst_eager_unprocessed_to_passive     true
% 23.24/3.48  --inst_prop_sim_given                   true
% 23.24/3.48  --inst_prop_sim_new                     false
% 23.24/3.48  --inst_subs_new                         false
% 23.24/3.48  --inst_eq_res_simp                      false
% 23.24/3.48  --inst_subs_given                       false
% 23.24/3.48  --inst_orphan_elimination               true
% 23.24/3.48  --inst_learning_loop_flag               true
% 23.24/3.48  --inst_learning_start                   3000
% 23.24/3.48  --inst_learning_factor                  2
% 23.24/3.48  --inst_start_prop_sim_after_learn       3
% 23.24/3.48  --inst_sel_renew                        solver
% 23.24/3.48  --inst_lit_activity_flag                true
% 23.24/3.48  --inst_restr_to_given                   false
% 23.24/3.48  --inst_activity_threshold               500
% 23.24/3.48  --inst_out_proof                        true
% 23.24/3.48  
% 23.24/3.48  ------ Resolution Options
% 23.24/3.48  
% 23.24/3.48  --resolution_flag                       false
% 23.24/3.48  --res_lit_sel                           adaptive
% 23.24/3.48  --res_lit_sel_side                      none
% 23.24/3.48  --res_ordering                          kbo
% 23.24/3.48  --res_to_prop_solver                    active
% 23.24/3.48  --res_prop_simpl_new                    false
% 23.24/3.48  --res_prop_simpl_given                  true
% 23.24/3.48  --res_passive_queue_type                priority_queues
% 23.24/3.48  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 23.24/3.48  --res_passive_queues_freq               [15;5]
% 23.24/3.48  --res_forward_subs                      full
% 23.24/3.48  --res_backward_subs                     full
% 23.24/3.48  --res_forward_subs_resolution           true
% 23.24/3.48  --res_backward_subs_resolution          true
% 23.24/3.48  --res_orphan_elimination                true
% 23.24/3.48  --res_time_limit                        2.
% 23.24/3.48  --res_out_proof                         true
% 23.24/3.48  
% 23.24/3.48  ------ Superposition Options
% 23.24/3.48  
% 23.24/3.48  --superposition_flag                    true
% 23.24/3.48  --sup_passive_queue_type                priority_queues
% 23.24/3.48  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 23.24/3.48  --sup_passive_queues_freq               [8;1;4]
% 23.24/3.48  --demod_completeness_check              fast
% 23.24/3.48  --demod_use_ground                      true
% 23.24/3.48  --sup_to_prop_solver                    passive
% 23.24/3.48  --sup_prop_simpl_new                    true
% 23.24/3.48  --sup_prop_simpl_given                  true
% 23.24/3.48  --sup_fun_splitting                     true
% 23.24/3.48  --sup_smt_interval                      50000
% 23.24/3.48  
% 23.24/3.48  ------ Superposition Simplification Setup
% 23.24/3.48  
% 23.24/3.48  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 23.24/3.48  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 23.24/3.48  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 23.24/3.48  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 23.24/3.48  --sup_full_triv                         [TrivRules;PropSubs]
% 23.24/3.48  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 23.24/3.48  --sup_full_bw                           [BwDemod;BwSubsumption]
% 23.24/3.48  --sup_immed_triv                        [TrivRules]
% 23.24/3.48  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 23.24/3.48  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 23.24/3.48  --sup_immed_bw_main                     []
% 23.24/3.48  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 23.24/3.48  --sup_input_triv                        [Unflattening;TrivRules]
% 23.24/3.48  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 23.24/3.48  --sup_input_bw                          []
% 23.24/3.48  
% 23.24/3.48  ------ Combination Options
% 23.24/3.48  
% 23.24/3.48  --comb_res_mult                         3
% 23.24/3.48  --comb_sup_mult                         2
% 23.24/3.48  --comb_inst_mult                        10
% 23.24/3.48  
% 23.24/3.48  ------ Debug Options
% 23.24/3.48  
% 23.24/3.48  --dbg_backtrace                         false
% 23.24/3.48  --dbg_dump_prop_clauses                 false
% 23.24/3.48  --dbg_dump_prop_clauses_file            -
% 23.24/3.48  --dbg_out_stat                          false
% 23.24/3.48  
% 23.24/3.48  
% 23.24/3.48  
% 23.24/3.48  
% 23.24/3.48  ------ Proving...
% 23.24/3.48  
% 23.24/3.48  
% 23.24/3.48  % SZS status Theorem for theBenchmark.p
% 23.24/3.48  
% 23.24/3.48  % SZS output start CNFRefutation for theBenchmark.p
% 23.24/3.48  
% 23.24/3.48  fof(f19,conjecture,(
% 23.24/3.48    ! [X0,X1,X2,X3] : ~(! [X4,X5] : ~(k4_tarski(X4,X5) = X3 & r2_hidden(X5,X2) & r2_hidden(X4,X1)) & r2_hidden(X3,X0) & r1_tarski(X0,k2_zfmisc_1(X1,X2)))),
% 23.24/3.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 23.24/3.48  
% 23.24/3.48  fof(f20,negated_conjecture,(
% 23.24/3.48    ~! [X0,X1,X2,X3] : ~(! [X4,X5] : ~(k4_tarski(X4,X5) = X3 & r2_hidden(X5,X2) & r2_hidden(X4,X1)) & r2_hidden(X3,X0) & r1_tarski(X0,k2_zfmisc_1(X1,X2)))),
% 23.24/3.48    inference(negated_conjecture,[],[f19])).
% 23.24/3.48  
% 23.24/3.48  fof(f27,plain,(
% 23.24/3.48    ? [X0,X1,X2,X3] : (! [X4,X5] : (k4_tarski(X4,X5) != X3 | ~r2_hidden(X5,X2) | ~r2_hidden(X4,X1)) & r2_hidden(X3,X0) & r1_tarski(X0,k2_zfmisc_1(X1,X2)))),
% 23.24/3.48    inference(ennf_transformation,[],[f20])).
% 23.24/3.48  
% 23.24/3.48  fof(f50,plain,(
% 23.24/3.48    ? [X0,X1,X2,X3] : (! [X4,X5] : (k4_tarski(X4,X5) != X3 | ~r2_hidden(X5,X2) | ~r2_hidden(X4,X1)) & r2_hidden(X3,X0) & r1_tarski(X0,k2_zfmisc_1(X1,X2))) => (! [X5,X4] : (k4_tarski(X4,X5) != sK11 | ~r2_hidden(X5,sK10) | ~r2_hidden(X4,sK9)) & r2_hidden(sK11,sK8) & r1_tarski(sK8,k2_zfmisc_1(sK9,sK10)))),
% 23.24/3.48    introduced(choice_axiom,[])).
% 23.24/3.48  
% 23.24/3.48  fof(f51,plain,(
% 23.24/3.48    ! [X4,X5] : (k4_tarski(X4,X5) != sK11 | ~r2_hidden(X5,sK10) | ~r2_hidden(X4,sK9)) & r2_hidden(sK11,sK8) & r1_tarski(sK8,k2_zfmisc_1(sK9,sK10))),
% 23.24/3.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8,sK9,sK10,sK11])],[f27,f50])).
% 23.24/3.48  
% 23.24/3.48  fof(f91,plain,(
% 23.24/3.48    r1_tarski(sK8,k2_zfmisc_1(sK9,sK10))),
% 23.24/3.48    inference(cnf_transformation,[],[f51])).
% 23.24/3.48  
% 23.24/3.48  fof(f18,axiom,(
% 23.24/3.48    ! [X0,X1] : (k4_xboole_0(X0,k1_tarski(X1)) = X0 <=> ~r2_hidden(X1,X0))),
% 23.24/3.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 23.24/3.48  
% 23.24/3.48  fof(f49,plain,(
% 23.24/3.48    ! [X0,X1] : ((k4_xboole_0(X0,k1_tarski(X1)) = X0 | r2_hidden(X1,X0)) & (~r2_hidden(X1,X0) | k4_xboole_0(X0,k1_tarski(X1)) != X0))),
% 23.24/3.48    inference(nnf_transformation,[],[f18])).
% 23.24/3.48  
% 23.24/3.48  fof(f90,plain,(
% 23.24/3.48    ( ! [X0,X1] : (k4_xboole_0(X0,k1_tarski(X1)) = X0 | r2_hidden(X1,X0)) )),
% 23.24/3.48    inference(cnf_transformation,[],[f49])).
% 23.24/3.48  
% 23.24/3.48  fof(f15,axiom,(
% 23.24/3.48    ! [X0,X1,X2] : (k2_zfmisc_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4,X5] : (k4_tarski(X4,X5) = X3 & r2_hidden(X5,X1) & r2_hidden(X4,X0))))),
% 23.24/3.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 23.24/3.48  
% 23.24/3.48  fof(f42,plain,(
% 23.24/3.48    ! [X0,X1,X2] : ((k2_zfmisc_1(X0,X1) = X2 | ? [X3] : ((! [X4,X5] : (k4_tarski(X4,X5) != X3 | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X0)) | ~r2_hidden(X3,X2)) & (? [X4,X5] : (k4_tarski(X4,X5) = X3 & r2_hidden(X5,X1) & r2_hidden(X4,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ! [X4,X5] : (k4_tarski(X4,X5) != X3 | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X0))) & (? [X4,X5] : (k4_tarski(X4,X5) = X3 & r2_hidden(X5,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X3,X2))) | k2_zfmisc_1(X0,X1) != X2))),
% 23.24/3.48    inference(nnf_transformation,[],[f15])).
% 23.24/3.48  
% 23.24/3.48  fof(f43,plain,(
% 23.24/3.48    ! [X0,X1,X2] : ((k2_zfmisc_1(X0,X1) = X2 | ? [X3] : ((! [X4,X5] : (k4_tarski(X4,X5) != X3 | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X0)) | ~r2_hidden(X3,X2)) & (? [X6,X7] : (k4_tarski(X6,X7) = X3 & r2_hidden(X7,X1) & r2_hidden(X6,X0)) | r2_hidden(X3,X2)))) & (! [X8] : ((r2_hidden(X8,X2) | ! [X9,X10] : (k4_tarski(X9,X10) != X8 | ~r2_hidden(X10,X1) | ~r2_hidden(X9,X0))) & (? [X11,X12] : (k4_tarski(X11,X12) = X8 & r2_hidden(X12,X1) & r2_hidden(X11,X0)) | ~r2_hidden(X8,X2))) | k2_zfmisc_1(X0,X1) != X2))),
% 23.24/3.48    inference(rectify,[],[f42])).
% 23.24/3.48  
% 23.24/3.48  fof(f46,plain,(
% 23.24/3.48    ! [X8,X1,X0] : (? [X11,X12] : (k4_tarski(X11,X12) = X8 & r2_hidden(X12,X1) & r2_hidden(X11,X0)) => (k4_tarski(sK6(X0,X1,X8),sK7(X0,X1,X8)) = X8 & r2_hidden(sK7(X0,X1,X8),X1) & r2_hidden(sK6(X0,X1,X8),X0)))),
% 23.24/3.48    introduced(choice_axiom,[])).
% 23.24/3.48  
% 23.24/3.48  fof(f45,plain,(
% 23.24/3.48    ( ! [X3] : (! [X2,X1,X0] : (? [X6,X7] : (k4_tarski(X6,X7) = X3 & r2_hidden(X7,X1) & r2_hidden(X6,X0)) => (k4_tarski(sK4(X0,X1,X2),sK5(X0,X1,X2)) = X3 & r2_hidden(sK5(X0,X1,X2),X1) & r2_hidden(sK4(X0,X1,X2),X0)))) )),
% 23.24/3.48    introduced(choice_axiom,[])).
% 23.24/3.48  
% 23.24/3.48  fof(f44,plain,(
% 23.24/3.48    ! [X2,X1,X0] : (? [X3] : ((! [X4,X5] : (k4_tarski(X4,X5) != X3 | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X0)) | ~r2_hidden(X3,X2)) & (? [X6,X7] : (k4_tarski(X6,X7) = X3 & r2_hidden(X7,X1) & r2_hidden(X6,X0)) | r2_hidden(X3,X2))) => ((! [X5,X4] : (k4_tarski(X4,X5) != sK3(X0,X1,X2) | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X0)) | ~r2_hidden(sK3(X0,X1,X2),X2)) & (? [X7,X6] : (k4_tarski(X6,X7) = sK3(X0,X1,X2) & r2_hidden(X7,X1) & r2_hidden(X6,X0)) | r2_hidden(sK3(X0,X1,X2),X2))))),
% 23.24/3.48    introduced(choice_axiom,[])).
% 23.24/3.48  
% 23.24/3.48  fof(f47,plain,(
% 23.24/3.48    ! [X0,X1,X2] : ((k2_zfmisc_1(X0,X1) = X2 | ((! [X4,X5] : (k4_tarski(X4,X5) != sK3(X0,X1,X2) | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X0)) | ~r2_hidden(sK3(X0,X1,X2),X2)) & ((k4_tarski(sK4(X0,X1,X2),sK5(X0,X1,X2)) = sK3(X0,X1,X2) & r2_hidden(sK5(X0,X1,X2),X1) & r2_hidden(sK4(X0,X1,X2),X0)) | r2_hidden(sK3(X0,X1,X2),X2)))) & (! [X8] : ((r2_hidden(X8,X2) | ! [X9,X10] : (k4_tarski(X9,X10) != X8 | ~r2_hidden(X10,X1) | ~r2_hidden(X9,X0))) & ((k4_tarski(sK6(X0,X1,X8),sK7(X0,X1,X8)) = X8 & r2_hidden(sK7(X0,X1,X8),X1) & r2_hidden(sK6(X0,X1,X8),X0)) | ~r2_hidden(X8,X2))) | k2_zfmisc_1(X0,X1) != X2))),
% 23.24/3.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5,sK6,sK7])],[f43,f46,f45,f44])).
% 23.24/3.48  
% 23.24/3.48  fof(f78,plain,(
% 23.24/3.48    ( ! [X2,X0,X8,X1] : (r2_hidden(sK6(X0,X1,X8),X0) | ~r2_hidden(X8,X2) | k2_zfmisc_1(X0,X1) != X2) )),
% 23.24/3.48    inference(cnf_transformation,[],[f47])).
% 23.24/3.48  
% 23.24/3.48  fof(f116,plain,(
% 23.24/3.48    ( ! [X0,X8,X1] : (r2_hidden(sK6(X0,X1,X8),X0) | ~r2_hidden(X8,k2_zfmisc_1(X0,X1))) )),
% 23.24/3.48    inference(equality_resolution,[],[f78])).
% 23.24/3.48  
% 23.24/3.48  fof(f79,plain,(
% 23.24/3.48    ( ! [X2,X0,X8,X1] : (r2_hidden(sK7(X0,X1,X8),X1) | ~r2_hidden(X8,X2) | k2_zfmisc_1(X0,X1) != X2) )),
% 23.24/3.48    inference(cnf_transformation,[],[f47])).
% 23.24/3.48  
% 23.24/3.48  fof(f115,plain,(
% 23.24/3.48    ( ! [X0,X8,X1] : (r2_hidden(sK7(X0,X1,X8),X1) | ~r2_hidden(X8,k2_zfmisc_1(X0,X1))) )),
% 23.24/3.48    inference(equality_resolution,[],[f79])).
% 23.24/3.48  
% 23.24/3.48  fof(f80,plain,(
% 23.24/3.48    ( ! [X2,X0,X8,X1] : (k4_tarski(sK6(X0,X1,X8),sK7(X0,X1,X8)) = X8 | ~r2_hidden(X8,X2) | k2_zfmisc_1(X0,X1) != X2) )),
% 23.24/3.48    inference(cnf_transformation,[],[f47])).
% 23.24/3.48  
% 23.24/3.48  fof(f114,plain,(
% 23.24/3.48    ( ! [X0,X8,X1] : (k4_tarski(sK6(X0,X1,X8),sK7(X0,X1,X8)) = X8 | ~r2_hidden(X8,k2_zfmisc_1(X0,X1))) )),
% 23.24/3.48    inference(equality_resolution,[],[f80])).
% 23.24/3.48  
% 23.24/3.48  fof(f93,plain,(
% 23.24/3.48    ( ! [X4,X5] : (k4_tarski(X4,X5) != sK11 | ~r2_hidden(X5,sK10) | ~r2_hidden(X4,sK9)) )),
% 23.24/3.48    inference(cnf_transformation,[],[f51])).
% 23.24/3.48  
% 23.24/3.48  fof(f6,axiom,(
% 23.24/3.48    ! [X0,X1,X2] : (r1_tarski(X0,k4_xboole_0(X1,X2)) => (r1_xboole_0(X0,X2) & r1_tarski(X0,X1)))),
% 23.24/3.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 23.24/3.48  
% 23.24/3.48  fof(f22,plain,(
% 23.24/3.48    ! [X0,X1,X2] : ((r1_xboole_0(X0,X2) & r1_tarski(X0,X1)) | ~r1_tarski(X0,k4_xboole_0(X1,X2)))),
% 23.24/3.48    inference(ennf_transformation,[],[f6])).
% 23.24/3.48  
% 23.24/3.48  fof(f69,plain,(
% 23.24/3.48    ( ! [X2,X0,X1] : (r1_xboole_0(X0,X2) | ~r1_tarski(X0,k4_xboole_0(X1,X2))) )),
% 23.24/3.48    inference(cnf_transformation,[],[f22])).
% 23.24/3.48  
% 23.24/3.48  fof(f10,axiom,(
% 23.24/3.48    ! [X0,X1,X2] : ((r1_xboole_0(X1,X2) & r1_tarski(X0,X1)) => r1_xboole_0(X0,X2))),
% 23.24/3.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 23.24/3.48  
% 23.24/3.48  fof(f23,plain,(
% 23.24/3.48    ! [X0,X1,X2] : (r1_xboole_0(X0,X2) | (~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X1)))),
% 23.24/3.48    inference(ennf_transformation,[],[f10])).
% 23.24/3.48  
% 23.24/3.48  fof(f24,plain,(
% 23.24/3.48    ! [X0,X1,X2] : (r1_xboole_0(X0,X2) | ~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X1))),
% 23.24/3.48    inference(flattening,[],[f23])).
% 23.24/3.48  
% 23.24/3.48  fof(f73,plain,(
% 23.24/3.48    ( ! [X2,X0,X1] : (r1_xboole_0(X0,X2) | ~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X1)) )),
% 23.24/3.48    inference(cnf_transformation,[],[f24])).
% 23.24/3.48  
% 23.24/3.48  fof(f13,axiom,(
% 23.24/3.48    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 23.24/3.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 23.24/3.48  
% 23.24/3.48  fof(f76,plain,(
% 23.24/3.48    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 23.24/3.48    inference(cnf_transformation,[],[f13])).
% 23.24/3.48  
% 23.24/3.48  fof(f14,axiom,(
% 23.24/3.48    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 23.24/3.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 23.24/3.48  
% 23.24/3.48  fof(f77,plain,(
% 23.24/3.48    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 23.24/3.48    inference(cnf_transformation,[],[f14])).
% 23.24/3.48  
% 23.24/3.48  fof(f103,plain,(
% 23.24/3.48    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k1_enumset1(X1,X1,X0)) )),
% 23.24/3.48    inference(definition_unfolding,[],[f76,f77,f77])).
% 23.24/3.48  
% 23.24/3.48  fof(f12,axiom,(
% 23.24/3.48    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 23.24/3.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 23.24/3.48  
% 23.24/3.48  fof(f75,plain,(
% 23.24/3.48    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 23.24/3.48    inference(cnf_transformation,[],[f12])).
% 23.24/3.48  
% 23.24/3.48  fof(f17,axiom,(
% 23.24/3.48    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 23.24/3.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 23.24/3.48  
% 23.24/3.48  fof(f88,plain,(
% 23.24/3.48    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 23.24/3.48    inference(cnf_transformation,[],[f17])).
% 23.24/3.48  
% 23.24/3.48  fof(f94,plain,(
% 23.24/3.48    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k1_enumset1(X0,X0,X1))) )),
% 23.24/3.48    inference(definition_unfolding,[],[f88,f77])).
% 23.24/3.48  
% 23.24/3.48  fof(f102,plain,(
% 23.24/3.48    ( ! [X0,X1] : (r1_tarski(X0,k3_tarski(k1_enumset1(X0,X0,X1)))) )),
% 23.24/3.48    inference(definition_unfolding,[],[f75,f94])).
% 23.24/3.48  
% 23.24/3.48  fof(f11,axiom,(
% 23.24/3.48    ! [X0,X1,X2] : ((r1_xboole_0(X0,X2) & r1_tarski(X0,k2_xboole_0(X1,X2))) => r1_tarski(X0,X1))),
% 23.24/3.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 23.24/3.48  
% 23.24/3.48  fof(f25,plain,(
% 23.24/3.48    ! [X0,X1,X2] : (r1_tarski(X0,X1) | (~r1_xboole_0(X0,X2) | ~r1_tarski(X0,k2_xboole_0(X1,X2))))),
% 23.24/3.48    inference(ennf_transformation,[],[f11])).
% 23.24/3.48  
% 23.24/3.48  fof(f26,plain,(
% 23.24/3.48    ! [X0,X1,X2] : (r1_tarski(X0,X1) | ~r1_xboole_0(X0,X2) | ~r1_tarski(X0,k2_xboole_0(X1,X2)))),
% 23.24/3.48    inference(flattening,[],[f25])).
% 23.24/3.48  
% 23.24/3.48  fof(f74,plain,(
% 23.24/3.48    ( ! [X2,X0,X1] : (r1_tarski(X0,X1) | ~r1_xboole_0(X0,X2) | ~r1_tarski(X0,k2_xboole_0(X1,X2))) )),
% 23.24/3.48    inference(cnf_transformation,[],[f26])).
% 23.24/3.48  
% 23.24/3.48  fof(f101,plain,(
% 23.24/3.48    ( ! [X2,X0,X1] : (r1_tarski(X0,X1) | ~r1_xboole_0(X0,X2) | ~r1_tarski(X0,k3_tarski(k1_enumset1(X1,X1,X2)))) )),
% 23.24/3.48    inference(definition_unfolding,[],[f74,f94])).
% 23.24/3.48  
% 23.24/3.48  fof(f16,axiom,(
% 23.24/3.48    ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) <=> r2_hidden(X0,X1))),
% 23.24/3.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 23.24/3.48  
% 23.24/3.48  fof(f48,plain,(
% 23.24/3.48    ! [X0,X1] : ((r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) & (r2_hidden(X0,X1) | ~r1_tarski(k1_tarski(X0),X1)))),
% 23.24/3.48    inference(nnf_transformation,[],[f16])).
% 23.24/3.48  
% 23.24/3.48  fof(f86,plain,(
% 23.24/3.48    ( ! [X0,X1] : (r2_hidden(X0,X1) | ~r1_tarski(k1_tarski(X0),X1)) )),
% 23.24/3.48    inference(cnf_transformation,[],[f48])).
% 23.24/3.48  
% 23.24/3.48  fof(f3,axiom,(
% 23.24/3.48    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 23.24/3.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 23.24/3.48  
% 23.24/3.48  fof(f33,plain,(
% 23.24/3.48    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : (((r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 23.24/3.48    inference(nnf_transformation,[],[f3])).
% 23.24/3.48  
% 23.24/3.48  fof(f34,plain,(
% 23.24/3.48    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 23.24/3.48    inference(flattening,[],[f33])).
% 23.24/3.48  
% 23.24/3.48  fof(f35,plain,(
% 23.24/3.48    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 23.24/3.48    inference(rectify,[],[f34])).
% 23.24/3.48  
% 23.24/3.48  fof(f36,plain,(
% 23.24/3.48    ! [X2,X1,X0] : (? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((r2_hidden(sK1(X0,X1,X2),X1) | ~r2_hidden(sK1(X0,X1,X2),X0) | ~r2_hidden(sK1(X0,X1,X2),X2)) & ((~r2_hidden(sK1(X0,X1,X2),X1) & r2_hidden(sK1(X0,X1,X2),X0)) | r2_hidden(sK1(X0,X1,X2),X2))))),
% 23.24/3.48    introduced(choice_axiom,[])).
% 23.24/3.48  
% 23.24/3.48  fof(f37,plain,(
% 23.24/3.48    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ((r2_hidden(sK1(X0,X1,X2),X1) | ~r2_hidden(sK1(X0,X1,X2),X0) | ~r2_hidden(sK1(X0,X1,X2),X2)) & ((~r2_hidden(sK1(X0,X1,X2),X1) & r2_hidden(sK1(X0,X1,X2),X0)) | r2_hidden(sK1(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 23.24/3.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f35,f36])).
% 23.24/3.48  
% 23.24/3.48  fof(f59,plain,(
% 23.24/3.48    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 23.24/3.48    inference(cnf_transformation,[],[f37])).
% 23.24/3.48  
% 23.24/3.48  fof(f108,plain,(
% 23.24/3.48    ( ! [X4,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,k4_xboole_0(X0,X1))) )),
% 23.24/3.48    inference(equality_resolution,[],[f59])).
% 23.24/3.48  
% 23.24/3.48  fof(f87,plain,(
% 23.24/3.48    ( ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) )),
% 23.24/3.48    inference(cnf_transformation,[],[f48])).
% 23.24/3.48  
% 23.24/3.48  fof(f8,axiom,(
% 23.24/3.48    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 23.24/3.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 23.24/3.48  
% 23.24/3.48  fof(f71,plain,(
% 23.24/3.48    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 23.24/3.48    inference(cnf_transformation,[],[f8])).
% 23.24/3.48  
% 23.24/3.48  fof(f92,plain,(
% 23.24/3.48    r2_hidden(sK11,sK8)),
% 23.24/3.48    inference(cnf_transformation,[],[f51])).
% 23.24/3.48  
% 23.24/3.48  cnf(c_38,negated_conjecture,
% 23.24/3.48      ( r1_tarski(sK8,k2_zfmisc_1(sK9,sK10)) ),
% 23.24/3.48      inference(cnf_transformation,[],[f91]) ).
% 23.24/3.48  
% 23.24/3.48  cnf(c_1524,plain,
% 23.24/3.48      ( r1_tarski(sK8,k2_zfmisc_1(sK9,sK10)) = iProver_top ),
% 23.24/3.48      inference(predicate_to_equality,[status(thm)],[c_38]) ).
% 23.24/3.48  
% 23.24/3.48  cnf(c_34,plain,
% 23.24/3.48      ( r2_hidden(X0,X1) | k4_xboole_0(X1,k1_tarski(X0)) = X1 ),
% 23.24/3.48      inference(cnf_transformation,[],[f90]) ).
% 23.24/3.48  
% 23.24/3.48  cnf(c_1528,plain,
% 23.24/3.48      ( k4_xboole_0(X0,k1_tarski(X1)) = X0
% 23.24/3.48      | r2_hidden(X1,X0) = iProver_top ),
% 23.24/3.48      inference(predicate_to_equality,[status(thm)],[c_34]) ).
% 23.24/3.48  
% 23.24/3.48  cnf(c_31,plain,
% 23.24/3.48      ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
% 23.24/3.48      | r2_hidden(sK6(X1,X2,X0),X1) ),
% 23.24/3.48      inference(cnf_transformation,[],[f116]) ).
% 23.24/3.48  
% 23.24/3.48  cnf(c_1531,plain,
% 23.24/3.48      ( r2_hidden(X0,k2_zfmisc_1(X1,X2)) != iProver_top
% 23.24/3.48      | r2_hidden(sK6(X1,X2,X0),X1) = iProver_top ),
% 23.24/3.48      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 23.24/3.48  
% 23.24/3.48  cnf(c_30,plain,
% 23.24/3.48      ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
% 23.24/3.48      | r2_hidden(sK7(X1,X2,X0),X2) ),
% 23.24/3.48      inference(cnf_transformation,[],[f115]) ).
% 23.24/3.48  
% 23.24/3.48  cnf(c_1532,plain,
% 23.24/3.48      ( r2_hidden(X0,k2_zfmisc_1(X1,X2)) != iProver_top
% 23.24/3.48      | r2_hidden(sK7(X1,X2,X0),X2) = iProver_top ),
% 23.24/3.48      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 23.24/3.48  
% 23.24/3.48  cnf(c_29,plain,
% 23.24/3.48      ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
% 23.24/3.48      | k4_tarski(sK6(X1,X2,X0),sK7(X1,X2,X0)) = X0 ),
% 23.24/3.48      inference(cnf_transformation,[],[f114]) ).
% 23.24/3.48  
% 23.24/3.48  cnf(c_1533,plain,
% 23.24/3.48      ( k4_tarski(sK6(X0,X1,X2),sK7(X0,X1,X2)) = X2
% 23.24/3.48      | r2_hidden(X2,k2_zfmisc_1(X0,X1)) != iProver_top ),
% 23.24/3.48      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 23.24/3.48  
% 23.24/3.48  cnf(c_7485,plain,
% 23.24/3.48      ( k4_tarski(sK6(X0,X1,X2),sK7(X0,X1,X2)) = X2
% 23.24/3.48      | k4_xboole_0(k2_zfmisc_1(X0,X1),k1_tarski(X2)) = k2_zfmisc_1(X0,X1) ),
% 23.24/3.48      inference(superposition,[status(thm)],[c_1528,c_1533]) ).
% 23.24/3.48  
% 23.24/3.48  cnf(c_36,negated_conjecture,
% 23.24/3.48      ( ~ r2_hidden(X0,sK9)
% 23.24/3.48      | ~ r2_hidden(X1,sK10)
% 23.24/3.48      | k4_tarski(X0,X1) != sK11 ),
% 23.24/3.48      inference(cnf_transformation,[],[f93]) ).
% 23.24/3.48  
% 23.24/3.48  cnf(c_1526,plain,
% 23.24/3.48      ( k4_tarski(X0,X1) != sK11
% 23.24/3.48      | r2_hidden(X0,sK9) != iProver_top
% 23.24/3.48      | r2_hidden(X1,sK10) != iProver_top ),
% 23.24/3.48      inference(predicate_to_equality,[status(thm)],[c_36]) ).
% 23.24/3.48  
% 23.24/3.48  cnf(c_65246,plain,
% 23.24/3.48      ( k4_xboole_0(k2_zfmisc_1(X0,X1),k1_tarski(X2)) = k2_zfmisc_1(X0,X1)
% 23.24/3.48      | sK11 != X2
% 23.24/3.48      | r2_hidden(sK7(X0,X1,X2),sK10) != iProver_top
% 23.24/3.48      | r2_hidden(sK6(X0,X1,X2),sK9) != iProver_top ),
% 23.24/3.48      inference(superposition,[status(thm)],[c_7485,c_1526]) ).
% 23.24/3.48  
% 23.24/3.48  cnf(c_69728,plain,
% 23.24/3.48      ( k4_xboole_0(k2_zfmisc_1(X0,X1),k1_tarski(sK11)) = k2_zfmisc_1(X0,X1)
% 23.24/3.48      | r2_hidden(sK7(X0,X1,sK11),sK10) != iProver_top
% 23.24/3.48      | r2_hidden(sK6(X0,X1,sK11),sK9) != iProver_top ),
% 23.24/3.48      inference(equality_resolution,[status(thm)],[c_65246]) ).
% 23.24/3.48  
% 23.24/3.48  cnf(c_69734,plain,
% 23.24/3.48      ( k4_xboole_0(k2_zfmisc_1(X0,sK10),k1_tarski(sK11)) = k2_zfmisc_1(X0,sK10)
% 23.24/3.48      | r2_hidden(sK6(X0,sK10,sK11),sK9) != iProver_top
% 23.24/3.48      | r2_hidden(sK11,k2_zfmisc_1(X0,sK10)) != iProver_top ),
% 23.24/3.48      inference(superposition,[status(thm)],[c_1532,c_69728]) ).
% 23.24/3.48  
% 23.24/3.48  cnf(c_70075,plain,
% 23.24/3.48      ( k4_xboole_0(k2_zfmisc_1(sK9,sK10),k1_tarski(sK11)) = k2_zfmisc_1(sK9,sK10)
% 23.24/3.48      | r2_hidden(sK11,k2_zfmisc_1(sK9,sK10)) != iProver_top ),
% 23.24/3.48      inference(superposition,[status(thm)],[c_1531,c_69734]) ).
% 23.24/3.48  
% 23.24/3.48  cnf(c_96175,plain,
% 23.24/3.48      ( k4_xboole_0(k2_zfmisc_1(sK9,sK10),k1_tarski(sK11)) = k2_zfmisc_1(sK9,sK10) ),
% 23.24/3.48      inference(superposition,[status(thm)],[c_1528,c_70075]) ).
% 23.24/3.48  
% 23.24/3.48  cnf(c_16,plain,
% 23.24/3.48      ( r1_xboole_0(X0,X1) | ~ r1_tarski(X0,k4_xboole_0(X2,X1)) ),
% 23.24/3.48      inference(cnf_transformation,[],[f69]) ).
% 23.24/3.48  
% 23.24/3.48  cnf(c_1544,plain,
% 23.24/3.48      ( r1_xboole_0(X0,X1) = iProver_top
% 23.24/3.48      | r1_tarski(X0,k4_xboole_0(X2,X1)) != iProver_top ),
% 23.24/3.48      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 23.24/3.48  
% 23.24/3.48  cnf(c_100372,plain,
% 23.24/3.48      ( r1_xboole_0(X0,k1_tarski(sK11)) = iProver_top
% 23.24/3.48      | r1_tarski(X0,k2_zfmisc_1(sK9,sK10)) != iProver_top ),
% 23.24/3.48      inference(superposition,[status(thm)],[c_96175,c_1544]) ).
% 23.24/3.48  
% 23.24/3.48  cnf(c_102763,plain,
% 23.24/3.48      ( r1_xboole_0(sK8,k1_tarski(sK11)) = iProver_top ),
% 23.24/3.48      inference(superposition,[status(thm)],[c_1524,c_100372]) ).
% 23.24/3.48  
% 23.24/3.48  cnf(c_20,plain,
% 23.24/3.48      ( ~ r1_xboole_0(X0,X1) | r1_xboole_0(X2,X1) | ~ r1_tarski(X2,X0) ),
% 23.24/3.48      inference(cnf_transformation,[],[f73]) ).
% 23.24/3.48  
% 23.24/3.48  cnf(c_1541,plain,
% 23.24/3.48      ( r1_xboole_0(X0,X1) != iProver_top
% 23.24/3.48      | r1_xboole_0(X2,X1) = iProver_top
% 23.24/3.48      | r1_tarski(X2,X0) != iProver_top ),
% 23.24/3.48      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 23.24/3.48  
% 23.24/3.48  cnf(c_103287,plain,
% 23.24/3.48      ( r1_xboole_0(X0,k1_tarski(sK11)) = iProver_top
% 23.24/3.48      | r1_tarski(X0,sK8) != iProver_top ),
% 23.24/3.48      inference(superposition,[status(thm)],[c_102763,c_1541]) ).
% 23.24/3.48  
% 23.24/3.48  cnf(c_23,plain,
% 23.24/3.48      ( k1_enumset1(X0,X0,X1) = k1_enumset1(X1,X1,X0) ),
% 23.24/3.48      inference(cnf_transformation,[],[f103]) ).
% 23.24/3.48  
% 23.24/3.48  cnf(c_22,plain,
% 23.24/3.48      ( r1_tarski(X0,k3_tarski(k1_enumset1(X0,X0,X1))) ),
% 23.24/3.48      inference(cnf_transformation,[],[f102]) ).
% 23.24/3.48  
% 23.24/3.48  cnf(c_1539,plain,
% 23.24/3.48      ( r1_tarski(X0,k3_tarski(k1_enumset1(X0,X0,X1))) = iProver_top ),
% 23.24/3.48      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 23.24/3.48  
% 23.24/3.48  cnf(c_2283,plain,
% 23.24/3.48      ( r1_tarski(X0,k3_tarski(k1_enumset1(X1,X1,X0))) = iProver_top ),
% 23.24/3.48      inference(superposition,[status(thm)],[c_23,c_1539]) ).
% 23.24/3.48  
% 23.24/3.48  cnf(c_21,plain,
% 23.24/3.48      ( ~ r1_xboole_0(X0,X1)
% 23.24/3.48      | r1_tarski(X0,X2)
% 23.24/3.48      | ~ r1_tarski(X0,k3_tarski(k1_enumset1(X2,X2,X1))) ),
% 23.24/3.48      inference(cnf_transformation,[],[f101]) ).
% 23.24/3.48  
% 23.24/3.48  cnf(c_1540,plain,
% 23.24/3.48      ( r1_xboole_0(X0,X1) != iProver_top
% 23.24/3.48      | r1_tarski(X0,X2) = iProver_top
% 23.24/3.48      | r1_tarski(X0,k3_tarski(k1_enumset1(X2,X2,X1))) != iProver_top ),
% 23.24/3.48      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 23.24/3.48  
% 23.24/3.48  cnf(c_9599,plain,
% 23.24/3.48      ( r1_xboole_0(X0,X0) != iProver_top
% 23.24/3.48      | r1_tarski(X0,X1) = iProver_top ),
% 23.24/3.48      inference(superposition,[status(thm)],[c_2283,c_1540]) ).
% 23.24/3.48  
% 23.24/3.48  cnf(c_103293,plain,
% 23.24/3.48      ( r1_tarski(k1_tarski(sK11),X0) = iProver_top
% 23.24/3.48      | r1_tarski(k1_tarski(sK11),sK8) != iProver_top ),
% 23.24/3.48      inference(superposition,[status(thm)],[c_103287,c_9599]) ).
% 23.24/3.48  
% 23.24/3.48  cnf(c_103296,plain,
% 23.24/3.48      ( r1_tarski(k1_tarski(sK11),sK8) != iProver_top
% 23.24/3.48      | r1_tarski(k1_tarski(sK11),k1_xboole_0) = iProver_top ),
% 23.24/3.48      inference(instantiation,[status(thm)],[c_103293]) ).
% 23.24/3.48  
% 23.24/3.48  cnf(c_805,plain,
% 23.24/3.48      ( ~ r2_hidden(X0,X1) | r2_hidden(X2,X3) | X2 != X0 | X3 != X1 ),
% 23.24/3.48      theory(equality) ).
% 23.24/3.48  
% 23.24/3.48  cnf(c_5485,plain,
% 23.24/3.48      ( r2_hidden(X0,X1) | ~ r2_hidden(sK11,X2) | X1 != X2 | X0 != sK11 ),
% 23.24/3.48      inference(instantiation,[status(thm)],[c_805]) ).
% 23.24/3.48  
% 23.24/3.48  cnf(c_10309,plain,
% 23.24/3.48      ( ~ r2_hidden(sK11,X0)
% 23.24/3.48      | r2_hidden(sK11,X1)
% 23.24/3.48      | X1 != X0
% 23.24/3.48      | sK11 != sK11 ),
% 23.24/3.48      inference(instantiation,[status(thm)],[c_5485]) ).
% 23.24/3.48  
% 23.24/3.48  cnf(c_21841,plain,
% 23.24/3.48      ( ~ r2_hidden(sK11,X0)
% 23.24/3.48      | r2_hidden(sK11,k4_xboole_0(X1,X2))
% 23.24/3.48      | k4_xboole_0(X1,X2) != X0
% 23.24/3.48      | sK11 != sK11 ),
% 23.24/3.48      inference(instantiation,[status(thm)],[c_10309]) ).
% 23.24/3.48  
% 23.24/3.48  cnf(c_21842,plain,
% 23.24/3.48      ( k4_xboole_0(X0,X1) != X2
% 23.24/3.48      | sK11 != sK11
% 23.24/3.48      | r2_hidden(sK11,X2) != iProver_top
% 23.24/3.48      | r2_hidden(sK11,k4_xboole_0(X0,X1)) = iProver_top ),
% 23.24/3.48      inference(predicate_to_equality,[status(thm)],[c_21841]) ).
% 23.24/3.48  
% 23.24/3.48  cnf(c_21844,plain,
% 23.24/3.48      ( k4_xboole_0(k1_xboole_0,k1_xboole_0) != k1_xboole_0
% 23.24/3.48      | sK11 != sK11
% 23.24/3.48      | r2_hidden(sK11,k4_xboole_0(k1_xboole_0,k1_xboole_0)) = iProver_top
% 23.24/3.48      | r2_hidden(sK11,k1_xboole_0) != iProver_top ),
% 23.24/3.48      inference(instantiation,[status(thm)],[c_21842]) ).
% 23.24/3.48  
% 23.24/3.48  cnf(c_802,plain,( X0 = X0 ),theory(equality) ).
% 23.24/3.48  
% 23.24/3.48  cnf(c_7339,plain,
% 23.24/3.48      ( sK11 = sK11 ),
% 23.24/3.48      inference(instantiation,[status(thm)],[c_802]) ).
% 23.24/3.48  
% 23.24/3.48  cnf(c_33,plain,
% 23.24/3.48      ( ~ r1_tarski(k1_tarski(X0),X1) | r2_hidden(X0,X1) ),
% 23.24/3.48      inference(cnf_transformation,[],[f86]) ).
% 23.24/3.48  
% 23.24/3.48  cnf(c_7156,plain,
% 23.24/3.48      ( ~ r1_tarski(k1_tarski(sK11),X0) | r2_hidden(sK11,X0) ),
% 23.24/3.48      inference(instantiation,[status(thm)],[c_33]) ).
% 23.24/3.48  
% 23.24/3.48  cnf(c_7157,plain,
% 23.24/3.48      ( r1_tarski(k1_tarski(sK11),X0) != iProver_top
% 23.24/3.48      | r2_hidden(sK11,X0) = iProver_top ),
% 23.24/3.48      inference(predicate_to_equality,[status(thm)],[c_7156]) ).
% 23.24/3.48  
% 23.24/3.48  cnf(c_7159,plain,
% 23.24/3.48      ( r1_tarski(k1_tarski(sK11),k1_xboole_0) != iProver_top
% 23.24/3.48      | r2_hidden(sK11,k1_xboole_0) = iProver_top ),
% 23.24/3.48      inference(instantiation,[status(thm)],[c_7157]) ).
% 23.24/3.48  
% 23.24/3.48  cnf(c_10,plain,
% 23.24/3.48      ( ~ r2_hidden(X0,X1) | ~ r2_hidden(X0,k4_xboole_0(X2,X1)) ),
% 23.24/3.48      inference(cnf_transformation,[],[f108]) ).
% 23.24/3.48  
% 23.24/3.48  cnf(c_3697,plain,
% 23.24/3.48      ( ~ r2_hidden(sK11,X0) | ~ r2_hidden(sK11,k4_xboole_0(X1,X0)) ),
% 23.24/3.48      inference(instantiation,[status(thm)],[c_10]) ).
% 23.24/3.48  
% 23.24/3.48  cnf(c_3698,plain,
% 23.24/3.48      ( r2_hidden(sK11,X0) != iProver_top
% 23.24/3.48      | r2_hidden(sK11,k4_xboole_0(X1,X0)) != iProver_top ),
% 23.24/3.48      inference(predicate_to_equality,[status(thm)],[c_3697]) ).
% 23.24/3.48  
% 23.24/3.48  cnf(c_3700,plain,
% 23.24/3.48      ( r2_hidden(sK11,k4_xboole_0(k1_xboole_0,k1_xboole_0)) != iProver_top
% 23.24/3.48      | r2_hidden(sK11,k1_xboole_0) != iProver_top ),
% 23.24/3.48      inference(instantiation,[status(thm)],[c_3698]) ).
% 23.24/3.48  
% 23.24/3.48  cnf(c_32,plain,
% 23.24/3.48      ( r1_tarski(k1_tarski(X0),X1) | ~ r2_hidden(X0,X1) ),
% 23.24/3.48      inference(cnf_transformation,[],[f87]) ).
% 23.24/3.48  
% 23.24/3.48  cnf(c_2592,plain,
% 23.24/3.48      ( r1_tarski(k1_tarski(sK11),sK8) | ~ r2_hidden(sK11,sK8) ),
% 23.24/3.48      inference(instantiation,[status(thm)],[c_32]) ).
% 23.24/3.48  
% 23.24/3.48  cnf(c_2593,plain,
% 23.24/3.48      ( r1_tarski(k1_tarski(sK11),sK8) = iProver_top
% 23.24/3.48      | r2_hidden(sK11,sK8) != iProver_top ),
% 23.24/3.48      inference(predicate_to_equality,[status(thm)],[c_2592]) ).
% 23.24/3.48  
% 23.24/3.48  cnf(c_19,plain,
% 23.24/3.48      ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
% 23.24/3.48      inference(cnf_transformation,[],[f71]) ).
% 23.24/3.48  
% 23.24/3.48  cnf(c_88,plain,
% 23.24/3.48      ( k4_xboole_0(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
% 23.24/3.48      inference(instantiation,[status(thm)],[c_19]) ).
% 23.24/3.48  
% 23.24/3.48  cnf(c_37,negated_conjecture,
% 23.24/3.48      ( r2_hidden(sK11,sK8) ),
% 23.24/3.48      inference(cnf_transformation,[],[f92]) ).
% 23.24/3.48  
% 23.24/3.48  cnf(c_40,plain,
% 23.24/3.48      ( r2_hidden(sK11,sK8) = iProver_top ),
% 23.24/3.48      inference(predicate_to_equality,[status(thm)],[c_37]) ).
% 23.24/3.48  
% 23.24/3.48  cnf(contradiction,plain,
% 23.24/3.48      ( $false ),
% 23.24/3.48      inference(minisat,
% 23.24/3.48                [status(thm)],
% 23.24/3.48                [c_103296,c_21844,c_7339,c_7159,c_3700,c_2593,c_88,c_40]) ).
% 23.24/3.48  
% 23.24/3.48  
% 23.24/3.48  % SZS output end CNFRefutation for theBenchmark.p
% 23.24/3.48  
% 23.24/3.48  ------                               Statistics
% 23.24/3.48  
% 23.24/3.48  ------ General
% 23.24/3.48  
% 23.24/3.48  abstr_ref_over_cycles:                  0
% 23.24/3.48  abstr_ref_under_cycles:                 0
% 23.24/3.48  gc_basic_clause_elim:                   0
% 23.24/3.48  forced_gc_time:                         0
% 23.24/3.48  parsing_time:                           0.009
% 23.24/3.48  unif_index_cands_time:                  0.
% 23.24/3.48  unif_index_add_time:                    0.
% 23.24/3.48  orderings_time:                         0.
% 23.24/3.48  out_proof_time:                         0.026
% 23.24/3.48  total_time:                             2.956
% 23.24/3.48  num_of_symbols:                         53
% 23.24/3.48  num_of_terms:                           149434
% 23.24/3.48  
% 23.24/3.48  ------ Preprocessing
% 23.24/3.48  
% 23.24/3.48  num_of_splits:                          0
% 23.24/3.48  num_of_split_atoms:                     0
% 23.24/3.48  num_of_reused_defs:                     0
% 23.24/3.48  num_eq_ax_congr_red:                    87
% 23.24/3.48  num_of_sem_filtered_clauses:            1
% 23.24/3.48  num_of_subtypes:                        0
% 23.24/3.48  monotx_restored_types:                  0
% 23.24/3.48  sat_num_of_epr_types:                   0
% 23.24/3.48  sat_num_of_non_cyclic_types:            0
% 23.24/3.48  sat_guarded_non_collapsed_types:        0
% 23.24/3.48  num_pure_diseq_elim:                    0
% 23.24/3.48  simp_replaced_by:                       0
% 23.24/3.48  res_preprocessed:                       169
% 23.24/3.48  prep_upred:                             0
% 23.24/3.48  prep_unflattend:                        0
% 23.24/3.48  smt_new_axioms:                         0
% 23.24/3.48  pred_elim_cands:                        3
% 23.24/3.48  pred_elim:                              0
% 23.24/3.48  pred_elim_cl:                           0
% 23.24/3.48  pred_elim_cycles:                       2
% 23.24/3.48  merged_defs:                            16
% 23.24/3.48  merged_defs_ncl:                        0
% 23.24/3.48  bin_hyper_res:                          16
% 23.24/3.48  prep_cycles:                            4
% 23.24/3.48  pred_elim_time:                         0.001
% 23.24/3.48  splitting_time:                         0.
% 23.24/3.48  sem_filter_time:                        0.
% 23.24/3.48  monotx_time:                            0.001
% 23.24/3.48  subtype_inf_time:                       0.
% 23.24/3.48  
% 23.24/3.48  ------ Problem properties
% 23.24/3.48  
% 23.24/3.48  clauses:                                38
% 23.24/3.48  conjectures:                            3
% 23.24/3.48  epr:                                    5
% 23.24/3.48  horn:                                   27
% 23.24/3.48  ground:                                 2
% 23.24/3.48  unary:                                  7
% 23.24/3.48  binary:                                 14
% 23.24/3.48  lits:                                   90
% 23.24/3.48  lits_eq:                                20
% 23.24/3.48  fd_pure:                                0
% 23.24/3.48  fd_pseudo:                              0
% 23.24/3.48  fd_cond:                                1
% 23.24/3.48  fd_pseudo_cond:                         11
% 23.24/3.48  ac_symbols:                             0
% 23.24/3.48  
% 23.24/3.48  ------ Propositional Solver
% 23.24/3.48  
% 23.24/3.48  prop_solver_calls:                      43
% 23.24/3.48  prop_fast_solver_calls:                 1732
% 23.24/3.48  smt_solver_calls:                       0
% 23.24/3.48  smt_fast_solver_calls:                  0
% 23.24/3.48  prop_num_of_clauses:                    42905
% 23.24/3.48  prop_preprocess_simplified:             57634
% 23.24/3.48  prop_fo_subsumed:                       22
% 23.24/3.48  prop_solver_time:                       0.
% 23.24/3.48  smt_solver_time:                        0.
% 23.24/3.48  smt_fast_solver_time:                   0.
% 23.24/3.48  prop_fast_solver_time:                  0.
% 23.24/3.48  prop_unsat_core_time:                   0.004
% 23.24/3.48  
% 23.24/3.48  ------ QBF
% 23.24/3.48  
% 23.24/3.48  qbf_q_res:                              0
% 23.24/3.48  qbf_num_tautologies:                    0
% 23.24/3.48  qbf_prep_cycles:                        0
% 23.24/3.48  
% 23.24/3.48  ------ BMC1
% 23.24/3.48  
% 23.24/3.48  bmc1_current_bound:                     -1
% 23.24/3.48  bmc1_last_solved_bound:                 -1
% 23.24/3.48  bmc1_unsat_core_size:                   -1
% 23.24/3.48  bmc1_unsat_core_parents_size:           -1
% 23.24/3.48  bmc1_merge_next_fun:                    0
% 23.24/3.48  bmc1_unsat_core_clauses_time:           0.
% 23.24/3.48  
% 23.24/3.48  ------ Instantiation
% 23.24/3.48  
% 23.24/3.48  inst_num_of_clauses:                    8188
% 23.24/3.48  inst_num_in_passive:                    4380
% 23.24/3.48  inst_num_in_active:                     1034
% 23.24/3.48  inst_num_in_unprocessed:                2774
% 23.24/3.48  inst_num_of_loops:                      2030
% 23.24/3.48  inst_num_of_learning_restarts:          0
% 23.24/3.48  inst_num_moves_active_passive:          996
% 23.24/3.48  inst_lit_activity:                      0
% 23.24/3.48  inst_lit_activity_moves:                0
% 23.24/3.48  inst_num_tautologies:                   0
% 23.24/3.48  inst_num_prop_implied:                  0
% 23.24/3.48  inst_num_existing_simplified:           0
% 23.24/3.48  inst_num_eq_res_simplified:             0
% 23.24/3.48  inst_num_child_elim:                    0
% 23.24/3.48  inst_num_of_dismatching_blockings:      16349
% 23.24/3.48  inst_num_of_non_proper_insts:           9059
% 23.24/3.48  inst_num_of_duplicates:                 0
% 23.24/3.48  inst_inst_num_from_inst_to_res:         0
% 23.24/3.48  inst_dismatching_checking_time:         0.
% 23.24/3.48  
% 23.24/3.48  ------ Resolution
% 23.24/3.48  
% 23.24/3.48  res_num_of_clauses:                     0
% 23.24/3.48  res_num_in_passive:                     0
% 23.24/3.48  res_num_in_active:                      0
% 23.24/3.48  res_num_of_loops:                       173
% 23.24/3.48  res_forward_subset_subsumed:            595
% 23.24/3.48  res_backward_subset_subsumed:           0
% 23.24/3.48  res_forward_subsumed:                   0
% 23.24/3.48  res_backward_subsumed:                  0
% 23.24/3.48  res_forward_subsumption_resolution:     0
% 23.24/3.48  res_backward_subsumption_resolution:    0
% 23.24/3.48  res_clause_to_clause_subsumption:       28500
% 23.24/3.48  res_orphan_elimination:                 0
% 23.24/3.48  res_tautology_del:                      397
% 23.24/3.48  res_num_eq_res_simplified:              0
% 23.24/3.48  res_num_sel_changes:                    0
% 23.24/3.48  res_moves_from_active_to_pass:          0
% 23.24/3.48  
% 23.24/3.48  ------ Superposition
% 23.24/3.48  
% 23.24/3.48  sup_time_total:                         0.
% 23.24/3.48  sup_time_generating:                    0.
% 23.24/3.48  sup_time_sim_full:                      0.
% 23.24/3.48  sup_time_sim_immed:                     0.
% 23.24/3.48  
% 23.24/3.48  sup_num_of_clauses:                     4761
% 23.24/3.48  sup_num_in_active:                      381
% 23.24/3.48  sup_num_in_passive:                     4380
% 23.24/3.48  sup_num_of_loops:                       405
% 23.24/3.48  sup_fw_superposition:                   5475
% 23.24/3.48  sup_bw_superposition:                   3695
% 23.24/3.48  sup_immediate_simplified:               2959
% 23.24/3.48  sup_given_eliminated:                   7
% 23.24/3.48  comparisons_done:                       0
% 23.24/3.48  comparisons_avoided:                    64
% 23.24/3.48  
% 23.24/3.48  ------ Simplifications
% 23.24/3.48  
% 23.24/3.48  
% 23.24/3.48  sim_fw_subset_subsumed:                 274
% 23.24/3.48  sim_bw_subset_subsumed:                 13
% 23.24/3.48  sim_fw_subsumed:                        1568
% 23.24/3.48  sim_bw_subsumed:                        144
% 23.24/3.48  sim_fw_subsumption_res:                 0
% 23.24/3.48  sim_bw_subsumption_res:                 0
% 23.24/3.48  sim_tautology_del:                      95
% 23.24/3.48  sim_eq_tautology_del:                   359
% 23.24/3.48  sim_eq_res_simp:                        3
% 23.24/3.48  sim_fw_demodulated:                     1177
% 23.24/3.48  sim_bw_demodulated:                     16
% 23.24/3.48  sim_light_normalised:                   566
% 23.24/3.48  sim_joinable_taut:                      0
% 23.24/3.48  sim_joinable_simp:                      0
% 23.24/3.48  sim_ac_normalised:                      0
% 23.24/3.48  sim_smt_subsumption:                    0
% 23.24/3.48  
%------------------------------------------------------------------------------
