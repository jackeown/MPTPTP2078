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
% DateTime   : Thu Dec  3 11:36:55 EST 2020

% Result     : Theorem 19.91s
% Output     : CNFRefutation 19.91s
% Verified   : 
% Statistics : Number of formulae       :  150 (1496 expanded)
%              Number of clauses        :   98 ( 470 expanded)
%              Number of leaves         :   16 ( 416 expanded)
%              Depth                    :   30
%              Number of atoms          :  494 (9209 expanded)
%              Number of equality atoms :  311 (3410 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal clause size      :   18 (   2 average)
%              Maximal term depth       :    7 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( k2_zfmisc_1(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ? [X4,X5] :
              ( k4_tarski(X4,X5) = X3
              & r2_hidden(X5,X1)
              & r2_hidden(X4,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
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
    inference(nnf_transformation,[],[f7])).

fof(f17,plain,(
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
    inference(rectify,[],[f16])).

fof(f20,plain,(
    ! [X8,X1,X0] :
      ( ? [X11,X12] :
          ( k4_tarski(X11,X12) = X8
          & r2_hidden(X12,X1)
          & r2_hidden(X11,X0) )
     => ( k4_tarski(sK4(X0,X1,X8),sK5(X0,X1,X8)) = X8
        & r2_hidden(sK5(X0,X1,X8),X1)
        & r2_hidden(sK4(X0,X1,X8),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X6,X7] :
          ( k4_tarski(X6,X7) = X3
          & r2_hidden(X7,X1)
          & r2_hidden(X6,X0) )
     => ( k4_tarski(sK2(X0,X1,X2),sK3(X0,X1,X2)) = X3
        & r2_hidden(sK3(X0,X1,X2),X1)
        & r2_hidden(sK2(X0,X1,X2),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
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
              ( k4_tarski(X4,X5) != sK1(X0,X1,X2)
              | ~ r2_hidden(X5,X1)
              | ~ r2_hidden(X4,X0) )
          | ~ r2_hidden(sK1(X0,X1,X2),X2) )
        & ( ? [X7,X6] :
              ( k4_tarski(X6,X7) = sK1(X0,X1,X2)
              & r2_hidden(X7,X1)
              & r2_hidden(X6,X0) )
          | r2_hidden(sK1(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( ( k2_zfmisc_1(X0,X1) = X2
        | ( ( ! [X4,X5] :
                ( k4_tarski(X4,X5) != sK1(X0,X1,X2)
                | ~ r2_hidden(X5,X1)
                | ~ r2_hidden(X4,X0) )
            | ~ r2_hidden(sK1(X0,X1,X2),X2) )
          & ( ( k4_tarski(sK2(X0,X1,X2),sK3(X0,X1,X2)) = sK1(X0,X1,X2)
              & r2_hidden(sK3(X0,X1,X2),X1)
              & r2_hidden(sK2(X0,X1,X2),X0) )
            | r2_hidden(sK1(X0,X1,X2),X2) ) ) )
      & ( ! [X8] :
            ( ( r2_hidden(X8,X2)
              | ! [X9,X10] :
                  ( k4_tarski(X9,X10) != X8
                  | ~ r2_hidden(X10,X1)
                  | ~ r2_hidden(X9,X0) ) )
            & ( ( k4_tarski(sK4(X0,X1,X8),sK5(X0,X1,X8)) = X8
                & r2_hidden(sK5(X0,X1,X8),X1)
                & r2_hidden(sK4(X0,X1,X8),X0) )
              | ~ r2_hidden(X8,X2) ) )
        | k2_zfmisc_1(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4,sK5])],[f17,f20,f19,f18])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( k2_zfmisc_1(X0,X1) = X2
      | r2_hidden(sK2(X0,X1,X2),X0)
      | r2_hidden(sK1(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f5,axiom,(
    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f5])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
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

fof(f12,plain,(
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
    inference(flattening,[],[f11])).

fof(f13,plain,(
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
    inference(rectify,[],[f12])).

fof(f14,plain,(
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

fof(f15,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f13,f14])).

fof(f29,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f15])).

fof(f4,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f52,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f29,f34])).

fof(f55,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,k5_xboole_0(X0,k3_xboole_0(X0,X1))) ) ),
    inference(equality_resolution,[],[f52])).

fof(f6,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f6])).

fof(f2,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f40,plain,(
    ! [X2,X0,X10,X8,X1,X9] :
      ( r2_hidden(X8,X2)
      | k4_tarski(X9,X10) != X8
      | ~ r2_hidden(X10,X1)
      | ~ r2_hidden(X9,X0)
      | k2_zfmisc_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f21])).

fof(f57,plain,(
    ! [X2,X0,X10,X1,X9] :
      ( r2_hidden(k4_tarski(X9,X10),X2)
      | ~ r2_hidden(X10,X1)
      | ~ r2_hidden(X9,X0)
      | k2_zfmisc_1(X0,X1) != X2 ) ),
    inference(equality_resolution,[],[f40])).

fof(f58,plain,(
    ! [X0,X10,X1,X9] :
      ( r2_hidden(k4_tarski(X9,X10),k2_zfmisc_1(X0,X1))
      | ~ r2_hidden(X10,X1)
      | ~ r2_hidden(X9,X0) ) ),
    inference(equality_resolution,[],[f57])).

fof(f38,plain,(
    ! [X2,X0,X8,X1] :
      ( r2_hidden(sK5(X0,X1,X8),X1)
      | ~ r2_hidden(X8,X2)
      | k2_zfmisc_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f21])).

fof(f60,plain,(
    ! [X0,X8,X1] :
      ( r2_hidden(sK5(X0,X1,X8),X1)
      | ~ r2_hidden(X8,k2_zfmisc_1(X0,X1)) ) ),
    inference(equality_resolution,[],[f38])).

fof(f37,plain,(
    ! [X2,X0,X8,X1] :
      ( r2_hidden(sK4(X0,X1,X8),X0)
      | ~ r2_hidden(X8,X2)
      | k2_zfmisc_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f21])).

fof(f61,plain,(
    ! [X0,X8,X1] :
      ( r2_hidden(sK4(X0,X1,X8),X0)
      | ~ r2_hidden(X8,k2_zfmisc_1(X0,X1)) ) ),
    inference(equality_resolution,[],[f37])).

fof(f28,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f15])).

fof(f53,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f28,f34])).

fof(f56,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,k5_xboole_0(X0,k3_xboole_0(X0,X1))) ) ),
    inference(equality_resolution,[],[f53])).

fof(f8,conjecture,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f9,negated_conjecture,(
    ~ ! [X0,X1] :
        ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      <=> ( k1_xboole_0 = X1
          | k1_xboole_0 = X0 ) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f10,plain,(
    ? [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <~> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f22,plain,(
    ? [X0,X1] :
      ( ( ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 )
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 = k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f10])).

fof(f23,plain,(
    ? [X0,X1] :
      ( ( ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 )
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 = k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f22])).

fof(f24,plain,
    ( ? [X0,X1] :
        ( ( ( k1_xboole_0 != X1
            & k1_xboole_0 != X0 )
          | k1_xboole_0 != k2_zfmisc_1(X0,X1) )
        & ( k1_xboole_0 = X1
          | k1_xboole_0 = X0
          | k1_xboole_0 = k2_zfmisc_1(X0,X1) ) )
   => ( ( ( k1_xboole_0 != sK7
          & k1_xboole_0 != sK6 )
        | k1_xboole_0 != k2_zfmisc_1(sK6,sK7) )
      & ( k1_xboole_0 = sK7
        | k1_xboole_0 = sK6
        | k1_xboole_0 = k2_zfmisc_1(sK6,sK7) ) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,
    ( ( ( k1_xboole_0 != sK7
        & k1_xboole_0 != sK6 )
      | k1_xboole_0 != k2_zfmisc_1(sK6,sK7) )
    & ( k1_xboole_0 = sK7
      | k1_xboole_0 = sK6
      | k1_xboole_0 = k2_zfmisc_1(sK6,sK7) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7])],[f23,f24])).

fof(f45,plain,
    ( k1_xboole_0 = sK7
    | k1_xboole_0 = sK6
    | k1_xboole_0 = k2_zfmisc_1(sK6,sK7) ),
    inference(cnf_transformation,[],[f25])).

fof(f31,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X0,X1) = X2
      | r2_hidden(sK0(X0,X1,X2),X0)
      | r2_hidden(sK0(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X2
      | r2_hidden(sK0(X0,X1,X2),X0)
      | r2_hidden(sK0(X0,X1,X2),X2) ) ),
    inference(definition_unfolding,[],[f31,f34])).

fof(f32,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X0,X1) = X2
      | ~ r2_hidden(sK0(X0,X1,X2),X1)
      | r2_hidden(sK0(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X2
      | ~ r2_hidden(sK0(X0,X1,X2),X1)
      | r2_hidden(sK0(X0,X1,X2),X2) ) ),
    inference(definition_unfolding,[],[f32,f34])).

fof(f46,plain,
    ( k1_xboole_0 != sK6
    | k1_xboole_0 != k2_zfmisc_1(sK6,sK7) ),
    inference(cnf_transformation,[],[f25])).

fof(f47,plain,
    ( k1_xboole_0 != sK7
    | k1_xboole_0 != k2_zfmisc_1(sK6,sK7) ),
    inference(cnf_transformation,[],[f25])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( k2_zfmisc_1(X0,X1) = X2
      | r2_hidden(sK3(X0,X1,X2),X1)
      | r2_hidden(sK1(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f21])).

cnf(c_13,plain,
    ( r2_hidden(sK2(X0,X1,X2),X0)
    | r2_hidden(sK1(X0,X1,X2),X2)
    | k2_zfmisc_1(X0,X1) = X2 ),
    inference(cnf_transformation,[],[f41])).

cnf(c_408,plain,
    ( k2_zfmisc_1(X0,X1) = X2
    | r2_hidden(sK2(X0,X1,X2),X0) = iProver_top
    | r2_hidden(sK1(X0,X1,X2),X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_8,plain,
    ( k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f35])).

cnf(c_0,plain,
    ( k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f26])).

cnf(c_567,plain,
    ( k3_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_8,c_0])).

cnf(c_6,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k5_xboole_0(X2,k3_xboole_0(X2,X1))) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_413,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,k5_xboole_0(X2,k3_xboole_0(X2,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_910,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,k5_xboole_0(k1_xboole_0,k1_xboole_0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_567,c_413])).

cnf(c_9,plain,
    ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f36])).

cnf(c_1,plain,
    ( k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f27])).

cnf(c_682,plain,
    ( k5_xboole_0(k1_xboole_0,X0) = X0 ),
    inference(superposition,[status(thm)],[c_9,c_1])).

cnf(c_913,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,k1_xboole_0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_910,c_682])).

cnf(c_1572,plain,
    ( k2_zfmisc_1(X0,X1) = X2
    | r2_hidden(sK2(X0,X1,X2),X0) = iProver_top
    | r2_hidden(sK1(X0,X1,X2),k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_408,c_913])).

cnf(c_14,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X2,X3)
    | r2_hidden(k4_tarski(X2,X0),k2_zfmisc_1(X3,X1)) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_407,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X2,X3) != iProver_top
    | r2_hidden(k4_tarski(X2,X0),k2_zfmisc_1(X3,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_16,plain,
    ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
    | r2_hidden(sK5(X1,X2,X0),X2) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_405,plain,
    ( r2_hidden(X0,k2_zfmisc_1(X1,X2)) != iProver_top
    | r2_hidden(sK5(X1,X2,X0),X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_1067,plain,
    ( r2_hidden(X0,k2_zfmisc_1(X1,X2)) != iProver_top
    | r2_hidden(sK5(X1,X2,X0),k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_405,c_913])).

cnf(c_1176,plain,
    ( r2_hidden(X0,k2_zfmisc_1(X1,k1_xboole_0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_405,c_1067])).

cnf(c_1535,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X2,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_407,c_1176])).

cnf(c_19401,plain,
    ( k2_zfmisc_1(X0,X1) = X2
    | r2_hidden(sK1(X0,X1,X2),k1_xboole_0) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_1572,c_1535])).

cnf(c_19407,plain,
    ( k2_zfmisc_1(X0,X1) = k1_xboole_0
    | r2_hidden(sK2(X0,X1,k1_xboole_0),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_408,c_19401])).

cnf(c_17,plain,
    ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
    | r2_hidden(sK4(X1,X2,X0),X1) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_404,plain,
    ( r2_hidden(X0,k2_zfmisc_1(X1,X2)) != iProver_top
    | r2_hidden(sK4(X1,X2,X0),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_7,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_412,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r2_hidden(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_743,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r2_hidden(X0,k5_xboole_0(X1,k3_xboole_0(X2,X1))) != iProver_top ),
    inference(superposition,[status(thm)],[c_0,c_412])).

cnf(c_888,plain,
    ( r2_hidden(X0,k2_zfmisc_1(X1,k5_xboole_0(X2,k3_xboole_0(X3,X2)))) != iProver_top
    | r2_hidden(sK5(X1,k5_xboole_0(X2,k3_xboole_0(X3,X2)),X0),X2) = iProver_top ),
    inference(superposition,[status(thm)],[c_405,c_743])).

cnf(c_12130,plain,
    ( r2_hidden(X0,k2_zfmisc_1(X1,k5_xboole_0(X2,k3_xboole_0(X3,X2)))) != iProver_top
    | r2_hidden(sK5(X1,k5_xboole_0(X2,k3_xboole_0(X2,X3)),X0),X2) = iProver_top ),
    inference(superposition,[status(thm)],[c_0,c_888])).

cnf(c_904,plain,
    ( r2_hidden(X0,k2_zfmisc_1(X1,k5_xboole_0(X2,k3_xboole_0(X2,X3)))) != iProver_top
    | r2_hidden(sK5(X1,k5_xboole_0(X2,k3_xboole_0(X2,X3)),X0),X3) != iProver_top ),
    inference(superposition,[status(thm)],[c_405,c_413])).

cnf(c_12815,plain,
    ( r2_hidden(X0,k2_zfmisc_1(X1,k5_xboole_0(X2,k3_xboole_0(X2,X2)))) != iProver_top ),
    inference(superposition,[status(thm)],[c_12130,c_904])).

cnf(c_13029,plain,
    ( r2_hidden(X0,k2_zfmisc_1(k2_zfmisc_1(X1,k5_xboole_0(X2,k3_xboole_0(X2,X2))),X3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_404,c_12815])).

cnf(c_19871,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,k5_xboole_0(X1,k3_xboole_0(X1,X1))),X2),X3) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_19407,c_13029])).

cnf(c_13831,plain,
    ( r2_hidden(X0,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,k5_xboole_0(X2,k3_xboole_0(X2,X2))),X3),X4)) != iProver_top ),
    inference(superposition,[status(thm)],[c_404,c_13029])).

cnf(c_19874,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,k5_xboole_0(X1,k3_xboole_0(X1,X1))),X2),X3),X4) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_19407,c_13831])).

cnf(c_19882,plain,
    ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_19871,c_19874])).

cnf(c_20,negated_conjecture,
    ( k1_xboole_0 = k2_zfmisc_1(sK6,sK7)
    | k1_xboole_0 = sK6
    | k1_xboole_0 = sK7 ),
    inference(cnf_transformation,[],[f45])).

cnf(c_1532,plain,
    ( sK6 = k1_xboole_0
    | sK7 = k1_xboole_0
    | r2_hidden(X0,sK6) != iProver_top
    | r2_hidden(X1,sK7) != iProver_top
    | r2_hidden(k4_tarski(X0,X1),k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_20,c_407])).

cnf(c_1558,plain,
    ( sK6 = k1_xboole_0
    | sK7 = k1_xboole_0
    | r2_hidden(X0,sK6) != iProver_top
    | r2_hidden(X1,sK7) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_1532,c_1535])).

cnf(c_1946,plain,
    ( sK6 = k1_xboole_0
    | sK7 = k1_xboole_0
    | r2_hidden(X0,k2_zfmisc_1(X1,sK7)) != iProver_top
    | r2_hidden(X2,sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_405,c_1558])).

cnf(c_2631,plain,
    ( sK6 = k1_xboole_0
    | sK7 = k1_xboole_0
    | r2_hidden(X0,sK6) != iProver_top
    | r2_hidden(X1,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_20,c_1946])).

cnf(c_2728,plain,
    ( sK6 = k1_xboole_0
    | sK7 = k1_xboole_0
    | r2_hidden(X0,k2_zfmisc_1(sK6,X1)) != iProver_top
    | r2_hidden(X2,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_404,c_2631])).

cnf(c_3999,plain,
    ( sK6 = k1_xboole_0
    | sK7 = k1_xboole_0
    | r2_hidden(X0,k1_xboole_0) != iProver_top
    | r2_hidden(X1,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_20,c_2728])).

cnf(c_4139,plain,
    ( sK6 = k1_xboole_0
    | sK7 = k1_xboole_0
    | r2_hidden(X0,k2_zfmisc_1(k1_xboole_0,X1)) != iProver_top
    | r2_hidden(X2,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_404,c_3999])).

cnf(c_4347,plain,
    ( sK6 = k1_xboole_0
    | sK7 = k1_xboole_0
    | r2_hidden(X0,k2_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1),X2)) != iProver_top
    | r2_hidden(X3,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_404,c_4139])).

cnf(c_45,plain,
    ( k5_xboole_0(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_46,plain,
    ( k3_xboole_0(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_173,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_184,plain,
    ( k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_173])).

cnf(c_574,plain,
    ( sK7 = sK7 ),
    inference(instantiation,[status(thm)],[c_173])).

cnf(c_578,plain,
    ( sK6 = sK6 ),
    inference(instantiation,[status(thm)],[c_173])).

cnf(c_174,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_564,plain,
    ( X0 != X1
    | sK7 != X1
    | sK7 = X0 ),
    inference(instantiation,[status(thm)],[c_174])).

cnf(c_573,plain,
    ( X0 != sK7
    | sK7 = X0
    | sK7 != sK7 ),
    inference(instantiation,[status(thm)],[c_564])).

cnf(c_585,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) != sK7
    | sK7 = k5_xboole_0(X0,k3_xboole_0(X0,X1))
    | sK7 != sK7 ),
    inference(instantiation,[status(thm)],[c_573])).

cnf(c_589,plain,
    ( k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,k1_xboole_0)) != sK7
    | sK7 = k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,k1_xboole_0))
    | sK7 != sK7 ),
    inference(instantiation,[status(thm)],[c_585])).

cnf(c_572,plain,
    ( X0 != X1
    | sK6 != X1
    | sK6 = X0 ),
    inference(instantiation,[status(thm)],[c_174])).

cnf(c_577,plain,
    ( X0 != sK6
    | sK6 = X0
    | sK6 != sK6 ),
    inference(instantiation,[status(thm)],[c_572])).

cnf(c_623,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) != sK6
    | sK6 = k5_xboole_0(X0,k3_xboole_0(X0,X1))
    | sK6 != sK6 ),
    inference(instantiation,[status(thm)],[c_577])).

cnf(c_627,plain,
    ( k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,k1_xboole_0)) != sK6
    | sK6 = k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,k1_xboole_0))
    | sK6 != sK6 ),
    inference(instantiation,[status(thm)],[c_623])).

cnf(c_712,plain,
    ( X0 != k5_xboole_0(X1,k3_xboole_0(X1,X2))
    | sK7 = X0
    | sK7 != k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    inference(instantiation,[status(thm)],[c_564])).

cnf(c_713,plain,
    ( sK7 != k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,k1_xboole_0))
    | sK7 = k1_xboole_0
    | k1_xboole_0 != k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,k1_xboole_0)) ),
    inference(instantiation,[status(thm)],[c_712])).

cnf(c_717,plain,
    ( X0 != k5_xboole_0(X1,k3_xboole_0(X1,X2))
    | sK6 = X0
    | sK6 != k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    inference(instantiation,[status(thm)],[c_572])).

cnf(c_718,plain,
    ( sK6 != k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,k1_xboole_0))
    | sK6 = k1_xboole_0
    | k1_xboole_0 != k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,k1_xboole_0)) ),
    inference(instantiation,[status(thm)],[c_717])).

cnf(c_795,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X2
    | k1_xboole_0 != X2
    | k1_xboole_0 = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(instantiation,[status(thm)],[c_174])).

cnf(c_1112,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) != k5_xboole_0(X0,X2)
    | k1_xboole_0 != k5_xboole_0(X0,X2)
    | k1_xboole_0 = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(instantiation,[status(thm)],[c_795])).

cnf(c_1114,plain,
    ( k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,k1_xboole_0)) != k5_xboole_0(k1_xboole_0,k1_xboole_0)
    | k1_xboole_0 = k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,k1_xboole_0))
    | k1_xboole_0 != k5_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_1112])).

cnf(c_176,plain,
    ( X0 != X1
    | k5_xboole_0(X2,X0) = k5_xboole_0(X2,X1) ),
    theory(equality)).

cnf(c_1113,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k5_xboole_0(X0,X2)
    | k3_xboole_0(X0,X1) != X2 ),
    inference(instantiation,[status(thm)],[c_176])).

cnf(c_1115,plain,
    ( k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,k1_xboole_0)) = k5_xboole_0(k1_xboole_0,k1_xboole_0)
    | k3_xboole_0(k1_xboole_0,k1_xboole_0) != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1113])).

cnf(c_4721,plain,
    ( k5_xboole_0(X0,X1) != X2
    | k1_xboole_0 != X2
    | k1_xboole_0 = k5_xboole_0(X0,X1) ),
    inference(instantiation,[status(thm)],[c_174])).

cnf(c_4722,plain,
    ( k5_xboole_0(k1_xboole_0,k1_xboole_0) != k1_xboole_0
    | k1_xboole_0 = k5_xboole_0(k1_xboole_0,k1_xboole_0)
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_4721])).

cnf(c_4,plain,
    ( r2_hidden(sK0(X0,X1,X2),X0)
    | r2_hidden(sK0(X0,X1,X2),X2)
    | k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X2 ),
    inference(cnf_transformation,[],[f50])).

cnf(c_415,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X2
    | r2_hidden(sK0(X0,X1,X2),X0) = iProver_top
    | r2_hidden(sK0(X0,X1,X2),X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_3,plain,
    ( ~ r2_hidden(sK0(X0,X1,X2),X1)
    | r2_hidden(sK0(X0,X1,X2),X2)
    | k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X2 ),
    inference(cnf_transformation,[],[f49])).

cnf(c_416,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X2
    | r2_hidden(sK0(X0,X1,X2),X1) != iProver_top
    | r2_hidden(sK0(X0,X1,X2),X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_3539,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,X0)) = X1
    | r2_hidden(sK0(X0,X0,X1),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_415,c_416])).

cnf(c_11285,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,X0)) = sK7
    | sK6 = k1_xboole_0
    | sK7 = k1_xboole_0
    | r2_hidden(X1,sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_3539,c_1558])).

cnf(c_11694,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,X0)) = sK6
    | k5_xboole_0(X1,k3_xboole_0(X1,X1)) = sK7
    | sK6 = k1_xboole_0
    | sK7 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_3539,c_11285])).

cnf(c_11902,plain,
    ( k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,k1_xboole_0)) = sK6
    | k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,k1_xboole_0)) = sK7
    | sK6 = k1_xboole_0
    | sK7 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_11694])).

cnf(c_11990,plain,
    ( sK6 = k1_xboole_0
    | sK7 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_4347,c_45,c_46,c_184,c_574,c_578,c_589,c_627,c_713,c_718,c_1114,c_1115,c_4722,c_11902])).

cnf(c_19,negated_conjecture,
    ( k1_xboole_0 != k2_zfmisc_1(sK6,sK7)
    | k1_xboole_0 != sK6 ),
    inference(cnf_transformation,[],[f46])).

cnf(c_12004,plain,
    ( k2_zfmisc_1(k1_xboole_0,sK7) != k1_xboole_0
    | sK6 != k1_xboole_0
    | sK7 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_11990,c_19])).

cnf(c_12009,plain,
    ( k2_zfmisc_1(k1_xboole_0,sK7) != k1_xboole_0
    | sK7 = k1_xboole_0 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_12004,c_11990])).

cnf(c_90590,plain,
    ( sK7 = k1_xboole_0
    | k1_xboole_0 != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_19882,c_12009])).

cnf(c_90615,plain,
    ( sK7 = k1_xboole_0 ),
    inference(equality_resolution_simp,[status(thm)],[c_90590])).

cnf(c_18,negated_conjecture,
    ( k1_xboole_0 != k2_zfmisc_1(sK6,sK7)
    | k1_xboole_0 != sK7 ),
    inference(cnf_transformation,[],[f47])).

cnf(c_91013,plain,
    ( k2_zfmisc_1(sK6,k1_xboole_0) != k1_xboole_0
    | k1_xboole_0 != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_90615,c_18])).

cnf(c_91014,plain,
    ( k2_zfmisc_1(sK6,k1_xboole_0) != k1_xboole_0 ),
    inference(equality_resolution_simp,[status(thm)],[c_91013])).

cnf(c_12,plain,
    ( r2_hidden(sK3(X0,X1,X2),X1)
    | r2_hidden(sK1(X0,X1,X2),X2)
    | k2_zfmisc_1(X0,X1) = X2 ),
    inference(cnf_transformation,[],[f42])).

cnf(c_409,plain,
    ( k2_zfmisc_1(X0,X1) = X2
    | r2_hidden(sK3(X0,X1,X2),X1) = iProver_top
    | r2_hidden(sK1(X0,X1,X2),X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_19406,plain,
    ( k2_zfmisc_1(X0,X1) = k1_xboole_0
    | r2_hidden(sK3(X0,X1,k1_xboole_0),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_409,c_19401])).

cnf(c_19668,plain,
    ( k2_zfmisc_1(X0,k2_zfmisc_1(k2_zfmisc_1(X1,k5_xboole_0(X2,k3_xboole_0(X2,X2))),X3)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_19406,c_13029])).

cnf(c_13830,plain,
    ( r2_hidden(X0,k2_zfmisc_1(X1,k2_zfmisc_1(k2_zfmisc_1(X2,k5_xboole_0(X3,k3_xboole_0(X3,X3))),X4))) != iProver_top ),
    inference(superposition,[status(thm)],[c_405,c_13029])).

cnf(c_19670,plain,
    ( k2_zfmisc_1(X0,k2_zfmisc_1(X1,k2_zfmisc_1(k2_zfmisc_1(X2,k5_xboole_0(X3,k3_xboole_0(X3,X3))),X4))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_19406,c_13830])).

cnf(c_19679,plain,
    ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_19668,c_19670])).

cnf(c_91016,plain,
    ( k1_xboole_0 != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_91014,c_19679])).

cnf(c_91017,plain,
    ( $false ),
    inference(equality_resolution_simp,[status(thm)],[c_91016])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.33  % Computer   : n008.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 15:58:30 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 19.91/2.99  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 19.91/2.99  
% 19.91/2.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 19.91/2.99  
% 19.91/2.99  ------  iProver source info
% 19.91/2.99  
% 19.91/2.99  git: date: 2020-06-30 10:37:57 +0100
% 19.91/2.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 19.91/2.99  git: non_committed_changes: false
% 19.91/2.99  git: last_make_outside_of_git: false
% 19.91/2.99  
% 19.91/2.99  ------ 
% 19.91/2.99  
% 19.91/2.99  ------ Input Options
% 19.91/2.99  
% 19.91/2.99  --out_options                           all
% 19.91/2.99  --tptp_safe_out                         true
% 19.91/2.99  --problem_path                          ""
% 19.91/2.99  --include_path                          ""
% 19.91/2.99  --clausifier                            res/vclausify_rel
% 19.91/2.99  --clausifier_options                    --mode clausify
% 19.91/2.99  --stdin                                 false
% 19.91/2.99  --stats_out                             all
% 19.91/2.99  
% 19.91/2.99  ------ General Options
% 19.91/2.99  
% 19.91/2.99  --fof                                   false
% 19.91/2.99  --time_out_real                         305.
% 19.91/2.99  --time_out_virtual                      -1.
% 19.91/2.99  --symbol_type_check                     false
% 19.91/2.99  --clausify_out                          false
% 19.91/2.99  --sig_cnt_out                           false
% 19.91/2.99  --trig_cnt_out                          false
% 19.91/2.99  --trig_cnt_out_tolerance                1.
% 19.91/2.99  --trig_cnt_out_sk_spl                   false
% 19.91/2.99  --abstr_cl_out                          false
% 19.91/2.99  
% 19.91/2.99  ------ Global Options
% 19.91/2.99  
% 19.91/2.99  --schedule                              default
% 19.91/2.99  --add_important_lit                     false
% 19.91/2.99  --prop_solver_per_cl                    1000
% 19.91/2.99  --min_unsat_core                        false
% 19.91/2.99  --soft_assumptions                      false
% 19.91/2.99  --soft_lemma_size                       3
% 19.91/2.99  --prop_impl_unit_size                   0
% 19.91/2.99  --prop_impl_unit                        []
% 19.91/2.99  --share_sel_clauses                     true
% 19.91/2.99  --reset_solvers                         false
% 19.91/2.99  --bc_imp_inh                            [conj_cone]
% 19.91/2.99  --conj_cone_tolerance                   3.
% 19.91/2.99  --extra_neg_conj                        none
% 19.91/2.99  --large_theory_mode                     true
% 19.91/2.99  --prolific_symb_bound                   200
% 19.91/2.99  --lt_threshold                          2000
% 19.91/2.99  --clause_weak_htbl                      true
% 19.91/2.99  --gc_record_bc_elim                     false
% 19.91/2.99  
% 19.91/2.99  ------ Preprocessing Options
% 19.91/2.99  
% 19.91/2.99  --preprocessing_flag                    true
% 19.91/2.99  --time_out_prep_mult                    0.1
% 19.91/2.99  --splitting_mode                        input
% 19.91/2.99  --splitting_grd                         true
% 19.91/2.99  --splitting_cvd                         false
% 19.91/2.99  --splitting_cvd_svl                     false
% 19.91/2.99  --splitting_nvd                         32
% 19.91/2.99  --sub_typing                            true
% 19.91/2.99  --prep_gs_sim                           true
% 19.91/2.99  --prep_unflatten                        true
% 19.91/2.99  --prep_res_sim                          true
% 19.91/2.99  --prep_upred                            true
% 19.91/2.99  --prep_sem_filter                       exhaustive
% 19.91/2.99  --prep_sem_filter_out                   false
% 19.91/2.99  --pred_elim                             true
% 19.91/2.99  --res_sim_input                         true
% 19.91/2.99  --eq_ax_congr_red                       true
% 19.91/2.99  --pure_diseq_elim                       true
% 19.91/2.99  --brand_transform                       false
% 19.91/2.99  --non_eq_to_eq                          false
% 19.91/2.99  --prep_def_merge                        true
% 19.91/2.99  --prep_def_merge_prop_impl              false
% 19.91/2.99  --prep_def_merge_mbd                    true
% 19.91/2.99  --prep_def_merge_tr_red                 false
% 19.91/2.99  --prep_def_merge_tr_cl                  false
% 19.91/2.99  --smt_preprocessing                     true
% 19.91/2.99  --smt_ac_axioms                         fast
% 19.91/2.99  --preprocessed_out                      false
% 19.91/2.99  --preprocessed_stats                    false
% 19.91/2.99  
% 19.91/2.99  ------ Abstraction refinement Options
% 19.91/2.99  
% 19.91/2.99  --abstr_ref                             []
% 19.91/2.99  --abstr_ref_prep                        false
% 19.91/2.99  --abstr_ref_until_sat                   false
% 19.91/2.99  --abstr_ref_sig_restrict                funpre
% 19.91/2.99  --abstr_ref_af_restrict_to_split_sk     false
% 19.91/2.99  --abstr_ref_under                       []
% 19.91/2.99  
% 19.91/2.99  ------ SAT Options
% 19.91/2.99  
% 19.91/2.99  --sat_mode                              false
% 19.91/2.99  --sat_fm_restart_options                ""
% 19.91/2.99  --sat_gr_def                            false
% 19.91/2.99  --sat_epr_types                         true
% 19.91/2.99  --sat_non_cyclic_types                  false
% 19.91/2.99  --sat_finite_models                     false
% 19.91/2.99  --sat_fm_lemmas                         false
% 19.91/2.99  --sat_fm_prep                           false
% 19.91/2.99  --sat_fm_uc_incr                        true
% 19.91/2.99  --sat_out_model                         small
% 19.91/2.99  --sat_out_clauses                       false
% 19.91/2.99  
% 19.91/2.99  ------ QBF Options
% 19.91/2.99  
% 19.91/2.99  --qbf_mode                              false
% 19.91/2.99  --qbf_elim_univ                         false
% 19.91/2.99  --qbf_dom_inst                          none
% 19.91/2.99  --qbf_dom_pre_inst                      false
% 19.91/2.99  --qbf_sk_in                             false
% 19.91/2.99  --qbf_pred_elim                         true
% 19.91/2.99  --qbf_split                             512
% 19.91/2.99  
% 19.91/2.99  ------ BMC1 Options
% 19.91/2.99  
% 19.91/2.99  --bmc1_incremental                      false
% 19.91/2.99  --bmc1_axioms                           reachable_all
% 19.91/2.99  --bmc1_min_bound                        0
% 19.91/2.99  --bmc1_max_bound                        -1
% 19.91/2.99  --bmc1_max_bound_default                -1
% 19.91/2.99  --bmc1_symbol_reachability              true
% 19.91/2.99  --bmc1_property_lemmas                  false
% 19.91/2.99  --bmc1_k_induction                      false
% 19.91/2.99  --bmc1_non_equiv_states                 false
% 19.91/2.99  --bmc1_deadlock                         false
% 19.91/2.99  --bmc1_ucm                              false
% 19.91/2.99  --bmc1_add_unsat_core                   none
% 19.91/2.99  --bmc1_unsat_core_children              false
% 19.91/2.99  --bmc1_unsat_core_extrapolate_axioms    false
% 19.91/2.99  --bmc1_out_stat                         full
% 19.91/2.99  --bmc1_ground_init                      false
% 19.91/2.99  --bmc1_pre_inst_next_state              false
% 19.91/2.99  --bmc1_pre_inst_state                   false
% 19.91/2.99  --bmc1_pre_inst_reach_state             false
% 19.91/2.99  --bmc1_out_unsat_core                   false
% 19.91/2.99  --bmc1_aig_witness_out                  false
% 19.91/2.99  --bmc1_verbose                          false
% 19.91/2.99  --bmc1_dump_clauses_tptp                false
% 19.91/2.99  --bmc1_dump_unsat_core_tptp             false
% 19.91/2.99  --bmc1_dump_file                        -
% 19.91/2.99  --bmc1_ucm_expand_uc_limit              128
% 19.91/2.99  --bmc1_ucm_n_expand_iterations          6
% 19.91/2.99  --bmc1_ucm_extend_mode                  1
% 19.91/2.99  --bmc1_ucm_init_mode                    2
% 19.91/2.99  --bmc1_ucm_cone_mode                    none
% 19.91/2.99  --bmc1_ucm_reduced_relation_type        0
% 19.91/2.99  --bmc1_ucm_relax_model                  4
% 19.91/2.99  --bmc1_ucm_full_tr_after_sat            true
% 19.91/2.99  --bmc1_ucm_expand_neg_assumptions       false
% 19.91/2.99  --bmc1_ucm_layered_model                none
% 19.91/2.99  --bmc1_ucm_max_lemma_size               10
% 19.91/2.99  
% 19.91/2.99  ------ AIG Options
% 19.91/2.99  
% 19.91/2.99  --aig_mode                              false
% 19.91/2.99  
% 19.91/2.99  ------ Instantiation Options
% 19.91/2.99  
% 19.91/2.99  --instantiation_flag                    true
% 19.91/2.99  --inst_sos_flag                         false
% 19.91/2.99  --inst_sos_phase                        true
% 19.91/2.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 19.91/2.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 19.91/2.99  --inst_lit_sel_side                     num_symb
% 19.91/2.99  --inst_solver_per_active                1400
% 19.91/2.99  --inst_solver_calls_frac                1.
% 19.91/2.99  --inst_passive_queue_type               priority_queues
% 19.91/2.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 19.91/2.99  --inst_passive_queues_freq              [25;2]
% 19.91/2.99  --inst_dismatching                      true
% 19.91/2.99  --inst_eager_unprocessed_to_passive     true
% 19.91/2.99  --inst_prop_sim_given                   true
% 19.91/2.99  --inst_prop_sim_new                     false
% 19.91/2.99  --inst_subs_new                         false
% 19.91/2.99  --inst_eq_res_simp                      false
% 19.91/2.99  --inst_subs_given                       false
% 19.91/2.99  --inst_orphan_elimination               true
% 19.91/2.99  --inst_learning_loop_flag               true
% 19.91/2.99  --inst_learning_start                   3000
% 19.91/2.99  --inst_learning_factor                  2
% 19.91/2.99  --inst_start_prop_sim_after_learn       3
% 19.91/2.99  --inst_sel_renew                        solver
% 19.91/2.99  --inst_lit_activity_flag                true
% 19.91/2.99  --inst_restr_to_given                   false
% 19.91/2.99  --inst_activity_threshold               500
% 19.91/2.99  --inst_out_proof                        true
% 19.91/2.99  
% 19.91/2.99  ------ Resolution Options
% 19.91/2.99  
% 19.91/2.99  --resolution_flag                       true
% 19.91/2.99  --res_lit_sel                           adaptive
% 19.91/2.99  --res_lit_sel_side                      none
% 19.91/2.99  --res_ordering                          kbo
% 19.91/2.99  --res_to_prop_solver                    active
% 19.91/2.99  --res_prop_simpl_new                    false
% 19.91/2.99  --res_prop_simpl_given                  true
% 19.91/2.99  --res_passive_queue_type                priority_queues
% 19.91/2.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 19.91/2.99  --res_passive_queues_freq               [15;5]
% 19.91/2.99  --res_forward_subs                      full
% 19.91/2.99  --res_backward_subs                     full
% 19.91/2.99  --res_forward_subs_resolution           true
% 19.91/2.99  --res_backward_subs_resolution          true
% 19.91/2.99  --res_orphan_elimination                true
% 19.91/2.99  --res_time_limit                        2.
% 19.91/2.99  --res_out_proof                         true
% 19.91/2.99  
% 19.91/2.99  ------ Superposition Options
% 19.91/2.99  
% 19.91/2.99  --superposition_flag                    true
% 19.91/2.99  --sup_passive_queue_type                priority_queues
% 19.91/2.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 19.91/2.99  --sup_passive_queues_freq               [8;1;4]
% 19.91/2.99  --demod_completeness_check              fast
% 19.91/2.99  --demod_use_ground                      true
% 19.91/2.99  --sup_to_prop_solver                    passive
% 19.91/2.99  --sup_prop_simpl_new                    true
% 19.91/2.99  --sup_prop_simpl_given                  true
% 19.91/2.99  --sup_fun_splitting                     false
% 19.91/2.99  --sup_smt_interval                      50000
% 19.91/2.99  
% 19.91/2.99  ------ Superposition Simplification Setup
% 19.91/2.99  
% 19.91/2.99  --sup_indices_passive                   []
% 19.91/2.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 19.91/2.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 19.91/2.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 19.91/2.99  --sup_full_triv                         [TrivRules;PropSubs]
% 19.91/2.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 19.91/2.99  --sup_full_bw                           [BwDemod]
% 19.91/2.99  --sup_immed_triv                        [TrivRules]
% 19.91/2.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 19.91/2.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 19.91/2.99  --sup_immed_bw_main                     []
% 19.91/2.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 19.91/2.99  --sup_input_triv                        [Unflattening;TrivRules]
% 19.91/2.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 19.91/2.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 19.91/2.99  
% 19.91/2.99  ------ Combination Options
% 19.91/2.99  
% 19.91/2.99  --comb_res_mult                         3
% 19.91/2.99  --comb_sup_mult                         2
% 19.91/2.99  --comb_inst_mult                        10
% 19.91/2.99  
% 19.91/2.99  ------ Debug Options
% 19.91/2.99  
% 19.91/2.99  --dbg_backtrace                         false
% 19.91/2.99  --dbg_dump_prop_clauses                 false
% 19.91/2.99  --dbg_dump_prop_clauses_file            -
% 19.91/2.99  --dbg_out_stat                          false
% 19.91/2.99  ------ Parsing...
% 19.91/2.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 19.91/2.99  
% 19.91/2.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 19.91/2.99  
% 19.91/2.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 19.91/2.99  
% 19.91/2.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 19.91/2.99  ------ Proving...
% 19.91/2.99  ------ Problem Properties 
% 19.91/2.99  
% 19.91/2.99  
% 19.91/2.99  clauses                                 21
% 19.91/2.99  conjectures                             3
% 19.91/2.99  EPR                                     0
% 19.91/2.99  Horn                                    13
% 19.91/2.99  unary                                   4
% 19.91/2.99  binary                                  7
% 19.91/2.99  lits                                    51
% 19.91/2.99  lits eq                                 21
% 19.91/2.99  fd_pure                                 0
% 19.91/2.99  fd_pseudo                               0
% 19.91/2.99  fd_cond                                 0
% 19.91/2.99  fd_pseudo_cond                          7
% 19.91/2.99  AC symbols                              0
% 19.91/2.99  
% 19.91/2.99  ------ Schedule dynamic 5 is on 
% 19.91/2.99  
% 19.91/2.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 19.91/2.99  
% 19.91/2.99  
% 19.91/2.99  ------ 
% 19.91/2.99  Current options:
% 19.91/2.99  ------ 
% 19.91/2.99  
% 19.91/2.99  ------ Input Options
% 19.91/2.99  
% 19.91/2.99  --out_options                           all
% 19.91/2.99  --tptp_safe_out                         true
% 19.91/2.99  --problem_path                          ""
% 19.91/2.99  --include_path                          ""
% 19.91/2.99  --clausifier                            res/vclausify_rel
% 19.91/2.99  --clausifier_options                    --mode clausify
% 19.91/2.99  --stdin                                 false
% 19.91/2.99  --stats_out                             all
% 19.91/2.99  
% 19.91/2.99  ------ General Options
% 19.91/2.99  
% 19.91/2.99  --fof                                   false
% 19.91/2.99  --time_out_real                         305.
% 19.91/2.99  --time_out_virtual                      -1.
% 19.91/2.99  --symbol_type_check                     false
% 19.91/2.99  --clausify_out                          false
% 19.91/2.99  --sig_cnt_out                           false
% 19.91/2.99  --trig_cnt_out                          false
% 19.91/2.99  --trig_cnt_out_tolerance                1.
% 19.91/2.99  --trig_cnt_out_sk_spl                   false
% 19.91/2.99  --abstr_cl_out                          false
% 19.91/2.99  
% 19.91/2.99  ------ Global Options
% 19.91/2.99  
% 19.91/2.99  --schedule                              default
% 19.91/2.99  --add_important_lit                     false
% 19.91/2.99  --prop_solver_per_cl                    1000
% 19.91/2.99  --min_unsat_core                        false
% 19.91/2.99  --soft_assumptions                      false
% 19.91/2.99  --soft_lemma_size                       3
% 19.91/2.99  --prop_impl_unit_size                   0
% 19.91/2.99  --prop_impl_unit                        []
% 19.91/2.99  --share_sel_clauses                     true
% 19.91/2.99  --reset_solvers                         false
% 19.91/2.99  --bc_imp_inh                            [conj_cone]
% 19.91/2.99  --conj_cone_tolerance                   3.
% 19.91/2.99  --extra_neg_conj                        none
% 19.91/2.99  --large_theory_mode                     true
% 19.91/2.99  --prolific_symb_bound                   200
% 19.91/2.99  --lt_threshold                          2000
% 19.91/2.99  --clause_weak_htbl                      true
% 19.91/2.99  --gc_record_bc_elim                     false
% 19.91/2.99  
% 19.91/2.99  ------ Preprocessing Options
% 19.91/2.99  
% 19.91/2.99  --preprocessing_flag                    true
% 19.91/2.99  --time_out_prep_mult                    0.1
% 19.91/2.99  --splitting_mode                        input
% 19.91/2.99  --splitting_grd                         true
% 19.91/2.99  --splitting_cvd                         false
% 19.91/2.99  --splitting_cvd_svl                     false
% 19.91/2.99  --splitting_nvd                         32
% 19.91/2.99  --sub_typing                            true
% 19.91/2.99  --prep_gs_sim                           true
% 19.91/2.99  --prep_unflatten                        true
% 19.91/2.99  --prep_res_sim                          true
% 19.91/2.99  --prep_upred                            true
% 19.91/2.99  --prep_sem_filter                       exhaustive
% 19.91/2.99  --prep_sem_filter_out                   false
% 19.91/2.99  --pred_elim                             true
% 19.91/2.99  --res_sim_input                         true
% 19.91/2.99  --eq_ax_congr_red                       true
% 19.91/2.99  --pure_diseq_elim                       true
% 19.91/2.99  --brand_transform                       false
% 19.91/2.99  --non_eq_to_eq                          false
% 19.91/2.99  --prep_def_merge                        true
% 19.91/2.99  --prep_def_merge_prop_impl              false
% 19.91/2.99  --prep_def_merge_mbd                    true
% 19.91/2.99  --prep_def_merge_tr_red                 false
% 19.91/2.99  --prep_def_merge_tr_cl                  false
% 19.91/2.99  --smt_preprocessing                     true
% 19.91/2.99  --smt_ac_axioms                         fast
% 19.91/2.99  --preprocessed_out                      false
% 19.91/2.99  --preprocessed_stats                    false
% 19.91/2.99  
% 19.91/2.99  ------ Abstraction refinement Options
% 19.91/2.99  
% 19.91/2.99  --abstr_ref                             []
% 19.91/2.99  --abstr_ref_prep                        false
% 19.91/2.99  --abstr_ref_until_sat                   false
% 19.91/2.99  --abstr_ref_sig_restrict                funpre
% 19.91/2.99  --abstr_ref_af_restrict_to_split_sk     false
% 19.91/2.99  --abstr_ref_under                       []
% 19.91/2.99  
% 19.91/2.99  ------ SAT Options
% 19.91/2.99  
% 19.91/2.99  --sat_mode                              false
% 19.91/2.99  --sat_fm_restart_options                ""
% 19.91/2.99  --sat_gr_def                            false
% 19.91/2.99  --sat_epr_types                         true
% 19.91/2.99  --sat_non_cyclic_types                  false
% 19.91/2.99  --sat_finite_models                     false
% 19.91/2.99  --sat_fm_lemmas                         false
% 19.91/2.99  --sat_fm_prep                           false
% 19.91/2.99  --sat_fm_uc_incr                        true
% 19.91/2.99  --sat_out_model                         small
% 19.91/2.99  --sat_out_clauses                       false
% 19.91/2.99  
% 19.91/2.99  ------ QBF Options
% 19.91/2.99  
% 19.91/2.99  --qbf_mode                              false
% 19.91/2.99  --qbf_elim_univ                         false
% 19.91/2.99  --qbf_dom_inst                          none
% 19.91/2.99  --qbf_dom_pre_inst                      false
% 19.91/2.99  --qbf_sk_in                             false
% 19.91/2.99  --qbf_pred_elim                         true
% 19.91/2.99  --qbf_split                             512
% 19.91/2.99  
% 19.91/2.99  ------ BMC1 Options
% 19.91/2.99  
% 19.91/2.99  --bmc1_incremental                      false
% 19.91/2.99  --bmc1_axioms                           reachable_all
% 19.91/2.99  --bmc1_min_bound                        0
% 19.91/2.99  --bmc1_max_bound                        -1
% 19.91/2.99  --bmc1_max_bound_default                -1
% 19.91/2.99  --bmc1_symbol_reachability              true
% 19.91/2.99  --bmc1_property_lemmas                  false
% 19.91/2.99  --bmc1_k_induction                      false
% 19.91/2.99  --bmc1_non_equiv_states                 false
% 19.91/2.99  --bmc1_deadlock                         false
% 19.91/2.99  --bmc1_ucm                              false
% 19.91/2.99  --bmc1_add_unsat_core                   none
% 19.91/2.99  --bmc1_unsat_core_children              false
% 19.91/2.99  --bmc1_unsat_core_extrapolate_axioms    false
% 19.91/2.99  --bmc1_out_stat                         full
% 19.91/2.99  --bmc1_ground_init                      false
% 19.91/2.99  --bmc1_pre_inst_next_state              false
% 19.91/2.99  --bmc1_pre_inst_state                   false
% 19.91/2.99  --bmc1_pre_inst_reach_state             false
% 19.91/2.99  --bmc1_out_unsat_core                   false
% 19.91/2.99  --bmc1_aig_witness_out                  false
% 19.91/2.99  --bmc1_verbose                          false
% 19.91/2.99  --bmc1_dump_clauses_tptp                false
% 19.91/2.99  --bmc1_dump_unsat_core_tptp             false
% 19.91/2.99  --bmc1_dump_file                        -
% 19.91/2.99  --bmc1_ucm_expand_uc_limit              128
% 19.91/2.99  --bmc1_ucm_n_expand_iterations          6
% 19.91/2.99  --bmc1_ucm_extend_mode                  1
% 19.91/2.99  --bmc1_ucm_init_mode                    2
% 19.91/2.99  --bmc1_ucm_cone_mode                    none
% 19.91/2.99  --bmc1_ucm_reduced_relation_type        0
% 19.91/2.99  --bmc1_ucm_relax_model                  4
% 19.91/2.99  --bmc1_ucm_full_tr_after_sat            true
% 19.91/2.99  --bmc1_ucm_expand_neg_assumptions       false
% 19.91/2.99  --bmc1_ucm_layered_model                none
% 19.91/2.99  --bmc1_ucm_max_lemma_size               10
% 19.91/2.99  
% 19.91/2.99  ------ AIG Options
% 19.91/2.99  
% 19.91/2.99  --aig_mode                              false
% 19.91/2.99  
% 19.91/2.99  ------ Instantiation Options
% 19.91/2.99  
% 19.91/2.99  --instantiation_flag                    true
% 19.91/2.99  --inst_sos_flag                         false
% 19.91/2.99  --inst_sos_phase                        true
% 19.91/2.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 19.91/2.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 19.91/2.99  --inst_lit_sel_side                     none
% 19.91/2.99  --inst_solver_per_active                1400
% 19.91/2.99  --inst_solver_calls_frac                1.
% 19.91/2.99  --inst_passive_queue_type               priority_queues
% 19.91/2.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 19.91/2.99  --inst_passive_queues_freq              [25;2]
% 19.91/2.99  --inst_dismatching                      true
% 19.91/2.99  --inst_eager_unprocessed_to_passive     true
% 19.91/2.99  --inst_prop_sim_given                   true
% 19.91/2.99  --inst_prop_sim_new                     false
% 19.91/2.99  --inst_subs_new                         false
% 19.91/2.99  --inst_eq_res_simp                      false
% 19.91/2.99  --inst_subs_given                       false
% 19.91/2.99  --inst_orphan_elimination               true
% 19.91/2.99  --inst_learning_loop_flag               true
% 19.91/2.99  --inst_learning_start                   3000
% 19.91/2.99  --inst_learning_factor                  2
% 19.91/2.99  --inst_start_prop_sim_after_learn       3
% 19.91/2.99  --inst_sel_renew                        solver
% 19.91/2.99  --inst_lit_activity_flag                true
% 19.91/2.99  --inst_restr_to_given                   false
% 19.91/2.99  --inst_activity_threshold               500
% 19.91/2.99  --inst_out_proof                        true
% 19.91/2.99  
% 19.91/2.99  ------ Resolution Options
% 19.91/2.99  
% 19.91/2.99  --resolution_flag                       false
% 19.91/2.99  --res_lit_sel                           adaptive
% 19.91/2.99  --res_lit_sel_side                      none
% 19.91/2.99  --res_ordering                          kbo
% 19.91/2.99  --res_to_prop_solver                    active
% 19.91/2.99  --res_prop_simpl_new                    false
% 19.91/2.99  --res_prop_simpl_given                  true
% 19.91/2.99  --res_passive_queue_type                priority_queues
% 19.91/2.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 19.91/2.99  --res_passive_queues_freq               [15;5]
% 19.91/2.99  --res_forward_subs                      full
% 19.91/2.99  --res_backward_subs                     full
% 19.91/2.99  --res_forward_subs_resolution           true
% 19.91/2.99  --res_backward_subs_resolution          true
% 19.91/2.99  --res_orphan_elimination                true
% 19.91/2.99  --res_time_limit                        2.
% 19.91/2.99  --res_out_proof                         true
% 19.91/2.99  
% 19.91/2.99  ------ Superposition Options
% 19.91/2.99  
% 19.91/2.99  --superposition_flag                    true
% 19.91/2.99  --sup_passive_queue_type                priority_queues
% 19.91/2.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 19.91/2.99  --sup_passive_queues_freq               [8;1;4]
% 19.91/2.99  --demod_completeness_check              fast
% 19.91/2.99  --demod_use_ground                      true
% 19.91/2.99  --sup_to_prop_solver                    passive
% 19.91/2.99  --sup_prop_simpl_new                    true
% 19.91/2.99  --sup_prop_simpl_given                  true
% 19.91/2.99  --sup_fun_splitting                     false
% 19.91/2.99  --sup_smt_interval                      50000
% 19.91/2.99  
% 19.91/2.99  ------ Superposition Simplification Setup
% 19.91/2.99  
% 19.91/2.99  --sup_indices_passive                   []
% 19.91/2.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 19.91/2.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 19.91/2.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 19.91/2.99  --sup_full_triv                         [TrivRules;PropSubs]
% 19.91/2.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 19.91/2.99  --sup_full_bw                           [BwDemod]
% 19.91/2.99  --sup_immed_triv                        [TrivRules]
% 19.91/2.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 19.91/2.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 19.91/2.99  --sup_immed_bw_main                     []
% 19.91/2.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 19.91/2.99  --sup_input_triv                        [Unflattening;TrivRules]
% 19.91/2.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 19.91/2.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 19.91/2.99  
% 19.91/2.99  ------ Combination Options
% 19.91/2.99  
% 19.91/2.99  --comb_res_mult                         3
% 19.91/2.99  --comb_sup_mult                         2
% 19.91/2.99  --comb_inst_mult                        10
% 19.91/2.99  
% 19.91/2.99  ------ Debug Options
% 19.91/2.99  
% 19.91/2.99  --dbg_backtrace                         false
% 19.91/2.99  --dbg_dump_prop_clauses                 false
% 19.91/2.99  --dbg_dump_prop_clauses_file            -
% 19.91/2.99  --dbg_out_stat                          false
% 19.91/2.99  
% 19.91/2.99  
% 19.91/2.99  
% 19.91/2.99  
% 19.91/2.99  ------ Proving...
% 19.91/2.99  
% 19.91/2.99  
% 19.91/2.99  % SZS status Theorem for theBenchmark.p
% 19.91/2.99  
% 19.91/2.99   Resolution empty clause
% 19.91/2.99  
% 19.91/2.99  % SZS output start CNFRefutation for theBenchmark.p
% 19.91/2.99  
% 19.91/2.99  fof(f7,axiom,(
% 19.91/2.99    ! [X0,X1,X2] : (k2_zfmisc_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4,X5] : (k4_tarski(X4,X5) = X3 & r2_hidden(X5,X1) & r2_hidden(X4,X0))))),
% 19.91/2.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.91/2.99  
% 19.91/2.99  fof(f16,plain,(
% 19.91/2.99    ! [X0,X1,X2] : ((k2_zfmisc_1(X0,X1) = X2 | ? [X3] : ((! [X4,X5] : (k4_tarski(X4,X5) != X3 | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X0)) | ~r2_hidden(X3,X2)) & (? [X4,X5] : (k4_tarski(X4,X5) = X3 & r2_hidden(X5,X1) & r2_hidden(X4,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ! [X4,X5] : (k4_tarski(X4,X5) != X3 | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X0))) & (? [X4,X5] : (k4_tarski(X4,X5) = X3 & r2_hidden(X5,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X3,X2))) | k2_zfmisc_1(X0,X1) != X2))),
% 19.91/2.99    inference(nnf_transformation,[],[f7])).
% 19.91/2.99  
% 19.91/2.99  fof(f17,plain,(
% 19.91/2.99    ! [X0,X1,X2] : ((k2_zfmisc_1(X0,X1) = X2 | ? [X3] : ((! [X4,X5] : (k4_tarski(X4,X5) != X3 | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X0)) | ~r2_hidden(X3,X2)) & (? [X6,X7] : (k4_tarski(X6,X7) = X3 & r2_hidden(X7,X1) & r2_hidden(X6,X0)) | r2_hidden(X3,X2)))) & (! [X8] : ((r2_hidden(X8,X2) | ! [X9,X10] : (k4_tarski(X9,X10) != X8 | ~r2_hidden(X10,X1) | ~r2_hidden(X9,X0))) & (? [X11,X12] : (k4_tarski(X11,X12) = X8 & r2_hidden(X12,X1) & r2_hidden(X11,X0)) | ~r2_hidden(X8,X2))) | k2_zfmisc_1(X0,X1) != X2))),
% 19.91/2.99    inference(rectify,[],[f16])).
% 19.91/2.99  
% 19.91/2.99  fof(f20,plain,(
% 19.91/2.99    ! [X8,X1,X0] : (? [X11,X12] : (k4_tarski(X11,X12) = X8 & r2_hidden(X12,X1) & r2_hidden(X11,X0)) => (k4_tarski(sK4(X0,X1,X8),sK5(X0,X1,X8)) = X8 & r2_hidden(sK5(X0,X1,X8),X1) & r2_hidden(sK4(X0,X1,X8),X0)))),
% 19.91/2.99    introduced(choice_axiom,[])).
% 19.91/2.99  
% 19.91/2.99  fof(f19,plain,(
% 19.91/2.99    ( ! [X3] : (! [X2,X1,X0] : (? [X6,X7] : (k4_tarski(X6,X7) = X3 & r2_hidden(X7,X1) & r2_hidden(X6,X0)) => (k4_tarski(sK2(X0,X1,X2),sK3(X0,X1,X2)) = X3 & r2_hidden(sK3(X0,X1,X2),X1) & r2_hidden(sK2(X0,X1,X2),X0)))) )),
% 19.91/2.99    introduced(choice_axiom,[])).
% 19.91/2.99  
% 19.91/2.99  fof(f18,plain,(
% 19.91/2.99    ! [X2,X1,X0] : (? [X3] : ((! [X4,X5] : (k4_tarski(X4,X5) != X3 | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X0)) | ~r2_hidden(X3,X2)) & (? [X6,X7] : (k4_tarski(X6,X7) = X3 & r2_hidden(X7,X1) & r2_hidden(X6,X0)) | r2_hidden(X3,X2))) => ((! [X5,X4] : (k4_tarski(X4,X5) != sK1(X0,X1,X2) | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X0)) | ~r2_hidden(sK1(X0,X1,X2),X2)) & (? [X7,X6] : (k4_tarski(X6,X7) = sK1(X0,X1,X2) & r2_hidden(X7,X1) & r2_hidden(X6,X0)) | r2_hidden(sK1(X0,X1,X2),X2))))),
% 19.91/2.99    introduced(choice_axiom,[])).
% 19.91/2.99  
% 19.91/2.99  fof(f21,plain,(
% 19.91/2.99    ! [X0,X1,X2] : ((k2_zfmisc_1(X0,X1) = X2 | ((! [X4,X5] : (k4_tarski(X4,X5) != sK1(X0,X1,X2) | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X0)) | ~r2_hidden(sK1(X0,X1,X2),X2)) & ((k4_tarski(sK2(X0,X1,X2),sK3(X0,X1,X2)) = sK1(X0,X1,X2) & r2_hidden(sK3(X0,X1,X2),X1) & r2_hidden(sK2(X0,X1,X2),X0)) | r2_hidden(sK1(X0,X1,X2),X2)))) & (! [X8] : ((r2_hidden(X8,X2) | ! [X9,X10] : (k4_tarski(X9,X10) != X8 | ~r2_hidden(X10,X1) | ~r2_hidden(X9,X0))) & ((k4_tarski(sK4(X0,X1,X8),sK5(X0,X1,X8)) = X8 & r2_hidden(sK5(X0,X1,X8),X1) & r2_hidden(sK4(X0,X1,X8),X0)) | ~r2_hidden(X8,X2))) | k2_zfmisc_1(X0,X1) != X2))),
% 19.91/2.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4,sK5])],[f17,f20,f19,f18])).
% 19.91/2.99  
% 19.91/2.99  fof(f41,plain,(
% 19.91/2.99    ( ! [X2,X0,X1] : (k2_zfmisc_1(X0,X1) = X2 | r2_hidden(sK2(X0,X1,X2),X0) | r2_hidden(sK1(X0,X1,X2),X2)) )),
% 19.91/2.99    inference(cnf_transformation,[],[f21])).
% 19.91/2.99  
% 19.91/2.99  fof(f5,axiom,(
% 19.91/2.99    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0),
% 19.91/2.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.91/2.99  
% 19.91/2.99  fof(f35,plain,(
% 19.91/2.99    ( ! [X0] : (k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0) )),
% 19.91/2.99    inference(cnf_transformation,[],[f5])).
% 19.91/2.99  
% 19.91/2.99  fof(f1,axiom,(
% 19.91/2.99    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 19.91/2.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.91/2.99  
% 19.91/2.99  fof(f26,plain,(
% 19.91/2.99    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 19.91/2.99    inference(cnf_transformation,[],[f1])).
% 19.91/2.99  
% 19.91/2.99  fof(f3,axiom,(
% 19.91/2.99    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 19.91/2.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.91/2.99  
% 19.91/2.99  fof(f11,plain,(
% 19.91/2.99    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : (((r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 19.91/2.99    inference(nnf_transformation,[],[f3])).
% 19.91/2.99  
% 19.91/2.99  fof(f12,plain,(
% 19.91/2.99    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 19.91/2.99    inference(flattening,[],[f11])).
% 19.91/2.99  
% 19.91/2.99  fof(f13,plain,(
% 19.91/2.99    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 19.91/2.99    inference(rectify,[],[f12])).
% 19.91/2.99  
% 19.91/2.99  fof(f14,plain,(
% 19.91/2.99    ! [X2,X1,X0] : (? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((r2_hidden(sK0(X0,X1,X2),X1) | ~r2_hidden(sK0(X0,X1,X2),X0) | ~r2_hidden(sK0(X0,X1,X2),X2)) & ((~r2_hidden(sK0(X0,X1,X2),X1) & r2_hidden(sK0(X0,X1,X2),X0)) | r2_hidden(sK0(X0,X1,X2),X2))))),
% 19.91/2.99    introduced(choice_axiom,[])).
% 19.91/2.99  
% 19.91/2.99  fof(f15,plain,(
% 19.91/2.99    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ((r2_hidden(sK0(X0,X1,X2),X1) | ~r2_hidden(sK0(X0,X1,X2),X0) | ~r2_hidden(sK0(X0,X1,X2),X2)) & ((~r2_hidden(sK0(X0,X1,X2),X1) & r2_hidden(sK0(X0,X1,X2),X0)) | r2_hidden(sK0(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 19.91/2.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f13,f14])).
% 19.91/2.99  
% 19.91/2.99  fof(f29,plain,(
% 19.91/2.99    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 19.91/2.99    inference(cnf_transformation,[],[f15])).
% 19.91/2.99  
% 19.91/2.99  fof(f4,axiom,(
% 19.91/2.99    ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1)),
% 19.91/2.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.91/2.99  
% 19.91/2.99  fof(f34,plain,(
% 19.91/2.99    ( ! [X0,X1] : (k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1)) )),
% 19.91/2.99    inference(cnf_transformation,[],[f4])).
% 19.91/2.99  
% 19.91/2.99  fof(f52,plain,(
% 19.91/2.99    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X2) )),
% 19.91/2.99    inference(definition_unfolding,[],[f29,f34])).
% 19.91/2.99  
% 19.91/2.99  fof(f55,plain,(
% 19.91/2.99    ( ! [X4,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,k5_xboole_0(X0,k3_xboole_0(X0,X1)))) )),
% 19.91/2.99    inference(equality_resolution,[],[f52])).
% 19.91/2.99  
% 19.91/2.99  fof(f6,axiom,(
% 19.91/2.99    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 19.91/2.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.91/2.99  
% 19.91/2.99  fof(f36,plain,(
% 19.91/2.99    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 19.91/2.99    inference(cnf_transformation,[],[f6])).
% 19.91/2.99  
% 19.91/2.99  fof(f2,axiom,(
% 19.91/2.99    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)),
% 19.91/2.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.91/2.99  
% 19.91/2.99  fof(f27,plain,(
% 19.91/2.99    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)) )),
% 19.91/2.99    inference(cnf_transformation,[],[f2])).
% 19.91/2.99  
% 19.91/2.99  fof(f40,plain,(
% 19.91/2.99    ( ! [X2,X0,X10,X8,X1,X9] : (r2_hidden(X8,X2) | k4_tarski(X9,X10) != X8 | ~r2_hidden(X10,X1) | ~r2_hidden(X9,X0) | k2_zfmisc_1(X0,X1) != X2) )),
% 19.91/2.99    inference(cnf_transformation,[],[f21])).
% 19.91/2.99  
% 19.91/2.99  fof(f57,plain,(
% 19.91/2.99    ( ! [X2,X0,X10,X1,X9] : (r2_hidden(k4_tarski(X9,X10),X2) | ~r2_hidden(X10,X1) | ~r2_hidden(X9,X0) | k2_zfmisc_1(X0,X1) != X2) )),
% 19.91/2.99    inference(equality_resolution,[],[f40])).
% 19.91/2.99  
% 19.91/2.99  fof(f58,plain,(
% 19.91/2.99    ( ! [X0,X10,X1,X9] : (r2_hidden(k4_tarski(X9,X10),k2_zfmisc_1(X0,X1)) | ~r2_hidden(X10,X1) | ~r2_hidden(X9,X0)) )),
% 19.91/2.99    inference(equality_resolution,[],[f57])).
% 19.91/2.99  
% 19.91/2.99  fof(f38,plain,(
% 19.91/2.99    ( ! [X2,X0,X8,X1] : (r2_hidden(sK5(X0,X1,X8),X1) | ~r2_hidden(X8,X2) | k2_zfmisc_1(X0,X1) != X2) )),
% 19.91/2.99    inference(cnf_transformation,[],[f21])).
% 19.91/2.99  
% 19.91/2.99  fof(f60,plain,(
% 19.91/2.99    ( ! [X0,X8,X1] : (r2_hidden(sK5(X0,X1,X8),X1) | ~r2_hidden(X8,k2_zfmisc_1(X0,X1))) )),
% 19.91/2.99    inference(equality_resolution,[],[f38])).
% 19.91/2.99  
% 19.91/2.99  fof(f37,plain,(
% 19.91/2.99    ( ! [X2,X0,X8,X1] : (r2_hidden(sK4(X0,X1,X8),X0) | ~r2_hidden(X8,X2) | k2_zfmisc_1(X0,X1) != X2) )),
% 19.91/2.99    inference(cnf_transformation,[],[f21])).
% 19.91/2.99  
% 19.91/2.99  fof(f61,plain,(
% 19.91/2.99    ( ! [X0,X8,X1] : (r2_hidden(sK4(X0,X1,X8),X0) | ~r2_hidden(X8,k2_zfmisc_1(X0,X1))) )),
% 19.91/2.99    inference(equality_resolution,[],[f37])).
% 19.91/2.99  
% 19.91/2.99  fof(f28,plain,(
% 19.91/2.99    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 19.91/2.99    inference(cnf_transformation,[],[f15])).
% 19.91/2.99  
% 19.91/2.99  fof(f53,plain,(
% 19.91/2.99    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,X2) | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X2) )),
% 19.91/2.99    inference(definition_unfolding,[],[f28,f34])).
% 19.91/2.99  
% 19.91/2.99  fof(f56,plain,(
% 19.91/2.99    ( ! [X4,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,k5_xboole_0(X0,k3_xboole_0(X0,X1)))) )),
% 19.91/2.99    inference(equality_resolution,[],[f53])).
% 19.91/2.99  
% 19.91/2.99  fof(f8,conjecture,(
% 19.91/2.99    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 19.91/2.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.91/2.99  
% 19.91/2.99  fof(f9,negated_conjecture,(
% 19.91/2.99    ~! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 19.91/2.99    inference(negated_conjecture,[],[f8])).
% 19.91/2.99  
% 19.91/2.99  fof(f10,plain,(
% 19.91/2.99    ? [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <~> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 19.91/2.99    inference(ennf_transformation,[],[f9])).
% 19.91/2.99  
% 19.91/2.99  fof(f22,plain,(
% 19.91/2.99    ? [X0,X1] : (((k1_xboole_0 != X1 & k1_xboole_0 != X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 = k2_zfmisc_1(X0,X1)))),
% 19.91/2.99    inference(nnf_transformation,[],[f10])).
% 19.91/2.99  
% 19.91/2.99  fof(f23,plain,(
% 19.91/2.99    ? [X0,X1] : (((k1_xboole_0 != X1 & k1_xboole_0 != X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 = k2_zfmisc_1(X0,X1)))),
% 19.91/2.99    inference(flattening,[],[f22])).
% 19.91/2.99  
% 19.91/2.99  fof(f24,plain,(
% 19.91/2.99    ? [X0,X1] : (((k1_xboole_0 != X1 & k1_xboole_0 != X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 = k2_zfmisc_1(X0,X1))) => (((k1_xboole_0 != sK7 & k1_xboole_0 != sK6) | k1_xboole_0 != k2_zfmisc_1(sK6,sK7)) & (k1_xboole_0 = sK7 | k1_xboole_0 = sK6 | k1_xboole_0 = k2_zfmisc_1(sK6,sK7)))),
% 19.91/2.99    introduced(choice_axiom,[])).
% 19.91/2.99  
% 19.91/2.99  fof(f25,plain,(
% 19.91/2.99    ((k1_xboole_0 != sK7 & k1_xboole_0 != sK6) | k1_xboole_0 != k2_zfmisc_1(sK6,sK7)) & (k1_xboole_0 = sK7 | k1_xboole_0 = sK6 | k1_xboole_0 = k2_zfmisc_1(sK6,sK7))),
% 19.91/2.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7])],[f23,f24])).
% 19.91/2.99  
% 19.91/2.99  fof(f45,plain,(
% 19.91/2.99    k1_xboole_0 = sK7 | k1_xboole_0 = sK6 | k1_xboole_0 = k2_zfmisc_1(sK6,sK7)),
% 19.91/2.99    inference(cnf_transformation,[],[f25])).
% 19.91/2.99  
% 19.91/2.99  fof(f31,plain,(
% 19.91/2.99    ( ! [X2,X0,X1] : (k4_xboole_0(X0,X1) = X2 | r2_hidden(sK0(X0,X1,X2),X0) | r2_hidden(sK0(X0,X1,X2),X2)) )),
% 19.91/2.99    inference(cnf_transformation,[],[f15])).
% 19.91/2.99  
% 19.91/2.99  fof(f50,plain,(
% 19.91/2.99    ( ! [X2,X0,X1] : (k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X2 | r2_hidden(sK0(X0,X1,X2),X0) | r2_hidden(sK0(X0,X1,X2),X2)) )),
% 19.91/2.99    inference(definition_unfolding,[],[f31,f34])).
% 19.91/2.99  
% 19.91/2.99  fof(f32,plain,(
% 19.91/2.99    ( ! [X2,X0,X1] : (k4_xboole_0(X0,X1) = X2 | ~r2_hidden(sK0(X0,X1,X2),X1) | r2_hidden(sK0(X0,X1,X2),X2)) )),
% 19.91/2.99    inference(cnf_transformation,[],[f15])).
% 19.91/2.99  
% 19.91/2.99  fof(f49,plain,(
% 19.91/2.99    ( ! [X2,X0,X1] : (k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X2 | ~r2_hidden(sK0(X0,X1,X2),X1) | r2_hidden(sK0(X0,X1,X2),X2)) )),
% 19.91/2.99    inference(definition_unfolding,[],[f32,f34])).
% 19.91/2.99  
% 19.91/2.99  fof(f46,plain,(
% 19.91/2.99    k1_xboole_0 != sK6 | k1_xboole_0 != k2_zfmisc_1(sK6,sK7)),
% 19.91/2.99    inference(cnf_transformation,[],[f25])).
% 19.91/2.99  
% 19.91/2.99  fof(f47,plain,(
% 19.91/2.99    k1_xboole_0 != sK7 | k1_xboole_0 != k2_zfmisc_1(sK6,sK7)),
% 19.91/2.99    inference(cnf_transformation,[],[f25])).
% 19.91/2.99  
% 19.91/2.99  fof(f42,plain,(
% 19.91/2.99    ( ! [X2,X0,X1] : (k2_zfmisc_1(X0,X1) = X2 | r2_hidden(sK3(X0,X1,X2),X1) | r2_hidden(sK1(X0,X1,X2),X2)) )),
% 19.91/2.99    inference(cnf_transformation,[],[f21])).
% 19.91/2.99  
% 19.91/2.99  cnf(c_13,plain,
% 19.91/2.99      ( r2_hidden(sK2(X0,X1,X2),X0)
% 19.91/2.99      | r2_hidden(sK1(X0,X1,X2),X2)
% 19.91/2.99      | k2_zfmisc_1(X0,X1) = X2 ),
% 19.91/2.99      inference(cnf_transformation,[],[f41]) ).
% 19.91/2.99  
% 19.91/2.99  cnf(c_408,plain,
% 19.91/2.99      ( k2_zfmisc_1(X0,X1) = X2
% 19.91/2.99      | r2_hidden(sK2(X0,X1,X2),X0) = iProver_top
% 19.91/2.99      | r2_hidden(sK1(X0,X1,X2),X2) = iProver_top ),
% 19.91/2.99      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 19.91/2.99  
% 19.91/2.99  cnf(c_8,plain,
% 19.91/2.99      ( k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
% 19.91/2.99      inference(cnf_transformation,[],[f35]) ).
% 19.91/2.99  
% 19.91/2.99  cnf(c_0,plain,
% 19.91/2.99      ( k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
% 19.91/2.99      inference(cnf_transformation,[],[f26]) ).
% 19.91/2.99  
% 19.91/2.99  cnf(c_567,plain,
% 19.91/2.99      ( k3_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
% 19.91/2.99      inference(superposition,[status(thm)],[c_8,c_0]) ).
% 19.91/2.99  
% 19.91/2.99  cnf(c_6,plain,
% 19.91/2.99      ( ~ r2_hidden(X0,X1)
% 19.91/2.99      | ~ r2_hidden(X0,k5_xboole_0(X2,k3_xboole_0(X2,X1))) ),
% 19.91/2.99      inference(cnf_transformation,[],[f55]) ).
% 19.91/2.99  
% 19.91/2.99  cnf(c_413,plain,
% 19.91/2.99      ( r2_hidden(X0,X1) != iProver_top
% 19.91/2.99      | r2_hidden(X0,k5_xboole_0(X2,k3_xboole_0(X2,X1))) != iProver_top ),
% 19.91/2.99      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 19.91/2.99  
% 19.91/2.99  cnf(c_910,plain,
% 19.91/2.99      ( r2_hidden(X0,X1) != iProver_top
% 19.91/2.99      | r2_hidden(X0,k5_xboole_0(k1_xboole_0,k1_xboole_0)) != iProver_top ),
% 19.91/2.99      inference(superposition,[status(thm)],[c_567,c_413]) ).
% 19.91/2.99  
% 19.91/2.99  cnf(c_9,plain,
% 19.91/2.99      ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
% 19.91/2.99      inference(cnf_transformation,[],[f36]) ).
% 19.91/2.99  
% 19.91/2.99  cnf(c_1,plain,
% 19.91/2.99      ( k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
% 19.91/2.99      inference(cnf_transformation,[],[f27]) ).
% 19.91/2.99  
% 19.91/2.99  cnf(c_682,plain,
% 19.91/2.99      ( k5_xboole_0(k1_xboole_0,X0) = X0 ),
% 19.91/2.99      inference(superposition,[status(thm)],[c_9,c_1]) ).
% 19.91/2.99  
% 19.91/2.99  cnf(c_913,plain,
% 19.91/2.99      ( r2_hidden(X0,X1) != iProver_top
% 19.91/2.99      | r2_hidden(X0,k1_xboole_0) != iProver_top ),
% 19.91/2.99      inference(demodulation,[status(thm)],[c_910,c_682]) ).
% 19.91/2.99  
% 19.91/2.99  cnf(c_1572,plain,
% 19.91/2.99      ( k2_zfmisc_1(X0,X1) = X2
% 19.91/2.99      | r2_hidden(sK2(X0,X1,X2),X0) = iProver_top
% 19.91/2.99      | r2_hidden(sK1(X0,X1,X2),k1_xboole_0) != iProver_top ),
% 19.91/2.99      inference(superposition,[status(thm)],[c_408,c_913]) ).
% 19.91/2.99  
% 19.91/2.99  cnf(c_14,plain,
% 19.91/2.99      ( ~ r2_hidden(X0,X1)
% 19.91/2.99      | ~ r2_hidden(X2,X3)
% 19.91/2.99      | r2_hidden(k4_tarski(X2,X0),k2_zfmisc_1(X3,X1)) ),
% 19.91/2.99      inference(cnf_transformation,[],[f58]) ).
% 19.91/2.99  
% 19.91/2.99  cnf(c_407,plain,
% 19.91/2.99      ( r2_hidden(X0,X1) != iProver_top
% 19.91/2.99      | r2_hidden(X2,X3) != iProver_top
% 19.91/2.99      | r2_hidden(k4_tarski(X2,X0),k2_zfmisc_1(X3,X1)) = iProver_top ),
% 19.91/2.99      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 19.91/2.99  
% 19.91/2.99  cnf(c_16,plain,
% 19.91/2.99      ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) | r2_hidden(sK5(X1,X2,X0),X2) ),
% 19.91/2.99      inference(cnf_transformation,[],[f60]) ).
% 19.91/2.99  
% 19.91/2.99  cnf(c_405,plain,
% 19.91/2.99      ( r2_hidden(X0,k2_zfmisc_1(X1,X2)) != iProver_top
% 19.91/2.99      | r2_hidden(sK5(X1,X2,X0),X2) = iProver_top ),
% 19.91/2.99      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 19.91/2.99  
% 19.91/2.99  cnf(c_1067,plain,
% 19.91/2.99      ( r2_hidden(X0,k2_zfmisc_1(X1,X2)) != iProver_top
% 19.91/2.99      | r2_hidden(sK5(X1,X2,X0),k1_xboole_0) != iProver_top ),
% 19.91/2.99      inference(superposition,[status(thm)],[c_405,c_913]) ).
% 19.91/2.99  
% 19.91/2.99  cnf(c_1176,plain,
% 19.91/2.99      ( r2_hidden(X0,k2_zfmisc_1(X1,k1_xboole_0)) != iProver_top ),
% 19.91/2.99      inference(superposition,[status(thm)],[c_405,c_1067]) ).
% 19.91/2.99  
% 19.91/2.99  cnf(c_1535,plain,
% 19.91/2.99      ( r2_hidden(X0,X1) != iProver_top
% 19.91/2.99      | r2_hidden(X2,k1_xboole_0) != iProver_top ),
% 19.91/2.99      inference(superposition,[status(thm)],[c_407,c_1176]) ).
% 19.91/2.99  
% 19.91/2.99  cnf(c_19401,plain,
% 19.91/2.99      ( k2_zfmisc_1(X0,X1) = X2
% 19.91/2.99      | r2_hidden(sK1(X0,X1,X2),k1_xboole_0) != iProver_top ),
% 19.91/2.99      inference(forward_subsumption_resolution,[status(thm)],[c_1572,c_1535]) ).
% 19.91/2.99  
% 19.91/2.99  cnf(c_19407,plain,
% 19.91/2.99      ( k2_zfmisc_1(X0,X1) = k1_xboole_0
% 19.91/2.99      | r2_hidden(sK2(X0,X1,k1_xboole_0),X0) = iProver_top ),
% 19.91/2.99      inference(superposition,[status(thm)],[c_408,c_19401]) ).
% 19.91/2.99  
% 19.91/2.99  cnf(c_17,plain,
% 19.91/2.99      ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) | r2_hidden(sK4(X1,X2,X0),X1) ),
% 19.91/2.99      inference(cnf_transformation,[],[f61]) ).
% 19.91/2.99  
% 19.91/2.99  cnf(c_404,plain,
% 19.91/2.99      ( r2_hidden(X0,k2_zfmisc_1(X1,X2)) != iProver_top
% 19.91/2.99      | r2_hidden(sK4(X1,X2,X0),X1) = iProver_top ),
% 19.91/2.99      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 19.91/2.99  
% 19.91/2.99  cnf(c_7,plain,
% 19.91/2.99      ( r2_hidden(X0,X1) | ~ r2_hidden(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) ),
% 19.91/2.99      inference(cnf_transformation,[],[f56]) ).
% 19.91/2.99  
% 19.91/2.99  cnf(c_412,plain,
% 19.91/2.99      ( r2_hidden(X0,X1) = iProver_top
% 19.91/2.99      | r2_hidden(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) != iProver_top ),
% 19.91/2.99      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 19.91/2.99  
% 19.91/2.99  cnf(c_743,plain,
% 19.91/2.99      ( r2_hidden(X0,X1) = iProver_top
% 19.91/2.99      | r2_hidden(X0,k5_xboole_0(X1,k3_xboole_0(X2,X1))) != iProver_top ),
% 19.91/2.99      inference(superposition,[status(thm)],[c_0,c_412]) ).
% 19.91/2.99  
% 19.91/2.99  cnf(c_888,plain,
% 19.91/2.99      ( r2_hidden(X0,k2_zfmisc_1(X1,k5_xboole_0(X2,k3_xboole_0(X3,X2)))) != iProver_top
% 19.91/2.99      | r2_hidden(sK5(X1,k5_xboole_0(X2,k3_xboole_0(X3,X2)),X0),X2) = iProver_top ),
% 19.91/2.99      inference(superposition,[status(thm)],[c_405,c_743]) ).
% 19.91/2.99  
% 19.91/2.99  cnf(c_12130,plain,
% 19.91/2.99      ( r2_hidden(X0,k2_zfmisc_1(X1,k5_xboole_0(X2,k3_xboole_0(X3,X2)))) != iProver_top
% 19.91/2.99      | r2_hidden(sK5(X1,k5_xboole_0(X2,k3_xboole_0(X2,X3)),X0),X2) = iProver_top ),
% 19.91/2.99      inference(superposition,[status(thm)],[c_0,c_888]) ).
% 19.91/2.99  
% 19.91/2.99  cnf(c_904,plain,
% 19.91/2.99      ( r2_hidden(X0,k2_zfmisc_1(X1,k5_xboole_0(X2,k3_xboole_0(X2,X3)))) != iProver_top
% 19.91/2.99      | r2_hidden(sK5(X1,k5_xboole_0(X2,k3_xboole_0(X2,X3)),X0),X3) != iProver_top ),
% 19.91/2.99      inference(superposition,[status(thm)],[c_405,c_413]) ).
% 19.91/2.99  
% 19.91/2.99  cnf(c_12815,plain,
% 19.91/2.99      ( r2_hidden(X0,k2_zfmisc_1(X1,k5_xboole_0(X2,k3_xboole_0(X2,X2)))) != iProver_top ),
% 19.91/2.99      inference(superposition,[status(thm)],[c_12130,c_904]) ).
% 19.91/2.99  
% 19.91/2.99  cnf(c_13029,plain,
% 19.91/2.99      ( r2_hidden(X0,k2_zfmisc_1(k2_zfmisc_1(X1,k5_xboole_0(X2,k3_xboole_0(X2,X2))),X3)) != iProver_top ),
% 19.91/2.99      inference(superposition,[status(thm)],[c_404,c_12815]) ).
% 19.91/2.99  
% 19.91/2.99  cnf(c_19871,plain,
% 19.91/2.99      ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,k5_xboole_0(X1,k3_xboole_0(X1,X1))),X2),X3) = k1_xboole_0 ),
% 19.91/2.99      inference(superposition,[status(thm)],[c_19407,c_13029]) ).
% 19.91/2.99  
% 19.91/2.99  cnf(c_13831,plain,
% 19.91/2.99      ( r2_hidden(X0,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,k5_xboole_0(X2,k3_xboole_0(X2,X2))),X3),X4)) != iProver_top ),
% 19.91/2.99      inference(superposition,[status(thm)],[c_404,c_13029]) ).
% 19.91/2.99  
% 19.91/2.99  cnf(c_19874,plain,
% 19.91/2.99      ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,k5_xboole_0(X1,k3_xboole_0(X1,X1))),X2),X3),X4) = k1_xboole_0 ),
% 19.91/2.99      inference(superposition,[status(thm)],[c_19407,c_13831]) ).
% 19.91/2.99  
% 19.91/2.99  cnf(c_19882,plain,
% 19.91/2.99      ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
% 19.91/2.99      inference(demodulation,[status(thm)],[c_19871,c_19874]) ).
% 19.91/2.99  
% 19.91/2.99  cnf(c_20,negated_conjecture,
% 19.91/2.99      ( k1_xboole_0 = k2_zfmisc_1(sK6,sK7)
% 19.91/2.99      | k1_xboole_0 = sK6
% 19.91/2.99      | k1_xboole_0 = sK7 ),
% 19.91/2.99      inference(cnf_transformation,[],[f45]) ).
% 19.91/2.99  
% 19.91/2.99  cnf(c_1532,plain,
% 19.91/2.99      ( sK6 = k1_xboole_0
% 19.91/2.99      | sK7 = k1_xboole_0
% 19.91/2.99      | r2_hidden(X0,sK6) != iProver_top
% 19.91/2.99      | r2_hidden(X1,sK7) != iProver_top
% 19.91/2.99      | r2_hidden(k4_tarski(X0,X1),k1_xboole_0) = iProver_top ),
% 19.91/2.99      inference(superposition,[status(thm)],[c_20,c_407]) ).
% 19.91/2.99  
% 19.91/2.99  cnf(c_1558,plain,
% 19.91/2.99      ( sK6 = k1_xboole_0
% 19.91/2.99      | sK7 = k1_xboole_0
% 19.91/2.99      | r2_hidden(X0,sK6) != iProver_top
% 19.91/2.99      | r2_hidden(X1,sK7) != iProver_top ),
% 19.91/2.99      inference(forward_subsumption_resolution,[status(thm)],[c_1532,c_1535]) ).
% 19.91/2.99  
% 19.91/2.99  cnf(c_1946,plain,
% 19.91/2.99      ( sK6 = k1_xboole_0
% 19.91/2.99      | sK7 = k1_xboole_0
% 19.91/2.99      | r2_hidden(X0,k2_zfmisc_1(X1,sK7)) != iProver_top
% 19.91/2.99      | r2_hidden(X2,sK6) != iProver_top ),
% 19.91/2.99      inference(superposition,[status(thm)],[c_405,c_1558]) ).
% 19.91/2.99  
% 19.91/2.99  cnf(c_2631,plain,
% 19.91/2.99      ( sK6 = k1_xboole_0
% 19.91/2.99      | sK7 = k1_xboole_0
% 19.91/2.99      | r2_hidden(X0,sK6) != iProver_top
% 19.91/2.99      | r2_hidden(X1,k1_xboole_0) != iProver_top ),
% 19.91/2.99      inference(superposition,[status(thm)],[c_20,c_1946]) ).
% 19.91/2.99  
% 19.91/2.99  cnf(c_2728,plain,
% 19.91/2.99      ( sK6 = k1_xboole_0
% 19.91/2.99      | sK7 = k1_xboole_0
% 19.91/2.99      | r2_hidden(X0,k2_zfmisc_1(sK6,X1)) != iProver_top
% 19.91/2.99      | r2_hidden(X2,k1_xboole_0) != iProver_top ),
% 19.91/2.99      inference(superposition,[status(thm)],[c_404,c_2631]) ).
% 19.91/2.99  
% 19.91/2.99  cnf(c_3999,plain,
% 19.91/2.99      ( sK6 = k1_xboole_0
% 19.91/2.99      | sK7 = k1_xboole_0
% 19.91/2.99      | r2_hidden(X0,k1_xboole_0) != iProver_top
% 19.91/2.99      | r2_hidden(X1,k1_xboole_0) != iProver_top ),
% 19.91/2.99      inference(superposition,[status(thm)],[c_20,c_2728]) ).
% 19.91/2.99  
% 19.91/2.99  cnf(c_4139,plain,
% 19.91/2.99      ( sK6 = k1_xboole_0
% 19.91/2.99      | sK7 = k1_xboole_0
% 19.91/2.99      | r2_hidden(X0,k2_zfmisc_1(k1_xboole_0,X1)) != iProver_top
% 19.91/2.99      | r2_hidden(X2,k1_xboole_0) != iProver_top ),
% 19.91/2.99      inference(superposition,[status(thm)],[c_404,c_3999]) ).
% 19.91/2.99  
% 19.91/2.99  cnf(c_4347,plain,
% 19.91/2.99      ( sK6 = k1_xboole_0
% 19.91/2.99      | sK7 = k1_xboole_0
% 19.91/2.99      | r2_hidden(X0,k2_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1),X2)) != iProver_top
% 19.91/2.99      | r2_hidden(X3,k1_xboole_0) != iProver_top ),
% 19.91/2.99      inference(superposition,[status(thm)],[c_404,c_4139]) ).
% 19.91/2.99  
% 19.91/2.99  cnf(c_45,plain,
% 19.91/2.99      ( k5_xboole_0(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
% 19.91/2.99      inference(instantiation,[status(thm)],[c_9]) ).
% 19.91/2.99  
% 19.91/2.99  cnf(c_46,plain,
% 19.91/2.99      ( k3_xboole_0(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
% 19.91/2.99      inference(instantiation,[status(thm)],[c_8]) ).
% 19.91/2.99  
% 19.91/2.99  cnf(c_173,plain,( X0 = X0 ),theory(equality) ).
% 19.91/2.99  
% 19.91/2.99  cnf(c_184,plain,
% 19.91/2.99      ( k1_xboole_0 = k1_xboole_0 ),
% 19.91/2.99      inference(instantiation,[status(thm)],[c_173]) ).
% 19.91/2.99  
% 19.91/2.99  cnf(c_574,plain,
% 19.91/2.99      ( sK7 = sK7 ),
% 19.91/2.99      inference(instantiation,[status(thm)],[c_173]) ).
% 19.91/2.99  
% 19.91/2.99  cnf(c_578,plain,
% 19.91/2.99      ( sK6 = sK6 ),
% 19.91/2.99      inference(instantiation,[status(thm)],[c_173]) ).
% 19.91/2.99  
% 19.91/2.99  cnf(c_174,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 19.91/2.99  
% 19.91/2.99  cnf(c_564,plain,
% 19.91/2.99      ( X0 != X1 | sK7 != X1 | sK7 = X0 ),
% 19.91/2.99      inference(instantiation,[status(thm)],[c_174]) ).
% 19.91/2.99  
% 19.91/2.99  cnf(c_573,plain,
% 19.91/2.99      ( X0 != sK7 | sK7 = X0 | sK7 != sK7 ),
% 19.91/2.99      inference(instantiation,[status(thm)],[c_564]) ).
% 19.91/2.99  
% 19.91/2.99  cnf(c_585,plain,
% 19.91/2.99      ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) != sK7
% 19.91/2.99      | sK7 = k5_xboole_0(X0,k3_xboole_0(X0,X1))
% 19.91/2.99      | sK7 != sK7 ),
% 19.91/2.99      inference(instantiation,[status(thm)],[c_573]) ).
% 19.91/2.99  
% 19.91/2.99  cnf(c_589,plain,
% 19.91/2.99      ( k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,k1_xboole_0)) != sK7
% 19.91/2.99      | sK7 = k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,k1_xboole_0))
% 19.91/2.99      | sK7 != sK7 ),
% 19.91/2.99      inference(instantiation,[status(thm)],[c_585]) ).
% 19.91/2.99  
% 19.91/2.99  cnf(c_572,plain,
% 19.91/2.99      ( X0 != X1 | sK6 != X1 | sK6 = X0 ),
% 19.91/2.99      inference(instantiation,[status(thm)],[c_174]) ).
% 19.91/2.99  
% 19.91/2.99  cnf(c_577,plain,
% 19.91/2.99      ( X0 != sK6 | sK6 = X0 | sK6 != sK6 ),
% 19.91/2.99      inference(instantiation,[status(thm)],[c_572]) ).
% 19.91/2.99  
% 19.91/2.99  cnf(c_623,plain,
% 19.91/2.99      ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) != sK6
% 19.91/2.99      | sK6 = k5_xboole_0(X0,k3_xboole_0(X0,X1))
% 19.91/2.99      | sK6 != sK6 ),
% 19.91/2.99      inference(instantiation,[status(thm)],[c_577]) ).
% 19.91/2.99  
% 19.91/2.99  cnf(c_627,plain,
% 19.91/2.99      ( k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,k1_xboole_0)) != sK6
% 19.91/2.99      | sK6 = k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,k1_xboole_0))
% 19.91/2.99      | sK6 != sK6 ),
% 19.91/2.99      inference(instantiation,[status(thm)],[c_623]) ).
% 19.91/2.99  
% 19.91/2.99  cnf(c_712,plain,
% 19.91/2.99      ( X0 != k5_xboole_0(X1,k3_xboole_0(X1,X2))
% 19.91/2.99      | sK7 = X0
% 19.91/2.99      | sK7 != k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
% 19.91/2.99      inference(instantiation,[status(thm)],[c_564]) ).
% 19.91/2.99  
% 19.91/2.99  cnf(c_713,plain,
% 19.91/2.99      ( sK7 != k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,k1_xboole_0))
% 19.91/2.99      | sK7 = k1_xboole_0
% 19.91/2.99      | k1_xboole_0 != k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,k1_xboole_0)) ),
% 19.91/2.99      inference(instantiation,[status(thm)],[c_712]) ).
% 19.91/2.99  
% 19.91/2.99  cnf(c_717,plain,
% 19.91/2.99      ( X0 != k5_xboole_0(X1,k3_xboole_0(X1,X2))
% 19.91/2.99      | sK6 = X0
% 19.91/2.99      | sK6 != k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
% 19.91/2.99      inference(instantiation,[status(thm)],[c_572]) ).
% 19.91/2.99  
% 19.91/2.99  cnf(c_718,plain,
% 19.91/2.99      ( sK6 != k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,k1_xboole_0))
% 19.91/2.99      | sK6 = k1_xboole_0
% 19.91/2.99      | k1_xboole_0 != k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,k1_xboole_0)) ),
% 19.91/2.99      inference(instantiation,[status(thm)],[c_717]) ).
% 19.91/2.99  
% 19.91/2.99  cnf(c_795,plain,
% 19.91/2.99      ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X2
% 19.91/2.99      | k1_xboole_0 != X2
% 19.91/2.99      | k1_xboole_0 = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
% 19.91/2.99      inference(instantiation,[status(thm)],[c_174]) ).
% 19.91/2.99  
% 19.91/2.99  cnf(c_1112,plain,
% 19.91/2.99      ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) != k5_xboole_0(X0,X2)
% 19.91/2.99      | k1_xboole_0 != k5_xboole_0(X0,X2)
% 19.91/2.99      | k1_xboole_0 = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
% 19.91/2.99      inference(instantiation,[status(thm)],[c_795]) ).
% 19.91/2.99  
% 19.91/2.99  cnf(c_1114,plain,
% 19.91/2.99      ( k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,k1_xboole_0)) != k5_xboole_0(k1_xboole_0,k1_xboole_0)
% 19.91/2.99      | k1_xboole_0 = k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,k1_xboole_0))
% 19.91/2.99      | k1_xboole_0 != k5_xboole_0(k1_xboole_0,k1_xboole_0) ),
% 19.91/2.99      inference(instantiation,[status(thm)],[c_1112]) ).
% 19.91/2.99  
% 19.91/2.99  cnf(c_176,plain,
% 19.91/2.99      ( X0 != X1 | k5_xboole_0(X2,X0) = k5_xboole_0(X2,X1) ),
% 19.91/2.99      theory(equality) ).
% 19.91/2.99  
% 19.91/2.99  cnf(c_1113,plain,
% 19.91/2.99      ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k5_xboole_0(X0,X2)
% 19.91/2.99      | k3_xboole_0(X0,X1) != X2 ),
% 19.91/2.99      inference(instantiation,[status(thm)],[c_176]) ).
% 19.91/2.99  
% 19.91/2.99  cnf(c_1115,plain,
% 19.91/2.99      ( k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,k1_xboole_0)) = k5_xboole_0(k1_xboole_0,k1_xboole_0)
% 19.91/2.99      | k3_xboole_0(k1_xboole_0,k1_xboole_0) != k1_xboole_0 ),
% 19.91/2.99      inference(instantiation,[status(thm)],[c_1113]) ).
% 19.91/2.99  
% 19.91/2.99  cnf(c_4721,plain,
% 19.91/2.99      ( k5_xboole_0(X0,X1) != X2
% 19.91/2.99      | k1_xboole_0 != X2
% 19.91/2.99      | k1_xboole_0 = k5_xboole_0(X0,X1) ),
% 19.91/2.99      inference(instantiation,[status(thm)],[c_174]) ).
% 19.91/2.99  
% 19.91/2.99  cnf(c_4722,plain,
% 19.91/2.99      ( k5_xboole_0(k1_xboole_0,k1_xboole_0) != k1_xboole_0
% 19.91/2.99      | k1_xboole_0 = k5_xboole_0(k1_xboole_0,k1_xboole_0)
% 19.91/2.99      | k1_xboole_0 != k1_xboole_0 ),
% 19.91/2.99      inference(instantiation,[status(thm)],[c_4721]) ).
% 19.91/2.99  
% 19.91/2.99  cnf(c_4,plain,
% 19.91/2.99      ( r2_hidden(sK0(X0,X1,X2),X0)
% 19.91/2.99      | r2_hidden(sK0(X0,X1,X2),X2)
% 19.91/2.99      | k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X2 ),
% 19.91/2.99      inference(cnf_transformation,[],[f50]) ).
% 19.91/2.99  
% 19.91/2.99  cnf(c_415,plain,
% 19.91/2.99      ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X2
% 19.91/2.99      | r2_hidden(sK0(X0,X1,X2),X0) = iProver_top
% 19.91/2.99      | r2_hidden(sK0(X0,X1,X2),X2) = iProver_top ),
% 19.91/2.99      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 19.91/2.99  
% 19.91/2.99  cnf(c_3,plain,
% 19.91/2.99      ( ~ r2_hidden(sK0(X0,X1,X2),X1)
% 19.91/2.99      | r2_hidden(sK0(X0,X1,X2),X2)
% 19.91/2.99      | k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X2 ),
% 19.91/2.99      inference(cnf_transformation,[],[f49]) ).
% 19.91/2.99  
% 19.91/2.99  cnf(c_416,plain,
% 19.91/2.99      ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X2
% 19.91/2.99      | r2_hidden(sK0(X0,X1,X2),X1) != iProver_top
% 19.91/2.99      | r2_hidden(sK0(X0,X1,X2),X2) = iProver_top ),
% 19.91/2.99      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 19.91/2.99  
% 19.91/2.99  cnf(c_3539,plain,
% 19.91/2.99      ( k5_xboole_0(X0,k3_xboole_0(X0,X0)) = X1
% 19.91/2.99      | r2_hidden(sK0(X0,X0,X1),X1) = iProver_top ),
% 19.91/2.99      inference(superposition,[status(thm)],[c_415,c_416]) ).
% 19.91/2.99  
% 19.91/2.99  cnf(c_11285,plain,
% 19.91/2.99      ( k5_xboole_0(X0,k3_xboole_0(X0,X0)) = sK7
% 19.91/2.99      | sK6 = k1_xboole_0
% 19.91/2.99      | sK7 = k1_xboole_0
% 19.91/2.99      | r2_hidden(X1,sK6) != iProver_top ),
% 19.91/2.99      inference(superposition,[status(thm)],[c_3539,c_1558]) ).
% 19.91/2.99  
% 19.91/2.99  cnf(c_11694,plain,
% 19.91/2.99      ( k5_xboole_0(X0,k3_xboole_0(X0,X0)) = sK6
% 19.91/2.99      | k5_xboole_0(X1,k3_xboole_0(X1,X1)) = sK7
% 19.91/2.99      | sK6 = k1_xboole_0
% 19.91/2.99      | sK7 = k1_xboole_0 ),
% 19.91/2.99      inference(superposition,[status(thm)],[c_3539,c_11285]) ).
% 19.91/2.99  
% 19.91/2.99  cnf(c_11902,plain,
% 19.91/2.99      ( k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,k1_xboole_0)) = sK6
% 19.91/2.99      | k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,k1_xboole_0)) = sK7
% 19.91/2.99      | sK6 = k1_xboole_0
% 19.91/2.99      | sK7 = k1_xboole_0 ),
% 19.91/2.99      inference(instantiation,[status(thm)],[c_11694]) ).
% 19.91/2.99  
% 19.91/2.99  cnf(c_11990,plain,
% 19.91/2.99      ( sK6 = k1_xboole_0 | sK7 = k1_xboole_0 ),
% 19.91/2.99      inference(global_propositional_subsumption,
% 19.91/2.99                [status(thm)],
% 19.91/2.99                [c_4347,c_45,c_46,c_184,c_574,c_578,c_589,c_627,c_713,c_718,
% 19.91/2.99                 c_1114,c_1115,c_4722,c_11902]) ).
% 19.91/2.99  
% 19.91/2.99  cnf(c_19,negated_conjecture,
% 19.91/2.99      ( k1_xboole_0 != k2_zfmisc_1(sK6,sK7) | k1_xboole_0 != sK6 ),
% 19.91/2.99      inference(cnf_transformation,[],[f46]) ).
% 19.91/2.99  
% 19.91/2.99  cnf(c_12004,plain,
% 19.91/2.99      ( k2_zfmisc_1(k1_xboole_0,sK7) != k1_xboole_0
% 19.91/2.99      | sK6 != k1_xboole_0
% 19.91/2.99      | sK7 = k1_xboole_0 ),
% 19.91/2.99      inference(superposition,[status(thm)],[c_11990,c_19]) ).
% 19.91/2.99  
% 19.91/2.99  cnf(c_12009,plain,
% 19.91/2.99      ( k2_zfmisc_1(k1_xboole_0,sK7) != k1_xboole_0 | sK7 = k1_xboole_0 ),
% 19.91/2.99      inference(forward_subsumption_resolution,[status(thm)],[c_12004,c_11990]) ).
% 19.91/2.99  
% 19.91/2.99  cnf(c_90590,plain,
% 19.91/2.99      ( sK7 = k1_xboole_0 | k1_xboole_0 != k1_xboole_0 ),
% 19.91/2.99      inference(demodulation,[status(thm)],[c_19882,c_12009]) ).
% 19.91/2.99  
% 19.91/2.99  cnf(c_90615,plain,
% 19.91/2.99      ( sK7 = k1_xboole_0 ),
% 19.91/2.99      inference(equality_resolution_simp,[status(thm)],[c_90590]) ).
% 19.91/2.99  
% 19.91/2.99  cnf(c_18,negated_conjecture,
% 19.91/2.99      ( k1_xboole_0 != k2_zfmisc_1(sK6,sK7) | k1_xboole_0 != sK7 ),
% 19.91/2.99      inference(cnf_transformation,[],[f47]) ).
% 19.91/2.99  
% 19.91/2.99  cnf(c_91013,plain,
% 19.91/2.99      ( k2_zfmisc_1(sK6,k1_xboole_0) != k1_xboole_0
% 19.91/2.99      | k1_xboole_0 != k1_xboole_0 ),
% 19.91/2.99      inference(demodulation,[status(thm)],[c_90615,c_18]) ).
% 19.91/2.99  
% 19.91/2.99  cnf(c_91014,plain,
% 19.91/2.99      ( k2_zfmisc_1(sK6,k1_xboole_0) != k1_xboole_0 ),
% 19.91/2.99      inference(equality_resolution_simp,[status(thm)],[c_91013]) ).
% 19.91/2.99  
% 19.91/2.99  cnf(c_12,plain,
% 19.91/2.99      ( r2_hidden(sK3(X0,X1,X2),X1)
% 19.91/2.99      | r2_hidden(sK1(X0,X1,X2),X2)
% 19.91/2.99      | k2_zfmisc_1(X0,X1) = X2 ),
% 19.91/2.99      inference(cnf_transformation,[],[f42]) ).
% 19.91/2.99  
% 19.91/2.99  cnf(c_409,plain,
% 19.91/2.99      ( k2_zfmisc_1(X0,X1) = X2
% 19.91/2.99      | r2_hidden(sK3(X0,X1,X2),X1) = iProver_top
% 19.91/2.99      | r2_hidden(sK1(X0,X1,X2),X2) = iProver_top ),
% 19.91/2.99      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 19.91/2.99  
% 19.91/2.99  cnf(c_19406,plain,
% 19.91/2.99      ( k2_zfmisc_1(X0,X1) = k1_xboole_0
% 19.91/2.99      | r2_hidden(sK3(X0,X1,k1_xboole_0),X1) = iProver_top ),
% 19.91/2.99      inference(superposition,[status(thm)],[c_409,c_19401]) ).
% 19.91/2.99  
% 19.91/2.99  cnf(c_19668,plain,
% 19.91/2.99      ( k2_zfmisc_1(X0,k2_zfmisc_1(k2_zfmisc_1(X1,k5_xboole_0(X2,k3_xboole_0(X2,X2))),X3)) = k1_xboole_0 ),
% 19.91/2.99      inference(superposition,[status(thm)],[c_19406,c_13029]) ).
% 19.91/2.99  
% 19.91/2.99  cnf(c_13830,plain,
% 19.91/2.99      ( r2_hidden(X0,k2_zfmisc_1(X1,k2_zfmisc_1(k2_zfmisc_1(X2,k5_xboole_0(X3,k3_xboole_0(X3,X3))),X4))) != iProver_top ),
% 19.91/2.99      inference(superposition,[status(thm)],[c_405,c_13029]) ).
% 19.91/2.99  
% 19.91/2.99  cnf(c_19670,plain,
% 19.91/2.99      ( k2_zfmisc_1(X0,k2_zfmisc_1(X1,k2_zfmisc_1(k2_zfmisc_1(X2,k5_xboole_0(X3,k3_xboole_0(X3,X3))),X4))) = k1_xboole_0 ),
% 19.91/2.99      inference(superposition,[status(thm)],[c_19406,c_13830]) ).
% 19.91/2.99  
% 19.91/2.99  cnf(c_19679,plain,
% 19.91/2.99      ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
% 19.91/2.99      inference(demodulation,[status(thm)],[c_19668,c_19670]) ).
% 19.91/2.99  
% 19.91/2.99  cnf(c_91016,plain,
% 19.91/2.99      ( k1_xboole_0 != k1_xboole_0 ),
% 19.91/2.99      inference(demodulation,[status(thm)],[c_91014,c_19679]) ).
% 19.91/2.99  
% 19.91/2.99  cnf(c_91017,plain,
% 19.91/2.99      ( $false ),
% 19.91/2.99      inference(equality_resolution_simp,[status(thm)],[c_91016]) ).
% 19.91/2.99  
% 19.91/2.99  
% 19.91/2.99  % SZS output end CNFRefutation for theBenchmark.p
% 19.91/2.99  
% 19.91/2.99  ------                               Statistics
% 19.91/2.99  
% 19.91/2.99  ------ General
% 19.91/2.99  
% 19.91/2.99  abstr_ref_over_cycles:                  0
% 19.91/2.99  abstr_ref_under_cycles:                 0
% 19.91/2.99  gc_basic_clause_elim:                   0
% 19.91/2.99  forced_gc_time:                         0
% 19.91/2.99  parsing_time:                           0.008
% 19.91/2.99  unif_index_cands_time:                  0.
% 19.91/2.99  unif_index_add_time:                    0.
% 19.91/2.99  orderings_time:                         0.
% 19.91/2.99  out_proof_time:                         0.011
% 19.91/2.99  total_time:                             2.385
% 19.91/2.99  num_of_symbols:                         45
% 19.91/2.99  num_of_terms:                           86593
% 19.91/2.99  
% 19.91/2.99  ------ Preprocessing
% 19.91/2.99  
% 19.91/2.99  num_of_splits:                          0
% 19.91/2.99  num_of_split_atoms:                     0
% 19.91/2.99  num_of_reused_defs:                     0
% 19.91/2.99  num_eq_ax_congr_red:                    40
% 19.91/2.99  num_of_sem_filtered_clauses:            1
% 19.91/2.99  num_of_subtypes:                        0
% 19.91/2.99  monotx_restored_types:                  0
% 19.91/2.99  sat_num_of_epr_types:                   0
% 19.91/2.99  sat_num_of_non_cyclic_types:            0
% 19.91/2.99  sat_guarded_non_collapsed_types:        0
% 19.91/2.99  num_pure_diseq_elim:                    0
% 19.91/2.99  simp_replaced_by:                       0
% 19.91/2.99  res_preprocessed:                       78
% 19.91/2.99  prep_upred:                             0
% 19.91/2.99  prep_unflattend:                        0
% 19.91/2.99  smt_new_axioms:                         0
% 19.91/2.99  pred_elim_cands:                        1
% 19.91/2.99  pred_elim:                              0
% 19.91/2.99  pred_elim_cl:                           0
% 19.91/2.99  pred_elim_cycles:                       1
% 19.91/2.99  merged_defs:                            0
% 19.91/2.99  merged_defs_ncl:                        0
% 19.91/2.99  bin_hyper_res:                          0
% 19.91/2.99  prep_cycles:                            3
% 19.91/2.99  pred_elim_time:                         0.
% 19.91/2.99  splitting_time:                         0.
% 19.91/2.99  sem_filter_time:                        0.
% 19.91/2.99  monotx_time:                            0.
% 19.91/2.99  subtype_inf_time:                       0.
% 19.91/2.99  
% 19.91/2.99  ------ Problem properties
% 19.91/2.99  
% 19.91/2.99  clauses:                                21
% 19.91/2.99  conjectures:                            3
% 19.91/2.99  epr:                                    0
% 19.91/2.99  horn:                                   13
% 19.91/2.99  ground:                                 3
% 19.91/2.99  unary:                                  4
% 19.91/2.99  binary:                                 7
% 19.91/2.99  lits:                                   51
% 19.91/2.99  lits_eq:                                21
% 19.91/2.99  fd_pure:                                0
% 19.91/2.99  fd_pseudo:                              0
% 19.91/2.99  fd_cond:                                0
% 19.91/2.99  fd_pseudo_cond:                         7
% 19.91/2.99  ac_symbols:                             0
% 19.91/2.99  
% 19.91/2.99  ------ Propositional Solver
% 19.91/2.99  
% 19.91/2.99  prop_solver_calls:                      27
% 19.91/2.99  prop_fast_solver_calls:                 3557
% 19.91/2.99  smt_solver_calls:                       0
% 19.91/2.99  smt_fast_solver_calls:                  0
% 19.91/2.99  prop_num_of_clauses:                    24540
% 19.91/2.99  prop_preprocess_simplified:             25667
% 19.91/2.99  prop_fo_subsumed:                       1029
% 19.91/2.99  prop_solver_time:                       0.
% 19.91/2.99  smt_solver_time:                        0.
% 19.91/2.99  smt_fast_solver_time:                   0.
% 19.91/2.99  prop_fast_solver_time:                  0.
% 19.91/2.99  prop_unsat_core_time:                   0.
% 19.91/2.99  
% 19.91/2.99  ------ QBF
% 19.91/2.99  
% 19.91/2.99  qbf_q_res:                              0
% 19.91/2.99  qbf_num_tautologies:                    0
% 19.91/2.99  qbf_prep_cycles:                        0
% 19.91/2.99  
% 19.91/2.99  ------ BMC1
% 19.91/2.99  
% 19.91/2.99  bmc1_current_bound:                     -1
% 19.91/2.99  bmc1_last_solved_bound:                 -1
% 19.91/2.99  bmc1_unsat_core_size:                   -1
% 19.91/2.99  bmc1_unsat_core_parents_size:           -1
% 19.91/2.99  bmc1_merge_next_fun:                    0
% 19.91/2.99  bmc1_unsat_core_clauses_time:           0.
% 19.91/2.99  
% 19.91/2.99  ------ Instantiation
% 19.91/2.99  
% 19.91/2.99  inst_num_of_clauses:                    3240
% 19.91/2.99  inst_num_in_passive:                    882
% 19.91/2.99  inst_num_in_active:                     1172
% 19.91/2.99  inst_num_in_unprocessed:                1186
% 19.91/2.99  inst_num_of_loops:                      1520
% 19.91/2.99  inst_num_of_learning_restarts:          0
% 19.91/2.99  inst_num_moves_active_passive:          343
% 19.91/2.99  inst_lit_activity:                      0
% 19.91/2.99  inst_lit_activity_moves:                0
% 19.91/2.99  inst_num_tautologies:                   0
% 19.91/2.99  inst_num_prop_implied:                  0
% 19.91/2.99  inst_num_existing_simplified:           0
% 19.91/2.99  inst_num_eq_res_simplified:             0
% 19.91/2.99  inst_num_child_elim:                    0
% 19.91/2.99  inst_num_of_dismatching_blockings:      2489
% 19.91/2.99  inst_num_of_non_proper_insts:           3433
% 19.91/2.99  inst_num_of_duplicates:                 0
% 19.91/2.99  inst_inst_num_from_inst_to_res:         0
% 19.91/2.99  inst_dismatching_checking_time:         0.
% 19.91/2.99  
% 19.91/2.99  ------ Resolution
% 19.91/2.99  
% 19.91/2.99  res_num_of_clauses:                     0
% 19.91/2.99  res_num_in_passive:                     0
% 19.91/2.99  res_num_in_active:                      0
% 19.91/2.99  res_num_of_loops:                       81
% 19.91/2.99  res_forward_subset_subsumed:            506
% 19.91/2.99  res_backward_subset_subsumed:           0
% 19.91/2.99  res_forward_subsumed:                   0
% 19.91/2.99  res_backward_subsumed:                  0
% 19.91/2.99  res_forward_subsumption_resolution:     0
% 19.91/2.99  res_backward_subsumption_resolution:    0
% 19.91/2.99  res_clause_to_clause_subsumption:       81099
% 19.91/2.99  res_orphan_elimination:                 0
% 19.91/2.99  res_tautology_del:                      421
% 19.91/2.99  res_num_eq_res_simplified:              0
% 19.91/2.99  res_num_sel_changes:                    0
% 19.91/2.99  res_moves_from_active_to_pass:          0
% 19.91/2.99  
% 19.91/2.99  ------ Superposition
% 19.91/2.99  
% 19.91/2.99  sup_time_total:                         0.
% 19.91/2.99  sup_time_generating:                    0.
% 19.91/2.99  sup_time_sim_full:                      0.
% 19.91/2.99  sup_time_sim_immed:                     0.
% 19.91/2.99  
% 19.91/2.99  sup_num_of_clauses:                     7074
% 19.91/2.99  sup_num_in_active:                      129
% 19.91/2.99  sup_num_in_passive:                     6945
% 19.91/2.99  sup_num_of_loops:                       302
% 19.91/2.99  sup_fw_superposition:                   6914
% 19.91/2.99  sup_bw_superposition:                   10191
% 19.91/2.99  sup_immediate_simplified:               3887
% 19.91/2.99  sup_given_eliminated:                   31
% 19.91/2.99  comparisons_done:                       0
% 19.91/2.99  comparisons_avoided:                    191
% 19.91/2.99  
% 19.91/2.99  ------ Simplifications
% 19.91/2.99  
% 19.91/2.99  
% 19.91/2.99  sim_fw_subset_subsumed:                 1966
% 19.91/2.99  sim_bw_subset_subsumed:                 75
% 19.91/2.99  sim_fw_subsumed:                        380
% 19.91/2.99  sim_bw_subsumed:                        315
% 19.91/2.99  sim_fw_subsumption_res:                 129
% 19.91/2.99  sim_bw_subsumption_res:                 1
% 19.91/2.99  sim_tautology_del:                      24
% 19.91/2.99  sim_eq_tautology_del:                   69
% 19.91/2.99  sim_eq_res_simp:                        3
% 19.91/2.99  sim_fw_demodulated:                     831
% 19.91/2.99  sim_bw_demodulated:                     548
% 19.91/2.99  sim_light_normalised:                   544
% 19.91/2.99  sim_joinable_taut:                      0
% 19.91/2.99  sim_joinable_simp:                      0
% 19.91/2.99  sim_ac_normalised:                      0
% 19.91/2.99  sim_smt_subsumption:                    0
% 19.91/2.99  
%------------------------------------------------------------------------------
