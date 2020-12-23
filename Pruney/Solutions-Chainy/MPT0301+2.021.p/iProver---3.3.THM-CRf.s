%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:36:58 EST 2020

% Result     : Theorem 11.53s
% Output     : CNFRefutation 11.53s
% Verified   : 
% Statistics : Number of formulae       :   95 ( 648 expanded)
%              Number of clauses        :   45 ( 254 expanded)
%              Number of leaves         :   16 ( 132 expanded)
%              Depth                    :   22
%              Number of atoms          :  380 (2812 expanded)
%              Number of equality atoms :  176 ( 909 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal clause size      :   18 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( k2_zfmisc_1(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ? [X4,X5] :
              ( k4_tarski(X4,X5) = X3
              & r2_hidden(X5,X1)
              & r2_hidden(X4,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
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
    inference(nnf_transformation,[],[f8])).

fof(f26,plain,(
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
    inference(rectify,[],[f25])).

fof(f29,plain,(
    ! [X8,X1,X0] :
      ( ? [X11,X12] :
          ( k4_tarski(X11,X12) = X8
          & r2_hidden(X12,X1)
          & r2_hidden(X11,X0) )
     => ( k4_tarski(sK5(X0,X1,X8),sK6(X0,X1,X8)) = X8
        & r2_hidden(sK6(X0,X1,X8),X1)
        & r2_hidden(sK5(X0,X1,X8),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X6,X7] :
          ( k4_tarski(X6,X7) = X3
          & r2_hidden(X7,X1)
          & r2_hidden(X6,X0) )
     => ( k4_tarski(sK3(X0,X1,X2),sK4(X0,X1,X2)) = X3
        & r2_hidden(sK4(X0,X1,X2),X1)
        & r2_hidden(sK3(X0,X1,X2),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,(
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
              ( k4_tarski(X4,X5) != sK2(X0,X1,X2)
              | ~ r2_hidden(X5,X1)
              | ~ r2_hidden(X4,X0) )
          | ~ r2_hidden(sK2(X0,X1,X2),X2) )
        & ( ? [X7,X6] :
              ( k4_tarski(X6,X7) = sK2(X0,X1,X2)
              & r2_hidden(X7,X1)
              & r2_hidden(X6,X0) )
          | r2_hidden(sK2(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( ( k2_zfmisc_1(X0,X1) = X2
        | ( ( ! [X4,X5] :
                ( k4_tarski(X4,X5) != sK2(X0,X1,X2)
                | ~ r2_hidden(X5,X1)
                | ~ r2_hidden(X4,X0) )
            | ~ r2_hidden(sK2(X0,X1,X2),X2) )
          & ( ( k4_tarski(sK3(X0,X1,X2),sK4(X0,X1,X2)) = sK2(X0,X1,X2)
              & r2_hidden(sK4(X0,X1,X2),X1)
              & r2_hidden(sK3(X0,X1,X2),X0) )
            | r2_hidden(sK2(X0,X1,X2),X2) ) ) )
      & ( ! [X8] :
            ( ( r2_hidden(X8,X2)
              | ! [X9,X10] :
                  ( k4_tarski(X9,X10) != X8
                  | ~ r2_hidden(X10,X1)
                  | ~ r2_hidden(X9,X0) ) )
            & ( ( k4_tarski(sK5(X0,X1,X8),sK6(X0,X1,X8)) = X8
                & r2_hidden(sK6(X0,X1,X8),X1)
                & r2_hidden(sK5(X0,X1,X8),X0) )
              | ~ r2_hidden(X8,X2) ) )
        | k2_zfmisc_1(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5,sK6])],[f26,f29,f28,f27])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( k2_zfmisc_1(X0,X1) = X2
      | r2_hidden(sK3(X0,X1,X2),X0)
      | r2_hidden(sK2(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f7,axiom,(
    ! [X0] : k5_xboole_0(X0,X0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f51,plain,(
    ! [X0] : k5_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f7])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k5_xboole_0(X1,X2))
    <=> ~ ( r2_hidden(X0,X1)
        <=> r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k5_xboole_0(X1,X2))
    <=> ( r2_hidden(X0,X1)
      <~> r2_hidden(X0,X2) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k5_xboole_0(X1,X2))
        | ( ( r2_hidden(X0,X1)
            | ~ r2_hidden(X0,X2) )
          & ( r2_hidden(X0,X2)
            | ~ r2_hidden(X0,X1) ) ) )
      & ( ( ( ~ r2_hidden(X0,X2)
            | ~ r2_hidden(X0,X1) )
          & ( r2_hidden(X0,X2)
            | r2_hidden(X0,X1) ) )
        | ~ r2_hidden(X0,k5_xboole_0(X1,X2)) ) ) ),
    inference(nnf_transformation,[],[f12])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X2)
      | ~ r2_hidden(X0,X1)
      | ~ r2_hidden(X0,k5_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f6,axiom,(
    ! [X0] :
      ( k1_xboole_0 != X0
     => r2_xboole_0(k1_xboole_0,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0] :
      ( r2_xboole_0(k1_xboole_0,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f6])).

fof(f50,plain,(
    ! [X0] :
      ( r2_xboole_0(k1_xboole_0,X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f15])).

fof(f4,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f5,axiom,(
    ! [X0,X1] :
      ~ ( r2_xboole_0(X1,X0)
        & r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1] :
      ( ~ r2_xboole_0(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ~ r2_xboole_0(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
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
    inference(nnf_transformation,[],[f1])).

fof(f18,plain,(
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
    inference(flattening,[],[f17])).

fof(f19,plain,(
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
    inference(rectify,[],[f18])).

fof(f20,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ~ r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( ~ r2_hidden(sK0(X0,X1,X2),X1)
          | ~ r2_hidden(sK0(X0,X1,X2),X0)
          | ~ r2_hidden(sK0(X0,X1,X2),X2) )
        & ( ( r2_hidden(sK0(X0,X1,X2),X1)
            & r2_hidden(sK0(X0,X1,X2),X0) )
          | r2_hidden(sK0(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ( ( ~ r2_hidden(sK0(X0,X1,X2),X1)
            | ~ r2_hidden(sK0(X0,X1,X2),X0)
            | ~ r2_hidden(sK0(X0,X1,X2),X2) )
          & ( ( r2_hidden(sK0(X0,X1,X2),X1)
              & r2_hidden(sK0(X0,X1,X2),X0) )
            | r2_hidden(sK0(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f19,f20])).

fof(f38,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f21])).

fof(f67,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X1)
      | ~ r2_hidden(X4,k3_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f38])).

fof(f3,axiom,(
    ! [X0] :
      ~ ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f3])).

fof(f23,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK1(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    ! [X0] :
      ( r2_hidden(sK1(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f13,f23])).

fof(f47,plain,(
    ! [X0] :
      ( r2_hidden(sK1(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f24])).

fof(f10,conjecture,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f11,negated_conjecture,(
    ~ ! [X0,X1] :
        ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      <=> ( k1_xboole_0 = X1
          | k1_xboole_0 = X0 ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f16,plain,(
    ? [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <~> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f33,plain,(
    ? [X0,X1] :
      ( ( ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 )
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 = k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f16])).

fof(f34,plain,(
    ? [X0,X1] :
      ( ( ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 )
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 = k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f33])).

fof(f35,plain,
    ( ? [X0,X1] :
        ( ( ( k1_xboole_0 != X1
            & k1_xboole_0 != X0 )
          | k1_xboole_0 != k2_zfmisc_1(X0,X1) )
        & ( k1_xboole_0 = X1
          | k1_xboole_0 = X0
          | k1_xboole_0 = k2_zfmisc_1(X0,X1) ) )
   => ( ( ( k1_xboole_0 != sK8
          & k1_xboole_0 != sK7 )
        | k1_xboole_0 != k2_zfmisc_1(sK7,sK8) )
      & ( k1_xboole_0 = sK8
        | k1_xboole_0 = sK7
        | k1_xboole_0 = k2_zfmisc_1(sK7,sK8) ) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,
    ( ( ( k1_xboole_0 != sK8
        & k1_xboole_0 != sK7 )
      | k1_xboole_0 != k2_zfmisc_1(sK7,sK8) )
    & ( k1_xboole_0 = sK8
      | k1_xboole_0 = sK7
      | k1_xboole_0 = k2_zfmisc_1(sK7,sK8) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7,sK8])],[f34,f35])).

fof(f63,plain,
    ( k1_xboole_0 = sK8
    | k1_xboole_0 = sK7
    | k1_xboole_0 = k2_zfmisc_1(sK7,sK8) ),
    inference(cnf_transformation,[],[f36])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
    <=> ( r2_hidden(X1,X3)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
        | ~ r2_hidden(X1,X3)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X3)
          & r2_hidden(X0,X2) )
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ) ),
    inference(nnf_transformation,[],[f9])).

fof(f32,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
        | ~ r2_hidden(X1,X3)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X3)
          & r2_hidden(X0,X2) )
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ) ),
    inference(flattening,[],[f31])).

fof(f62,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
      | ~ r2_hidden(X1,X3)
      | ~ r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f64,plain,
    ( k1_xboole_0 != sK7
    | k1_xboole_0 != k2_zfmisc_1(sK7,sK8) ),
    inference(cnf_transformation,[],[f36])).

fof(f65,plain,
    ( k1_xboole_0 != sK8
    | k1_xboole_0 != k2_zfmisc_1(sK7,sK8) ),
    inference(cnf_transformation,[],[f36])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( k2_zfmisc_1(X0,X1) = X2
      | r2_hidden(sK4(X0,X1,X2),X1)
      | r2_hidden(sK2(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_18,plain,
    ( r2_hidden(sK3(X0,X1,X2),X0)
    | r2_hidden(sK2(X0,X1,X2),X2)
    | k2_zfmisc_1(X0,X1) = X2 ),
    inference(cnf_transformation,[],[f56])).

cnf(c_785,plain,
    ( k2_zfmisc_1(X0,X1) = X2
    | r2_hidden(sK3(X0,X1,X2),X0) = iProver_top
    | r2_hidden(sK2(X0,X1,X2),X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_14,plain,
    ( k5_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f51])).

cnf(c_8,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X0,X2)
    | ~ r2_hidden(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_791,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,X2) != iProver_top
    | r2_hidden(X0,k5_xboole_0(X1,X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_4221,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_14,c_791])).

cnf(c_13,plain,
    ( r2_xboole_0(k1_xboole_0,X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f50])).

cnf(c_11,plain,
    ( r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_12,plain,
    ( ~ r2_xboole_0(X0,X1)
    | ~ r1_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_286,plain,
    ( ~ r2_xboole_0(X0,X1)
    | X0 != X2
    | k3_xboole_0(X2,X3) != X1 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_12])).

cnf(c_287,plain,
    ( ~ r2_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(unflattening,[status(thm)],[c_286])).

cnf(c_297,plain,
    ( k3_xboole_0(X0,X1) != X2
    | k1_xboole_0 != X0
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_287])).

cnf(c_298,plain,
    ( k1_xboole_0 = k3_xboole_0(k1_xboole_0,X0) ),
    inference(unflattening,[status(thm)],[c_297])).

cnf(c_4,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k3_xboole_0(X2,X1)) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_795,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r2_hidden(X0,k3_xboole_0(X2,X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_1246,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r2_hidden(X0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_298,c_795])).

cnf(c_4248,plain,
    ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4221,c_1246])).

cnf(c_4254,plain,
    ( k2_zfmisc_1(k1_xboole_0,X0) = X1
    | r2_hidden(sK2(k1_xboole_0,X0,X1),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_785,c_4248])).

cnf(c_4253,plain,
    ( k2_zfmisc_1(X0,X1) = k1_xboole_0
    | r2_hidden(sK3(X0,X1,k1_xboole_0),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_785,c_4248])).

cnf(c_5885,plain,
    ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_4253,c_4248])).

cnf(c_6026,plain,
    ( k1_xboole_0 = X0
    | r2_hidden(sK2(k1_xboole_0,X1,X0),X0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_4254,c_5885])).

cnf(c_10,plain,
    ( r2_hidden(sK1(X0),X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f47])).

cnf(c_789,plain,
    ( k1_xboole_0 = X0
    | r2_hidden(sK1(X0),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_28,negated_conjecture,
    ( k1_xboole_0 = k2_zfmisc_1(sK7,sK8)
    | k1_xboole_0 = sK7
    | k1_xboole_0 = sK8 ),
    inference(cnf_transformation,[],[f63])).

cnf(c_23,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X2,X3)
    | r2_hidden(k4_tarski(X0,X2),k2_zfmisc_1(X1,X3)) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_780,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X2,X3) != iProver_top
    | r2_hidden(k4_tarski(X0,X2),k2_zfmisc_1(X1,X3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_2811,plain,
    ( sK7 = k1_xboole_0
    | sK8 = k1_xboole_0
    | r2_hidden(X0,sK7) != iProver_top
    | r2_hidden(X1,sK8) != iProver_top
    | r2_hidden(k4_tarski(X0,X1),k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_28,c_780])).

cnf(c_3124,plain,
    ( sK7 = k1_xboole_0
    | sK8 = k1_xboole_0
    | r2_hidden(X0,sK7) != iProver_top
    | r2_hidden(X1,sK8) != iProver_top
    | r2_hidden(k4_tarski(X0,X1),X2) = iProver_top ),
    inference(superposition,[status(thm)],[c_2811,c_1246])).

cnf(c_4259,plain,
    ( sK7 = k1_xboole_0
    | sK8 = k1_xboole_0
    | r2_hidden(X0,sK7) != iProver_top
    | r2_hidden(X1,sK8) != iProver_top ),
    inference(superposition,[status(thm)],[c_3124,c_4248])).

cnf(c_4615,plain,
    ( sK7 = k1_xboole_0
    | sK8 = k1_xboole_0
    | r2_hidden(X0,sK8) != iProver_top ),
    inference(superposition,[status(thm)],[c_789,c_4259])).

cnf(c_6507,plain,
    ( sK7 = k1_xboole_0
    | sK8 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_6026,c_4615])).

cnf(c_27,negated_conjecture,
    ( k1_xboole_0 != k2_zfmisc_1(sK7,sK8)
    | k1_xboole_0 != sK7 ),
    inference(cnf_transformation,[],[f64])).

cnf(c_28910,plain,
    ( k2_zfmisc_1(k1_xboole_0,sK8) != k1_xboole_0
    | sK7 != k1_xboole_0
    | sK8 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_6507,c_27])).

cnf(c_28912,plain,
    ( sK7 != k1_xboole_0
    | sK8 = k1_xboole_0
    | k1_xboole_0 != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_28910,c_5885])).

cnf(c_28913,plain,
    ( sK7 != k1_xboole_0
    | sK8 = k1_xboole_0 ),
    inference(equality_resolution_simp,[status(thm)],[c_28912])).

cnf(c_33527,plain,
    ( sK8 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_28913,c_6507])).

cnf(c_26,negated_conjecture,
    ( k1_xboole_0 != k2_zfmisc_1(sK7,sK8)
    | k1_xboole_0 != sK8 ),
    inference(cnf_transformation,[],[f65])).

cnf(c_33531,plain,
    ( k2_zfmisc_1(sK7,k1_xboole_0) != k1_xboole_0
    | k1_xboole_0 != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_33527,c_26])).

cnf(c_33532,plain,
    ( k2_zfmisc_1(sK7,k1_xboole_0) != k1_xboole_0 ),
    inference(equality_resolution_simp,[status(thm)],[c_33531])).

cnf(c_17,plain,
    ( r2_hidden(sK4(X0,X1,X2),X1)
    | r2_hidden(sK2(X0,X1,X2),X2)
    | k2_zfmisc_1(X0,X1) = X2 ),
    inference(cnf_transformation,[],[f57])).

cnf(c_786,plain,
    ( k2_zfmisc_1(X0,X1) = X2
    | r2_hidden(sK4(X0,X1,X2),X1) = iProver_top
    | r2_hidden(sK2(X0,X1,X2),X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_4349,plain,
    ( k2_zfmisc_1(X0,X1) = k1_xboole_0
    | r2_hidden(sK4(X0,X1,k1_xboole_0),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_786,c_4248])).

cnf(c_6056,plain,
    ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_4349,c_4248])).

cnf(c_33533,plain,
    ( k1_xboole_0 != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_33532,c_6056])).

cnf(c_33534,plain,
    ( $false ),
    inference(equality_resolution_simp,[status(thm)],[c_33533])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 20:41:39 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 11.53/2.00  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 11.53/2.00  
% 11.53/2.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 11.53/2.00  
% 11.53/2.00  ------  iProver source info
% 11.53/2.00  
% 11.53/2.00  git: date: 2020-06-30 10:37:57 +0100
% 11.53/2.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 11.53/2.00  git: non_committed_changes: false
% 11.53/2.00  git: last_make_outside_of_git: false
% 11.53/2.00  
% 11.53/2.00  ------ 
% 11.53/2.00  
% 11.53/2.00  ------ Input Options
% 11.53/2.00  
% 11.53/2.00  --out_options                           all
% 11.53/2.00  --tptp_safe_out                         true
% 11.53/2.00  --problem_path                          ""
% 11.53/2.00  --include_path                          ""
% 11.53/2.00  --clausifier                            res/vclausify_rel
% 11.53/2.00  --clausifier_options                    ""
% 11.53/2.00  --stdin                                 false
% 11.53/2.00  --stats_out                             all
% 11.53/2.00  
% 11.53/2.00  ------ General Options
% 11.53/2.00  
% 11.53/2.00  --fof                                   false
% 11.53/2.00  --time_out_real                         305.
% 11.53/2.00  --time_out_virtual                      -1.
% 11.53/2.00  --symbol_type_check                     false
% 11.53/2.00  --clausify_out                          false
% 11.53/2.00  --sig_cnt_out                           false
% 11.53/2.00  --trig_cnt_out                          false
% 11.53/2.00  --trig_cnt_out_tolerance                1.
% 11.53/2.00  --trig_cnt_out_sk_spl                   false
% 11.53/2.00  --abstr_cl_out                          false
% 11.53/2.00  
% 11.53/2.00  ------ Global Options
% 11.53/2.00  
% 11.53/2.00  --schedule                              default
% 11.53/2.00  --add_important_lit                     false
% 11.53/2.00  --prop_solver_per_cl                    1000
% 11.53/2.00  --min_unsat_core                        false
% 11.53/2.00  --soft_assumptions                      false
% 11.53/2.00  --soft_lemma_size                       3
% 11.53/2.00  --prop_impl_unit_size                   0
% 11.53/2.00  --prop_impl_unit                        []
% 11.53/2.00  --share_sel_clauses                     true
% 11.53/2.00  --reset_solvers                         false
% 11.53/2.00  --bc_imp_inh                            [conj_cone]
% 11.53/2.00  --conj_cone_tolerance                   3.
% 11.53/2.00  --extra_neg_conj                        none
% 11.53/2.00  --large_theory_mode                     true
% 11.53/2.00  --prolific_symb_bound                   200
% 11.53/2.00  --lt_threshold                          2000
% 11.53/2.00  --clause_weak_htbl                      true
% 11.53/2.00  --gc_record_bc_elim                     false
% 11.53/2.00  
% 11.53/2.00  ------ Preprocessing Options
% 11.53/2.00  
% 11.53/2.00  --preprocessing_flag                    true
% 11.53/2.00  --time_out_prep_mult                    0.1
% 11.53/2.00  --splitting_mode                        input
% 11.53/2.00  --splitting_grd                         true
% 11.53/2.00  --splitting_cvd                         false
% 11.53/2.00  --splitting_cvd_svl                     false
% 11.53/2.00  --splitting_nvd                         32
% 11.53/2.00  --sub_typing                            true
% 11.53/2.00  --prep_gs_sim                           true
% 11.53/2.00  --prep_unflatten                        true
% 11.53/2.00  --prep_res_sim                          true
% 11.53/2.00  --prep_upred                            true
% 11.53/2.00  --prep_sem_filter                       exhaustive
% 11.53/2.00  --prep_sem_filter_out                   false
% 11.53/2.00  --pred_elim                             true
% 11.53/2.00  --res_sim_input                         true
% 11.53/2.00  --eq_ax_congr_red                       true
% 11.53/2.00  --pure_diseq_elim                       true
% 11.53/2.00  --brand_transform                       false
% 11.53/2.00  --non_eq_to_eq                          false
% 11.53/2.00  --prep_def_merge                        true
% 11.53/2.00  --prep_def_merge_prop_impl              false
% 11.53/2.00  --prep_def_merge_mbd                    true
% 11.53/2.00  --prep_def_merge_tr_red                 false
% 11.53/2.00  --prep_def_merge_tr_cl                  false
% 11.53/2.00  --smt_preprocessing                     true
% 11.53/2.00  --smt_ac_axioms                         fast
% 11.53/2.00  --preprocessed_out                      false
% 11.53/2.00  --preprocessed_stats                    false
% 11.53/2.00  
% 11.53/2.00  ------ Abstraction refinement Options
% 11.53/2.00  
% 11.53/2.00  --abstr_ref                             []
% 11.53/2.00  --abstr_ref_prep                        false
% 11.53/2.00  --abstr_ref_until_sat                   false
% 11.53/2.00  --abstr_ref_sig_restrict                funpre
% 11.53/2.00  --abstr_ref_af_restrict_to_split_sk     false
% 11.53/2.00  --abstr_ref_under                       []
% 11.53/2.00  
% 11.53/2.00  ------ SAT Options
% 11.53/2.00  
% 11.53/2.00  --sat_mode                              false
% 11.53/2.00  --sat_fm_restart_options                ""
% 11.53/2.00  --sat_gr_def                            false
% 11.53/2.00  --sat_epr_types                         true
% 11.53/2.00  --sat_non_cyclic_types                  false
% 11.53/2.00  --sat_finite_models                     false
% 11.53/2.00  --sat_fm_lemmas                         false
% 11.53/2.00  --sat_fm_prep                           false
% 11.53/2.00  --sat_fm_uc_incr                        true
% 11.53/2.00  --sat_out_model                         small
% 11.53/2.00  --sat_out_clauses                       false
% 11.53/2.00  
% 11.53/2.00  ------ QBF Options
% 11.53/2.00  
% 11.53/2.00  --qbf_mode                              false
% 11.53/2.00  --qbf_elim_univ                         false
% 11.53/2.00  --qbf_dom_inst                          none
% 11.53/2.00  --qbf_dom_pre_inst                      false
% 11.53/2.00  --qbf_sk_in                             false
% 11.53/2.00  --qbf_pred_elim                         true
% 11.53/2.00  --qbf_split                             512
% 11.53/2.00  
% 11.53/2.00  ------ BMC1 Options
% 11.53/2.00  
% 11.53/2.00  --bmc1_incremental                      false
% 11.53/2.00  --bmc1_axioms                           reachable_all
% 11.53/2.00  --bmc1_min_bound                        0
% 11.53/2.00  --bmc1_max_bound                        -1
% 11.53/2.00  --bmc1_max_bound_default                -1
% 11.53/2.00  --bmc1_symbol_reachability              true
% 11.53/2.00  --bmc1_property_lemmas                  false
% 11.53/2.00  --bmc1_k_induction                      false
% 11.53/2.00  --bmc1_non_equiv_states                 false
% 11.53/2.00  --bmc1_deadlock                         false
% 11.53/2.00  --bmc1_ucm                              false
% 11.53/2.00  --bmc1_add_unsat_core                   none
% 11.53/2.00  --bmc1_unsat_core_children              false
% 11.53/2.00  --bmc1_unsat_core_extrapolate_axioms    false
% 11.53/2.00  --bmc1_out_stat                         full
% 11.53/2.00  --bmc1_ground_init                      false
% 11.53/2.00  --bmc1_pre_inst_next_state              false
% 11.53/2.00  --bmc1_pre_inst_state                   false
% 11.53/2.00  --bmc1_pre_inst_reach_state             false
% 11.53/2.00  --bmc1_out_unsat_core                   false
% 11.53/2.00  --bmc1_aig_witness_out                  false
% 11.53/2.00  --bmc1_verbose                          false
% 11.53/2.00  --bmc1_dump_clauses_tptp                false
% 11.53/2.00  --bmc1_dump_unsat_core_tptp             false
% 11.53/2.00  --bmc1_dump_file                        -
% 11.53/2.00  --bmc1_ucm_expand_uc_limit              128
% 11.53/2.00  --bmc1_ucm_n_expand_iterations          6
% 11.53/2.00  --bmc1_ucm_extend_mode                  1
% 11.53/2.00  --bmc1_ucm_init_mode                    2
% 11.53/2.00  --bmc1_ucm_cone_mode                    none
% 11.53/2.00  --bmc1_ucm_reduced_relation_type        0
% 11.53/2.00  --bmc1_ucm_relax_model                  4
% 11.53/2.00  --bmc1_ucm_full_tr_after_sat            true
% 11.53/2.00  --bmc1_ucm_expand_neg_assumptions       false
% 11.53/2.00  --bmc1_ucm_layered_model                none
% 11.53/2.00  --bmc1_ucm_max_lemma_size               10
% 11.53/2.00  
% 11.53/2.00  ------ AIG Options
% 11.53/2.00  
% 11.53/2.00  --aig_mode                              false
% 11.53/2.00  
% 11.53/2.00  ------ Instantiation Options
% 11.53/2.00  
% 11.53/2.00  --instantiation_flag                    true
% 11.53/2.00  --inst_sos_flag                         true
% 11.53/2.00  --inst_sos_phase                        true
% 11.53/2.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 11.53/2.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 11.53/2.00  --inst_lit_sel_side                     num_symb
% 11.53/2.00  --inst_solver_per_active                1400
% 11.53/2.00  --inst_solver_calls_frac                1.
% 11.53/2.00  --inst_passive_queue_type               priority_queues
% 11.53/2.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 11.53/2.00  --inst_passive_queues_freq              [25;2]
% 11.53/2.00  --inst_dismatching                      true
% 11.53/2.00  --inst_eager_unprocessed_to_passive     true
% 11.53/2.00  --inst_prop_sim_given                   true
% 11.53/2.00  --inst_prop_sim_new                     false
% 11.53/2.00  --inst_subs_new                         false
% 11.53/2.00  --inst_eq_res_simp                      false
% 11.53/2.00  --inst_subs_given                       false
% 11.53/2.00  --inst_orphan_elimination               true
% 11.53/2.00  --inst_learning_loop_flag               true
% 11.53/2.00  --inst_learning_start                   3000
% 11.53/2.00  --inst_learning_factor                  2
% 11.53/2.00  --inst_start_prop_sim_after_learn       3
% 11.53/2.00  --inst_sel_renew                        solver
% 11.53/2.00  --inst_lit_activity_flag                true
% 11.53/2.00  --inst_restr_to_given                   false
% 11.53/2.00  --inst_activity_threshold               500
% 11.53/2.00  --inst_out_proof                        true
% 11.53/2.00  
% 11.53/2.00  ------ Resolution Options
% 11.53/2.00  
% 11.53/2.00  --resolution_flag                       true
% 11.53/2.00  --res_lit_sel                           adaptive
% 11.53/2.00  --res_lit_sel_side                      none
% 11.53/2.00  --res_ordering                          kbo
% 11.53/2.00  --res_to_prop_solver                    active
% 11.53/2.00  --res_prop_simpl_new                    false
% 11.53/2.00  --res_prop_simpl_given                  true
% 11.53/2.00  --res_passive_queue_type                priority_queues
% 11.53/2.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 11.53/2.00  --res_passive_queues_freq               [15;5]
% 11.53/2.00  --res_forward_subs                      full
% 11.53/2.00  --res_backward_subs                     full
% 11.53/2.00  --res_forward_subs_resolution           true
% 11.53/2.00  --res_backward_subs_resolution          true
% 11.53/2.00  --res_orphan_elimination                true
% 11.53/2.00  --res_time_limit                        2.
% 11.53/2.00  --res_out_proof                         true
% 11.53/2.00  
% 11.53/2.00  ------ Superposition Options
% 11.53/2.00  
% 11.53/2.00  --superposition_flag                    true
% 11.53/2.00  --sup_passive_queue_type                priority_queues
% 11.53/2.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 11.53/2.00  --sup_passive_queues_freq               [8;1;4]
% 11.53/2.00  --demod_completeness_check              fast
% 11.53/2.00  --demod_use_ground                      true
% 11.53/2.00  --sup_to_prop_solver                    passive
% 11.53/2.00  --sup_prop_simpl_new                    true
% 11.53/2.00  --sup_prop_simpl_given                  true
% 11.53/2.00  --sup_fun_splitting                     true
% 11.53/2.00  --sup_smt_interval                      50000
% 11.53/2.00  
% 11.53/2.00  ------ Superposition Simplification Setup
% 11.53/2.00  
% 11.53/2.00  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 11.53/2.00  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 11.53/2.00  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 11.53/2.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 11.53/2.00  --sup_full_triv                         [TrivRules;PropSubs]
% 11.53/2.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 11.53/2.00  --sup_full_bw                           [BwDemod;BwSubsumption]
% 11.53/2.00  --sup_immed_triv                        [TrivRules]
% 11.53/2.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 11.53/2.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 11.53/2.00  --sup_immed_bw_main                     []
% 11.53/2.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 11.53/2.00  --sup_input_triv                        [Unflattening;TrivRules]
% 11.53/2.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 11.53/2.00  --sup_input_bw                          []
% 11.53/2.00  
% 11.53/2.00  ------ Combination Options
% 11.53/2.00  
% 11.53/2.00  --comb_res_mult                         3
% 11.53/2.00  --comb_sup_mult                         2
% 11.53/2.00  --comb_inst_mult                        10
% 11.53/2.00  
% 11.53/2.00  ------ Debug Options
% 11.53/2.00  
% 11.53/2.00  --dbg_backtrace                         false
% 11.53/2.00  --dbg_dump_prop_clauses                 false
% 11.53/2.00  --dbg_dump_prop_clauses_file            -
% 11.53/2.00  --dbg_out_stat                          false
% 11.53/2.00  ------ Parsing...
% 11.53/2.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 11.53/2.00  
% 11.53/2.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 11.53/2.00  
% 11.53/2.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 11.53/2.00  
% 11.53/2.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 11.53/2.00  ------ Proving...
% 11.53/2.00  ------ Problem Properties 
% 11.53/2.00  
% 11.53/2.00  
% 11.53/2.00  clauses                                 27
% 11.53/2.00  conjectures                             3
% 11.53/2.00  EPR                                     0
% 11.53/2.00  Horn                                    17
% 11.53/2.00  unary                                   2
% 11.53/2.00  binary                                  10
% 11.53/2.00  lits                                    70
% 11.53/2.00  lits eq                                 20
% 11.53/2.00  fd_pure                                 0
% 11.53/2.00  fd_pseudo                               0
% 11.53/2.00  fd_cond                                 1
% 11.53/2.00  fd_pseudo_cond                          7
% 11.53/2.00  AC symbols                              0
% 11.53/2.00  
% 11.53/2.00  ------ Schedule dynamic 5 is on 
% 11.53/2.00  
% 11.53/2.00  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 11.53/2.00  
% 11.53/2.00  
% 11.53/2.00  ------ 
% 11.53/2.00  Current options:
% 11.53/2.00  ------ 
% 11.53/2.00  
% 11.53/2.00  ------ Input Options
% 11.53/2.00  
% 11.53/2.00  --out_options                           all
% 11.53/2.00  --tptp_safe_out                         true
% 11.53/2.00  --problem_path                          ""
% 11.53/2.00  --include_path                          ""
% 11.53/2.00  --clausifier                            res/vclausify_rel
% 11.53/2.00  --clausifier_options                    ""
% 11.53/2.00  --stdin                                 false
% 11.53/2.00  --stats_out                             all
% 11.53/2.00  
% 11.53/2.00  ------ General Options
% 11.53/2.00  
% 11.53/2.00  --fof                                   false
% 11.53/2.00  --time_out_real                         305.
% 11.53/2.00  --time_out_virtual                      -1.
% 11.53/2.00  --symbol_type_check                     false
% 11.53/2.00  --clausify_out                          false
% 11.53/2.00  --sig_cnt_out                           false
% 11.53/2.00  --trig_cnt_out                          false
% 11.53/2.00  --trig_cnt_out_tolerance                1.
% 11.53/2.00  --trig_cnt_out_sk_spl                   false
% 11.53/2.00  --abstr_cl_out                          false
% 11.53/2.00  
% 11.53/2.00  ------ Global Options
% 11.53/2.00  
% 11.53/2.00  --schedule                              default
% 11.53/2.00  --add_important_lit                     false
% 11.53/2.00  --prop_solver_per_cl                    1000
% 11.53/2.00  --min_unsat_core                        false
% 11.53/2.00  --soft_assumptions                      false
% 11.53/2.00  --soft_lemma_size                       3
% 11.53/2.00  --prop_impl_unit_size                   0
% 11.53/2.00  --prop_impl_unit                        []
% 11.53/2.00  --share_sel_clauses                     true
% 11.53/2.00  --reset_solvers                         false
% 11.53/2.00  --bc_imp_inh                            [conj_cone]
% 11.53/2.00  --conj_cone_tolerance                   3.
% 11.53/2.00  --extra_neg_conj                        none
% 11.53/2.00  --large_theory_mode                     true
% 11.53/2.00  --prolific_symb_bound                   200
% 11.53/2.00  --lt_threshold                          2000
% 11.53/2.00  --clause_weak_htbl                      true
% 11.53/2.00  --gc_record_bc_elim                     false
% 11.53/2.00  
% 11.53/2.00  ------ Preprocessing Options
% 11.53/2.00  
% 11.53/2.00  --preprocessing_flag                    true
% 11.53/2.00  --time_out_prep_mult                    0.1
% 11.53/2.00  --splitting_mode                        input
% 11.53/2.00  --splitting_grd                         true
% 11.53/2.00  --splitting_cvd                         false
% 11.53/2.00  --splitting_cvd_svl                     false
% 11.53/2.00  --splitting_nvd                         32
% 11.53/2.00  --sub_typing                            true
% 11.53/2.00  --prep_gs_sim                           true
% 11.53/2.00  --prep_unflatten                        true
% 11.53/2.00  --prep_res_sim                          true
% 11.53/2.00  --prep_upred                            true
% 11.53/2.00  --prep_sem_filter                       exhaustive
% 11.53/2.00  --prep_sem_filter_out                   false
% 11.53/2.00  --pred_elim                             true
% 11.53/2.00  --res_sim_input                         true
% 11.53/2.00  --eq_ax_congr_red                       true
% 11.53/2.00  --pure_diseq_elim                       true
% 11.53/2.00  --brand_transform                       false
% 11.53/2.00  --non_eq_to_eq                          false
% 11.53/2.00  --prep_def_merge                        true
% 11.53/2.00  --prep_def_merge_prop_impl              false
% 11.53/2.00  --prep_def_merge_mbd                    true
% 11.53/2.00  --prep_def_merge_tr_red                 false
% 11.53/2.00  --prep_def_merge_tr_cl                  false
% 11.53/2.00  --smt_preprocessing                     true
% 11.53/2.00  --smt_ac_axioms                         fast
% 11.53/2.00  --preprocessed_out                      false
% 11.53/2.00  --preprocessed_stats                    false
% 11.53/2.00  
% 11.53/2.00  ------ Abstraction refinement Options
% 11.53/2.00  
% 11.53/2.00  --abstr_ref                             []
% 11.53/2.00  --abstr_ref_prep                        false
% 11.53/2.00  --abstr_ref_until_sat                   false
% 11.53/2.00  --abstr_ref_sig_restrict                funpre
% 11.53/2.00  --abstr_ref_af_restrict_to_split_sk     false
% 11.53/2.00  --abstr_ref_under                       []
% 11.53/2.00  
% 11.53/2.00  ------ SAT Options
% 11.53/2.00  
% 11.53/2.00  --sat_mode                              false
% 11.53/2.00  --sat_fm_restart_options                ""
% 11.53/2.00  --sat_gr_def                            false
% 11.53/2.00  --sat_epr_types                         true
% 11.53/2.00  --sat_non_cyclic_types                  false
% 11.53/2.00  --sat_finite_models                     false
% 11.53/2.00  --sat_fm_lemmas                         false
% 11.53/2.00  --sat_fm_prep                           false
% 11.53/2.00  --sat_fm_uc_incr                        true
% 11.53/2.00  --sat_out_model                         small
% 11.53/2.00  --sat_out_clauses                       false
% 11.53/2.00  
% 11.53/2.00  ------ QBF Options
% 11.53/2.00  
% 11.53/2.00  --qbf_mode                              false
% 11.53/2.00  --qbf_elim_univ                         false
% 11.53/2.00  --qbf_dom_inst                          none
% 11.53/2.00  --qbf_dom_pre_inst                      false
% 11.53/2.00  --qbf_sk_in                             false
% 11.53/2.00  --qbf_pred_elim                         true
% 11.53/2.00  --qbf_split                             512
% 11.53/2.00  
% 11.53/2.00  ------ BMC1 Options
% 11.53/2.00  
% 11.53/2.00  --bmc1_incremental                      false
% 11.53/2.00  --bmc1_axioms                           reachable_all
% 11.53/2.00  --bmc1_min_bound                        0
% 11.53/2.00  --bmc1_max_bound                        -1
% 11.53/2.00  --bmc1_max_bound_default                -1
% 11.53/2.00  --bmc1_symbol_reachability              true
% 11.53/2.00  --bmc1_property_lemmas                  false
% 11.53/2.00  --bmc1_k_induction                      false
% 11.53/2.00  --bmc1_non_equiv_states                 false
% 11.53/2.00  --bmc1_deadlock                         false
% 11.53/2.00  --bmc1_ucm                              false
% 11.53/2.00  --bmc1_add_unsat_core                   none
% 11.53/2.00  --bmc1_unsat_core_children              false
% 11.53/2.00  --bmc1_unsat_core_extrapolate_axioms    false
% 11.53/2.00  --bmc1_out_stat                         full
% 11.53/2.00  --bmc1_ground_init                      false
% 11.53/2.00  --bmc1_pre_inst_next_state              false
% 11.53/2.00  --bmc1_pre_inst_state                   false
% 11.53/2.00  --bmc1_pre_inst_reach_state             false
% 11.53/2.00  --bmc1_out_unsat_core                   false
% 11.53/2.00  --bmc1_aig_witness_out                  false
% 11.53/2.00  --bmc1_verbose                          false
% 11.53/2.00  --bmc1_dump_clauses_tptp                false
% 11.53/2.00  --bmc1_dump_unsat_core_tptp             false
% 11.53/2.00  --bmc1_dump_file                        -
% 11.53/2.00  --bmc1_ucm_expand_uc_limit              128
% 11.53/2.00  --bmc1_ucm_n_expand_iterations          6
% 11.53/2.00  --bmc1_ucm_extend_mode                  1
% 11.53/2.00  --bmc1_ucm_init_mode                    2
% 11.53/2.00  --bmc1_ucm_cone_mode                    none
% 11.53/2.00  --bmc1_ucm_reduced_relation_type        0
% 11.53/2.00  --bmc1_ucm_relax_model                  4
% 11.53/2.00  --bmc1_ucm_full_tr_after_sat            true
% 11.53/2.00  --bmc1_ucm_expand_neg_assumptions       false
% 11.53/2.00  --bmc1_ucm_layered_model                none
% 11.53/2.00  --bmc1_ucm_max_lemma_size               10
% 11.53/2.00  
% 11.53/2.00  ------ AIG Options
% 11.53/2.00  
% 11.53/2.00  --aig_mode                              false
% 11.53/2.00  
% 11.53/2.00  ------ Instantiation Options
% 11.53/2.00  
% 11.53/2.00  --instantiation_flag                    true
% 11.53/2.00  --inst_sos_flag                         true
% 11.53/2.00  --inst_sos_phase                        true
% 11.53/2.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 11.53/2.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 11.53/2.00  --inst_lit_sel_side                     none
% 11.53/2.00  --inst_solver_per_active                1400
% 11.53/2.00  --inst_solver_calls_frac                1.
% 11.53/2.00  --inst_passive_queue_type               priority_queues
% 11.53/2.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 11.53/2.00  --inst_passive_queues_freq              [25;2]
% 11.53/2.00  --inst_dismatching                      true
% 11.53/2.00  --inst_eager_unprocessed_to_passive     true
% 11.53/2.00  --inst_prop_sim_given                   true
% 11.53/2.00  --inst_prop_sim_new                     false
% 11.53/2.00  --inst_subs_new                         false
% 11.53/2.00  --inst_eq_res_simp                      false
% 11.53/2.00  --inst_subs_given                       false
% 11.53/2.00  --inst_orphan_elimination               true
% 11.53/2.00  --inst_learning_loop_flag               true
% 11.53/2.00  --inst_learning_start                   3000
% 11.53/2.00  --inst_learning_factor                  2
% 11.53/2.00  --inst_start_prop_sim_after_learn       3
% 11.53/2.00  --inst_sel_renew                        solver
% 11.53/2.00  --inst_lit_activity_flag                true
% 11.53/2.00  --inst_restr_to_given                   false
% 11.53/2.00  --inst_activity_threshold               500
% 11.53/2.00  --inst_out_proof                        true
% 11.53/2.00  
% 11.53/2.00  ------ Resolution Options
% 11.53/2.00  
% 11.53/2.00  --resolution_flag                       false
% 11.53/2.00  --res_lit_sel                           adaptive
% 11.53/2.00  --res_lit_sel_side                      none
% 11.53/2.00  --res_ordering                          kbo
% 11.53/2.00  --res_to_prop_solver                    active
% 11.53/2.00  --res_prop_simpl_new                    false
% 11.53/2.00  --res_prop_simpl_given                  true
% 11.53/2.00  --res_passive_queue_type                priority_queues
% 11.53/2.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 11.53/2.00  --res_passive_queues_freq               [15;5]
% 11.53/2.00  --res_forward_subs                      full
% 11.53/2.00  --res_backward_subs                     full
% 11.53/2.00  --res_forward_subs_resolution           true
% 11.53/2.00  --res_backward_subs_resolution          true
% 11.53/2.00  --res_orphan_elimination                true
% 11.53/2.00  --res_time_limit                        2.
% 11.53/2.00  --res_out_proof                         true
% 11.53/2.00  
% 11.53/2.00  ------ Superposition Options
% 11.53/2.00  
% 11.53/2.00  --superposition_flag                    true
% 11.53/2.00  --sup_passive_queue_type                priority_queues
% 11.53/2.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 11.53/2.00  --sup_passive_queues_freq               [8;1;4]
% 11.53/2.00  --demod_completeness_check              fast
% 11.53/2.00  --demod_use_ground                      true
% 11.53/2.00  --sup_to_prop_solver                    passive
% 11.53/2.00  --sup_prop_simpl_new                    true
% 11.53/2.00  --sup_prop_simpl_given                  true
% 11.53/2.00  --sup_fun_splitting                     true
% 11.53/2.00  --sup_smt_interval                      50000
% 11.53/2.00  
% 11.53/2.00  ------ Superposition Simplification Setup
% 11.53/2.00  
% 11.53/2.00  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 11.53/2.00  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 11.53/2.00  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 11.53/2.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 11.53/2.00  --sup_full_triv                         [TrivRules;PropSubs]
% 11.53/2.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 11.53/2.00  --sup_full_bw                           [BwDemod;BwSubsumption]
% 11.53/2.00  --sup_immed_triv                        [TrivRules]
% 11.53/2.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 11.53/2.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 11.53/2.00  --sup_immed_bw_main                     []
% 11.53/2.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 11.53/2.00  --sup_input_triv                        [Unflattening;TrivRules]
% 11.53/2.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 11.53/2.00  --sup_input_bw                          []
% 11.53/2.00  
% 11.53/2.00  ------ Combination Options
% 11.53/2.00  
% 11.53/2.00  --comb_res_mult                         3
% 11.53/2.00  --comb_sup_mult                         2
% 11.53/2.00  --comb_inst_mult                        10
% 11.53/2.00  
% 11.53/2.00  ------ Debug Options
% 11.53/2.00  
% 11.53/2.00  --dbg_backtrace                         false
% 11.53/2.00  --dbg_dump_prop_clauses                 false
% 11.53/2.00  --dbg_dump_prop_clauses_file            -
% 11.53/2.00  --dbg_out_stat                          false
% 11.53/2.00  
% 11.53/2.00  
% 11.53/2.00  
% 11.53/2.00  
% 11.53/2.00  ------ Proving...
% 11.53/2.00  
% 11.53/2.00  
% 11.53/2.00  % SZS status Theorem for theBenchmark.p
% 11.53/2.00  
% 11.53/2.00   Resolution empty clause
% 11.53/2.00  
% 11.53/2.00  % SZS output start CNFRefutation for theBenchmark.p
% 11.53/2.00  
% 11.53/2.00  fof(f8,axiom,(
% 11.53/2.00    ! [X0,X1,X2] : (k2_zfmisc_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4,X5] : (k4_tarski(X4,X5) = X3 & r2_hidden(X5,X1) & r2_hidden(X4,X0))))),
% 11.53/2.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.53/2.00  
% 11.53/2.00  fof(f25,plain,(
% 11.53/2.00    ! [X0,X1,X2] : ((k2_zfmisc_1(X0,X1) = X2 | ? [X3] : ((! [X4,X5] : (k4_tarski(X4,X5) != X3 | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X0)) | ~r2_hidden(X3,X2)) & (? [X4,X5] : (k4_tarski(X4,X5) = X3 & r2_hidden(X5,X1) & r2_hidden(X4,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ! [X4,X5] : (k4_tarski(X4,X5) != X3 | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X0))) & (? [X4,X5] : (k4_tarski(X4,X5) = X3 & r2_hidden(X5,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X3,X2))) | k2_zfmisc_1(X0,X1) != X2))),
% 11.53/2.00    inference(nnf_transformation,[],[f8])).
% 11.53/2.00  
% 11.53/2.00  fof(f26,plain,(
% 11.53/2.00    ! [X0,X1,X2] : ((k2_zfmisc_1(X0,X1) = X2 | ? [X3] : ((! [X4,X5] : (k4_tarski(X4,X5) != X3 | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X0)) | ~r2_hidden(X3,X2)) & (? [X6,X7] : (k4_tarski(X6,X7) = X3 & r2_hidden(X7,X1) & r2_hidden(X6,X0)) | r2_hidden(X3,X2)))) & (! [X8] : ((r2_hidden(X8,X2) | ! [X9,X10] : (k4_tarski(X9,X10) != X8 | ~r2_hidden(X10,X1) | ~r2_hidden(X9,X0))) & (? [X11,X12] : (k4_tarski(X11,X12) = X8 & r2_hidden(X12,X1) & r2_hidden(X11,X0)) | ~r2_hidden(X8,X2))) | k2_zfmisc_1(X0,X1) != X2))),
% 11.53/2.00    inference(rectify,[],[f25])).
% 11.53/2.00  
% 11.53/2.00  fof(f29,plain,(
% 11.53/2.00    ! [X8,X1,X0] : (? [X11,X12] : (k4_tarski(X11,X12) = X8 & r2_hidden(X12,X1) & r2_hidden(X11,X0)) => (k4_tarski(sK5(X0,X1,X8),sK6(X0,X1,X8)) = X8 & r2_hidden(sK6(X0,X1,X8),X1) & r2_hidden(sK5(X0,X1,X8),X0)))),
% 11.53/2.00    introduced(choice_axiom,[])).
% 11.53/2.00  
% 11.53/2.00  fof(f28,plain,(
% 11.53/2.00    ( ! [X3] : (! [X2,X1,X0] : (? [X6,X7] : (k4_tarski(X6,X7) = X3 & r2_hidden(X7,X1) & r2_hidden(X6,X0)) => (k4_tarski(sK3(X0,X1,X2),sK4(X0,X1,X2)) = X3 & r2_hidden(sK4(X0,X1,X2),X1) & r2_hidden(sK3(X0,X1,X2),X0)))) )),
% 11.53/2.00    introduced(choice_axiom,[])).
% 11.53/2.00  
% 11.53/2.00  fof(f27,plain,(
% 11.53/2.00    ! [X2,X1,X0] : (? [X3] : ((! [X4,X5] : (k4_tarski(X4,X5) != X3 | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X0)) | ~r2_hidden(X3,X2)) & (? [X6,X7] : (k4_tarski(X6,X7) = X3 & r2_hidden(X7,X1) & r2_hidden(X6,X0)) | r2_hidden(X3,X2))) => ((! [X5,X4] : (k4_tarski(X4,X5) != sK2(X0,X1,X2) | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X0)) | ~r2_hidden(sK2(X0,X1,X2),X2)) & (? [X7,X6] : (k4_tarski(X6,X7) = sK2(X0,X1,X2) & r2_hidden(X7,X1) & r2_hidden(X6,X0)) | r2_hidden(sK2(X0,X1,X2),X2))))),
% 11.53/2.00    introduced(choice_axiom,[])).
% 11.53/2.00  
% 11.53/2.00  fof(f30,plain,(
% 11.53/2.00    ! [X0,X1,X2] : ((k2_zfmisc_1(X0,X1) = X2 | ((! [X4,X5] : (k4_tarski(X4,X5) != sK2(X0,X1,X2) | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X0)) | ~r2_hidden(sK2(X0,X1,X2),X2)) & ((k4_tarski(sK3(X0,X1,X2),sK4(X0,X1,X2)) = sK2(X0,X1,X2) & r2_hidden(sK4(X0,X1,X2),X1) & r2_hidden(sK3(X0,X1,X2),X0)) | r2_hidden(sK2(X0,X1,X2),X2)))) & (! [X8] : ((r2_hidden(X8,X2) | ! [X9,X10] : (k4_tarski(X9,X10) != X8 | ~r2_hidden(X10,X1) | ~r2_hidden(X9,X0))) & ((k4_tarski(sK5(X0,X1,X8),sK6(X0,X1,X8)) = X8 & r2_hidden(sK6(X0,X1,X8),X1) & r2_hidden(sK5(X0,X1,X8),X0)) | ~r2_hidden(X8,X2))) | k2_zfmisc_1(X0,X1) != X2))),
% 11.53/2.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5,sK6])],[f26,f29,f28,f27])).
% 11.53/2.00  
% 11.53/2.00  fof(f56,plain,(
% 11.53/2.00    ( ! [X2,X0,X1] : (k2_zfmisc_1(X0,X1) = X2 | r2_hidden(sK3(X0,X1,X2),X0) | r2_hidden(sK2(X0,X1,X2),X2)) )),
% 11.53/2.00    inference(cnf_transformation,[],[f30])).
% 11.53/2.00  
% 11.53/2.00  fof(f7,axiom,(
% 11.53/2.00    ! [X0] : k5_xboole_0(X0,X0) = k1_xboole_0),
% 11.53/2.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.53/2.00  
% 11.53/2.00  fof(f51,plain,(
% 11.53/2.00    ( ! [X0] : (k5_xboole_0(X0,X0) = k1_xboole_0) )),
% 11.53/2.00    inference(cnf_transformation,[],[f7])).
% 11.53/2.00  
% 11.53/2.00  fof(f2,axiom,(
% 11.53/2.00    ! [X0,X1,X2] : (r2_hidden(X0,k5_xboole_0(X1,X2)) <=> ~(r2_hidden(X0,X1) <=> r2_hidden(X0,X2)))),
% 11.53/2.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.53/2.00  
% 11.53/2.00  fof(f12,plain,(
% 11.53/2.00    ! [X0,X1,X2] : (r2_hidden(X0,k5_xboole_0(X1,X2)) <=> (r2_hidden(X0,X1) <~> r2_hidden(X0,X2)))),
% 11.53/2.00    inference(ennf_transformation,[],[f2])).
% 11.53/2.00  
% 11.53/2.00  fof(f22,plain,(
% 11.53/2.00    ! [X0,X1,X2] : ((r2_hidden(X0,k5_xboole_0(X1,X2)) | ((r2_hidden(X0,X1) | ~r2_hidden(X0,X2)) & (r2_hidden(X0,X2) | ~r2_hidden(X0,X1)))) & (((~r2_hidden(X0,X2) | ~r2_hidden(X0,X1)) & (r2_hidden(X0,X2) | r2_hidden(X0,X1))) | ~r2_hidden(X0,k5_xboole_0(X1,X2))))),
% 11.53/2.00    inference(nnf_transformation,[],[f12])).
% 11.53/2.00  
% 11.53/2.00  fof(f44,plain,(
% 11.53/2.00    ( ! [X2,X0,X1] : (~r2_hidden(X0,X2) | ~r2_hidden(X0,X1) | ~r2_hidden(X0,k5_xboole_0(X1,X2))) )),
% 11.53/2.00    inference(cnf_transformation,[],[f22])).
% 11.53/2.00  
% 11.53/2.00  fof(f6,axiom,(
% 11.53/2.00    ! [X0] : (k1_xboole_0 != X0 => r2_xboole_0(k1_xboole_0,X0))),
% 11.53/2.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.53/2.00  
% 11.53/2.00  fof(f15,plain,(
% 11.53/2.00    ! [X0] : (r2_xboole_0(k1_xboole_0,X0) | k1_xboole_0 = X0)),
% 11.53/2.00    inference(ennf_transformation,[],[f6])).
% 11.53/2.00  
% 11.53/2.00  fof(f50,plain,(
% 11.53/2.00    ( ! [X0] : (r2_xboole_0(k1_xboole_0,X0) | k1_xboole_0 = X0) )),
% 11.53/2.00    inference(cnf_transformation,[],[f15])).
% 11.53/2.00  
% 11.53/2.00  fof(f4,axiom,(
% 11.53/2.00    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 11.53/2.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.53/2.00  
% 11.53/2.00  fof(f48,plain,(
% 11.53/2.00    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 11.53/2.00    inference(cnf_transformation,[],[f4])).
% 11.53/2.00  
% 11.53/2.00  fof(f5,axiom,(
% 11.53/2.00    ! [X0,X1] : ~(r2_xboole_0(X1,X0) & r1_tarski(X0,X1))),
% 11.53/2.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.53/2.00  
% 11.53/2.00  fof(f14,plain,(
% 11.53/2.00    ! [X0,X1] : (~r2_xboole_0(X1,X0) | ~r1_tarski(X0,X1))),
% 11.53/2.00    inference(ennf_transformation,[],[f5])).
% 11.53/2.00  
% 11.53/2.00  fof(f49,plain,(
% 11.53/2.00    ( ! [X0,X1] : (~r2_xboole_0(X1,X0) | ~r1_tarski(X0,X1)) )),
% 11.53/2.00    inference(cnf_transformation,[],[f14])).
% 11.53/2.00  
% 11.53/2.00  fof(f1,axiom,(
% 11.53/2.00    ! [X0,X1,X2] : (k3_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 11.53/2.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.53/2.00  
% 11.53/2.00  fof(f17,plain,(
% 11.53/2.00    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k3_xboole_0(X0,X1) != X2))),
% 11.53/2.00    inference(nnf_transformation,[],[f1])).
% 11.53/2.00  
% 11.53/2.00  fof(f18,plain,(
% 11.53/2.00    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ~r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k3_xboole_0(X0,X1) != X2))),
% 11.53/2.00    inference(flattening,[],[f17])).
% 11.53/2.00  
% 11.53/2.00  fof(f19,plain,(
% 11.53/2.00    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k3_xboole_0(X0,X1) != X2))),
% 11.53/2.00    inference(rectify,[],[f18])).
% 11.53/2.00  
% 11.53/2.00  fof(f20,plain,(
% 11.53/2.00    ! [X2,X1,X0] : (? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((~r2_hidden(sK0(X0,X1,X2),X1) | ~r2_hidden(sK0(X0,X1,X2),X0) | ~r2_hidden(sK0(X0,X1,X2),X2)) & ((r2_hidden(sK0(X0,X1,X2),X1) & r2_hidden(sK0(X0,X1,X2),X0)) | r2_hidden(sK0(X0,X1,X2),X2))))),
% 11.53/2.00    introduced(choice_axiom,[])).
% 11.53/2.00  
% 11.53/2.00  fof(f21,plain,(
% 11.53/2.00    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ((~r2_hidden(sK0(X0,X1,X2),X1) | ~r2_hidden(sK0(X0,X1,X2),X0) | ~r2_hidden(sK0(X0,X1,X2),X2)) & ((r2_hidden(sK0(X0,X1,X2),X1) & r2_hidden(sK0(X0,X1,X2),X0)) | r2_hidden(sK0(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k3_xboole_0(X0,X1) != X2))),
% 11.53/2.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f19,f20])).
% 11.53/2.00  
% 11.53/2.00  fof(f38,plain,(
% 11.53/2.00    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k3_xboole_0(X0,X1) != X2) )),
% 11.53/2.00    inference(cnf_transformation,[],[f21])).
% 11.53/2.00  
% 11.53/2.00  fof(f67,plain,(
% 11.53/2.00    ( ! [X4,X0,X1] : (r2_hidden(X4,X1) | ~r2_hidden(X4,k3_xboole_0(X0,X1))) )),
% 11.53/2.00    inference(equality_resolution,[],[f38])).
% 11.53/2.00  
% 11.53/2.00  fof(f3,axiom,(
% 11.53/2.00    ! [X0] : ~(! [X1] : ~r2_hidden(X1,X0) & k1_xboole_0 != X0)),
% 11.53/2.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.53/2.00  
% 11.53/2.00  fof(f13,plain,(
% 11.53/2.00    ! [X0] : (? [X1] : r2_hidden(X1,X0) | k1_xboole_0 = X0)),
% 11.53/2.00    inference(ennf_transformation,[],[f3])).
% 11.53/2.00  
% 11.53/2.00  fof(f23,plain,(
% 11.53/2.00    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK1(X0),X0))),
% 11.53/2.00    introduced(choice_axiom,[])).
% 11.53/2.00  
% 11.53/2.00  fof(f24,plain,(
% 11.53/2.00    ! [X0] : (r2_hidden(sK1(X0),X0) | k1_xboole_0 = X0)),
% 11.53/2.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f13,f23])).
% 11.53/2.00  
% 11.53/2.00  fof(f47,plain,(
% 11.53/2.00    ( ! [X0] : (r2_hidden(sK1(X0),X0) | k1_xboole_0 = X0) )),
% 11.53/2.00    inference(cnf_transformation,[],[f24])).
% 11.53/2.00  
% 11.53/2.00  fof(f10,conjecture,(
% 11.53/2.00    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 11.53/2.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.53/2.00  
% 11.53/2.00  fof(f11,negated_conjecture,(
% 11.53/2.00    ~! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 11.53/2.00    inference(negated_conjecture,[],[f10])).
% 11.53/2.00  
% 11.53/2.00  fof(f16,plain,(
% 11.53/2.00    ? [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <~> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 11.53/2.00    inference(ennf_transformation,[],[f11])).
% 11.53/2.00  
% 11.53/2.00  fof(f33,plain,(
% 11.53/2.00    ? [X0,X1] : (((k1_xboole_0 != X1 & k1_xboole_0 != X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 = k2_zfmisc_1(X0,X1)))),
% 11.53/2.00    inference(nnf_transformation,[],[f16])).
% 11.53/2.00  
% 11.53/2.00  fof(f34,plain,(
% 11.53/2.00    ? [X0,X1] : (((k1_xboole_0 != X1 & k1_xboole_0 != X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 = k2_zfmisc_1(X0,X1)))),
% 11.53/2.00    inference(flattening,[],[f33])).
% 11.53/2.00  
% 11.53/2.00  fof(f35,plain,(
% 11.53/2.00    ? [X0,X1] : (((k1_xboole_0 != X1 & k1_xboole_0 != X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 = k2_zfmisc_1(X0,X1))) => (((k1_xboole_0 != sK8 & k1_xboole_0 != sK7) | k1_xboole_0 != k2_zfmisc_1(sK7,sK8)) & (k1_xboole_0 = sK8 | k1_xboole_0 = sK7 | k1_xboole_0 = k2_zfmisc_1(sK7,sK8)))),
% 11.53/2.00    introduced(choice_axiom,[])).
% 11.53/2.00  
% 11.53/2.00  fof(f36,plain,(
% 11.53/2.00    ((k1_xboole_0 != sK8 & k1_xboole_0 != sK7) | k1_xboole_0 != k2_zfmisc_1(sK7,sK8)) & (k1_xboole_0 = sK8 | k1_xboole_0 = sK7 | k1_xboole_0 = k2_zfmisc_1(sK7,sK8))),
% 11.53/2.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7,sK8])],[f34,f35])).
% 11.53/2.00  
% 11.53/2.00  fof(f63,plain,(
% 11.53/2.00    k1_xboole_0 = sK8 | k1_xboole_0 = sK7 | k1_xboole_0 = k2_zfmisc_1(sK7,sK8)),
% 11.53/2.00    inference(cnf_transformation,[],[f36])).
% 11.53/2.00  
% 11.53/2.00  fof(f9,axiom,(
% 11.53/2.00    ! [X0,X1,X2,X3] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) <=> (r2_hidden(X1,X3) & r2_hidden(X0,X2)))),
% 11.53/2.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.53/2.00  
% 11.53/2.00  fof(f31,plain,(
% 11.53/2.00    ! [X0,X1,X2,X3] : ((r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | (~r2_hidden(X1,X3) | ~r2_hidden(X0,X2))) & ((r2_hidden(X1,X3) & r2_hidden(X0,X2)) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))))),
% 11.53/2.00    inference(nnf_transformation,[],[f9])).
% 11.53/2.00  
% 11.53/2.00  fof(f32,plain,(
% 11.53/2.00    ! [X0,X1,X2,X3] : ((r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | ~r2_hidden(X1,X3) | ~r2_hidden(X0,X2)) & ((r2_hidden(X1,X3) & r2_hidden(X0,X2)) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))))),
% 11.53/2.00    inference(flattening,[],[f31])).
% 11.53/2.00  
% 11.53/2.00  fof(f62,plain,(
% 11.53/2.00    ( ! [X2,X0,X3,X1] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | ~r2_hidden(X1,X3) | ~r2_hidden(X0,X2)) )),
% 11.53/2.00    inference(cnf_transformation,[],[f32])).
% 11.53/2.00  
% 11.53/2.00  fof(f64,plain,(
% 11.53/2.00    k1_xboole_0 != sK7 | k1_xboole_0 != k2_zfmisc_1(sK7,sK8)),
% 11.53/2.00    inference(cnf_transformation,[],[f36])).
% 11.53/2.00  
% 11.53/2.00  fof(f65,plain,(
% 11.53/2.00    k1_xboole_0 != sK8 | k1_xboole_0 != k2_zfmisc_1(sK7,sK8)),
% 11.53/2.00    inference(cnf_transformation,[],[f36])).
% 11.53/2.00  
% 11.53/2.00  fof(f57,plain,(
% 11.53/2.00    ( ! [X2,X0,X1] : (k2_zfmisc_1(X0,X1) = X2 | r2_hidden(sK4(X0,X1,X2),X1) | r2_hidden(sK2(X0,X1,X2),X2)) )),
% 11.53/2.00    inference(cnf_transformation,[],[f30])).
% 11.53/2.00  
% 11.53/2.00  cnf(c_18,plain,
% 11.53/2.00      ( r2_hidden(sK3(X0,X1,X2),X0)
% 11.53/2.00      | r2_hidden(sK2(X0,X1,X2),X2)
% 11.53/2.00      | k2_zfmisc_1(X0,X1) = X2 ),
% 11.53/2.00      inference(cnf_transformation,[],[f56]) ).
% 11.53/2.00  
% 11.53/2.00  cnf(c_785,plain,
% 11.53/2.00      ( k2_zfmisc_1(X0,X1) = X2
% 11.53/2.00      | r2_hidden(sK3(X0,X1,X2),X0) = iProver_top
% 11.53/2.00      | r2_hidden(sK2(X0,X1,X2),X2) = iProver_top ),
% 11.53/2.00      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 11.53/2.00  
% 11.53/2.00  cnf(c_14,plain,
% 11.53/2.00      ( k5_xboole_0(X0,X0) = k1_xboole_0 ),
% 11.53/2.00      inference(cnf_transformation,[],[f51]) ).
% 11.53/2.00  
% 11.53/2.00  cnf(c_8,plain,
% 11.53/2.00      ( ~ r2_hidden(X0,X1)
% 11.53/2.00      | ~ r2_hidden(X0,X2)
% 11.53/2.00      | ~ r2_hidden(X0,k5_xboole_0(X1,X2)) ),
% 11.53/2.00      inference(cnf_transformation,[],[f44]) ).
% 11.53/2.00  
% 11.53/2.00  cnf(c_791,plain,
% 11.53/2.00      ( r2_hidden(X0,X1) != iProver_top
% 11.53/2.00      | r2_hidden(X0,X2) != iProver_top
% 11.53/2.00      | r2_hidden(X0,k5_xboole_0(X1,X2)) != iProver_top ),
% 11.53/2.00      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 11.53/2.00  
% 11.53/2.00  cnf(c_4221,plain,
% 11.53/2.00      ( r2_hidden(X0,X1) != iProver_top
% 11.53/2.00      | r2_hidden(X0,k1_xboole_0) != iProver_top ),
% 11.53/2.00      inference(superposition,[status(thm)],[c_14,c_791]) ).
% 11.53/2.00  
% 11.53/2.00  cnf(c_13,plain,
% 11.53/2.00      ( r2_xboole_0(k1_xboole_0,X0) | k1_xboole_0 = X0 ),
% 11.53/2.00      inference(cnf_transformation,[],[f50]) ).
% 11.53/2.00  
% 11.53/2.00  cnf(c_11,plain,
% 11.53/2.00      ( r1_tarski(k3_xboole_0(X0,X1),X0) ),
% 11.53/2.00      inference(cnf_transformation,[],[f48]) ).
% 11.53/2.00  
% 11.53/2.00  cnf(c_12,plain,
% 11.53/2.00      ( ~ r2_xboole_0(X0,X1) | ~ r1_tarski(X1,X0) ),
% 11.53/2.00      inference(cnf_transformation,[],[f49]) ).
% 11.53/2.00  
% 11.53/2.00  cnf(c_286,plain,
% 11.53/2.00      ( ~ r2_xboole_0(X0,X1) | X0 != X2 | k3_xboole_0(X2,X3) != X1 ),
% 11.53/2.00      inference(resolution_lifted,[status(thm)],[c_11,c_12]) ).
% 11.53/2.00  
% 11.53/2.00  cnf(c_287,plain,
% 11.53/2.00      ( ~ r2_xboole_0(X0,k3_xboole_0(X0,X1)) ),
% 11.53/2.00      inference(unflattening,[status(thm)],[c_286]) ).
% 11.53/2.00  
% 11.53/2.00  cnf(c_297,plain,
% 11.53/2.00      ( k3_xboole_0(X0,X1) != X2 | k1_xboole_0 != X0 | k1_xboole_0 = X2 ),
% 11.53/2.00      inference(resolution_lifted,[status(thm)],[c_13,c_287]) ).
% 11.53/2.00  
% 11.53/2.00  cnf(c_298,plain,
% 11.53/2.00      ( k1_xboole_0 = k3_xboole_0(k1_xboole_0,X0) ),
% 11.53/2.00      inference(unflattening,[status(thm)],[c_297]) ).
% 11.53/2.00  
% 11.53/2.00  cnf(c_4,plain,
% 11.53/2.00      ( r2_hidden(X0,X1) | ~ r2_hidden(X0,k3_xboole_0(X2,X1)) ),
% 11.53/2.00      inference(cnf_transformation,[],[f67]) ).
% 11.53/2.00  
% 11.53/2.00  cnf(c_795,plain,
% 11.53/2.00      ( r2_hidden(X0,X1) = iProver_top
% 11.53/2.00      | r2_hidden(X0,k3_xboole_0(X2,X1)) != iProver_top ),
% 11.53/2.00      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 11.53/2.00  
% 11.53/2.00  cnf(c_1246,plain,
% 11.53/2.00      ( r2_hidden(X0,X1) = iProver_top
% 11.53/2.00      | r2_hidden(X0,k1_xboole_0) != iProver_top ),
% 11.53/2.00      inference(superposition,[status(thm)],[c_298,c_795]) ).
% 11.53/2.00  
% 11.53/2.00  cnf(c_4248,plain,
% 11.53/2.00      ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
% 11.53/2.00      inference(global_propositional_subsumption,[status(thm)],[c_4221,c_1246]) ).
% 11.53/2.00  
% 11.53/2.00  cnf(c_4254,plain,
% 11.53/2.00      ( k2_zfmisc_1(k1_xboole_0,X0) = X1
% 11.53/2.00      | r2_hidden(sK2(k1_xboole_0,X0,X1),X1) = iProver_top ),
% 11.53/2.00      inference(superposition,[status(thm)],[c_785,c_4248]) ).
% 11.53/2.00  
% 11.53/2.00  cnf(c_4253,plain,
% 11.53/2.00      ( k2_zfmisc_1(X0,X1) = k1_xboole_0
% 11.53/2.00      | r2_hidden(sK3(X0,X1,k1_xboole_0),X0) = iProver_top ),
% 11.53/2.00      inference(superposition,[status(thm)],[c_785,c_4248]) ).
% 11.53/2.00  
% 11.53/2.00  cnf(c_5885,plain,
% 11.53/2.00      ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
% 11.53/2.00      inference(superposition,[status(thm)],[c_4253,c_4248]) ).
% 11.53/2.00  
% 11.53/2.00  cnf(c_6026,plain,
% 11.53/2.00      ( k1_xboole_0 = X0 | r2_hidden(sK2(k1_xboole_0,X1,X0),X0) = iProver_top ),
% 11.53/2.00      inference(demodulation,[status(thm)],[c_4254,c_5885]) ).
% 11.53/2.00  
% 11.53/2.00  cnf(c_10,plain,
% 11.53/2.00      ( r2_hidden(sK1(X0),X0) | k1_xboole_0 = X0 ),
% 11.53/2.00      inference(cnf_transformation,[],[f47]) ).
% 11.53/2.00  
% 11.53/2.00  cnf(c_789,plain,
% 11.53/2.00      ( k1_xboole_0 = X0 | r2_hidden(sK1(X0),X0) = iProver_top ),
% 11.53/2.00      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 11.53/2.00  
% 11.53/2.00  cnf(c_28,negated_conjecture,
% 11.53/2.00      ( k1_xboole_0 = k2_zfmisc_1(sK7,sK8)
% 11.53/2.00      | k1_xboole_0 = sK7
% 11.53/2.00      | k1_xboole_0 = sK8 ),
% 11.53/2.00      inference(cnf_transformation,[],[f63]) ).
% 11.53/2.00  
% 11.53/2.00  cnf(c_23,plain,
% 11.53/2.00      ( ~ r2_hidden(X0,X1)
% 11.53/2.00      | ~ r2_hidden(X2,X3)
% 11.53/2.00      | r2_hidden(k4_tarski(X0,X2),k2_zfmisc_1(X1,X3)) ),
% 11.53/2.00      inference(cnf_transformation,[],[f62]) ).
% 11.53/2.00  
% 11.53/2.00  cnf(c_780,plain,
% 11.53/2.00      ( r2_hidden(X0,X1) != iProver_top
% 11.53/2.00      | r2_hidden(X2,X3) != iProver_top
% 11.53/2.00      | r2_hidden(k4_tarski(X0,X2),k2_zfmisc_1(X1,X3)) = iProver_top ),
% 11.53/2.00      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 11.53/2.01  
% 11.53/2.01  cnf(c_2811,plain,
% 11.53/2.01      ( sK7 = k1_xboole_0
% 11.53/2.01      | sK8 = k1_xboole_0
% 11.53/2.01      | r2_hidden(X0,sK7) != iProver_top
% 11.53/2.01      | r2_hidden(X1,sK8) != iProver_top
% 11.53/2.01      | r2_hidden(k4_tarski(X0,X1),k1_xboole_0) = iProver_top ),
% 11.53/2.01      inference(superposition,[status(thm)],[c_28,c_780]) ).
% 11.53/2.01  
% 11.53/2.01  cnf(c_3124,plain,
% 11.53/2.01      ( sK7 = k1_xboole_0
% 11.53/2.01      | sK8 = k1_xboole_0
% 11.53/2.01      | r2_hidden(X0,sK7) != iProver_top
% 11.53/2.01      | r2_hidden(X1,sK8) != iProver_top
% 11.53/2.01      | r2_hidden(k4_tarski(X0,X1),X2) = iProver_top ),
% 11.53/2.01      inference(superposition,[status(thm)],[c_2811,c_1246]) ).
% 11.53/2.01  
% 11.53/2.01  cnf(c_4259,plain,
% 11.53/2.01      ( sK7 = k1_xboole_0
% 11.53/2.01      | sK8 = k1_xboole_0
% 11.53/2.01      | r2_hidden(X0,sK7) != iProver_top
% 11.53/2.01      | r2_hidden(X1,sK8) != iProver_top ),
% 11.53/2.01      inference(superposition,[status(thm)],[c_3124,c_4248]) ).
% 11.53/2.01  
% 11.53/2.01  cnf(c_4615,plain,
% 11.53/2.01      ( sK7 = k1_xboole_0
% 11.53/2.01      | sK8 = k1_xboole_0
% 11.53/2.01      | r2_hidden(X0,sK8) != iProver_top ),
% 11.53/2.01      inference(superposition,[status(thm)],[c_789,c_4259]) ).
% 11.53/2.01  
% 11.53/2.01  cnf(c_6507,plain,
% 11.53/2.01      ( sK7 = k1_xboole_0 | sK8 = k1_xboole_0 ),
% 11.53/2.01      inference(superposition,[status(thm)],[c_6026,c_4615]) ).
% 11.53/2.01  
% 11.53/2.01  cnf(c_27,negated_conjecture,
% 11.53/2.01      ( k1_xboole_0 != k2_zfmisc_1(sK7,sK8) | k1_xboole_0 != sK7 ),
% 11.53/2.01      inference(cnf_transformation,[],[f64]) ).
% 11.53/2.01  
% 11.53/2.01  cnf(c_28910,plain,
% 11.53/2.01      ( k2_zfmisc_1(k1_xboole_0,sK8) != k1_xboole_0
% 11.53/2.01      | sK7 != k1_xboole_0
% 11.53/2.01      | sK8 = k1_xboole_0 ),
% 11.53/2.01      inference(superposition,[status(thm)],[c_6507,c_27]) ).
% 11.53/2.01  
% 11.53/2.01  cnf(c_28912,plain,
% 11.53/2.01      ( sK7 != k1_xboole_0 | sK8 = k1_xboole_0 | k1_xboole_0 != k1_xboole_0 ),
% 11.53/2.01      inference(demodulation,[status(thm)],[c_28910,c_5885]) ).
% 11.53/2.01  
% 11.53/2.01  cnf(c_28913,plain,
% 11.53/2.01      ( sK7 != k1_xboole_0 | sK8 = k1_xboole_0 ),
% 11.53/2.01      inference(equality_resolution_simp,[status(thm)],[c_28912]) ).
% 11.53/2.01  
% 11.53/2.01  cnf(c_33527,plain,
% 11.53/2.01      ( sK8 = k1_xboole_0 ),
% 11.53/2.01      inference(global_propositional_subsumption,
% 11.53/2.01                [status(thm)],
% 11.53/2.01                [c_28913,c_6507]) ).
% 11.53/2.01  
% 11.53/2.01  cnf(c_26,negated_conjecture,
% 11.53/2.01      ( k1_xboole_0 != k2_zfmisc_1(sK7,sK8) | k1_xboole_0 != sK8 ),
% 11.53/2.01      inference(cnf_transformation,[],[f65]) ).
% 11.53/2.01  
% 11.53/2.01  cnf(c_33531,plain,
% 11.53/2.01      ( k2_zfmisc_1(sK7,k1_xboole_0) != k1_xboole_0
% 11.53/2.01      | k1_xboole_0 != k1_xboole_0 ),
% 11.53/2.01      inference(demodulation,[status(thm)],[c_33527,c_26]) ).
% 11.53/2.01  
% 11.53/2.01  cnf(c_33532,plain,
% 11.53/2.01      ( k2_zfmisc_1(sK7,k1_xboole_0) != k1_xboole_0 ),
% 11.53/2.01      inference(equality_resolution_simp,[status(thm)],[c_33531]) ).
% 11.53/2.01  
% 11.53/2.01  cnf(c_17,plain,
% 11.53/2.01      ( r2_hidden(sK4(X0,X1,X2),X1)
% 11.53/2.01      | r2_hidden(sK2(X0,X1,X2),X2)
% 11.53/2.01      | k2_zfmisc_1(X0,X1) = X2 ),
% 11.53/2.01      inference(cnf_transformation,[],[f57]) ).
% 11.53/2.01  
% 11.53/2.01  cnf(c_786,plain,
% 11.53/2.01      ( k2_zfmisc_1(X0,X1) = X2
% 11.53/2.01      | r2_hidden(sK4(X0,X1,X2),X1) = iProver_top
% 11.53/2.01      | r2_hidden(sK2(X0,X1,X2),X2) = iProver_top ),
% 11.53/2.01      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 11.53/2.01  
% 11.53/2.01  cnf(c_4349,plain,
% 11.53/2.01      ( k2_zfmisc_1(X0,X1) = k1_xboole_0
% 11.53/2.01      | r2_hidden(sK4(X0,X1,k1_xboole_0),X1) = iProver_top ),
% 11.53/2.01      inference(superposition,[status(thm)],[c_786,c_4248]) ).
% 11.53/2.01  
% 11.53/2.01  cnf(c_6056,plain,
% 11.53/2.01      ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
% 11.53/2.01      inference(superposition,[status(thm)],[c_4349,c_4248]) ).
% 11.53/2.01  
% 11.53/2.01  cnf(c_33533,plain,
% 11.53/2.01      ( k1_xboole_0 != k1_xboole_0 ),
% 11.53/2.01      inference(demodulation,[status(thm)],[c_33532,c_6056]) ).
% 11.53/2.01  
% 11.53/2.01  cnf(c_33534,plain,
% 11.53/2.01      ( $false ),
% 11.53/2.01      inference(equality_resolution_simp,[status(thm)],[c_33533]) ).
% 11.53/2.01  
% 11.53/2.01  
% 11.53/2.01  % SZS output end CNFRefutation for theBenchmark.p
% 11.53/2.01  
% 11.53/2.01  ------                               Statistics
% 11.53/2.01  
% 11.53/2.01  ------ General
% 11.53/2.01  
% 11.53/2.01  abstr_ref_over_cycles:                  0
% 11.53/2.01  abstr_ref_under_cycles:                 0
% 11.53/2.01  gc_basic_clause_elim:                   0
% 11.53/2.01  forced_gc_time:                         0
% 11.53/2.01  parsing_time:                           0.008
% 11.53/2.01  unif_index_cands_time:                  0.
% 11.53/2.01  unif_index_add_time:                    0.
% 11.53/2.01  orderings_time:                         0.
% 11.53/2.01  out_proof_time:                         0.009
% 11.53/2.01  total_time:                             1.103
% 11.53/2.01  num_of_symbols:                         48
% 11.53/2.01  num_of_terms:                           64663
% 11.53/2.01  
% 11.53/2.01  ------ Preprocessing
% 11.53/2.01  
% 11.53/2.01  num_of_splits:                          0
% 11.53/2.01  num_of_split_atoms:                     0
% 11.53/2.01  num_of_reused_defs:                     0
% 11.53/2.01  num_eq_ax_congr_red:                    69
% 11.53/2.01  num_of_sem_filtered_clauses:            1
% 11.53/2.01  num_of_subtypes:                        0
% 11.53/2.01  monotx_restored_types:                  0
% 11.53/2.01  sat_num_of_epr_types:                   0
% 11.53/2.01  sat_num_of_non_cyclic_types:            0
% 11.53/2.01  sat_guarded_non_collapsed_types:        0
% 11.53/2.01  num_pure_diseq_elim:                    0
% 11.53/2.01  simp_replaced_by:                       0
% 11.53/2.01  res_preprocessed:                       123
% 11.53/2.01  prep_upred:                             0
% 11.53/2.01  prep_unflattend:                        4
% 11.53/2.01  smt_new_axioms:                         0
% 11.53/2.01  pred_elim_cands:                        1
% 11.53/2.01  pred_elim:                              2
% 11.53/2.01  pred_elim_cl:                           2
% 11.53/2.01  pred_elim_cycles:                       4
% 11.53/2.01  merged_defs:                            0
% 11.53/2.01  merged_defs_ncl:                        0
% 11.53/2.01  bin_hyper_res:                          0
% 11.53/2.01  prep_cycles:                            4
% 11.53/2.01  pred_elim_time:                         0.002
% 11.53/2.01  splitting_time:                         0.
% 11.53/2.01  sem_filter_time:                        0.
% 11.53/2.01  monotx_time:                            0.001
% 11.53/2.01  subtype_inf_time:                       0.
% 11.53/2.01  
% 11.53/2.01  ------ Problem properties
% 11.53/2.01  
% 11.53/2.01  clauses:                                27
% 11.53/2.01  conjectures:                            3
% 11.53/2.01  epr:                                    0
% 11.53/2.01  horn:                                   17
% 11.53/2.01  ground:                                 3
% 11.53/2.01  unary:                                  2
% 11.53/2.01  binary:                                 10
% 11.53/2.01  lits:                                   70
% 11.53/2.01  lits_eq:                                20
% 11.53/2.01  fd_pure:                                0
% 11.53/2.01  fd_pseudo:                              0
% 11.53/2.01  fd_cond:                                1
% 11.53/2.01  fd_pseudo_cond:                         7
% 11.53/2.01  ac_symbols:                             0
% 11.53/2.01  
% 11.53/2.01  ------ Propositional Solver
% 11.53/2.01  
% 11.53/2.01  prop_solver_calls:                      32
% 11.53/2.01  prop_fast_solver_calls:                 2411
% 11.53/2.01  smt_solver_calls:                       0
% 11.53/2.01  smt_fast_solver_calls:                  0
% 11.53/2.01  prop_num_of_clauses:                    15927
% 11.53/2.01  prop_preprocess_simplified:             30915
% 11.53/2.01  prop_fo_subsumed:                       564
% 11.53/2.01  prop_solver_time:                       0.
% 11.53/2.01  smt_solver_time:                        0.
% 11.53/2.01  smt_fast_solver_time:                   0.
% 11.53/2.01  prop_fast_solver_time:                  0.
% 11.53/2.01  prop_unsat_core_time:                   0.
% 11.53/2.01  
% 11.53/2.01  ------ QBF
% 11.53/2.01  
% 11.53/2.01  qbf_q_res:                              0
% 11.53/2.01  qbf_num_tautologies:                    0
% 11.53/2.01  qbf_prep_cycles:                        0
% 11.53/2.01  
% 11.53/2.01  ------ BMC1
% 11.53/2.01  
% 11.53/2.01  bmc1_current_bound:                     -1
% 11.53/2.01  bmc1_last_solved_bound:                 -1
% 11.53/2.01  bmc1_unsat_core_size:                   -1
% 11.53/2.01  bmc1_unsat_core_parents_size:           -1
% 11.53/2.01  bmc1_merge_next_fun:                    0
% 11.53/2.01  bmc1_unsat_core_clauses_time:           0.
% 11.53/2.01  
% 11.53/2.01  ------ Instantiation
% 11.53/2.01  
% 11.53/2.01  inst_num_of_clauses:                    3326
% 11.53/2.01  inst_num_in_passive:                    2460
% 11.53/2.01  inst_num_in_active:                     747
% 11.53/2.01  inst_num_in_unprocessed:                122
% 11.53/2.01  inst_num_of_loops:                      910
% 11.53/2.01  inst_num_of_learning_restarts:          0
% 11.53/2.01  inst_num_moves_active_passive:          161
% 11.53/2.01  inst_lit_activity:                      0
% 11.53/2.01  inst_lit_activity_moves:                0
% 11.53/2.01  inst_num_tautologies:                   0
% 11.53/2.01  inst_num_prop_implied:                  0
% 11.53/2.01  inst_num_existing_simplified:           0
% 11.53/2.01  inst_num_eq_res_simplified:             0
% 11.53/2.01  inst_num_child_elim:                    0
% 11.53/2.01  inst_num_of_dismatching_blockings:      3532
% 11.53/2.01  inst_num_of_non_proper_insts:           2359
% 11.53/2.01  inst_num_of_duplicates:                 0
% 11.53/2.01  inst_inst_num_from_inst_to_res:         0
% 11.53/2.01  inst_dismatching_checking_time:         0.
% 11.53/2.01  
% 11.53/2.01  ------ Resolution
% 11.53/2.01  
% 11.53/2.01  res_num_of_clauses:                     0
% 11.53/2.01  res_num_in_passive:                     0
% 11.53/2.01  res_num_in_active:                      0
% 11.53/2.01  res_num_of_loops:                       127
% 11.53/2.01  res_forward_subset_subsumed:            43
% 11.53/2.01  res_backward_subset_subsumed:           6
% 11.53/2.01  res_forward_subsumed:                   0
% 11.53/2.01  res_backward_subsumed:                  0
% 11.53/2.01  res_forward_subsumption_resolution:     0
% 11.53/2.01  res_backward_subsumption_resolution:    0
% 11.53/2.01  res_clause_to_clause_subsumption:       8345
% 11.53/2.01  res_orphan_elimination:                 0
% 11.53/2.01  res_tautology_del:                      114
% 11.53/2.01  res_num_eq_res_simplified:              0
% 11.53/2.01  res_num_sel_changes:                    0
% 11.53/2.01  res_moves_from_active_to_pass:          0
% 11.53/2.01  
% 11.53/2.01  ------ Superposition
% 11.53/2.01  
% 11.53/2.01  sup_time_total:                         0.
% 11.53/2.01  sup_time_generating:                    0.
% 11.53/2.01  sup_time_sim_full:                      0.
% 11.53/2.01  sup_time_sim_immed:                     0.
% 11.53/2.01  
% 11.53/2.01  sup_num_of_clauses:                     1041
% 11.53/2.01  sup_num_in_active:                      150
% 11.53/2.01  sup_num_in_passive:                     891
% 11.53/2.01  sup_num_of_loops:                       180
% 11.53/2.01  sup_fw_superposition:                   515
% 11.53/2.01  sup_bw_superposition:                   1875
% 11.53/2.01  sup_immediate_simplified:               1023
% 11.53/2.01  sup_given_eliminated:                   2
% 11.53/2.01  comparisons_done:                       0
% 11.53/2.01  comparisons_avoided:                    105
% 11.53/2.01  
% 11.53/2.01  ------ Simplifications
% 11.53/2.01  
% 11.53/2.01  
% 11.53/2.01  sim_fw_subset_subsumed:                 724
% 11.53/2.01  sim_bw_subset_subsumed:                 31
% 11.53/2.01  sim_fw_subsumed:                        74
% 11.53/2.01  sim_bw_subsumed:                        33
% 11.53/2.01  sim_fw_subsumption_res:                 0
% 11.53/2.01  sim_bw_subsumption_res:                 0
% 11.53/2.01  sim_tautology_del:                      34
% 11.53/2.01  sim_eq_tautology_del:                   188
% 11.53/2.01  sim_eq_res_simp:                        9
% 11.53/2.01  sim_fw_demodulated:                     261
% 11.53/2.01  sim_bw_demodulated:                     9
% 11.53/2.01  sim_light_normalised:                   88
% 11.53/2.01  sim_joinable_taut:                      0
% 11.53/2.01  sim_joinable_simp:                      0
% 11.53/2.01  sim_ac_normalised:                      0
% 11.53/2.01  sim_smt_subsumption:                    0
% 11.53/2.01  
%------------------------------------------------------------------------------
