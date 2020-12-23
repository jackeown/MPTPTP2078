%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:36:57 EST 2020

% Result     : Theorem 3.69s
% Output     : CNFRefutation 3.69s
% Verified   : 
% Statistics : Number of formulae       :  134 (1263 expanded)
%              Number of clauses        :   85 ( 488 expanded)
%              Number of leaves         :   17 ( 324 expanded)
%              Depth                    :   23
%              Number of atoms          :  477 (5861 expanded)
%              Number of equality atoms :  242 (1490 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal clause size      :   18 (   2 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f6,axiom,(
    ! [X0,X1] :
      ( k3_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] :
              ( r2_hidden(X3,X0)
              & r2_hidden(X2,X3) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
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
    inference(nnf_transformation,[],[f6])).

fof(f23,plain,(
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
    inference(rectify,[],[f22])).

fof(f26,plain,(
    ! [X5,X0] :
      ( ? [X7] :
          ( r2_hidden(X7,X0)
          & r2_hidden(X5,X7) )
     => ( r2_hidden(sK8(X0,X5),X0)
        & r2_hidden(X5,sK8(X0,X5)) ) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( r2_hidden(X4,X0)
          & r2_hidden(X2,X4) )
     => ( r2_hidden(sK7(X0,X1),X0)
        & r2_hidden(X2,sK7(X0,X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
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
              | ~ r2_hidden(sK6(X0,X1),X3) )
          | ~ r2_hidden(sK6(X0,X1),X1) )
        & ( ? [X4] :
              ( r2_hidden(X4,X0)
              & r2_hidden(sK6(X0,X1),X4) )
          | r2_hidden(sK6(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( k3_tarski(X0) = X1
        | ( ( ! [X3] :
                ( ~ r2_hidden(X3,X0)
                | ~ r2_hidden(sK6(X0,X1),X3) )
            | ~ r2_hidden(sK6(X0,X1),X1) )
          & ( ( r2_hidden(sK7(X0,X1),X0)
              & r2_hidden(sK6(X0,X1),sK7(X0,X1)) )
            | r2_hidden(sK6(X0,X1),X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] :
                  ( ~ r2_hidden(X6,X0)
                  | ~ r2_hidden(X5,X6) ) )
            & ( ( r2_hidden(sK8(X0,X5),X0)
                & r2_hidden(X5,sK8(X0,X5)) )
              | ~ r2_hidden(X5,X1) ) )
        | k3_tarski(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7,sK8])],[f23,f26,f25,f24])).

fof(f50,plain,(
    ! [X0,X1] :
      ( k3_tarski(X0) = X1
      | r2_hidden(sK7(X0,X1),X0)
      | r2_hidden(sK6(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f2,axiom,(
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

fof(f9,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X3] :
              ~ ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f2])).

fof(f12,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f14,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
     => ( r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ( r2_hidden(sK0(X0,X1),X1)
          & r2_hidden(sK0(X0,X1),X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f12,f14])).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f4,axiom,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f4])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f10,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    inference(unused_predicate_definition_removal,[],[f1])).

fof(f11,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) )
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f32,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f3,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f47,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(sK8(X0,X5),X0)
      | ~ r2_hidden(X5,X1)
      | k3_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f27])).

fof(f61,plain,(
    ! [X0,X5] :
      ( r2_hidden(sK8(X0,X5),X0)
      | ~ r2_hidden(X5,k3_tarski(X0)) ) ),
    inference(equality_resolution,[],[f47])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( k2_zfmisc_1(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ? [X4,X5] :
              ( k4_tarski(X4,X5) = X3
              & r2_hidden(X5,X1)
              & r2_hidden(X4,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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
    inference(nnf_transformation,[],[f5])).

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

fof(f39,plain,(
    ! [X2,X0,X8,X1] :
      ( r2_hidden(sK5(X0,X1,X8),X1)
      | ~ r2_hidden(X8,X2)
      | k2_zfmisc_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f21])).

fof(f58,plain,(
    ! [X0,X8,X1] :
      ( r2_hidden(sK5(X0,X1,X8),X1)
      | ~ r2_hidden(X8,k2_zfmisc_1(X0,X1)) ) ),
    inference(equality_resolution,[],[f39])).

fof(f38,plain,(
    ! [X2,X0,X8,X1] :
      ( r2_hidden(sK4(X0,X1,X8),X0)
      | ~ r2_hidden(X8,X2)
      | k2_zfmisc_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f21])).

fof(f59,plain,(
    ! [X0,X8,X1] :
      ( r2_hidden(sK4(X0,X1,X8),X0)
      | ~ r2_hidden(X8,k2_zfmisc_1(X0,X1)) ) ),
    inference(equality_resolution,[],[f38])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( k2_zfmisc_1(X0,X1) = X2
      | r2_hidden(sK2(X0,X1,X2),X0)
      | r2_hidden(sK1(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f7,conjecture,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f8,negated_conjecture,(
    ~ ! [X0,X1] :
        ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      <=> ( k1_xboole_0 = X1
          | k1_xboole_0 = X0 ) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f13,plain,(
    ? [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <~> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f28,plain,(
    ? [X0,X1] :
      ( ( ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 )
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 = k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f13])).

fof(f29,plain,(
    ? [X0,X1] :
      ( ( ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 )
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 = k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f28])).

fof(f30,plain,
    ( ? [X0,X1] :
        ( ( ( k1_xboole_0 != X1
            & k1_xboole_0 != X0 )
          | k1_xboole_0 != k2_zfmisc_1(X0,X1) )
        & ( k1_xboole_0 = X1
          | k1_xboole_0 = X0
          | k1_xboole_0 = k2_zfmisc_1(X0,X1) ) )
   => ( ( ( k1_xboole_0 != sK10
          & k1_xboole_0 != sK9 )
        | k1_xboole_0 != k2_zfmisc_1(sK9,sK10) )
      & ( k1_xboole_0 = sK10
        | k1_xboole_0 = sK9
        | k1_xboole_0 = k2_zfmisc_1(sK9,sK10) ) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,
    ( ( ( k1_xboole_0 != sK10
        & k1_xboole_0 != sK9 )
      | k1_xboole_0 != k2_zfmisc_1(sK9,sK10) )
    & ( k1_xboole_0 = sK10
      | k1_xboole_0 = sK9
      | k1_xboole_0 = k2_zfmisc_1(sK9,sK10) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK9,sK10])],[f29,f30])).

fof(f52,plain,
    ( k1_xboole_0 = sK10
    | k1_xboole_0 = sK9
    | k1_xboole_0 = k2_zfmisc_1(sK9,sK10) ),
    inference(cnf_transformation,[],[f31])).

fof(f41,plain,(
    ! [X2,X0,X10,X8,X1,X9] :
      ( r2_hidden(X8,X2)
      | k4_tarski(X9,X10) != X8
      | ~ r2_hidden(X10,X1)
      | ~ r2_hidden(X9,X0)
      | k2_zfmisc_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f21])).

fof(f55,plain,(
    ! [X2,X0,X10,X1,X9] :
      ( r2_hidden(k4_tarski(X9,X10),X2)
      | ~ r2_hidden(X10,X1)
      | ~ r2_hidden(X9,X0)
      | k2_zfmisc_1(X0,X1) != X2 ) ),
    inference(equality_resolution,[],[f41])).

fof(f56,plain,(
    ! [X0,X10,X1,X9] :
      ( r2_hidden(k4_tarski(X9,X10),k2_zfmisc_1(X0,X1))
      | ~ r2_hidden(X10,X1)
      | ~ r2_hidden(X9,X0) ) ),
    inference(equality_resolution,[],[f55])).

fof(f53,plain,
    ( k1_xboole_0 != sK9
    | k1_xboole_0 != k2_zfmisc_1(sK9,sK10) ),
    inference(cnf_transformation,[],[f31])).

fof(f54,plain,
    ( k1_xboole_0 != sK10
    | k1_xboole_0 != k2_zfmisc_1(sK9,sK10) ),
    inference(cnf_transformation,[],[f31])).

cnf(c_15,plain,
    ( r2_hidden(sK7(X0,X1),X0)
    | r2_hidden(sK6(X0,X1),X1)
    | k3_tarski(X0) = X1 ),
    inference(cnf_transformation,[],[f50])).

cnf(c_776,plain,
    ( k3_tarski(X0) = X1
    | r2_hidden(sK7(X0,X1),X0) = iProver_top
    | r2_hidden(sK6(X0,X1),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_1,plain,
    ( ~ r1_xboole_0(X0,X1)
    | ~ r2_hidden(X2,X0)
    | ~ r2_hidden(X2,X1) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_5,plain,
    ( r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_271,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X0,X2)
    | X3 != X1
    | k1_xboole_0 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_1,c_5])).

cnf(c_272,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k1_xboole_0) ),
    inference(unflattening,[status(thm)],[c_271])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r2_hidden(X2,X0)
    | r2_hidden(X2,X1) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_4,plain,
    ( r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_232,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | X3 != X2
    | k1_xboole_0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_4])).

cnf(c_233,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k1_xboole_0) ),
    inference(unflattening,[status(thm)],[c_232])).

cnf(c_276,plain,
    ( ~ r2_hidden(X0,k1_xboole_0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_272,c_233])).

cnf(c_771,plain,
    ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_276])).

cnf(c_1867,plain,
    ( k3_tarski(k1_xboole_0) = X0
    | r2_hidden(sK6(k1_xboole_0,X0),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_776,c_771])).

cnf(c_1861,plain,
    ( k3_tarski(X0) = k1_xboole_0
    | r2_hidden(sK7(X0,k1_xboole_0),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_776,c_771])).

cnf(c_18,plain,
    ( ~ r2_hidden(X0,k3_tarski(X1))
    | r2_hidden(sK8(X1,X0),X1) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_773,plain,
    ( r2_hidden(X0,k3_tarski(X1)) != iProver_top
    | r2_hidden(sK8(X1,X0),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_12,plain,
    ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
    | r2_hidden(sK5(X1,X2,X0),X2) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_779,plain,
    ( r2_hidden(X0,k2_zfmisc_1(X1,X2)) != iProver_top
    | r2_hidden(sK5(X1,X2,X0),X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_1154,plain,
    ( r2_hidden(X0,k2_zfmisc_1(X1,k1_xboole_0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_779,c_771])).

cnf(c_4836,plain,
    ( r2_hidden(X0,k3_tarski(k2_zfmisc_1(X1,k1_xboole_0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_773,c_1154])).

cnf(c_11939,plain,
    ( k3_tarski(k3_tarski(k2_zfmisc_1(X0,k1_xboole_0))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1861,c_4836])).

cnf(c_5902,plain,
    ( r2_hidden(X0,k3_tarski(k3_tarski(k2_zfmisc_1(X1,k1_xboole_0)))) != iProver_top ),
    inference(superposition,[status(thm)],[c_773,c_4836])).

cnf(c_11950,plain,
    ( k3_tarski(k3_tarski(k3_tarski(k2_zfmisc_1(X0,k1_xboole_0)))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1861,c_5902])).

cnf(c_11974,plain,
    ( k3_tarski(k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_11939,c_11950])).

cnf(c_13404,plain,
    ( k1_xboole_0 = X0
    | r2_hidden(sK6(k1_xboole_0,X0),X0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_1867,c_11974])).

cnf(c_13414,plain,
    ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_13404,c_1154])).

cnf(c_13,plain,
    ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
    | r2_hidden(sK4(X1,X2,X0),X1) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_778,plain,
    ( r2_hidden(X0,k2_zfmisc_1(X1,X2)) != iProver_top
    | r2_hidden(sK4(X1,X2,X0),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_4833,plain,
    ( r2_hidden(X0,k2_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0),X2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_778,c_1154])).

cnf(c_13425,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0),X1) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_13404,c_4833])).

cnf(c_13460,plain,
    ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_13414,c_13425])).

cnf(c_9,plain,
    ( r2_hidden(sK2(X0,X1,X2),X0)
    | r2_hidden(sK1(X0,X1,X2),X2)
    | k2_zfmisc_1(X0,X1) = X2 ),
    inference(cnf_transformation,[],[f42])).

cnf(c_782,plain,
    ( k2_zfmisc_1(X0,X1) = X2
    | r2_hidden(sK2(X0,X1,X2),X0) = iProver_top
    | r2_hidden(sK1(X0,X1,X2),X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_22,negated_conjecture,
    ( k1_xboole_0 = k2_zfmisc_1(sK9,sK10)
    | k1_xboole_0 = sK9
    | k1_xboole_0 = sK10 ),
    inference(cnf_transformation,[],[f52])).

cnf(c_10,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X2,X3)
    | r2_hidden(k4_tarski(X2,X0),k2_zfmisc_1(X3,X1)) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_781,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X2,X3) != iProver_top
    | r2_hidden(k4_tarski(X2,X0),k2_zfmisc_1(X3,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_2109,plain,
    ( sK9 = k1_xboole_0
    | sK10 = k1_xboole_0
    | r2_hidden(X0,sK9) != iProver_top
    | r2_hidden(X1,sK10) != iProver_top
    | r2_hidden(k4_tarski(X0,X1),k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_22,c_781])).

cnf(c_2215,plain,
    ( sK9 = k1_xboole_0
    | sK10 = k1_xboole_0
    | r2_hidden(X0,sK9) != iProver_top
    | r2_hidden(X1,sK10) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_2109,c_771])).

cnf(c_3474,plain,
    ( k2_zfmisc_1(X0,X1) = sK10
    | sK9 = k1_xboole_0
    | sK10 = k1_xboole_0
    | r2_hidden(X2,sK9) != iProver_top
    | r2_hidden(sK2(X0,X1,sK10),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_782,c_2215])).

cnf(c_66,plain,
    ( r1_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_65,plain,
    ( r1_xboole_0(X0,k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_67,plain,
    ( r1_xboole_0(k1_xboole_0,k1_xboole_0) = iProver_top ),
    inference(instantiation,[status(thm)],[c_65])).

cnf(c_453,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_464,plain,
    ( k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_453])).

cnf(c_967,plain,
    ( sK10 = sK10 ),
    inference(instantiation,[status(thm)],[c_453])).

cnf(c_971,plain,
    ( sK9 = sK9 ),
    inference(instantiation,[status(thm)],[c_453])).

cnf(c_454,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_958,plain,
    ( X0 != X1
    | sK10 != X1
    | sK10 = X0 ),
    inference(instantiation,[status(thm)],[c_454])).

cnf(c_966,plain,
    ( X0 != sK10
    | sK10 = X0
    | sK10 != sK10 ),
    inference(instantiation,[status(thm)],[c_958])).

cnf(c_984,plain,
    ( k3_tarski(X0) != sK10
    | sK10 = k3_tarski(X0)
    | sK10 != sK10 ),
    inference(instantiation,[status(thm)],[c_966])).

cnf(c_986,plain,
    ( k3_tarski(k1_xboole_0) != sK10
    | sK10 = k3_tarski(k1_xboole_0)
    | sK10 != sK10 ),
    inference(instantiation,[status(thm)],[c_984])).

cnf(c_965,plain,
    ( X0 != X1
    | sK9 != X1
    | sK9 = X0 ),
    inference(instantiation,[status(thm)],[c_454])).

cnf(c_970,plain,
    ( X0 != sK9
    | sK9 = X0
    | sK9 != sK9 ),
    inference(instantiation,[status(thm)],[c_965])).

cnf(c_999,plain,
    ( k3_tarski(X0) != sK9
    | sK9 = k3_tarski(X0)
    | sK9 != sK9 ),
    inference(instantiation,[status(thm)],[c_970])).

cnf(c_1001,plain,
    ( k3_tarski(k1_xboole_0) != sK9
    | sK9 = k3_tarski(k1_xboole_0)
    | sK9 != sK9 ),
    inference(instantiation,[status(thm)],[c_999])).

cnf(c_1023,plain,
    ( X0 != k3_tarski(X1)
    | sK10 = X0
    | sK10 != k3_tarski(X1) ),
    inference(instantiation,[status(thm)],[c_958])).

cnf(c_1024,plain,
    ( sK10 != k3_tarski(k1_xboole_0)
    | sK10 = k1_xboole_0
    | k1_xboole_0 != k3_tarski(k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_1023])).

cnf(c_1027,plain,
    ( X0 != k3_tarski(X1)
    | sK9 = X0
    | sK9 != k3_tarski(X1) ),
    inference(instantiation,[status(thm)],[c_965])).

cnf(c_1028,plain,
    ( sK9 != k3_tarski(k1_xboole_0)
    | sK9 = k1_xboole_0
    | k1_xboole_0 != k3_tarski(k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_1027])).

cnf(c_1192,plain,
    ( ~ r1_xboole_0(X0,X1)
    | ~ r2_hidden(sK7(X0,sK10),X0)
    | ~ r2_hidden(sK7(X0,sK10),X1) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_1193,plain,
    ( r1_xboole_0(X0,X1) != iProver_top
    | r2_hidden(sK7(X0,sK10),X0) != iProver_top
    | r2_hidden(sK7(X0,sK10),X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1192])).

cnf(c_1195,plain,
    ( r1_xboole_0(k1_xboole_0,k1_xboole_0) != iProver_top
    | r2_hidden(sK7(k1_xboole_0,sK10),k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1193])).

cnf(c_1335,plain,
    ( ~ r1_xboole_0(X0,X1)
    | ~ r2_hidden(sK7(X0,sK9),X0)
    | ~ r2_hidden(sK7(X0,sK9),X1) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_1336,plain,
    ( r1_xboole_0(X0,X1) != iProver_top
    | r2_hidden(sK7(X0,sK9),X0) != iProver_top
    | r2_hidden(sK7(X0,sK9),X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1335])).

cnf(c_1338,plain,
    ( r1_xboole_0(k1_xboole_0,k1_xboole_0) != iProver_top
    | r2_hidden(sK7(k1_xboole_0,sK9),k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1336])).

cnf(c_1643,plain,
    ( k3_tarski(X0) != X1
    | k1_xboole_0 != X1
    | k1_xboole_0 = k3_tarski(X0) ),
    inference(instantiation,[status(thm)],[c_454])).

cnf(c_1644,plain,
    ( k3_tarski(k1_xboole_0) != k1_xboole_0
    | k1_xboole_0 = k3_tarski(k1_xboole_0)
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1643])).

cnf(c_1937,plain,
    ( r2_hidden(sK7(X0,k1_xboole_0),X0)
    | k3_tarski(X0) = k1_xboole_0 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_1861])).

cnf(c_1939,plain,
    ( r2_hidden(sK7(k1_xboole_0,k1_xboole_0),k1_xboole_0)
    | k3_tarski(k1_xboole_0) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1937])).

cnf(c_2837,plain,
    ( ~ r1_xboole_0(X0,X1)
    | ~ r2_hidden(sK7(X0,X2),X1)
    | ~ r2_hidden(sK7(X0,X2),X0) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_2839,plain,
    ( ~ r1_xboole_0(k1_xboole_0,k1_xboole_0)
    | ~ r2_hidden(sK7(k1_xboole_0,k1_xboole_0),k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_2837])).

cnf(c_2224,plain,
    ( k3_tarski(X0) = sK10
    | sK9 = k1_xboole_0
    | sK10 = k1_xboole_0
    | r2_hidden(X1,sK9) != iProver_top
    | r2_hidden(sK7(X0,sK10),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_776,c_2215])).

cnf(c_3319,plain,
    ( k3_tarski(X0) = sK9
    | k3_tarski(X1) = sK10
    | sK9 = k1_xboole_0
    | sK10 = k1_xboole_0
    | r2_hidden(sK7(X0,sK9),X0) = iProver_top
    | r2_hidden(sK7(X1,sK10),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_776,c_2224])).

cnf(c_3411,plain,
    ( k3_tarski(k1_xboole_0) = sK9
    | k3_tarski(k1_xboole_0) = sK10
    | sK9 = k1_xboole_0
    | sK10 = k1_xboole_0
    | r2_hidden(sK7(k1_xboole_0,sK9),k1_xboole_0) = iProver_top
    | r2_hidden(sK7(k1_xboole_0,sK10),k1_xboole_0) = iProver_top ),
    inference(instantiation,[status(thm)],[c_3319])).

cnf(c_4580,plain,
    ( sK9 = k1_xboole_0
    | sK10 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3474,c_66,c_67,c_464,c_967,c_971,c_986,c_1001,c_1024,c_1028,c_1195,c_1338,c_1644,c_1939,c_2839,c_3411])).

cnf(c_21,negated_conjecture,
    ( k1_xboole_0 != k2_zfmisc_1(sK9,sK10)
    | k1_xboole_0 != sK9 ),
    inference(cnf_transformation,[],[f53])).

cnf(c_4587,plain,
    ( k2_zfmisc_1(k1_xboole_0,sK10) != k1_xboole_0
    | sK9 != k1_xboole_0
    | sK10 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_4580,c_21])).

cnf(c_4592,plain,
    ( k2_zfmisc_1(k1_xboole_0,sK10) != k1_xboole_0
    | sK10 = k1_xboole_0 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_4587,c_4580])).

cnf(c_13676,plain,
    ( sK10 = k1_xboole_0
    | k1_xboole_0 != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_13460,c_4592])).

cnf(c_13677,plain,
    ( sK10 = k1_xboole_0 ),
    inference(equality_resolution_simp,[status(thm)],[c_13676])).

cnf(c_20,negated_conjecture,
    ( k1_xboole_0 != k2_zfmisc_1(sK9,sK10)
    | k1_xboole_0 != sK10 ),
    inference(cnf_transformation,[],[f54])).

cnf(c_13722,plain,
    ( k2_zfmisc_1(sK9,k1_xboole_0) != k1_xboole_0
    | k1_xboole_0 != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_13677,c_20])).

cnf(c_13723,plain,
    ( k2_zfmisc_1(sK9,k1_xboole_0) != k1_xboole_0 ),
    inference(equality_resolution_simp,[status(thm)],[c_13722])).

cnf(c_13725,plain,
    ( k1_xboole_0 != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_13723,c_13414])).

cnf(c_13726,plain,
    ( $false ),
    inference(equality_resolution_simp,[status(thm)],[c_13725])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n021.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 18:39:34 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  % Running in FOF mode
% 3.69/1.03  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.69/1.03  
% 3.69/1.03  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.69/1.03  
% 3.69/1.03  ------  iProver source info
% 3.69/1.03  
% 3.69/1.03  git: date: 2020-06-30 10:37:57 +0100
% 3.69/1.03  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.69/1.03  git: non_committed_changes: false
% 3.69/1.03  git: last_make_outside_of_git: false
% 3.69/1.03  
% 3.69/1.03  ------ 
% 3.69/1.03  
% 3.69/1.03  ------ Input Options
% 3.69/1.03  
% 3.69/1.03  --out_options                           all
% 3.69/1.03  --tptp_safe_out                         true
% 3.69/1.03  --problem_path                          ""
% 3.69/1.03  --include_path                          ""
% 3.69/1.03  --clausifier                            res/vclausify_rel
% 3.69/1.03  --clausifier_options                    --mode clausify
% 3.69/1.03  --stdin                                 false
% 3.69/1.03  --stats_out                             all
% 3.69/1.03  
% 3.69/1.03  ------ General Options
% 3.69/1.03  
% 3.69/1.03  --fof                                   false
% 3.69/1.03  --time_out_real                         305.
% 3.69/1.03  --time_out_virtual                      -1.
% 3.69/1.03  --symbol_type_check                     false
% 3.69/1.03  --clausify_out                          false
% 3.69/1.03  --sig_cnt_out                           false
% 3.69/1.03  --trig_cnt_out                          false
% 3.69/1.03  --trig_cnt_out_tolerance                1.
% 3.69/1.03  --trig_cnt_out_sk_spl                   false
% 3.69/1.03  --abstr_cl_out                          false
% 3.69/1.03  
% 3.69/1.03  ------ Global Options
% 3.69/1.03  
% 3.69/1.03  --schedule                              default
% 3.69/1.03  --add_important_lit                     false
% 3.69/1.03  --prop_solver_per_cl                    1000
% 3.69/1.03  --min_unsat_core                        false
% 3.69/1.03  --soft_assumptions                      false
% 3.69/1.03  --soft_lemma_size                       3
% 3.69/1.03  --prop_impl_unit_size                   0
% 3.69/1.03  --prop_impl_unit                        []
% 3.69/1.03  --share_sel_clauses                     true
% 3.69/1.03  --reset_solvers                         false
% 3.69/1.03  --bc_imp_inh                            [conj_cone]
% 3.69/1.03  --conj_cone_tolerance                   3.
% 3.69/1.03  --extra_neg_conj                        none
% 3.69/1.03  --large_theory_mode                     true
% 3.69/1.03  --prolific_symb_bound                   200
% 3.69/1.03  --lt_threshold                          2000
% 3.69/1.03  --clause_weak_htbl                      true
% 3.69/1.03  --gc_record_bc_elim                     false
% 3.69/1.03  
% 3.69/1.03  ------ Preprocessing Options
% 3.69/1.03  
% 3.69/1.03  --preprocessing_flag                    true
% 3.69/1.03  --time_out_prep_mult                    0.1
% 3.69/1.03  --splitting_mode                        input
% 3.69/1.03  --splitting_grd                         true
% 3.69/1.03  --splitting_cvd                         false
% 3.69/1.03  --splitting_cvd_svl                     false
% 3.69/1.03  --splitting_nvd                         32
% 3.69/1.03  --sub_typing                            true
% 3.69/1.03  --prep_gs_sim                           true
% 3.69/1.03  --prep_unflatten                        true
% 3.69/1.03  --prep_res_sim                          true
% 3.69/1.03  --prep_upred                            true
% 3.69/1.03  --prep_sem_filter                       exhaustive
% 3.69/1.03  --prep_sem_filter_out                   false
% 3.69/1.03  --pred_elim                             true
% 3.69/1.03  --res_sim_input                         true
% 3.69/1.03  --eq_ax_congr_red                       true
% 3.69/1.03  --pure_diseq_elim                       true
% 3.69/1.03  --brand_transform                       false
% 3.69/1.03  --non_eq_to_eq                          false
% 3.69/1.03  --prep_def_merge                        true
% 3.69/1.03  --prep_def_merge_prop_impl              false
% 3.69/1.03  --prep_def_merge_mbd                    true
% 3.69/1.03  --prep_def_merge_tr_red                 false
% 3.69/1.03  --prep_def_merge_tr_cl                  false
% 3.69/1.03  --smt_preprocessing                     true
% 3.69/1.03  --smt_ac_axioms                         fast
% 3.69/1.03  --preprocessed_out                      false
% 3.69/1.03  --preprocessed_stats                    false
% 3.69/1.03  
% 3.69/1.03  ------ Abstraction refinement Options
% 3.69/1.03  
% 3.69/1.03  --abstr_ref                             []
% 3.69/1.03  --abstr_ref_prep                        false
% 3.69/1.03  --abstr_ref_until_sat                   false
% 3.69/1.03  --abstr_ref_sig_restrict                funpre
% 3.69/1.03  --abstr_ref_af_restrict_to_split_sk     false
% 3.69/1.03  --abstr_ref_under                       []
% 3.69/1.03  
% 3.69/1.03  ------ SAT Options
% 3.69/1.03  
% 3.69/1.03  --sat_mode                              false
% 3.69/1.03  --sat_fm_restart_options                ""
% 3.69/1.03  --sat_gr_def                            false
% 3.69/1.03  --sat_epr_types                         true
% 3.69/1.03  --sat_non_cyclic_types                  false
% 3.69/1.03  --sat_finite_models                     false
% 3.69/1.03  --sat_fm_lemmas                         false
% 3.69/1.03  --sat_fm_prep                           false
% 3.69/1.03  --sat_fm_uc_incr                        true
% 3.69/1.03  --sat_out_model                         small
% 3.69/1.03  --sat_out_clauses                       false
% 3.69/1.03  
% 3.69/1.03  ------ QBF Options
% 3.69/1.03  
% 3.69/1.03  --qbf_mode                              false
% 3.69/1.03  --qbf_elim_univ                         false
% 3.69/1.03  --qbf_dom_inst                          none
% 3.69/1.03  --qbf_dom_pre_inst                      false
% 3.69/1.03  --qbf_sk_in                             false
% 3.69/1.03  --qbf_pred_elim                         true
% 3.69/1.03  --qbf_split                             512
% 3.69/1.03  
% 3.69/1.03  ------ BMC1 Options
% 3.69/1.03  
% 3.69/1.03  --bmc1_incremental                      false
% 3.69/1.03  --bmc1_axioms                           reachable_all
% 3.69/1.03  --bmc1_min_bound                        0
% 3.69/1.03  --bmc1_max_bound                        -1
% 3.69/1.03  --bmc1_max_bound_default                -1
% 3.69/1.03  --bmc1_symbol_reachability              true
% 3.69/1.03  --bmc1_property_lemmas                  false
% 3.69/1.03  --bmc1_k_induction                      false
% 3.69/1.03  --bmc1_non_equiv_states                 false
% 3.69/1.03  --bmc1_deadlock                         false
% 3.69/1.03  --bmc1_ucm                              false
% 3.69/1.03  --bmc1_add_unsat_core                   none
% 3.69/1.03  --bmc1_unsat_core_children              false
% 3.69/1.03  --bmc1_unsat_core_extrapolate_axioms    false
% 3.69/1.03  --bmc1_out_stat                         full
% 3.69/1.03  --bmc1_ground_init                      false
% 3.69/1.03  --bmc1_pre_inst_next_state              false
% 3.69/1.03  --bmc1_pre_inst_state                   false
% 3.69/1.03  --bmc1_pre_inst_reach_state             false
% 3.69/1.03  --bmc1_out_unsat_core                   false
% 3.69/1.03  --bmc1_aig_witness_out                  false
% 3.69/1.03  --bmc1_verbose                          false
% 3.69/1.03  --bmc1_dump_clauses_tptp                false
% 3.69/1.03  --bmc1_dump_unsat_core_tptp             false
% 3.69/1.03  --bmc1_dump_file                        -
% 3.69/1.03  --bmc1_ucm_expand_uc_limit              128
% 3.69/1.03  --bmc1_ucm_n_expand_iterations          6
% 3.69/1.03  --bmc1_ucm_extend_mode                  1
% 3.69/1.03  --bmc1_ucm_init_mode                    2
% 3.69/1.03  --bmc1_ucm_cone_mode                    none
% 3.69/1.03  --bmc1_ucm_reduced_relation_type        0
% 3.69/1.03  --bmc1_ucm_relax_model                  4
% 3.69/1.03  --bmc1_ucm_full_tr_after_sat            true
% 3.69/1.03  --bmc1_ucm_expand_neg_assumptions       false
% 3.69/1.03  --bmc1_ucm_layered_model                none
% 3.69/1.03  --bmc1_ucm_max_lemma_size               10
% 3.69/1.03  
% 3.69/1.03  ------ AIG Options
% 3.69/1.03  
% 3.69/1.03  --aig_mode                              false
% 3.69/1.03  
% 3.69/1.03  ------ Instantiation Options
% 3.69/1.03  
% 3.69/1.03  --instantiation_flag                    true
% 3.69/1.03  --inst_sos_flag                         false
% 3.69/1.03  --inst_sos_phase                        true
% 3.69/1.03  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.69/1.03  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.69/1.03  --inst_lit_sel_side                     num_symb
% 3.69/1.03  --inst_solver_per_active                1400
% 3.69/1.03  --inst_solver_calls_frac                1.
% 3.69/1.03  --inst_passive_queue_type               priority_queues
% 3.69/1.03  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.69/1.03  --inst_passive_queues_freq              [25;2]
% 3.69/1.03  --inst_dismatching                      true
% 3.69/1.03  --inst_eager_unprocessed_to_passive     true
% 3.69/1.03  --inst_prop_sim_given                   true
% 3.69/1.03  --inst_prop_sim_new                     false
% 3.69/1.03  --inst_subs_new                         false
% 3.69/1.03  --inst_eq_res_simp                      false
% 3.69/1.03  --inst_subs_given                       false
% 3.69/1.03  --inst_orphan_elimination               true
% 3.69/1.03  --inst_learning_loop_flag               true
% 3.69/1.03  --inst_learning_start                   3000
% 3.69/1.03  --inst_learning_factor                  2
% 3.69/1.03  --inst_start_prop_sim_after_learn       3
% 3.69/1.03  --inst_sel_renew                        solver
% 3.69/1.03  --inst_lit_activity_flag                true
% 3.69/1.03  --inst_restr_to_given                   false
% 3.69/1.03  --inst_activity_threshold               500
% 3.69/1.03  --inst_out_proof                        true
% 3.69/1.03  
% 3.69/1.03  ------ Resolution Options
% 3.69/1.03  
% 3.69/1.03  --resolution_flag                       true
% 3.69/1.03  --res_lit_sel                           adaptive
% 3.69/1.03  --res_lit_sel_side                      none
% 3.69/1.03  --res_ordering                          kbo
% 3.69/1.03  --res_to_prop_solver                    active
% 3.69/1.03  --res_prop_simpl_new                    false
% 3.69/1.03  --res_prop_simpl_given                  true
% 3.69/1.03  --res_passive_queue_type                priority_queues
% 3.69/1.03  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.69/1.03  --res_passive_queues_freq               [15;5]
% 3.69/1.03  --res_forward_subs                      full
% 3.69/1.03  --res_backward_subs                     full
% 3.69/1.03  --res_forward_subs_resolution           true
% 3.69/1.03  --res_backward_subs_resolution          true
% 3.69/1.03  --res_orphan_elimination                true
% 3.69/1.03  --res_time_limit                        2.
% 3.69/1.03  --res_out_proof                         true
% 3.69/1.03  
% 3.69/1.03  ------ Superposition Options
% 3.69/1.03  
% 3.69/1.03  --superposition_flag                    true
% 3.69/1.03  --sup_passive_queue_type                priority_queues
% 3.69/1.03  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.69/1.03  --sup_passive_queues_freq               [8;1;4]
% 3.69/1.03  --demod_completeness_check              fast
% 3.69/1.03  --demod_use_ground                      true
% 3.69/1.03  --sup_to_prop_solver                    passive
% 3.69/1.03  --sup_prop_simpl_new                    true
% 3.69/1.03  --sup_prop_simpl_given                  true
% 3.69/1.03  --sup_fun_splitting                     false
% 3.69/1.03  --sup_smt_interval                      50000
% 3.69/1.03  
% 3.69/1.03  ------ Superposition Simplification Setup
% 3.69/1.03  
% 3.69/1.03  --sup_indices_passive                   []
% 3.69/1.03  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.69/1.03  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.69/1.03  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.69/1.03  --sup_full_triv                         [TrivRules;PropSubs]
% 3.69/1.03  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.69/1.03  --sup_full_bw                           [BwDemod]
% 3.69/1.03  --sup_immed_triv                        [TrivRules]
% 3.69/1.03  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.69/1.03  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.69/1.03  --sup_immed_bw_main                     []
% 3.69/1.03  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.69/1.03  --sup_input_triv                        [Unflattening;TrivRules]
% 3.69/1.03  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.69/1.03  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.69/1.03  
% 3.69/1.03  ------ Combination Options
% 3.69/1.03  
% 3.69/1.03  --comb_res_mult                         3
% 3.69/1.03  --comb_sup_mult                         2
% 3.69/1.03  --comb_inst_mult                        10
% 3.69/1.03  
% 3.69/1.03  ------ Debug Options
% 3.69/1.03  
% 3.69/1.03  --dbg_backtrace                         false
% 3.69/1.03  --dbg_dump_prop_clauses                 false
% 3.69/1.03  --dbg_dump_prop_clauses_file            -
% 3.69/1.03  --dbg_out_stat                          false
% 3.69/1.03  ------ Parsing...
% 3.69/1.03  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.69/1.03  
% 3.69/1.03  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 3.69/1.03  
% 3.69/1.03  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.69/1.03  
% 3.69/1.03  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.69/1.03  ------ Proving...
% 3.69/1.03  ------ Problem Properties 
% 3.69/1.03  
% 3.69/1.03  
% 3.69/1.03  clauses                                 22
% 3.69/1.03  conjectures                             3
% 3.69/1.03  EPR                                     3
% 3.69/1.03  Horn                                    14
% 3.69/1.03  unary                                   2
% 3.69/1.03  binary                                  9
% 3.69/1.03  lits                                    56
% 3.69/1.03  lits eq                                 17
% 3.69/1.03  fd_pure                                 0
% 3.69/1.03  fd_pseudo                               0
% 3.69/1.03  fd_cond                                 0
% 3.69/1.03  fd_pseudo_cond                          7
% 3.69/1.03  AC symbols                              0
% 3.69/1.03  
% 3.69/1.03  ------ Schedule dynamic 5 is on 
% 3.69/1.03  
% 3.69/1.03  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.69/1.03  
% 3.69/1.03  
% 3.69/1.03  ------ 
% 3.69/1.03  Current options:
% 3.69/1.03  ------ 
% 3.69/1.03  
% 3.69/1.03  ------ Input Options
% 3.69/1.03  
% 3.69/1.03  --out_options                           all
% 3.69/1.03  --tptp_safe_out                         true
% 3.69/1.03  --problem_path                          ""
% 3.69/1.03  --include_path                          ""
% 3.69/1.03  --clausifier                            res/vclausify_rel
% 3.69/1.03  --clausifier_options                    --mode clausify
% 3.69/1.03  --stdin                                 false
% 3.69/1.03  --stats_out                             all
% 3.69/1.03  
% 3.69/1.03  ------ General Options
% 3.69/1.03  
% 3.69/1.03  --fof                                   false
% 3.69/1.03  --time_out_real                         305.
% 3.69/1.03  --time_out_virtual                      -1.
% 3.69/1.03  --symbol_type_check                     false
% 3.69/1.03  --clausify_out                          false
% 3.69/1.03  --sig_cnt_out                           false
% 3.69/1.03  --trig_cnt_out                          false
% 3.69/1.03  --trig_cnt_out_tolerance                1.
% 3.69/1.03  --trig_cnt_out_sk_spl                   false
% 3.69/1.03  --abstr_cl_out                          false
% 3.69/1.03  
% 3.69/1.03  ------ Global Options
% 3.69/1.03  
% 3.69/1.03  --schedule                              default
% 3.69/1.03  --add_important_lit                     false
% 3.69/1.03  --prop_solver_per_cl                    1000
% 3.69/1.03  --min_unsat_core                        false
% 3.69/1.03  --soft_assumptions                      false
% 3.69/1.03  --soft_lemma_size                       3
% 3.69/1.03  --prop_impl_unit_size                   0
% 3.69/1.03  --prop_impl_unit                        []
% 3.69/1.03  --share_sel_clauses                     true
% 3.69/1.03  --reset_solvers                         false
% 3.69/1.03  --bc_imp_inh                            [conj_cone]
% 3.69/1.03  --conj_cone_tolerance                   3.
% 3.69/1.03  --extra_neg_conj                        none
% 3.69/1.03  --large_theory_mode                     true
% 3.69/1.03  --prolific_symb_bound                   200
% 3.69/1.03  --lt_threshold                          2000
% 3.69/1.03  --clause_weak_htbl                      true
% 3.69/1.03  --gc_record_bc_elim                     false
% 3.69/1.03  
% 3.69/1.03  ------ Preprocessing Options
% 3.69/1.03  
% 3.69/1.03  --preprocessing_flag                    true
% 3.69/1.03  --time_out_prep_mult                    0.1
% 3.69/1.03  --splitting_mode                        input
% 3.69/1.03  --splitting_grd                         true
% 3.69/1.03  --splitting_cvd                         false
% 3.69/1.03  --splitting_cvd_svl                     false
% 3.69/1.03  --splitting_nvd                         32
% 3.69/1.03  --sub_typing                            true
% 3.69/1.03  --prep_gs_sim                           true
% 3.69/1.03  --prep_unflatten                        true
% 3.69/1.03  --prep_res_sim                          true
% 3.69/1.03  --prep_upred                            true
% 3.69/1.03  --prep_sem_filter                       exhaustive
% 3.69/1.03  --prep_sem_filter_out                   false
% 3.69/1.03  --pred_elim                             true
% 3.69/1.03  --res_sim_input                         true
% 3.69/1.03  --eq_ax_congr_red                       true
% 3.69/1.03  --pure_diseq_elim                       true
% 3.69/1.03  --brand_transform                       false
% 3.69/1.03  --non_eq_to_eq                          false
% 3.69/1.03  --prep_def_merge                        true
% 3.69/1.03  --prep_def_merge_prop_impl              false
% 3.69/1.03  --prep_def_merge_mbd                    true
% 3.69/1.03  --prep_def_merge_tr_red                 false
% 3.69/1.03  --prep_def_merge_tr_cl                  false
% 3.69/1.03  --smt_preprocessing                     true
% 3.69/1.03  --smt_ac_axioms                         fast
% 3.69/1.03  --preprocessed_out                      false
% 3.69/1.03  --preprocessed_stats                    false
% 3.69/1.03  
% 3.69/1.03  ------ Abstraction refinement Options
% 3.69/1.03  
% 3.69/1.03  --abstr_ref                             []
% 3.69/1.03  --abstr_ref_prep                        false
% 3.69/1.03  --abstr_ref_until_sat                   false
% 3.69/1.03  --abstr_ref_sig_restrict                funpre
% 3.69/1.03  --abstr_ref_af_restrict_to_split_sk     false
% 3.69/1.03  --abstr_ref_under                       []
% 3.69/1.03  
% 3.69/1.03  ------ SAT Options
% 3.69/1.03  
% 3.69/1.03  --sat_mode                              false
% 3.69/1.03  --sat_fm_restart_options                ""
% 3.69/1.03  --sat_gr_def                            false
% 3.69/1.03  --sat_epr_types                         true
% 3.69/1.03  --sat_non_cyclic_types                  false
% 3.69/1.03  --sat_finite_models                     false
% 3.69/1.03  --sat_fm_lemmas                         false
% 3.69/1.03  --sat_fm_prep                           false
% 3.69/1.03  --sat_fm_uc_incr                        true
% 3.69/1.03  --sat_out_model                         small
% 3.69/1.03  --sat_out_clauses                       false
% 3.69/1.03  
% 3.69/1.03  ------ QBF Options
% 3.69/1.03  
% 3.69/1.03  --qbf_mode                              false
% 3.69/1.03  --qbf_elim_univ                         false
% 3.69/1.03  --qbf_dom_inst                          none
% 3.69/1.03  --qbf_dom_pre_inst                      false
% 3.69/1.03  --qbf_sk_in                             false
% 3.69/1.03  --qbf_pred_elim                         true
% 3.69/1.03  --qbf_split                             512
% 3.69/1.03  
% 3.69/1.03  ------ BMC1 Options
% 3.69/1.03  
% 3.69/1.03  --bmc1_incremental                      false
% 3.69/1.03  --bmc1_axioms                           reachable_all
% 3.69/1.03  --bmc1_min_bound                        0
% 3.69/1.03  --bmc1_max_bound                        -1
% 3.69/1.03  --bmc1_max_bound_default                -1
% 3.69/1.03  --bmc1_symbol_reachability              true
% 3.69/1.03  --bmc1_property_lemmas                  false
% 3.69/1.03  --bmc1_k_induction                      false
% 3.69/1.03  --bmc1_non_equiv_states                 false
% 3.69/1.03  --bmc1_deadlock                         false
% 3.69/1.03  --bmc1_ucm                              false
% 3.69/1.03  --bmc1_add_unsat_core                   none
% 3.69/1.03  --bmc1_unsat_core_children              false
% 3.69/1.03  --bmc1_unsat_core_extrapolate_axioms    false
% 3.69/1.03  --bmc1_out_stat                         full
% 3.69/1.03  --bmc1_ground_init                      false
% 3.69/1.03  --bmc1_pre_inst_next_state              false
% 3.69/1.03  --bmc1_pre_inst_state                   false
% 3.69/1.03  --bmc1_pre_inst_reach_state             false
% 3.69/1.03  --bmc1_out_unsat_core                   false
% 3.69/1.03  --bmc1_aig_witness_out                  false
% 3.69/1.03  --bmc1_verbose                          false
% 3.69/1.03  --bmc1_dump_clauses_tptp                false
% 3.69/1.03  --bmc1_dump_unsat_core_tptp             false
% 3.69/1.03  --bmc1_dump_file                        -
% 3.69/1.03  --bmc1_ucm_expand_uc_limit              128
% 3.69/1.03  --bmc1_ucm_n_expand_iterations          6
% 3.69/1.03  --bmc1_ucm_extend_mode                  1
% 3.69/1.03  --bmc1_ucm_init_mode                    2
% 3.69/1.03  --bmc1_ucm_cone_mode                    none
% 3.69/1.03  --bmc1_ucm_reduced_relation_type        0
% 3.69/1.03  --bmc1_ucm_relax_model                  4
% 3.69/1.03  --bmc1_ucm_full_tr_after_sat            true
% 3.69/1.03  --bmc1_ucm_expand_neg_assumptions       false
% 3.69/1.03  --bmc1_ucm_layered_model                none
% 3.69/1.03  --bmc1_ucm_max_lemma_size               10
% 3.69/1.03  
% 3.69/1.03  ------ AIG Options
% 3.69/1.03  
% 3.69/1.03  --aig_mode                              false
% 3.69/1.03  
% 3.69/1.03  ------ Instantiation Options
% 3.69/1.03  
% 3.69/1.03  --instantiation_flag                    true
% 3.69/1.03  --inst_sos_flag                         false
% 3.69/1.03  --inst_sos_phase                        true
% 3.69/1.03  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.69/1.03  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.69/1.03  --inst_lit_sel_side                     none
% 3.69/1.03  --inst_solver_per_active                1400
% 3.69/1.03  --inst_solver_calls_frac                1.
% 3.69/1.03  --inst_passive_queue_type               priority_queues
% 3.69/1.03  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.69/1.03  --inst_passive_queues_freq              [25;2]
% 3.69/1.03  --inst_dismatching                      true
% 3.69/1.03  --inst_eager_unprocessed_to_passive     true
% 3.69/1.03  --inst_prop_sim_given                   true
% 3.69/1.03  --inst_prop_sim_new                     false
% 3.69/1.03  --inst_subs_new                         false
% 3.69/1.03  --inst_eq_res_simp                      false
% 3.69/1.03  --inst_subs_given                       false
% 3.69/1.03  --inst_orphan_elimination               true
% 3.69/1.03  --inst_learning_loop_flag               true
% 3.69/1.03  --inst_learning_start                   3000
% 3.69/1.03  --inst_learning_factor                  2
% 3.69/1.03  --inst_start_prop_sim_after_learn       3
% 3.69/1.03  --inst_sel_renew                        solver
% 3.69/1.03  --inst_lit_activity_flag                true
% 3.69/1.03  --inst_restr_to_given                   false
% 3.69/1.03  --inst_activity_threshold               500
% 3.69/1.03  --inst_out_proof                        true
% 3.69/1.03  
% 3.69/1.03  ------ Resolution Options
% 3.69/1.03  
% 3.69/1.03  --resolution_flag                       false
% 3.69/1.03  --res_lit_sel                           adaptive
% 3.69/1.03  --res_lit_sel_side                      none
% 3.69/1.03  --res_ordering                          kbo
% 3.69/1.03  --res_to_prop_solver                    active
% 3.69/1.03  --res_prop_simpl_new                    false
% 3.69/1.03  --res_prop_simpl_given                  true
% 3.69/1.03  --res_passive_queue_type                priority_queues
% 3.69/1.03  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.69/1.03  --res_passive_queues_freq               [15;5]
% 3.69/1.03  --res_forward_subs                      full
% 3.69/1.03  --res_backward_subs                     full
% 3.69/1.03  --res_forward_subs_resolution           true
% 3.69/1.03  --res_backward_subs_resolution          true
% 3.69/1.03  --res_orphan_elimination                true
% 3.69/1.03  --res_time_limit                        2.
% 3.69/1.03  --res_out_proof                         true
% 3.69/1.03  
% 3.69/1.03  ------ Superposition Options
% 3.69/1.03  
% 3.69/1.03  --superposition_flag                    true
% 3.69/1.03  --sup_passive_queue_type                priority_queues
% 3.69/1.03  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.69/1.03  --sup_passive_queues_freq               [8;1;4]
% 3.69/1.03  --demod_completeness_check              fast
% 3.69/1.03  --demod_use_ground                      true
% 3.69/1.03  --sup_to_prop_solver                    passive
% 3.69/1.03  --sup_prop_simpl_new                    true
% 3.69/1.03  --sup_prop_simpl_given                  true
% 3.69/1.03  --sup_fun_splitting                     false
% 3.69/1.03  --sup_smt_interval                      50000
% 3.69/1.03  
% 3.69/1.03  ------ Superposition Simplification Setup
% 3.69/1.03  
% 3.69/1.03  --sup_indices_passive                   []
% 3.69/1.03  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.69/1.03  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.69/1.03  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.69/1.03  --sup_full_triv                         [TrivRules;PropSubs]
% 3.69/1.03  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.69/1.03  --sup_full_bw                           [BwDemod]
% 3.69/1.03  --sup_immed_triv                        [TrivRules]
% 3.69/1.03  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.69/1.03  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.69/1.03  --sup_immed_bw_main                     []
% 3.69/1.03  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.69/1.03  --sup_input_triv                        [Unflattening;TrivRules]
% 3.69/1.03  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.69/1.03  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.69/1.03  
% 3.69/1.03  ------ Combination Options
% 3.69/1.03  
% 3.69/1.03  --comb_res_mult                         3
% 3.69/1.03  --comb_sup_mult                         2
% 3.69/1.03  --comb_inst_mult                        10
% 3.69/1.03  
% 3.69/1.03  ------ Debug Options
% 3.69/1.03  
% 3.69/1.03  --dbg_backtrace                         false
% 3.69/1.03  --dbg_dump_prop_clauses                 false
% 3.69/1.03  --dbg_dump_prop_clauses_file            -
% 3.69/1.03  --dbg_out_stat                          false
% 3.69/1.03  
% 3.69/1.03  
% 3.69/1.03  
% 3.69/1.03  
% 3.69/1.03  ------ Proving...
% 3.69/1.03  
% 3.69/1.03  
% 3.69/1.03  % SZS status Theorem for theBenchmark.p
% 3.69/1.03  
% 3.69/1.03   Resolution empty clause
% 3.69/1.03  
% 3.69/1.03  % SZS output start CNFRefutation for theBenchmark.p
% 3.69/1.03  
% 3.69/1.03  fof(f6,axiom,(
% 3.69/1.03    ! [X0,X1] : (k3_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (r2_hidden(X3,X0) & r2_hidden(X2,X3))))),
% 3.69/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.69/1.03  
% 3.69/1.03  fof(f22,plain,(
% 3.69/1.03    ! [X0,X1] : ((k3_tarski(X0) = X1 | ? [X2] : ((! [X3] : (~r2_hidden(X3,X0) | ~r2_hidden(X2,X3)) | ~r2_hidden(X2,X1)) & (? [X3] : (r2_hidden(X3,X0) & r2_hidden(X2,X3)) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ! [X3] : (~r2_hidden(X3,X0) | ~r2_hidden(X2,X3))) & (? [X3] : (r2_hidden(X3,X0) & r2_hidden(X2,X3)) | ~r2_hidden(X2,X1))) | k3_tarski(X0) != X1))),
% 3.69/1.03    inference(nnf_transformation,[],[f6])).
% 3.69/1.03  
% 3.69/1.03  fof(f23,plain,(
% 3.69/1.03    ! [X0,X1] : ((k3_tarski(X0) = X1 | ? [X2] : ((! [X3] : (~r2_hidden(X3,X0) | ~r2_hidden(X2,X3)) | ~r2_hidden(X2,X1)) & (? [X4] : (r2_hidden(X4,X0) & r2_hidden(X2,X4)) | r2_hidden(X2,X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : (~r2_hidden(X6,X0) | ~r2_hidden(X5,X6))) & (? [X7] : (r2_hidden(X7,X0) & r2_hidden(X5,X7)) | ~r2_hidden(X5,X1))) | k3_tarski(X0) != X1))),
% 3.69/1.03    inference(rectify,[],[f22])).
% 3.69/1.03  
% 3.69/1.03  fof(f26,plain,(
% 3.69/1.03    ! [X5,X0] : (? [X7] : (r2_hidden(X7,X0) & r2_hidden(X5,X7)) => (r2_hidden(sK8(X0,X5),X0) & r2_hidden(X5,sK8(X0,X5))))),
% 3.69/1.03    introduced(choice_axiom,[])).
% 3.69/1.03  
% 3.69/1.03  fof(f25,plain,(
% 3.69/1.03    ( ! [X2] : (! [X1,X0] : (? [X4] : (r2_hidden(X4,X0) & r2_hidden(X2,X4)) => (r2_hidden(sK7(X0,X1),X0) & r2_hidden(X2,sK7(X0,X1))))) )),
% 3.69/1.03    introduced(choice_axiom,[])).
% 3.69/1.03  
% 3.69/1.03  fof(f24,plain,(
% 3.69/1.03    ! [X1,X0] : (? [X2] : ((! [X3] : (~r2_hidden(X3,X0) | ~r2_hidden(X2,X3)) | ~r2_hidden(X2,X1)) & (? [X4] : (r2_hidden(X4,X0) & r2_hidden(X2,X4)) | r2_hidden(X2,X1))) => ((! [X3] : (~r2_hidden(X3,X0) | ~r2_hidden(sK6(X0,X1),X3)) | ~r2_hidden(sK6(X0,X1),X1)) & (? [X4] : (r2_hidden(X4,X0) & r2_hidden(sK6(X0,X1),X4)) | r2_hidden(sK6(X0,X1),X1))))),
% 3.69/1.03    introduced(choice_axiom,[])).
% 3.69/1.03  
% 3.69/1.03  fof(f27,plain,(
% 3.69/1.03    ! [X0,X1] : ((k3_tarski(X0) = X1 | ((! [X3] : (~r2_hidden(X3,X0) | ~r2_hidden(sK6(X0,X1),X3)) | ~r2_hidden(sK6(X0,X1),X1)) & ((r2_hidden(sK7(X0,X1),X0) & r2_hidden(sK6(X0,X1),sK7(X0,X1))) | r2_hidden(sK6(X0,X1),X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : (~r2_hidden(X6,X0) | ~r2_hidden(X5,X6))) & ((r2_hidden(sK8(X0,X5),X0) & r2_hidden(X5,sK8(X0,X5))) | ~r2_hidden(X5,X1))) | k3_tarski(X0) != X1))),
% 3.69/1.03    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7,sK8])],[f23,f26,f25,f24])).
% 3.69/1.03  
% 3.69/1.03  fof(f50,plain,(
% 3.69/1.03    ( ! [X0,X1] : (k3_tarski(X0) = X1 | r2_hidden(sK7(X0,X1),X0) | r2_hidden(sK6(X0,X1),X1)) )),
% 3.69/1.03    inference(cnf_transformation,[],[f27])).
% 3.69/1.03  
% 3.69/1.03  fof(f2,axiom,(
% 3.69/1.03    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 3.69/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.69/1.03  
% 3.69/1.03  fof(f9,plain,(
% 3.69/1.03    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 3.69/1.03    inference(rectify,[],[f2])).
% 3.69/1.03  
% 3.69/1.03  fof(f12,plain,(
% 3.69/1.03    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 3.69/1.03    inference(ennf_transformation,[],[f9])).
% 3.69/1.03  
% 3.69/1.03  fof(f14,plain,(
% 3.69/1.03    ! [X1,X0] : (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) => (r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 3.69/1.03    introduced(choice_axiom,[])).
% 3.69/1.03  
% 3.69/1.03  fof(f15,plain,(
% 3.69/1.03    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & ((r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)) | r1_xboole_0(X0,X1)))),
% 3.69/1.03    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f12,f14])).
% 3.69/1.03  
% 3.69/1.03  fof(f35,plain,(
% 3.69/1.03    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) )),
% 3.69/1.03    inference(cnf_transformation,[],[f15])).
% 3.69/1.03  
% 3.69/1.03  fof(f4,axiom,(
% 3.69/1.03    ! [X0] : r1_xboole_0(X0,k1_xboole_0)),
% 3.69/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.69/1.03  
% 3.69/1.03  fof(f37,plain,(
% 3.69/1.03    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) )),
% 3.69/1.03    inference(cnf_transformation,[],[f4])).
% 3.69/1.03  
% 3.69/1.03  fof(f1,axiom,(
% 3.69/1.03    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 3.69/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.69/1.03  
% 3.69/1.03  fof(f10,plain,(
% 3.69/1.03    ! [X0,X1] : (r1_tarski(X0,X1) => ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 3.69/1.03    inference(unused_predicate_definition_removal,[],[f1])).
% 3.69/1.03  
% 3.69/1.03  fof(f11,plain,(
% 3.69/1.03    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1))),
% 3.69/1.03    inference(ennf_transformation,[],[f10])).
% 3.69/1.03  
% 3.69/1.03  fof(f32,plain,(
% 3.69/1.03    ( ! [X2,X0,X1] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0) | ~r1_tarski(X0,X1)) )),
% 3.69/1.03    inference(cnf_transformation,[],[f11])).
% 3.69/1.03  
% 3.69/1.03  fof(f3,axiom,(
% 3.69/1.03    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 3.69/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.69/1.03  
% 3.69/1.03  fof(f36,plain,(
% 3.69/1.03    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 3.69/1.03    inference(cnf_transformation,[],[f3])).
% 3.69/1.03  
% 3.69/1.03  fof(f47,plain,(
% 3.69/1.03    ( ! [X0,X5,X1] : (r2_hidden(sK8(X0,X5),X0) | ~r2_hidden(X5,X1) | k3_tarski(X0) != X1) )),
% 3.69/1.03    inference(cnf_transformation,[],[f27])).
% 3.69/1.03  
% 3.69/1.03  fof(f61,plain,(
% 3.69/1.03    ( ! [X0,X5] : (r2_hidden(sK8(X0,X5),X0) | ~r2_hidden(X5,k3_tarski(X0))) )),
% 3.69/1.03    inference(equality_resolution,[],[f47])).
% 3.69/1.03  
% 3.69/1.03  fof(f5,axiom,(
% 3.69/1.03    ! [X0,X1,X2] : (k2_zfmisc_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4,X5] : (k4_tarski(X4,X5) = X3 & r2_hidden(X5,X1) & r2_hidden(X4,X0))))),
% 3.69/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.69/1.03  
% 3.69/1.03  fof(f16,plain,(
% 3.69/1.03    ! [X0,X1,X2] : ((k2_zfmisc_1(X0,X1) = X2 | ? [X3] : ((! [X4,X5] : (k4_tarski(X4,X5) != X3 | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X0)) | ~r2_hidden(X3,X2)) & (? [X4,X5] : (k4_tarski(X4,X5) = X3 & r2_hidden(X5,X1) & r2_hidden(X4,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ! [X4,X5] : (k4_tarski(X4,X5) != X3 | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X0))) & (? [X4,X5] : (k4_tarski(X4,X5) = X3 & r2_hidden(X5,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X3,X2))) | k2_zfmisc_1(X0,X1) != X2))),
% 3.69/1.03    inference(nnf_transformation,[],[f5])).
% 3.69/1.03  
% 3.69/1.03  fof(f17,plain,(
% 3.69/1.03    ! [X0,X1,X2] : ((k2_zfmisc_1(X0,X1) = X2 | ? [X3] : ((! [X4,X5] : (k4_tarski(X4,X5) != X3 | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X0)) | ~r2_hidden(X3,X2)) & (? [X6,X7] : (k4_tarski(X6,X7) = X3 & r2_hidden(X7,X1) & r2_hidden(X6,X0)) | r2_hidden(X3,X2)))) & (! [X8] : ((r2_hidden(X8,X2) | ! [X9,X10] : (k4_tarski(X9,X10) != X8 | ~r2_hidden(X10,X1) | ~r2_hidden(X9,X0))) & (? [X11,X12] : (k4_tarski(X11,X12) = X8 & r2_hidden(X12,X1) & r2_hidden(X11,X0)) | ~r2_hidden(X8,X2))) | k2_zfmisc_1(X0,X1) != X2))),
% 3.69/1.03    inference(rectify,[],[f16])).
% 3.69/1.03  
% 3.69/1.03  fof(f20,plain,(
% 3.69/1.03    ! [X8,X1,X0] : (? [X11,X12] : (k4_tarski(X11,X12) = X8 & r2_hidden(X12,X1) & r2_hidden(X11,X0)) => (k4_tarski(sK4(X0,X1,X8),sK5(X0,X1,X8)) = X8 & r2_hidden(sK5(X0,X1,X8),X1) & r2_hidden(sK4(X0,X1,X8),X0)))),
% 3.69/1.03    introduced(choice_axiom,[])).
% 3.69/1.03  
% 3.69/1.03  fof(f19,plain,(
% 3.69/1.03    ( ! [X3] : (! [X2,X1,X0] : (? [X6,X7] : (k4_tarski(X6,X7) = X3 & r2_hidden(X7,X1) & r2_hidden(X6,X0)) => (k4_tarski(sK2(X0,X1,X2),sK3(X0,X1,X2)) = X3 & r2_hidden(sK3(X0,X1,X2),X1) & r2_hidden(sK2(X0,X1,X2),X0)))) )),
% 3.69/1.03    introduced(choice_axiom,[])).
% 3.69/1.03  
% 3.69/1.03  fof(f18,plain,(
% 3.69/1.03    ! [X2,X1,X0] : (? [X3] : ((! [X4,X5] : (k4_tarski(X4,X5) != X3 | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X0)) | ~r2_hidden(X3,X2)) & (? [X6,X7] : (k4_tarski(X6,X7) = X3 & r2_hidden(X7,X1) & r2_hidden(X6,X0)) | r2_hidden(X3,X2))) => ((! [X5,X4] : (k4_tarski(X4,X5) != sK1(X0,X1,X2) | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X0)) | ~r2_hidden(sK1(X0,X1,X2),X2)) & (? [X7,X6] : (k4_tarski(X6,X7) = sK1(X0,X1,X2) & r2_hidden(X7,X1) & r2_hidden(X6,X0)) | r2_hidden(sK1(X0,X1,X2),X2))))),
% 3.69/1.03    introduced(choice_axiom,[])).
% 3.69/1.03  
% 3.69/1.03  fof(f21,plain,(
% 3.69/1.03    ! [X0,X1,X2] : ((k2_zfmisc_1(X0,X1) = X2 | ((! [X4,X5] : (k4_tarski(X4,X5) != sK1(X0,X1,X2) | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X0)) | ~r2_hidden(sK1(X0,X1,X2),X2)) & ((k4_tarski(sK2(X0,X1,X2),sK3(X0,X1,X2)) = sK1(X0,X1,X2) & r2_hidden(sK3(X0,X1,X2),X1) & r2_hidden(sK2(X0,X1,X2),X0)) | r2_hidden(sK1(X0,X1,X2),X2)))) & (! [X8] : ((r2_hidden(X8,X2) | ! [X9,X10] : (k4_tarski(X9,X10) != X8 | ~r2_hidden(X10,X1) | ~r2_hidden(X9,X0))) & ((k4_tarski(sK4(X0,X1,X8),sK5(X0,X1,X8)) = X8 & r2_hidden(sK5(X0,X1,X8),X1) & r2_hidden(sK4(X0,X1,X8),X0)) | ~r2_hidden(X8,X2))) | k2_zfmisc_1(X0,X1) != X2))),
% 3.69/1.03    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4,sK5])],[f17,f20,f19,f18])).
% 3.69/1.03  
% 3.69/1.03  fof(f39,plain,(
% 3.69/1.03    ( ! [X2,X0,X8,X1] : (r2_hidden(sK5(X0,X1,X8),X1) | ~r2_hidden(X8,X2) | k2_zfmisc_1(X0,X1) != X2) )),
% 3.69/1.03    inference(cnf_transformation,[],[f21])).
% 3.69/1.03  
% 3.69/1.03  fof(f58,plain,(
% 3.69/1.03    ( ! [X0,X8,X1] : (r2_hidden(sK5(X0,X1,X8),X1) | ~r2_hidden(X8,k2_zfmisc_1(X0,X1))) )),
% 3.69/1.03    inference(equality_resolution,[],[f39])).
% 3.69/1.03  
% 3.69/1.03  fof(f38,plain,(
% 3.69/1.03    ( ! [X2,X0,X8,X1] : (r2_hidden(sK4(X0,X1,X8),X0) | ~r2_hidden(X8,X2) | k2_zfmisc_1(X0,X1) != X2) )),
% 3.69/1.03    inference(cnf_transformation,[],[f21])).
% 3.69/1.03  
% 3.69/1.03  fof(f59,plain,(
% 3.69/1.03    ( ! [X0,X8,X1] : (r2_hidden(sK4(X0,X1,X8),X0) | ~r2_hidden(X8,k2_zfmisc_1(X0,X1))) )),
% 3.69/1.03    inference(equality_resolution,[],[f38])).
% 3.69/1.03  
% 3.69/1.03  fof(f42,plain,(
% 3.69/1.03    ( ! [X2,X0,X1] : (k2_zfmisc_1(X0,X1) = X2 | r2_hidden(sK2(X0,X1,X2),X0) | r2_hidden(sK1(X0,X1,X2),X2)) )),
% 3.69/1.03    inference(cnf_transformation,[],[f21])).
% 3.69/1.03  
% 3.69/1.03  fof(f7,conjecture,(
% 3.69/1.03    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 3.69/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.69/1.03  
% 3.69/1.03  fof(f8,negated_conjecture,(
% 3.69/1.03    ~! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 3.69/1.03    inference(negated_conjecture,[],[f7])).
% 3.69/1.03  
% 3.69/1.03  fof(f13,plain,(
% 3.69/1.03    ? [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <~> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 3.69/1.03    inference(ennf_transformation,[],[f8])).
% 3.69/1.03  
% 3.69/1.03  fof(f28,plain,(
% 3.69/1.03    ? [X0,X1] : (((k1_xboole_0 != X1 & k1_xboole_0 != X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 = k2_zfmisc_1(X0,X1)))),
% 3.69/1.03    inference(nnf_transformation,[],[f13])).
% 3.69/1.03  
% 3.69/1.03  fof(f29,plain,(
% 3.69/1.03    ? [X0,X1] : (((k1_xboole_0 != X1 & k1_xboole_0 != X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 = k2_zfmisc_1(X0,X1)))),
% 3.69/1.03    inference(flattening,[],[f28])).
% 3.69/1.03  
% 3.69/1.03  fof(f30,plain,(
% 3.69/1.03    ? [X0,X1] : (((k1_xboole_0 != X1 & k1_xboole_0 != X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 = k2_zfmisc_1(X0,X1))) => (((k1_xboole_0 != sK10 & k1_xboole_0 != sK9) | k1_xboole_0 != k2_zfmisc_1(sK9,sK10)) & (k1_xboole_0 = sK10 | k1_xboole_0 = sK9 | k1_xboole_0 = k2_zfmisc_1(sK9,sK10)))),
% 3.69/1.03    introduced(choice_axiom,[])).
% 3.69/1.03  
% 3.69/1.03  fof(f31,plain,(
% 3.69/1.03    ((k1_xboole_0 != sK10 & k1_xboole_0 != sK9) | k1_xboole_0 != k2_zfmisc_1(sK9,sK10)) & (k1_xboole_0 = sK10 | k1_xboole_0 = sK9 | k1_xboole_0 = k2_zfmisc_1(sK9,sK10))),
% 3.69/1.03    inference(skolemisation,[status(esa),new_symbols(skolem,[sK9,sK10])],[f29,f30])).
% 3.69/1.03  
% 3.69/1.03  fof(f52,plain,(
% 3.69/1.03    k1_xboole_0 = sK10 | k1_xboole_0 = sK9 | k1_xboole_0 = k2_zfmisc_1(sK9,sK10)),
% 3.69/1.03    inference(cnf_transformation,[],[f31])).
% 3.69/1.03  
% 3.69/1.03  fof(f41,plain,(
% 3.69/1.03    ( ! [X2,X0,X10,X8,X1,X9] : (r2_hidden(X8,X2) | k4_tarski(X9,X10) != X8 | ~r2_hidden(X10,X1) | ~r2_hidden(X9,X0) | k2_zfmisc_1(X0,X1) != X2) )),
% 3.69/1.03    inference(cnf_transformation,[],[f21])).
% 3.69/1.03  
% 3.69/1.03  fof(f55,plain,(
% 3.69/1.03    ( ! [X2,X0,X10,X1,X9] : (r2_hidden(k4_tarski(X9,X10),X2) | ~r2_hidden(X10,X1) | ~r2_hidden(X9,X0) | k2_zfmisc_1(X0,X1) != X2) )),
% 3.69/1.03    inference(equality_resolution,[],[f41])).
% 3.69/1.03  
% 3.69/1.03  fof(f56,plain,(
% 3.69/1.03    ( ! [X0,X10,X1,X9] : (r2_hidden(k4_tarski(X9,X10),k2_zfmisc_1(X0,X1)) | ~r2_hidden(X10,X1) | ~r2_hidden(X9,X0)) )),
% 3.69/1.03    inference(equality_resolution,[],[f55])).
% 3.69/1.03  
% 3.69/1.03  fof(f53,plain,(
% 3.69/1.03    k1_xboole_0 != sK9 | k1_xboole_0 != k2_zfmisc_1(sK9,sK10)),
% 3.69/1.03    inference(cnf_transformation,[],[f31])).
% 3.69/1.03  
% 3.69/1.03  fof(f54,plain,(
% 3.69/1.03    k1_xboole_0 != sK10 | k1_xboole_0 != k2_zfmisc_1(sK9,sK10)),
% 3.69/1.03    inference(cnf_transformation,[],[f31])).
% 3.69/1.03  
% 3.69/1.03  cnf(c_15,plain,
% 3.69/1.03      ( r2_hidden(sK7(X0,X1),X0)
% 3.69/1.03      | r2_hidden(sK6(X0,X1),X1)
% 3.69/1.03      | k3_tarski(X0) = X1 ),
% 3.69/1.03      inference(cnf_transformation,[],[f50]) ).
% 3.69/1.03  
% 3.69/1.03  cnf(c_776,plain,
% 3.69/1.03      ( k3_tarski(X0) = X1
% 3.69/1.03      | r2_hidden(sK7(X0,X1),X0) = iProver_top
% 3.69/1.03      | r2_hidden(sK6(X0,X1),X1) = iProver_top ),
% 3.69/1.03      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 3.69/1.03  
% 3.69/1.03  cnf(c_1,plain,
% 3.69/1.03      ( ~ r1_xboole_0(X0,X1) | ~ r2_hidden(X2,X0) | ~ r2_hidden(X2,X1) ),
% 3.69/1.03      inference(cnf_transformation,[],[f35]) ).
% 3.69/1.03  
% 3.69/1.03  cnf(c_5,plain,
% 3.69/1.03      ( r1_xboole_0(X0,k1_xboole_0) ),
% 3.69/1.03      inference(cnf_transformation,[],[f37]) ).
% 3.69/1.03  
% 3.69/1.03  cnf(c_271,plain,
% 3.69/1.03      ( ~ r2_hidden(X0,X1)
% 3.69/1.03      | ~ r2_hidden(X0,X2)
% 3.69/1.03      | X3 != X1
% 3.69/1.03      | k1_xboole_0 != X2 ),
% 3.69/1.03      inference(resolution_lifted,[status(thm)],[c_1,c_5]) ).
% 3.69/1.03  
% 3.69/1.03  cnf(c_272,plain,
% 3.69/1.03      ( ~ r2_hidden(X0,X1) | ~ r2_hidden(X0,k1_xboole_0) ),
% 3.69/1.03      inference(unflattening,[status(thm)],[c_271]) ).
% 3.69/1.03  
% 3.69/1.03  cnf(c_0,plain,
% 3.69/1.03      ( ~ r1_tarski(X0,X1) | ~ r2_hidden(X2,X0) | r2_hidden(X2,X1) ),
% 3.69/1.03      inference(cnf_transformation,[],[f32]) ).
% 3.69/1.03  
% 3.69/1.03  cnf(c_4,plain,
% 3.69/1.03      ( r1_tarski(k1_xboole_0,X0) ),
% 3.69/1.03      inference(cnf_transformation,[],[f36]) ).
% 3.69/1.03  
% 3.69/1.03  cnf(c_232,plain,
% 3.69/1.03      ( ~ r2_hidden(X0,X1) | r2_hidden(X0,X2) | X3 != X2 | k1_xboole_0 != X1 ),
% 3.69/1.03      inference(resolution_lifted,[status(thm)],[c_0,c_4]) ).
% 3.69/1.03  
% 3.69/1.03  cnf(c_233,plain,
% 3.69/1.03      ( r2_hidden(X0,X1) | ~ r2_hidden(X0,k1_xboole_0) ),
% 3.69/1.03      inference(unflattening,[status(thm)],[c_232]) ).
% 3.69/1.03  
% 3.69/1.03  cnf(c_276,plain,
% 3.69/1.03      ( ~ r2_hidden(X0,k1_xboole_0) ),
% 3.69/1.03      inference(global_propositional_subsumption,[status(thm)],[c_272,c_233]) ).
% 3.69/1.03  
% 3.69/1.03  cnf(c_771,plain,
% 3.69/1.03      ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
% 3.69/1.03      inference(predicate_to_equality,[status(thm)],[c_276]) ).
% 3.69/1.03  
% 3.69/1.03  cnf(c_1867,plain,
% 3.69/1.03      ( k3_tarski(k1_xboole_0) = X0
% 3.69/1.03      | r2_hidden(sK6(k1_xboole_0,X0),X0) = iProver_top ),
% 3.69/1.03      inference(superposition,[status(thm)],[c_776,c_771]) ).
% 3.69/1.03  
% 3.69/1.03  cnf(c_1861,plain,
% 3.69/1.03      ( k3_tarski(X0) = k1_xboole_0
% 3.69/1.03      | r2_hidden(sK7(X0,k1_xboole_0),X0) = iProver_top ),
% 3.69/1.03      inference(superposition,[status(thm)],[c_776,c_771]) ).
% 3.69/1.03  
% 3.69/1.03  cnf(c_18,plain,
% 3.69/1.03      ( ~ r2_hidden(X0,k3_tarski(X1)) | r2_hidden(sK8(X1,X0),X1) ),
% 3.69/1.03      inference(cnf_transformation,[],[f61]) ).
% 3.69/1.03  
% 3.69/1.03  cnf(c_773,plain,
% 3.69/1.03      ( r2_hidden(X0,k3_tarski(X1)) != iProver_top
% 3.69/1.03      | r2_hidden(sK8(X1,X0),X1) = iProver_top ),
% 3.69/1.03      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 3.69/1.03  
% 3.69/1.03  cnf(c_12,plain,
% 3.69/1.03      ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) | r2_hidden(sK5(X1,X2,X0),X2) ),
% 3.69/1.03      inference(cnf_transformation,[],[f58]) ).
% 3.69/1.03  
% 3.69/1.03  cnf(c_779,plain,
% 3.69/1.03      ( r2_hidden(X0,k2_zfmisc_1(X1,X2)) != iProver_top
% 3.69/1.03      | r2_hidden(sK5(X1,X2,X0),X2) = iProver_top ),
% 3.69/1.03      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 3.69/1.03  
% 3.69/1.03  cnf(c_1154,plain,
% 3.69/1.03      ( r2_hidden(X0,k2_zfmisc_1(X1,k1_xboole_0)) != iProver_top ),
% 3.69/1.03      inference(superposition,[status(thm)],[c_779,c_771]) ).
% 3.69/1.03  
% 3.69/1.03  cnf(c_4836,plain,
% 3.69/1.03      ( r2_hidden(X0,k3_tarski(k2_zfmisc_1(X1,k1_xboole_0))) != iProver_top ),
% 3.69/1.03      inference(superposition,[status(thm)],[c_773,c_1154]) ).
% 3.69/1.03  
% 3.69/1.03  cnf(c_11939,plain,
% 3.69/1.03      ( k3_tarski(k3_tarski(k2_zfmisc_1(X0,k1_xboole_0))) = k1_xboole_0 ),
% 3.69/1.03      inference(superposition,[status(thm)],[c_1861,c_4836]) ).
% 3.69/1.03  
% 3.69/1.03  cnf(c_5902,plain,
% 3.69/1.03      ( r2_hidden(X0,k3_tarski(k3_tarski(k2_zfmisc_1(X1,k1_xboole_0)))) != iProver_top ),
% 3.69/1.03      inference(superposition,[status(thm)],[c_773,c_4836]) ).
% 3.69/1.03  
% 3.69/1.03  cnf(c_11950,plain,
% 3.69/1.03      ( k3_tarski(k3_tarski(k3_tarski(k2_zfmisc_1(X0,k1_xboole_0)))) = k1_xboole_0 ),
% 3.69/1.03      inference(superposition,[status(thm)],[c_1861,c_5902]) ).
% 3.69/1.03  
% 3.69/1.03  cnf(c_11974,plain,
% 3.69/1.03      ( k3_tarski(k1_xboole_0) = k1_xboole_0 ),
% 3.69/1.03      inference(demodulation,[status(thm)],[c_11939,c_11950]) ).
% 3.69/1.03  
% 3.69/1.03  cnf(c_13404,plain,
% 3.69/1.03      ( k1_xboole_0 = X0 | r2_hidden(sK6(k1_xboole_0,X0),X0) = iProver_top ),
% 3.69/1.03      inference(demodulation,[status(thm)],[c_1867,c_11974]) ).
% 3.69/1.03  
% 3.69/1.03  cnf(c_13414,plain,
% 3.69/1.03      ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
% 3.69/1.03      inference(superposition,[status(thm)],[c_13404,c_1154]) ).
% 3.69/1.03  
% 3.69/1.03  cnf(c_13,plain,
% 3.69/1.03      ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) | r2_hidden(sK4(X1,X2,X0),X1) ),
% 3.69/1.03      inference(cnf_transformation,[],[f59]) ).
% 3.69/1.03  
% 3.69/1.03  cnf(c_778,plain,
% 3.69/1.03      ( r2_hidden(X0,k2_zfmisc_1(X1,X2)) != iProver_top
% 3.69/1.03      | r2_hidden(sK4(X1,X2,X0),X1) = iProver_top ),
% 3.69/1.03      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 3.69/1.03  
% 3.69/1.03  cnf(c_4833,plain,
% 3.69/1.03      ( r2_hidden(X0,k2_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0),X2)) != iProver_top ),
% 3.69/1.03      inference(superposition,[status(thm)],[c_778,c_1154]) ).
% 3.69/1.03  
% 3.69/1.03  cnf(c_13425,plain,
% 3.69/1.03      ( k2_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0),X1) = k1_xboole_0 ),
% 3.69/1.03      inference(superposition,[status(thm)],[c_13404,c_4833]) ).
% 3.69/1.03  
% 3.69/1.03  cnf(c_13460,plain,
% 3.69/1.03      ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
% 3.69/1.03      inference(demodulation,[status(thm)],[c_13414,c_13425]) ).
% 3.69/1.03  
% 3.69/1.03  cnf(c_9,plain,
% 3.69/1.03      ( r2_hidden(sK2(X0,X1,X2),X0)
% 3.69/1.03      | r2_hidden(sK1(X0,X1,X2),X2)
% 3.69/1.03      | k2_zfmisc_1(X0,X1) = X2 ),
% 3.69/1.03      inference(cnf_transformation,[],[f42]) ).
% 3.69/1.03  
% 3.69/1.03  cnf(c_782,plain,
% 3.69/1.03      ( k2_zfmisc_1(X0,X1) = X2
% 3.69/1.03      | r2_hidden(sK2(X0,X1,X2),X0) = iProver_top
% 3.69/1.03      | r2_hidden(sK1(X0,X1,X2),X2) = iProver_top ),
% 3.69/1.03      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 3.69/1.03  
% 3.69/1.03  cnf(c_22,negated_conjecture,
% 3.69/1.03      ( k1_xboole_0 = k2_zfmisc_1(sK9,sK10)
% 3.69/1.03      | k1_xboole_0 = sK9
% 3.69/1.03      | k1_xboole_0 = sK10 ),
% 3.69/1.03      inference(cnf_transformation,[],[f52]) ).
% 3.69/1.03  
% 3.69/1.03  cnf(c_10,plain,
% 3.69/1.03      ( ~ r2_hidden(X0,X1)
% 3.69/1.03      | ~ r2_hidden(X2,X3)
% 3.69/1.03      | r2_hidden(k4_tarski(X2,X0),k2_zfmisc_1(X3,X1)) ),
% 3.69/1.03      inference(cnf_transformation,[],[f56]) ).
% 3.69/1.03  
% 3.69/1.03  cnf(c_781,plain,
% 3.69/1.03      ( r2_hidden(X0,X1) != iProver_top
% 3.69/1.03      | r2_hidden(X2,X3) != iProver_top
% 3.69/1.03      | r2_hidden(k4_tarski(X2,X0),k2_zfmisc_1(X3,X1)) = iProver_top ),
% 3.69/1.03      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 3.69/1.03  
% 3.69/1.03  cnf(c_2109,plain,
% 3.69/1.03      ( sK9 = k1_xboole_0
% 3.69/1.03      | sK10 = k1_xboole_0
% 3.69/1.03      | r2_hidden(X0,sK9) != iProver_top
% 3.69/1.03      | r2_hidden(X1,sK10) != iProver_top
% 3.69/1.03      | r2_hidden(k4_tarski(X0,X1),k1_xboole_0) = iProver_top ),
% 3.69/1.03      inference(superposition,[status(thm)],[c_22,c_781]) ).
% 3.69/1.03  
% 3.69/1.03  cnf(c_2215,plain,
% 3.69/1.03      ( sK9 = k1_xboole_0
% 3.69/1.03      | sK10 = k1_xboole_0
% 3.69/1.03      | r2_hidden(X0,sK9) != iProver_top
% 3.69/1.03      | r2_hidden(X1,sK10) != iProver_top ),
% 3.69/1.03      inference(forward_subsumption_resolution,[status(thm)],[c_2109,c_771]) ).
% 3.69/1.03  
% 3.69/1.03  cnf(c_3474,plain,
% 3.69/1.03      ( k2_zfmisc_1(X0,X1) = sK10
% 3.69/1.03      | sK9 = k1_xboole_0
% 3.69/1.03      | sK10 = k1_xboole_0
% 3.69/1.03      | r2_hidden(X2,sK9) != iProver_top
% 3.69/1.03      | r2_hidden(sK2(X0,X1,sK10),X0) = iProver_top ),
% 3.69/1.03      inference(superposition,[status(thm)],[c_782,c_2215]) ).
% 3.69/1.03  
% 3.69/1.03  cnf(c_66,plain,
% 3.69/1.03      ( r1_xboole_0(k1_xboole_0,k1_xboole_0) ),
% 3.69/1.03      inference(instantiation,[status(thm)],[c_5]) ).
% 3.69/1.03  
% 3.69/1.03  cnf(c_65,plain,
% 3.69/1.03      ( r1_xboole_0(X0,k1_xboole_0) = iProver_top ),
% 3.69/1.03      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 3.69/1.03  
% 3.69/1.03  cnf(c_67,plain,
% 3.69/1.03      ( r1_xboole_0(k1_xboole_0,k1_xboole_0) = iProver_top ),
% 3.69/1.03      inference(instantiation,[status(thm)],[c_65]) ).
% 3.69/1.03  
% 3.69/1.03  cnf(c_453,plain,( X0 = X0 ),theory(equality) ).
% 3.69/1.03  
% 3.69/1.03  cnf(c_464,plain,
% 3.69/1.03      ( k1_xboole_0 = k1_xboole_0 ),
% 3.69/1.03      inference(instantiation,[status(thm)],[c_453]) ).
% 3.69/1.03  
% 3.69/1.03  cnf(c_967,plain,
% 3.69/1.03      ( sK10 = sK10 ),
% 3.69/1.03      inference(instantiation,[status(thm)],[c_453]) ).
% 3.69/1.03  
% 3.69/1.03  cnf(c_971,plain,
% 3.69/1.03      ( sK9 = sK9 ),
% 3.69/1.03      inference(instantiation,[status(thm)],[c_453]) ).
% 3.69/1.03  
% 3.69/1.03  cnf(c_454,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 3.69/1.03  
% 3.69/1.03  cnf(c_958,plain,
% 3.69/1.03      ( X0 != X1 | sK10 != X1 | sK10 = X0 ),
% 3.69/1.03      inference(instantiation,[status(thm)],[c_454]) ).
% 3.69/1.03  
% 3.69/1.03  cnf(c_966,plain,
% 3.69/1.03      ( X0 != sK10 | sK10 = X0 | sK10 != sK10 ),
% 3.69/1.03      inference(instantiation,[status(thm)],[c_958]) ).
% 3.69/1.03  
% 3.69/1.03  cnf(c_984,plain,
% 3.69/1.03      ( k3_tarski(X0) != sK10 | sK10 = k3_tarski(X0) | sK10 != sK10 ),
% 3.69/1.03      inference(instantiation,[status(thm)],[c_966]) ).
% 3.69/1.03  
% 3.69/1.03  cnf(c_986,plain,
% 3.69/1.03      ( k3_tarski(k1_xboole_0) != sK10
% 3.69/1.03      | sK10 = k3_tarski(k1_xboole_0)
% 3.69/1.03      | sK10 != sK10 ),
% 3.69/1.03      inference(instantiation,[status(thm)],[c_984]) ).
% 3.69/1.03  
% 3.69/1.03  cnf(c_965,plain,
% 3.69/1.03      ( X0 != X1 | sK9 != X1 | sK9 = X0 ),
% 3.69/1.03      inference(instantiation,[status(thm)],[c_454]) ).
% 3.69/1.03  
% 3.69/1.03  cnf(c_970,plain,
% 3.69/1.03      ( X0 != sK9 | sK9 = X0 | sK9 != sK9 ),
% 3.69/1.03      inference(instantiation,[status(thm)],[c_965]) ).
% 3.69/1.03  
% 3.69/1.03  cnf(c_999,plain,
% 3.69/1.03      ( k3_tarski(X0) != sK9 | sK9 = k3_tarski(X0) | sK9 != sK9 ),
% 3.69/1.03      inference(instantiation,[status(thm)],[c_970]) ).
% 3.69/1.03  
% 3.69/1.03  cnf(c_1001,plain,
% 3.69/1.03      ( k3_tarski(k1_xboole_0) != sK9
% 3.69/1.03      | sK9 = k3_tarski(k1_xboole_0)
% 3.69/1.03      | sK9 != sK9 ),
% 3.69/1.03      inference(instantiation,[status(thm)],[c_999]) ).
% 3.69/1.03  
% 3.69/1.03  cnf(c_1023,plain,
% 3.69/1.03      ( X0 != k3_tarski(X1) | sK10 = X0 | sK10 != k3_tarski(X1) ),
% 3.69/1.03      inference(instantiation,[status(thm)],[c_958]) ).
% 3.69/1.03  
% 3.69/1.03  cnf(c_1024,plain,
% 3.69/1.03      ( sK10 != k3_tarski(k1_xboole_0)
% 3.69/1.03      | sK10 = k1_xboole_0
% 3.69/1.03      | k1_xboole_0 != k3_tarski(k1_xboole_0) ),
% 3.69/1.03      inference(instantiation,[status(thm)],[c_1023]) ).
% 3.69/1.03  
% 3.69/1.03  cnf(c_1027,plain,
% 3.69/1.03      ( X0 != k3_tarski(X1) | sK9 = X0 | sK9 != k3_tarski(X1) ),
% 3.69/1.03      inference(instantiation,[status(thm)],[c_965]) ).
% 3.69/1.03  
% 3.69/1.03  cnf(c_1028,plain,
% 3.69/1.03      ( sK9 != k3_tarski(k1_xboole_0)
% 3.69/1.03      | sK9 = k1_xboole_0
% 3.69/1.03      | k1_xboole_0 != k3_tarski(k1_xboole_0) ),
% 3.69/1.03      inference(instantiation,[status(thm)],[c_1027]) ).
% 3.69/1.03  
% 3.69/1.03  cnf(c_1192,plain,
% 3.69/1.03      ( ~ r1_xboole_0(X0,X1)
% 3.69/1.03      | ~ r2_hidden(sK7(X0,sK10),X0)
% 3.69/1.03      | ~ r2_hidden(sK7(X0,sK10),X1) ),
% 3.69/1.03      inference(instantiation,[status(thm)],[c_1]) ).
% 3.69/1.03  
% 3.69/1.03  cnf(c_1193,plain,
% 3.69/1.03      ( r1_xboole_0(X0,X1) != iProver_top
% 3.69/1.03      | r2_hidden(sK7(X0,sK10),X0) != iProver_top
% 3.69/1.03      | r2_hidden(sK7(X0,sK10),X1) != iProver_top ),
% 3.69/1.03      inference(predicate_to_equality,[status(thm)],[c_1192]) ).
% 3.69/1.03  
% 3.69/1.03  cnf(c_1195,plain,
% 3.69/1.03      ( r1_xboole_0(k1_xboole_0,k1_xboole_0) != iProver_top
% 3.69/1.03      | r2_hidden(sK7(k1_xboole_0,sK10),k1_xboole_0) != iProver_top ),
% 3.69/1.03      inference(instantiation,[status(thm)],[c_1193]) ).
% 3.69/1.03  
% 3.69/1.03  cnf(c_1335,plain,
% 3.69/1.03      ( ~ r1_xboole_0(X0,X1)
% 3.69/1.03      | ~ r2_hidden(sK7(X0,sK9),X0)
% 3.69/1.03      | ~ r2_hidden(sK7(X0,sK9),X1) ),
% 3.69/1.03      inference(instantiation,[status(thm)],[c_1]) ).
% 3.69/1.03  
% 3.69/1.03  cnf(c_1336,plain,
% 3.69/1.03      ( r1_xboole_0(X0,X1) != iProver_top
% 3.69/1.03      | r2_hidden(sK7(X0,sK9),X0) != iProver_top
% 3.69/1.03      | r2_hidden(sK7(X0,sK9),X1) != iProver_top ),
% 3.69/1.03      inference(predicate_to_equality,[status(thm)],[c_1335]) ).
% 3.69/1.03  
% 3.69/1.03  cnf(c_1338,plain,
% 3.69/1.03      ( r1_xboole_0(k1_xboole_0,k1_xboole_0) != iProver_top
% 3.69/1.03      | r2_hidden(sK7(k1_xboole_0,sK9),k1_xboole_0) != iProver_top ),
% 3.69/1.03      inference(instantiation,[status(thm)],[c_1336]) ).
% 3.69/1.03  
% 3.69/1.03  cnf(c_1643,plain,
% 3.69/1.03      ( k3_tarski(X0) != X1 | k1_xboole_0 != X1 | k1_xboole_0 = k3_tarski(X0) ),
% 3.69/1.03      inference(instantiation,[status(thm)],[c_454]) ).
% 3.69/1.03  
% 3.69/1.03  cnf(c_1644,plain,
% 3.69/1.03      ( k3_tarski(k1_xboole_0) != k1_xboole_0
% 3.69/1.03      | k1_xboole_0 = k3_tarski(k1_xboole_0)
% 3.69/1.03      | k1_xboole_0 != k1_xboole_0 ),
% 3.69/1.03      inference(instantiation,[status(thm)],[c_1643]) ).
% 3.69/1.03  
% 3.69/1.03  cnf(c_1937,plain,
% 3.69/1.03      ( r2_hidden(sK7(X0,k1_xboole_0),X0) | k3_tarski(X0) = k1_xboole_0 ),
% 3.69/1.03      inference(predicate_to_equality_rev,[status(thm)],[c_1861]) ).
% 3.69/1.03  
% 3.69/1.03  cnf(c_1939,plain,
% 3.69/1.03      ( r2_hidden(sK7(k1_xboole_0,k1_xboole_0),k1_xboole_0)
% 3.69/1.03      | k3_tarski(k1_xboole_0) = k1_xboole_0 ),
% 3.69/1.03      inference(instantiation,[status(thm)],[c_1937]) ).
% 3.69/1.03  
% 3.69/1.03  cnf(c_2837,plain,
% 3.69/1.03      ( ~ r1_xboole_0(X0,X1)
% 3.69/1.03      | ~ r2_hidden(sK7(X0,X2),X1)
% 3.69/1.03      | ~ r2_hidden(sK7(X0,X2),X0) ),
% 3.69/1.03      inference(instantiation,[status(thm)],[c_1]) ).
% 3.69/1.03  
% 3.69/1.03  cnf(c_2839,plain,
% 3.69/1.03      ( ~ r1_xboole_0(k1_xboole_0,k1_xboole_0)
% 3.69/1.03      | ~ r2_hidden(sK7(k1_xboole_0,k1_xboole_0),k1_xboole_0) ),
% 3.69/1.03      inference(instantiation,[status(thm)],[c_2837]) ).
% 3.69/1.03  
% 3.69/1.03  cnf(c_2224,plain,
% 3.69/1.03      ( k3_tarski(X0) = sK10
% 3.69/1.03      | sK9 = k1_xboole_0
% 3.69/1.03      | sK10 = k1_xboole_0
% 3.69/1.03      | r2_hidden(X1,sK9) != iProver_top
% 3.69/1.03      | r2_hidden(sK7(X0,sK10),X0) = iProver_top ),
% 3.69/1.03      inference(superposition,[status(thm)],[c_776,c_2215]) ).
% 3.69/1.03  
% 3.69/1.03  cnf(c_3319,plain,
% 3.69/1.03      ( k3_tarski(X0) = sK9
% 3.69/1.03      | k3_tarski(X1) = sK10
% 3.69/1.03      | sK9 = k1_xboole_0
% 3.69/1.03      | sK10 = k1_xboole_0
% 3.69/1.03      | r2_hidden(sK7(X0,sK9),X0) = iProver_top
% 3.69/1.03      | r2_hidden(sK7(X1,sK10),X1) = iProver_top ),
% 3.69/1.03      inference(superposition,[status(thm)],[c_776,c_2224]) ).
% 3.69/1.03  
% 3.69/1.03  cnf(c_3411,plain,
% 3.69/1.03      ( k3_tarski(k1_xboole_0) = sK9
% 3.69/1.03      | k3_tarski(k1_xboole_0) = sK10
% 3.69/1.03      | sK9 = k1_xboole_0
% 3.69/1.03      | sK10 = k1_xboole_0
% 3.69/1.03      | r2_hidden(sK7(k1_xboole_0,sK9),k1_xboole_0) = iProver_top
% 3.69/1.03      | r2_hidden(sK7(k1_xboole_0,sK10),k1_xboole_0) = iProver_top ),
% 3.69/1.03      inference(instantiation,[status(thm)],[c_3319]) ).
% 3.69/1.03  
% 3.69/1.03  cnf(c_4580,plain,
% 3.69/1.03      ( sK9 = k1_xboole_0 | sK10 = k1_xboole_0 ),
% 3.69/1.03      inference(global_propositional_subsumption,
% 3.69/1.03                [status(thm)],
% 3.69/1.03                [c_3474,c_66,c_67,c_464,c_967,c_971,c_986,c_1001,c_1024,
% 3.69/1.03                 c_1028,c_1195,c_1338,c_1644,c_1939,c_2839,c_3411]) ).
% 3.69/1.03  
% 3.69/1.03  cnf(c_21,negated_conjecture,
% 3.69/1.03      ( k1_xboole_0 != k2_zfmisc_1(sK9,sK10) | k1_xboole_0 != sK9 ),
% 3.69/1.03      inference(cnf_transformation,[],[f53]) ).
% 3.69/1.03  
% 3.69/1.03  cnf(c_4587,plain,
% 3.69/1.03      ( k2_zfmisc_1(k1_xboole_0,sK10) != k1_xboole_0
% 3.69/1.03      | sK9 != k1_xboole_0
% 3.69/1.03      | sK10 = k1_xboole_0 ),
% 3.69/1.03      inference(superposition,[status(thm)],[c_4580,c_21]) ).
% 3.69/1.03  
% 3.69/1.03  cnf(c_4592,plain,
% 3.69/1.03      ( k2_zfmisc_1(k1_xboole_0,sK10) != k1_xboole_0 | sK10 = k1_xboole_0 ),
% 3.69/1.03      inference(forward_subsumption_resolution,[status(thm)],[c_4587,c_4580]) ).
% 3.69/1.03  
% 3.69/1.03  cnf(c_13676,plain,
% 3.69/1.03      ( sK10 = k1_xboole_0 | k1_xboole_0 != k1_xboole_0 ),
% 3.69/1.03      inference(demodulation,[status(thm)],[c_13460,c_4592]) ).
% 3.69/1.03  
% 3.69/1.03  cnf(c_13677,plain,
% 3.69/1.03      ( sK10 = k1_xboole_0 ),
% 3.69/1.03      inference(equality_resolution_simp,[status(thm)],[c_13676]) ).
% 3.69/1.03  
% 3.69/1.03  cnf(c_20,negated_conjecture,
% 3.69/1.03      ( k1_xboole_0 != k2_zfmisc_1(sK9,sK10) | k1_xboole_0 != sK10 ),
% 3.69/1.03      inference(cnf_transformation,[],[f54]) ).
% 3.69/1.03  
% 3.69/1.03  cnf(c_13722,plain,
% 3.69/1.03      ( k2_zfmisc_1(sK9,k1_xboole_0) != k1_xboole_0
% 3.69/1.03      | k1_xboole_0 != k1_xboole_0 ),
% 3.69/1.03      inference(demodulation,[status(thm)],[c_13677,c_20]) ).
% 3.69/1.03  
% 3.69/1.03  cnf(c_13723,plain,
% 3.69/1.03      ( k2_zfmisc_1(sK9,k1_xboole_0) != k1_xboole_0 ),
% 3.69/1.03      inference(equality_resolution_simp,[status(thm)],[c_13722]) ).
% 3.69/1.03  
% 3.69/1.03  cnf(c_13725,plain,
% 3.69/1.03      ( k1_xboole_0 != k1_xboole_0 ),
% 3.69/1.03      inference(demodulation,[status(thm)],[c_13723,c_13414]) ).
% 3.69/1.03  
% 3.69/1.03  cnf(c_13726,plain,
% 3.69/1.03      ( $false ),
% 3.69/1.03      inference(equality_resolution_simp,[status(thm)],[c_13725]) ).
% 3.69/1.03  
% 3.69/1.03  
% 3.69/1.03  % SZS output end CNFRefutation for theBenchmark.p
% 3.69/1.03  
% 3.69/1.03  ------                               Statistics
% 3.69/1.03  
% 3.69/1.03  ------ General
% 3.69/1.03  
% 3.69/1.03  abstr_ref_over_cycles:                  0
% 3.69/1.03  abstr_ref_under_cycles:                 0
% 3.69/1.03  gc_basic_clause_elim:                   0
% 3.69/1.03  forced_gc_time:                         0
% 3.69/1.03  parsing_time:                           0.006
% 3.69/1.03  unif_index_cands_time:                  0.
% 3.69/1.03  unif_index_add_time:                    0.
% 3.69/1.03  orderings_time:                         0.
% 3.69/1.03  out_proof_time:                         0.009
% 3.69/1.03  total_time:                             0.328
% 3.69/1.03  num_of_symbols:                         49
% 3.69/1.03  num_of_terms:                           21651
% 3.69/1.03  
% 3.69/1.03  ------ Preprocessing
% 3.69/1.03  
% 3.69/1.03  num_of_splits:                          0
% 3.69/1.03  num_of_split_atoms:                     0
% 3.69/1.03  num_of_reused_defs:                     0
% 3.69/1.03  num_eq_ax_congr_red:                    76
% 3.69/1.03  num_of_sem_filtered_clauses:            1
% 3.69/1.03  num_of_subtypes:                        0
% 3.69/1.03  monotx_restored_types:                  0
% 3.69/1.03  sat_num_of_epr_types:                   0
% 3.69/1.03  sat_num_of_non_cyclic_types:            0
% 3.69/1.03  sat_guarded_non_collapsed_types:        0
% 3.69/1.03  num_pure_diseq_elim:                    0
% 3.69/1.03  simp_replaced_by:                       0
% 3.69/1.03  res_preprocessed:                       102
% 3.69/1.03  prep_upred:                             0
% 3.69/1.03  prep_unflattend:                        6
% 3.69/1.03  smt_new_axioms:                         0
% 3.69/1.03  pred_elim_cands:                        2
% 3.69/1.03  pred_elim:                              1
% 3.69/1.03  pred_elim_cl:                           1
% 3.69/1.03  pred_elim_cycles:                       4
% 3.69/1.03  merged_defs:                            0
% 3.69/1.03  merged_defs_ncl:                        0
% 3.69/1.03  bin_hyper_res:                          0
% 3.69/1.03  prep_cycles:                            4
% 3.69/1.03  pred_elim_time:                         0.001
% 3.69/1.03  splitting_time:                         0.
% 3.69/1.03  sem_filter_time:                        0.
% 3.69/1.03  monotx_time:                            0.
% 3.69/1.03  subtype_inf_time:                       0.
% 3.69/1.03  
% 3.69/1.03  ------ Problem properties
% 3.69/1.03  
% 3.69/1.03  clauses:                                22
% 3.69/1.03  conjectures:                            3
% 3.69/1.03  epr:                                    3
% 3.69/1.03  horn:                                   14
% 3.69/1.03  ground:                                 3
% 3.69/1.03  unary:                                  2
% 3.69/1.03  binary:                                 9
% 3.69/1.03  lits:                                   56
% 3.69/1.03  lits_eq:                                17
% 3.69/1.03  fd_pure:                                0
% 3.69/1.03  fd_pseudo:                              0
% 3.69/1.03  fd_cond:                                0
% 3.69/1.03  fd_pseudo_cond:                         7
% 3.69/1.03  ac_symbols:                             0
% 3.69/1.03  
% 3.69/1.03  ------ Propositional Solver
% 3.69/1.03  
% 3.69/1.03  prop_solver_calls:                      29
% 3.69/1.03  prop_fast_solver_calls:                 1247
% 3.69/1.03  smt_solver_calls:                       0
% 3.69/1.03  smt_fast_solver_calls:                  0
% 3.69/1.03  prop_num_of_clauses:                    4741
% 3.69/1.03  prop_preprocess_simplified:             8444
% 3.69/1.03  prop_fo_subsumed:                       207
% 3.69/1.03  prop_solver_time:                       0.
% 3.69/1.03  smt_solver_time:                        0.
% 3.69/1.03  smt_fast_solver_time:                   0.
% 3.69/1.03  prop_fast_solver_time:                  0.
% 3.69/1.03  prop_unsat_core_time:                   0.
% 3.69/1.03  
% 3.69/1.03  ------ QBF
% 3.69/1.03  
% 3.69/1.03  qbf_q_res:                              0
% 3.69/1.03  qbf_num_tautologies:                    0
% 3.69/1.03  qbf_prep_cycles:                        0
% 3.69/1.03  
% 3.69/1.03  ------ BMC1
% 3.69/1.03  
% 3.69/1.03  bmc1_current_bound:                     -1
% 3.69/1.03  bmc1_last_solved_bound:                 -1
% 3.69/1.03  bmc1_unsat_core_size:                   -1
% 3.69/1.03  bmc1_unsat_core_parents_size:           -1
% 3.69/1.03  bmc1_merge_next_fun:                    0
% 3.69/1.03  bmc1_unsat_core_clauses_time:           0.
% 3.69/1.03  
% 3.69/1.03  ------ Instantiation
% 3.69/1.03  
% 3.69/1.03  inst_num_of_clauses:                    957
% 3.69/1.03  inst_num_in_passive:                    13
% 3.69/1.03  inst_num_in_active:                     511
% 3.69/1.03  inst_num_in_unprocessed:                433
% 3.69/1.03  inst_num_of_loops:                      720
% 3.69/1.03  inst_num_of_learning_restarts:          0
% 3.69/1.03  inst_num_moves_active_passive:          202
% 3.69/1.03  inst_lit_activity:                      0
% 3.69/1.03  inst_lit_activity_moves:                0
% 3.69/1.03  inst_num_tautologies:                   0
% 3.69/1.03  inst_num_prop_implied:                  0
% 3.69/1.03  inst_num_existing_simplified:           0
% 3.69/1.03  inst_num_eq_res_simplified:             0
% 3.69/1.03  inst_num_child_elim:                    0
% 3.69/1.03  inst_num_of_dismatching_blockings:      1224
% 3.69/1.03  inst_num_of_non_proper_insts:           1095
% 3.69/1.03  inst_num_of_duplicates:                 0
% 3.69/1.03  inst_inst_num_from_inst_to_res:         0
% 3.69/1.03  inst_dismatching_checking_time:         0.
% 3.69/1.03  
% 3.69/1.03  ------ Resolution
% 3.69/1.03  
% 3.69/1.03  res_num_of_clauses:                     0
% 3.69/1.03  res_num_in_passive:                     0
% 3.69/1.03  res_num_in_active:                      0
% 3.69/1.03  res_num_of_loops:                       106
% 3.69/1.03  res_forward_subset_subsumed:            35
% 3.69/1.03  res_backward_subset_subsumed:           0
% 3.69/1.03  res_forward_subsumed:                   0
% 3.69/1.03  res_backward_subsumed:                  1
% 3.69/1.03  res_forward_subsumption_resolution:     0
% 3.69/1.03  res_backward_subsumption_resolution:    0
% 3.69/1.03  res_clause_to_clause_subsumption:       1567
% 3.69/1.03  res_orphan_elimination:                 0
% 3.69/1.03  res_tautology_del:                      90
% 3.69/1.03  res_num_eq_res_simplified:              0
% 3.69/1.03  res_num_sel_changes:                    0
% 3.69/1.03  res_moves_from_active_to_pass:          0
% 3.69/1.03  
% 3.69/1.03  ------ Superposition
% 3.69/1.03  
% 3.69/1.03  sup_time_total:                         0.
% 3.69/1.03  sup_time_generating:                    0.
% 3.69/1.03  sup_time_sim_full:                      0.
% 3.69/1.03  sup_time_sim_immed:                     0.
% 3.69/1.03  
% 3.69/1.03  sup_num_of_clauses:                     478
% 3.69/1.03  sup_num_in_active:                      34
% 3.69/1.03  sup_num_in_passive:                     444
% 3.69/1.03  sup_num_of_loops:                       143
% 3.69/1.03  sup_fw_superposition:                   523
% 3.69/1.03  sup_bw_superposition:                   255
% 3.69/1.03  sup_immediate_simplified:               95
% 3.69/1.03  sup_given_eliminated:                   0
% 3.69/1.03  comparisons_done:                       0
% 3.69/1.03  comparisons_avoided:                    13
% 3.69/1.03  
% 3.69/1.03  ------ Simplifications
% 3.69/1.03  
% 3.69/1.03  
% 3.69/1.03  sim_fw_subset_subsumed:                 16
% 3.69/1.03  sim_bw_subset_subsumed:                 31
% 3.69/1.03  sim_fw_subsumed:                        39
% 3.69/1.03  sim_bw_subsumed:                        0
% 3.69/1.03  sim_fw_subsumption_res:                 2
% 3.69/1.03  sim_bw_subsumption_res:                 0
% 3.69/1.03  sim_tautology_del:                      3
% 3.69/1.03  sim_eq_tautology_del:                   10
% 3.69/1.03  sim_eq_res_simp:                        2
% 3.69/1.03  sim_fw_demodulated:                     18
% 3.69/1.03  sim_bw_demodulated:                     119
% 3.69/1.03  sim_light_normalised:                   36
% 3.69/1.03  sim_joinable_taut:                      0
% 3.69/1.03  sim_joinable_simp:                      0
% 3.69/1.03  sim_ac_normalised:                      0
% 3.69/1.03  sim_smt_subsumption:                    0
% 3.69/1.03  
%------------------------------------------------------------------------------
