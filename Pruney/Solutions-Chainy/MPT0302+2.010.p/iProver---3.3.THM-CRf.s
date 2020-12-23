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
% DateTime   : Thu Dec  3 11:37:04 EST 2020

% Result     : Theorem 3.53s
% Output     : CNFRefutation 3.53s
% Verified   : 
% Statistics : Number of formulae       :  114 ( 328 expanded)
%              Number of clauses        :   62 ( 114 expanded)
%              Number of leaves         :   14 (  65 expanded)
%              Depth                    :   15
%              Number of atoms          :  385 (1236 expanded)
%              Number of equality atoms :  208 ( 577 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal clause size      :   18 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f10,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f14,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f10])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f14])).

fof(f16,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK0(X0,X1),X1)
          & r2_hidden(sK0(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f15,f16])).

fof(f34,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK0(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
    <=> ( r2_hidden(X1,X3)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
        | ~ r2_hidden(X1,X3)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X3)
          & r2_hidden(X0,X2) )
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f28,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
        | ~ r2_hidden(X1,X3)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X3)
          & r2_hidden(X0,X2) )
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ) ),
    inference(flattening,[],[f27])).

fof(f54,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
      | ~ r2_hidden(X1,X3)
      | ~ r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f8,conjecture,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X1,X0)
     => ( X0 = X1
        | k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f9,negated_conjecture,(
    ~ ! [X0,X1] :
        ( k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X1,X0)
       => ( X0 = X1
          | k1_xboole_0 = X1
          | k1_xboole_0 = X0 ) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f12,plain,(
    ? [X0,X1] :
      ( X0 != X1
      & k1_xboole_0 != X1
      & k1_xboole_0 != X0
      & k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X1,X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f13,plain,(
    ? [X0,X1] :
      ( X0 != X1
      & k1_xboole_0 != X1
      & k1_xboole_0 != X0
      & k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X1,X0) ) ),
    inference(flattening,[],[f12])).

fof(f31,plain,
    ( ? [X0,X1] :
        ( X0 != X1
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0
        & k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X1,X0) )
   => ( sK6 != sK7
      & k1_xboole_0 != sK7
      & k1_xboole_0 != sK6
      & k2_zfmisc_1(sK6,sK7) = k2_zfmisc_1(sK7,sK6) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,
    ( sK6 != sK7
    & k1_xboole_0 != sK7
    & k1_xboole_0 != sK6
    & k2_zfmisc_1(sK6,sK7) = k2_zfmisc_1(sK7,sK6) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7])],[f13,f31])).

fof(f58,plain,(
    k2_zfmisc_1(sK6,sK7) = k2_zfmisc_1(sK7,sK6) ),
    inference(cnf_transformation,[],[f32])).

fof(f53,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X1,X3)
      | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f59,plain,(
    k1_xboole_0 != sK6 ),
    inference(cnf_transformation,[],[f32])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f7])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f29])).

fof(f55,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f56,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f30])).

fof(f70,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f56])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( k2_zfmisc_1(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ? [X4,X5] :
              ( k4_tarski(X4,X5) = X3
              & r2_hidden(X5,X1)
              & r2_hidden(X4,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
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

fof(f22,plain,(
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
    inference(rectify,[],[f21])).

fof(f25,plain,(
    ! [X8,X1,X0] :
      ( ? [X11,X12] :
          ( k4_tarski(X11,X12) = X8
          & r2_hidden(X12,X1)
          & r2_hidden(X11,X0) )
     => ( k4_tarski(sK4(X0,X1,X8),sK5(X0,X1,X8)) = X8
        & r2_hidden(sK5(X0,X1,X8),X1)
        & r2_hidden(sK4(X0,X1,X8),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X6,X7] :
          ( k4_tarski(X6,X7) = X3
          & r2_hidden(X7,X1)
          & r2_hidden(X6,X0) )
     => ( k4_tarski(sK2(X0,X1,X2),sK3(X0,X1,X2)) = X3
        & r2_hidden(sK3(X0,X1,X2),X1)
        & r2_hidden(sK2(X0,X1,X2),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
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

fof(f26,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4,sK5])],[f22,f25,f24,f23])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( k2_zfmisc_1(X0,X1) = X2
      | r2_hidden(sK3(X0,X1,X2),X1)
      | r2_hidden(sK1(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f4,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f4])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k5_xboole_0(X1,X2))
    <=> ~ ( r2_hidden(X0,X1)
        <=> r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k5_xboole_0(X1,X2))
    <=> ( r2_hidden(X0,X1)
      <~> r2_hidden(X0,X2) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f18,plain,(
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
    inference(nnf_transformation,[],[f11])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,k5_xboole_0(X1,X2))
      | r2_hidden(X0,X1)
      | ~ r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f57,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f30])).

fof(f69,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f57])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X2)
      | ~ r2_hidden(X0,X1)
      | ~ r2_hidden(X0,k5_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f35,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK0(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f52,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X0,X2)
      | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f60,plain,(
    k1_xboole_0 != sK7 ),
    inference(cnf_transformation,[],[f32])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( k2_zfmisc_1(X0,X1) = X2
      | r2_hidden(sK2(X0,X1,X2),X0)
      | r2_hidden(sK1(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f19])).

fof(f42,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f61,plain,(
    sK6 != sK7 ),
    inference(cnf_transformation,[],[f32])).

cnf(c_1,plain,
    ( r2_hidden(sK0(X0,X1),X0)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_598,plain,
    ( r2_hidden(sK0(X0,X1),X0) = iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_19,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X2,X3)
    | r2_hidden(k4_tarski(X0,X2),k2_zfmisc_1(X1,X3)) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_582,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X2,X3) != iProver_top
    | r2_hidden(k4_tarski(X0,X2),k2_zfmisc_1(X1,X3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_28,negated_conjecture,
    ( k2_zfmisc_1(sK6,sK7) = k2_zfmisc_1(sK7,sK6) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_20,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(k4_tarski(X2,X0),k2_zfmisc_1(X3,X1)) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_581,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r2_hidden(k4_tarski(X2,X0),k2_zfmisc_1(X3,X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_986,plain,
    ( r2_hidden(X0,sK6) = iProver_top
    | r2_hidden(k4_tarski(X1,X0),k2_zfmisc_1(sK6,sK7)) != iProver_top ),
    inference(superposition,[status(thm)],[c_28,c_581])).

cnf(c_1758,plain,
    ( r2_hidden(X0,sK7) != iProver_top
    | r2_hidden(X1,sK6) != iProver_top
    | r2_hidden(X0,sK6) = iProver_top ),
    inference(superposition,[status(thm)],[c_582,c_986])).

cnf(c_4779,plain,
    ( r2_hidden(X0,sK6) != iProver_top
    | r2_hidden(sK0(sK7,X1),sK6) = iProver_top
    | r1_tarski(sK7,X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_598,c_1758])).

cnf(c_9278,plain,
    ( r2_hidden(sK0(sK7,X0),sK6) = iProver_top
    | r1_tarski(sK7,X0) = iProver_top
    | r1_tarski(sK6,X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_598,c_4779])).

cnf(c_27,negated_conjecture,
    ( k1_xboole_0 != sK6 ),
    inference(cnf_transformation,[],[f59])).

cnf(c_24,plain,
    ( k2_zfmisc_1(X0,X1) != k1_xboole_0
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f55])).

cnf(c_29,plain,
    ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) != k1_xboole_0
    | k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_24])).

cnf(c_23,plain,
    ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f70])).

cnf(c_30,plain,
    ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_23])).

cnf(c_283,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_791,plain,
    ( sK6 != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = sK6 ),
    inference(instantiation,[status(thm)],[c_283])).

cnf(c_792,plain,
    ( sK6 != k1_xboole_0
    | k1_xboole_0 = sK6
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_791])).

cnf(c_13,plain,
    ( r2_hidden(sK3(X0,X1,X2),X1)
    | r2_hidden(sK1(X0,X1,X2),X2)
    | k2_zfmisc_1(X0,X1) = X2 ),
    inference(cnf_transformation,[],[f49])).

cnf(c_588,plain,
    ( k2_zfmisc_1(X0,X1) = X2
    | r2_hidden(sK3(X0,X1,X2),X1) = iProver_top
    | r2_hidden(sK1(X0,X1,X2),X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_10,plain,
    ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f43])).

cnf(c_3,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | r2_hidden(X0,k5_xboole_0(X2,X1)) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_596,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,X2) = iProver_top
    | r2_hidden(X0,k5_xboole_0(X2,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_2707,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r2_hidden(X0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_10,c_596])).

cnf(c_3000,plain,
    ( k2_zfmisc_1(X0,k1_xboole_0) = X1
    | r2_hidden(sK3(X0,k1_xboole_0,X1),X2) = iProver_top
    | r2_hidden(sK1(X0,k1_xboole_0,X1),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_588,c_2707])).

cnf(c_22,plain,
    ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f69])).

cnf(c_3004,plain,
    ( k1_xboole_0 = X0
    | r2_hidden(sK3(X1,k1_xboole_0,X0),X2) = iProver_top
    | r2_hidden(sK1(X1,k1_xboole_0,X0),X0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_3000,c_22])).

cnf(c_5,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X0,X2)
    | ~ r2_hidden(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_594,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,X2) != iProver_top
    | r2_hidden(X0,k5_xboole_0(X1,X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_4351,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_10,c_594])).

cnf(c_4572,plain,
    ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4351,c_2707])).

cnf(c_4587,plain,
    ( k1_xboole_0 = X0
    | r2_hidden(sK1(X1,k1_xboole_0,X0),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_3004,c_4572])).

cnf(c_9299,plain,
    ( sK6 = k1_xboole_0
    | r2_hidden(sK0(sK7,X0),sK6) = iProver_top
    | r1_tarski(sK7,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_4587,c_4779])).

cnf(c_9688,plain,
    ( r1_tarski(sK7,X0) = iProver_top
    | r2_hidden(sK0(sK7,X0),sK6) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_9278,c_27,c_29,c_30,c_792,c_9299])).

cnf(c_9689,plain,
    ( r2_hidden(sK0(sK7,X0),sK6) = iProver_top
    | r1_tarski(sK7,X0) = iProver_top ),
    inference(renaming,[status(thm)],[c_9688])).

cnf(c_0,plain,
    ( ~ r2_hidden(sK0(X0,X1),X1)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_599,plain,
    ( r2_hidden(sK0(X0,X1),X1) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_9696,plain,
    ( r1_tarski(sK7,sK6) = iProver_top ),
    inference(superposition,[status(thm)],[c_9689,c_599])).

cnf(c_21,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(k4_tarski(X0,X2),k2_zfmisc_1(X1,X3)) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_580,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r2_hidden(k4_tarski(X0,X2),k2_zfmisc_1(X1,X3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_987,plain,
    ( r2_hidden(X0,sK7) = iProver_top
    | r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(sK6,sK7)) != iProver_top ),
    inference(superposition,[status(thm)],[c_28,c_580])).

cnf(c_1763,plain,
    ( r2_hidden(X0,sK7) != iProver_top
    | r2_hidden(X1,sK7) = iProver_top
    | r2_hidden(X1,sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_582,c_987])).

cnf(c_5740,plain,
    ( r2_hidden(X0,sK7) = iProver_top
    | r2_hidden(X0,sK6) != iProver_top
    | r1_tarski(sK7,X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_598,c_1763])).

cnf(c_26,negated_conjecture,
    ( k1_xboole_0 != sK7 ),
    inference(cnf_transformation,[],[f60])).

cnf(c_789,plain,
    ( sK7 != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = sK7 ),
    inference(instantiation,[status(thm)],[c_283])).

cnf(c_790,plain,
    ( sK7 != k1_xboole_0
    | k1_xboole_0 = sK7
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_789])).

cnf(c_14,plain,
    ( r2_hidden(sK2(X0,X1,X2),X0)
    | r2_hidden(sK1(X0,X1,X2),X2)
    | k2_zfmisc_1(X0,X1) = X2 ),
    inference(cnf_transformation,[],[f48])).

cnf(c_587,plain,
    ( k2_zfmisc_1(X0,X1) = X2
    | r2_hidden(sK2(X0,X1,X2),X0) = iProver_top
    | r2_hidden(sK1(X0,X1,X2),X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_2737,plain,
    ( k2_zfmisc_1(k1_xboole_0,X0) = X1
    | r2_hidden(sK2(k1_xboole_0,X0,X1),X2) = iProver_top
    | r2_hidden(sK1(k1_xboole_0,X0,X1),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_587,c_2707])).

cnf(c_2753,plain,
    ( k1_xboole_0 = X0
    | r2_hidden(sK2(k1_xboole_0,X1,X0),X2) = iProver_top
    | r2_hidden(sK1(k1_xboole_0,X1,X0),X0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_2737,c_23])).

cnf(c_4585,plain,
    ( k1_xboole_0 = X0
    | r2_hidden(sK1(k1_xboole_0,X1,X0),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_2753,c_4572])).

cnf(c_6288,plain,
    ( sK7 = k1_xboole_0
    | r2_hidden(X0,sK7) = iProver_top
    | r2_hidden(X0,sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_4585,c_1763])).

cnf(c_7549,plain,
    ( r2_hidden(X0,sK6) != iProver_top
    | r2_hidden(X0,sK7) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5740,c_26,c_29,c_30,c_790,c_6288])).

cnf(c_7550,plain,
    ( r2_hidden(X0,sK7) = iProver_top
    | r2_hidden(X0,sK6) != iProver_top ),
    inference(renaming,[status(thm)],[c_7549])).

cnf(c_7557,plain,
    ( r2_hidden(sK0(sK6,X0),sK7) = iProver_top
    | r1_tarski(sK6,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_598,c_7550])).

cnf(c_7885,plain,
    ( r1_tarski(sK6,sK7) = iProver_top ),
    inference(superposition,[status(thm)],[c_7557,c_599])).

cnf(c_7,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f42])).

cnf(c_25,negated_conjecture,
    ( sK6 != sK7 ),
    inference(cnf_transformation,[],[f61])).

cnf(c_1121,plain,
    ( ~ r1_tarski(sK7,sK6)
    | ~ r1_tarski(sK6,sK7) ),
    inference(resolution,[status(thm)],[c_7,c_25])).

cnf(c_1122,plain,
    ( r1_tarski(sK7,sK6) != iProver_top
    | r1_tarski(sK6,sK7) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1121])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_9696,c_7885,c_1122])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 13:45:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 3.53/0.99  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.53/0.99  
% 3.53/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.53/0.99  
% 3.53/0.99  ------  iProver source info
% 3.53/0.99  
% 3.53/0.99  git: date: 2020-06-30 10:37:57 +0100
% 3.53/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.53/0.99  git: non_committed_changes: false
% 3.53/0.99  git: last_make_outside_of_git: false
% 3.53/0.99  
% 3.53/0.99  ------ 
% 3.53/0.99  
% 3.53/0.99  ------ Input Options
% 3.53/0.99  
% 3.53/0.99  --out_options                           all
% 3.53/0.99  --tptp_safe_out                         true
% 3.53/0.99  --problem_path                          ""
% 3.53/0.99  --include_path                          ""
% 3.53/0.99  --clausifier                            res/vclausify_rel
% 3.53/0.99  --clausifier_options                    --mode clausify
% 3.53/0.99  --stdin                                 false
% 3.53/0.99  --stats_out                             sel
% 3.53/0.99  
% 3.53/0.99  ------ General Options
% 3.53/0.99  
% 3.53/0.99  --fof                                   false
% 3.53/0.99  --time_out_real                         604.99
% 3.53/0.99  --time_out_virtual                      -1.
% 3.53/0.99  --symbol_type_check                     false
% 3.53/0.99  --clausify_out                          false
% 3.53/0.99  --sig_cnt_out                           false
% 3.53/0.99  --trig_cnt_out                          false
% 3.53/0.99  --trig_cnt_out_tolerance                1.
% 3.53/0.99  --trig_cnt_out_sk_spl                   false
% 3.53/0.99  --abstr_cl_out                          false
% 3.53/0.99  
% 3.53/0.99  ------ Global Options
% 3.53/0.99  
% 3.53/0.99  --schedule                              none
% 3.53/0.99  --add_important_lit                     false
% 3.53/0.99  --prop_solver_per_cl                    1000
% 3.53/0.99  --min_unsat_core                        false
% 3.53/0.99  --soft_assumptions                      false
% 3.53/0.99  --soft_lemma_size                       3
% 3.53/0.99  --prop_impl_unit_size                   0
% 3.53/0.99  --prop_impl_unit                        []
% 3.53/0.99  --share_sel_clauses                     true
% 3.53/0.99  --reset_solvers                         false
% 3.53/0.99  --bc_imp_inh                            [conj_cone]
% 3.53/0.99  --conj_cone_tolerance                   3.
% 3.53/0.99  --extra_neg_conj                        none
% 3.53/0.99  --large_theory_mode                     true
% 3.53/0.99  --prolific_symb_bound                   200
% 3.53/0.99  --lt_threshold                          2000
% 3.53/0.99  --clause_weak_htbl                      true
% 3.53/0.99  --gc_record_bc_elim                     false
% 3.53/0.99  
% 3.53/0.99  ------ Preprocessing Options
% 3.53/0.99  
% 3.53/0.99  --preprocessing_flag                    true
% 3.53/0.99  --time_out_prep_mult                    0.1
% 3.53/0.99  --splitting_mode                        input
% 3.53/0.99  --splitting_grd                         true
% 3.53/0.99  --splitting_cvd                         false
% 3.53/0.99  --splitting_cvd_svl                     false
% 3.53/0.99  --splitting_nvd                         32
% 3.53/0.99  --sub_typing                            true
% 3.53/0.99  --prep_gs_sim                           false
% 3.53/0.99  --prep_unflatten                        true
% 3.53/0.99  --prep_res_sim                          true
% 3.53/0.99  --prep_upred                            true
% 3.53/0.99  --prep_sem_filter                       exhaustive
% 3.53/0.99  --prep_sem_filter_out                   false
% 3.53/0.99  --pred_elim                             false
% 3.53/0.99  --res_sim_input                         true
% 3.53/0.99  --eq_ax_congr_red                       true
% 3.53/0.99  --pure_diseq_elim                       true
% 3.53/0.99  --brand_transform                       false
% 3.53/0.99  --non_eq_to_eq                          false
% 3.53/0.99  --prep_def_merge                        true
% 3.53/0.99  --prep_def_merge_prop_impl              false
% 3.53/0.99  --prep_def_merge_mbd                    true
% 3.53/0.99  --prep_def_merge_tr_red                 false
% 3.53/0.99  --prep_def_merge_tr_cl                  false
% 3.53/0.99  --smt_preprocessing                     true
% 3.53/0.99  --smt_ac_axioms                         fast
% 3.53/0.99  --preprocessed_out                      false
% 3.53/0.99  --preprocessed_stats                    false
% 3.53/0.99  
% 3.53/0.99  ------ Abstraction refinement Options
% 3.53/0.99  
% 3.53/0.99  --abstr_ref                             []
% 3.53/0.99  --abstr_ref_prep                        false
% 3.53/0.99  --abstr_ref_until_sat                   false
% 3.53/0.99  --abstr_ref_sig_restrict                funpre
% 3.53/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 3.53/0.99  --abstr_ref_under                       []
% 3.53/0.99  
% 3.53/0.99  ------ SAT Options
% 3.53/0.99  
% 3.53/0.99  --sat_mode                              false
% 3.53/0.99  --sat_fm_restart_options                ""
% 3.53/0.99  --sat_gr_def                            false
% 3.53/0.99  --sat_epr_types                         true
% 3.53/0.99  --sat_non_cyclic_types                  false
% 3.53/0.99  --sat_finite_models                     false
% 3.53/0.99  --sat_fm_lemmas                         false
% 3.53/0.99  --sat_fm_prep                           false
% 3.53/0.99  --sat_fm_uc_incr                        true
% 3.53/0.99  --sat_out_model                         small
% 3.53/0.99  --sat_out_clauses                       false
% 3.53/0.99  
% 3.53/0.99  ------ QBF Options
% 3.53/0.99  
% 3.53/0.99  --qbf_mode                              false
% 3.53/0.99  --qbf_elim_univ                         false
% 3.53/0.99  --qbf_dom_inst                          none
% 3.53/0.99  --qbf_dom_pre_inst                      false
% 3.53/0.99  --qbf_sk_in                             false
% 3.53/0.99  --qbf_pred_elim                         true
% 3.53/0.99  --qbf_split                             512
% 3.53/0.99  
% 3.53/0.99  ------ BMC1 Options
% 3.53/0.99  
% 3.53/0.99  --bmc1_incremental                      false
% 3.53/0.99  --bmc1_axioms                           reachable_all
% 3.53/0.99  --bmc1_min_bound                        0
% 3.53/0.99  --bmc1_max_bound                        -1
% 3.53/0.99  --bmc1_max_bound_default                -1
% 3.53/0.99  --bmc1_symbol_reachability              true
% 3.53/0.99  --bmc1_property_lemmas                  false
% 3.53/0.99  --bmc1_k_induction                      false
% 3.53/0.99  --bmc1_non_equiv_states                 false
% 3.53/0.99  --bmc1_deadlock                         false
% 3.53/0.99  --bmc1_ucm                              false
% 3.53/0.99  --bmc1_add_unsat_core                   none
% 3.53/0.99  --bmc1_unsat_core_children              false
% 3.53/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 3.53/0.99  --bmc1_out_stat                         full
% 3.53/0.99  --bmc1_ground_init                      false
% 3.53/0.99  --bmc1_pre_inst_next_state              false
% 3.53/0.99  --bmc1_pre_inst_state                   false
% 3.53/0.99  --bmc1_pre_inst_reach_state             false
% 3.53/0.99  --bmc1_out_unsat_core                   false
% 3.53/0.99  --bmc1_aig_witness_out                  false
% 3.53/0.99  --bmc1_verbose                          false
% 3.53/0.99  --bmc1_dump_clauses_tptp                false
% 3.53/0.99  --bmc1_dump_unsat_core_tptp             false
% 3.53/0.99  --bmc1_dump_file                        -
% 3.53/0.99  --bmc1_ucm_expand_uc_limit              128
% 3.53/0.99  --bmc1_ucm_n_expand_iterations          6
% 3.53/0.99  --bmc1_ucm_extend_mode                  1
% 3.53/0.99  --bmc1_ucm_init_mode                    2
% 3.53/0.99  --bmc1_ucm_cone_mode                    none
% 3.53/0.99  --bmc1_ucm_reduced_relation_type        0
% 3.53/0.99  --bmc1_ucm_relax_model                  4
% 3.53/0.99  --bmc1_ucm_full_tr_after_sat            true
% 3.53/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 3.53/0.99  --bmc1_ucm_layered_model                none
% 3.53/0.99  --bmc1_ucm_max_lemma_size               10
% 3.53/0.99  
% 3.53/0.99  ------ AIG Options
% 3.53/0.99  
% 3.53/0.99  --aig_mode                              false
% 3.53/0.99  
% 3.53/0.99  ------ Instantiation Options
% 3.53/0.99  
% 3.53/0.99  --instantiation_flag                    true
% 3.53/0.99  --inst_sos_flag                         false
% 3.53/0.99  --inst_sos_phase                        true
% 3.53/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.53/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.53/0.99  --inst_lit_sel_side                     num_symb
% 3.53/0.99  --inst_solver_per_active                1400
% 3.53/0.99  --inst_solver_calls_frac                1.
% 3.53/0.99  --inst_passive_queue_type               priority_queues
% 3.53/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.53/0.99  --inst_passive_queues_freq              [25;2]
% 3.53/0.99  --inst_dismatching                      true
% 3.53/0.99  --inst_eager_unprocessed_to_passive     true
% 3.53/0.99  --inst_prop_sim_given                   true
% 3.53/0.99  --inst_prop_sim_new                     false
% 3.53/0.99  --inst_subs_new                         false
% 3.53/0.99  --inst_eq_res_simp                      false
% 3.53/0.99  --inst_subs_given                       false
% 3.53/0.99  --inst_orphan_elimination               true
% 3.53/0.99  --inst_learning_loop_flag               true
% 3.53/0.99  --inst_learning_start                   3000
% 3.53/0.99  --inst_learning_factor                  2
% 3.53/0.99  --inst_start_prop_sim_after_learn       3
% 3.53/0.99  --inst_sel_renew                        solver
% 3.53/0.99  --inst_lit_activity_flag                true
% 3.53/0.99  --inst_restr_to_given                   false
% 3.53/0.99  --inst_activity_threshold               500
% 3.53/0.99  --inst_out_proof                        true
% 3.53/0.99  
% 3.53/0.99  ------ Resolution Options
% 3.53/0.99  
% 3.53/0.99  --resolution_flag                       true
% 3.53/0.99  --res_lit_sel                           adaptive
% 3.53/0.99  --res_lit_sel_side                      none
% 3.53/0.99  --res_ordering                          kbo
% 3.53/0.99  --res_to_prop_solver                    active
% 3.53/0.99  --res_prop_simpl_new                    false
% 3.53/0.99  --res_prop_simpl_given                  true
% 3.53/0.99  --res_passive_queue_type                priority_queues
% 3.53/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.53/0.99  --res_passive_queues_freq               [15;5]
% 3.53/0.99  --res_forward_subs                      full
% 3.53/0.99  --res_backward_subs                     full
% 3.53/0.99  --res_forward_subs_resolution           true
% 3.53/0.99  --res_backward_subs_resolution          true
% 3.53/0.99  --res_orphan_elimination                true
% 3.53/0.99  --res_time_limit                        2.
% 3.53/0.99  --res_out_proof                         true
% 3.53/0.99  
% 3.53/0.99  ------ Superposition Options
% 3.53/0.99  
% 3.53/0.99  --superposition_flag                    true
% 3.53/0.99  --sup_passive_queue_type                priority_queues
% 3.53/0.99  --sup_passive_queues                    [[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.53/0.99  --sup_passive_queues_freq               [1;4]
% 3.53/0.99  --demod_completeness_check              fast
% 3.53/0.99  --demod_use_ground                      true
% 3.53/0.99  --sup_to_prop_solver                    passive
% 3.53/0.99  --sup_prop_simpl_new                    true
% 3.53/0.99  --sup_prop_simpl_given                  true
% 3.53/0.99  --sup_fun_splitting                     false
% 3.53/0.99  --sup_smt_interval                      50000
% 3.53/0.99  
% 3.53/0.99  ------ Superposition Simplification Setup
% 3.53/0.99  
% 3.53/0.99  --sup_indices_passive                   []
% 3.53/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.53/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.53/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.53/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 3.53/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.53/0.99  --sup_full_bw                           [BwDemod]
% 3.53/0.99  --sup_immed_triv                        [TrivRules]
% 3.53/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.53/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.53/0.99  --sup_immed_bw_main                     []
% 3.53/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.53/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 3.53/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.53/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.53/0.99  
% 3.53/0.99  ------ Combination Options
% 3.53/0.99  
% 3.53/0.99  --comb_res_mult                         3
% 3.53/0.99  --comb_sup_mult                         2
% 3.53/0.99  --comb_inst_mult                        10
% 3.53/0.99  
% 3.53/0.99  ------ Debug Options
% 3.53/0.99  
% 3.53/0.99  --dbg_backtrace                         false
% 3.53/0.99  --dbg_dump_prop_clauses                 false
% 3.53/0.99  --dbg_dump_prop_clauses_file            -
% 3.53/0.99  --dbg_out_stat                          false
% 3.53/0.99  ------ Parsing...
% 3.53/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.53/0.99  
% 3.53/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 1 0s  sf_e 
% 3.53/0.99  
% 3.53/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.53/0.99  
% 3.53/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.53/0.99  ------ Proving...
% 3.53/0.99  ------ Problem Properties 
% 3.53/0.99  
% 3.53/0.99  
% 3.53/0.99  clauses                                 28
% 3.53/0.99  conjectures                             4
% 3.53/0.99  EPR                                     6
% 3.53/0.99  Horn                                    20
% 3.53/0.99  unary                                   8
% 3.53/0.99  binary                                  7
% 3.53/0.99  lits                                    63
% 3.53/0.99  lits eq                                 18
% 3.53/0.99  fd_pure                                 0
% 3.53/0.99  fd_pseudo                               0
% 3.53/0.99  fd_cond                                 1
% 3.53/0.99  fd_pseudo_cond                          5
% 3.53/0.99  AC symbols                              0
% 3.53/0.99  
% 3.53/0.99  ------ Input Options Time Limit: Unbounded
% 3.53/0.99  
% 3.53/0.99  
% 3.53/0.99  ------ 
% 3.53/0.99  Current options:
% 3.53/0.99  ------ 
% 3.53/0.99  
% 3.53/0.99  ------ Input Options
% 3.53/0.99  
% 3.53/0.99  --out_options                           all
% 3.53/0.99  --tptp_safe_out                         true
% 3.53/0.99  --problem_path                          ""
% 3.53/0.99  --include_path                          ""
% 3.53/0.99  --clausifier                            res/vclausify_rel
% 3.53/0.99  --clausifier_options                    --mode clausify
% 3.53/0.99  --stdin                                 false
% 3.53/0.99  --stats_out                             sel
% 3.53/0.99  
% 3.53/0.99  ------ General Options
% 3.53/0.99  
% 3.53/0.99  --fof                                   false
% 3.53/0.99  --time_out_real                         604.99
% 3.53/0.99  --time_out_virtual                      -1.
% 3.53/0.99  --symbol_type_check                     false
% 3.53/0.99  --clausify_out                          false
% 3.53/0.99  --sig_cnt_out                           false
% 3.53/0.99  --trig_cnt_out                          false
% 3.53/0.99  --trig_cnt_out_tolerance                1.
% 3.53/0.99  --trig_cnt_out_sk_spl                   false
% 3.53/0.99  --abstr_cl_out                          false
% 3.53/0.99  
% 3.53/0.99  ------ Global Options
% 3.53/0.99  
% 3.53/0.99  --schedule                              none
% 3.53/0.99  --add_important_lit                     false
% 3.53/0.99  --prop_solver_per_cl                    1000
% 3.53/0.99  --min_unsat_core                        false
% 3.53/0.99  --soft_assumptions                      false
% 3.53/0.99  --soft_lemma_size                       3
% 3.53/0.99  --prop_impl_unit_size                   0
% 3.53/0.99  --prop_impl_unit                        []
% 3.53/0.99  --share_sel_clauses                     true
% 3.53/0.99  --reset_solvers                         false
% 3.53/0.99  --bc_imp_inh                            [conj_cone]
% 3.53/0.99  --conj_cone_tolerance                   3.
% 3.53/0.99  --extra_neg_conj                        none
% 3.53/0.99  --large_theory_mode                     true
% 3.53/0.99  --prolific_symb_bound                   200
% 3.53/0.99  --lt_threshold                          2000
% 3.53/0.99  --clause_weak_htbl                      true
% 3.53/0.99  --gc_record_bc_elim                     false
% 3.53/0.99  
% 3.53/0.99  ------ Preprocessing Options
% 3.53/0.99  
% 3.53/0.99  --preprocessing_flag                    true
% 3.53/0.99  --time_out_prep_mult                    0.1
% 3.53/0.99  --splitting_mode                        input
% 3.53/0.99  --splitting_grd                         true
% 3.53/0.99  --splitting_cvd                         false
% 3.53/0.99  --splitting_cvd_svl                     false
% 3.53/0.99  --splitting_nvd                         32
% 3.53/0.99  --sub_typing                            true
% 3.53/0.99  --prep_gs_sim                           false
% 3.53/0.99  --prep_unflatten                        true
% 3.53/0.99  --prep_res_sim                          true
% 3.53/0.99  --prep_upred                            true
% 3.53/0.99  --prep_sem_filter                       exhaustive
% 3.53/0.99  --prep_sem_filter_out                   false
% 3.53/0.99  --pred_elim                             false
% 3.53/0.99  --res_sim_input                         true
% 3.53/0.99  --eq_ax_congr_red                       true
% 3.53/0.99  --pure_diseq_elim                       true
% 3.53/0.99  --brand_transform                       false
% 3.53/0.99  --non_eq_to_eq                          false
% 3.53/0.99  --prep_def_merge                        true
% 3.53/0.99  --prep_def_merge_prop_impl              false
% 3.53/0.99  --prep_def_merge_mbd                    true
% 3.53/0.99  --prep_def_merge_tr_red                 false
% 3.53/0.99  --prep_def_merge_tr_cl                  false
% 3.53/0.99  --smt_preprocessing                     true
% 3.53/0.99  --smt_ac_axioms                         fast
% 3.53/0.99  --preprocessed_out                      false
% 3.53/0.99  --preprocessed_stats                    false
% 3.53/0.99  
% 3.53/0.99  ------ Abstraction refinement Options
% 3.53/0.99  
% 3.53/0.99  --abstr_ref                             []
% 3.53/0.99  --abstr_ref_prep                        false
% 3.53/0.99  --abstr_ref_until_sat                   false
% 3.53/0.99  --abstr_ref_sig_restrict                funpre
% 3.53/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 3.53/0.99  --abstr_ref_under                       []
% 3.53/0.99  
% 3.53/0.99  ------ SAT Options
% 3.53/0.99  
% 3.53/0.99  --sat_mode                              false
% 3.53/0.99  --sat_fm_restart_options                ""
% 3.53/0.99  --sat_gr_def                            false
% 3.53/0.99  --sat_epr_types                         true
% 3.53/0.99  --sat_non_cyclic_types                  false
% 3.53/0.99  --sat_finite_models                     false
% 3.53/0.99  --sat_fm_lemmas                         false
% 3.53/0.99  --sat_fm_prep                           false
% 3.53/0.99  --sat_fm_uc_incr                        true
% 3.53/0.99  --sat_out_model                         small
% 3.53/0.99  --sat_out_clauses                       false
% 3.53/0.99  
% 3.53/0.99  ------ QBF Options
% 3.53/0.99  
% 3.53/0.99  --qbf_mode                              false
% 3.53/0.99  --qbf_elim_univ                         false
% 3.53/0.99  --qbf_dom_inst                          none
% 3.53/0.99  --qbf_dom_pre_inst                      false
% 3.53/0.99  --qbf_sk_in                             false
% 3.53/0.99  --qbf_pred_elim                         true
% 3.53/0.99  --qbf_split                             512
% 3.53/0.99  
% 3.53/0.99  ------ BMC1 Options
% 3.53/0.99  
% 3.53/0.99  --bmc1_incremental                      false
% 3.53/0.99  --bmc1_axioms                           reachable_all
% 3.53/0.99  --bmc1_min_bound                        0
% 3.53/0.99  --bmc1_max_bound                        -1
% 3.53/0.99  --bmc1_max_bound_default                -1
% 3.53/0.99  --bmc1_symbol_reachability              true
% 3.53/0.99  --bmc1_property_lemmas                  false
% 3.53/0.99  --bmc1_k_induction                      false
% 3.53/0.99  --bmc1_non_equiv_states                 false
% 3.53/0.99  --bmc1_deadlock                         false
% 3.53/0.99  --bmc1_ucm                              false
% 3.53/0.99  --bmc1_add_unsat_core                   none
% 3.53/0.99  --bmc1_unsat_core_children              false
% 3.53/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 3.53/0.99  --bmc1_out_stat                         full
% 3.53/0.99  --bmc1_ground_init                      false
% 3.53/0.99  --bmc1_pre_inst_next_state              false
% 3.53/0.99  --bmc1_pre_inst_state                   false
% 3.53/0.99  --bmc1_pre_inst_reach_state             false
% 3.53/0.99  --bmc1_out_unsat_core                   false
% 3.53/0.99  --bmc1_aig_witness_out                  false
% 3.53/0.99  --bmc1_verbose                          false
% 3.53/0.99  --bmc1_dump_clauses_tptp                false
% 3.53/0.99  --bmc1_dump_unsat_core_tptp             false
% 3.53/0.99  --bmc1_dump_file                        -
% 3.53/0.99  --bmc1_ucm_expand_uc_limit              128
% 3.53/0.99  --bmc1_ucm_n_expand_iterations          6
% 3.53/0.99  --bmc1_ucm_extend_mode                  1
% 3.53/0.99  --bmc1_ucm_init_mode                    2
% 3.53/0.99  --bmc1_ucm_cone_mode                    none
% 3.53/0.99  --bmc1_ucm_reduced_relation_type        0
% 3.53/0.99  --bmc1_ucm_relax_model                  4
% 3.53/0.99  --bmc1_ucm_full_tr_after_sat            true
% 3.53/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 3.53/0.99  --bmc1_ucm_layered_model                none
% 3.53/0.99  --bmc1_ucm_max_lemma_size               10
% 3.53/0.99  
% 3.53/0.99  ------ AIG Options
% 3.53/0.99  
% 3.53/0.99  --aig_mode                              false
% 3.53/0.99  
% 3.53/0.99  ------ Instantiation Options
% 3.53/0.99  
% 3.53/0.99  --instantiation_flag                    true
% 3.53/0.99  --inst_sos_flag                         false
% 3.53/0.99  --inst_sos_phase                        true
% 3.53/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.53/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.53/0.99  --inst_lit_sel_side                     num_symb
% 3.53/0.99  --inst_solver_per_active                1400
% 3.53/0.99  --inst_solver_calls_frac                1.
% 3.53/0.99  --inst_passive_queue_type               priority_queues
% 3.53/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.53/0.99  --inst_passive_queues_freq              [25;2]
% 3.53/0.99  --inst_dismatching                      true
% 3.53/0.99  --inst_eager_unprocessed_to_passive     true
% 3.53/0.99  --inst_prop_sim_given                   true
% 3.53/0.99  --inst_prop_sim_new                     false
% 3.53/0.99  --inst_subs_new                         false
% 3.53/0.99  --inst_eq_res_simp                      false
% 3.53/0.99  --inst_subs_given                       false
% 3.53/0.99  --inst_orphan_elimination               true
% 3.53/0.99  --inst_learning_loop_flag               true
% 3.53/0.99  --inst_learning_start                   3000
% 3.53/0.99  --inst_learning_factor                  2
% 3.53/0.99  --inst_start_prop_sim_after_learn       3
% 3.53/0.99  --inst_sel_renew                        solver
% 3.53/0.99  --inst_lit_activity_flag                true
% 3.53/0.99  --inst_restr_to_given                   false
% 3.53/0.99  --inst_activity_threshold               500
% 3.53/0.99  --inst_out_proof                        true
% 3.53/0.99  
% 3.53/0.99  ------ Resolution Options
% 3.53/0.99  
% 3.53/0.99  --resolution_flag                       true
% 3.53/0.99  --res_lit_sel                           adaptive
% 3.53/0.99  --res_lit_sel_side                      none
% 3.53/0.99  --res_ordering                          kbo
% 3.53/0.99  --res_to_prop_solver                    active
% 3.53/0.99  --res_prop_simpl_new                    false
% 3.53/0.99  --res_prop_simpl_given                  true
% 3.53/0.99  --res_passive_queue_type                priority_queues
% 3.53/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.53/0.99  --res_passive_queues_freq               [15;5]
% 3.53/0.99  --res_forward_subs                      full
% 3.53/0.99  --res_backward_subs                     full
% 3.53/0.99  --res_forward_subs_resolution           true
% 3.53/0.99  --res_backward_subs_resolution          true
% 3.53/0.99  --res_orphan_elimination                true
% 3.53/0.99  --res_time_limit                        2.
% 3.53/0.99  --res_out_proof                         true
% 3.53/0.99  
% 3.53/0.99  ------ Superposition Options
% 3.53/0.99  
% 3.53/0.99  --superposition_flag                    true
% 3.53/0.99  --sup_passive_queue_type                priority_queues
% 3.53/0.99  --sup_passive_queues                    [[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.53/0.99  --sup_passive_queues_freq               [1;4]
% 3.53/0.99  --demod_completeness_check              fast
% 3.53/0.99  --demod_use_ground                      true
% 3.53/0.99  --sup_to_prop_solver                    passive
% 3.53/0.99  --sup_prop_simpl_new                    true
% 3.53/0.99  --sup_prop_simpl_given                  true
% 3.53/0.99  --sup_fun_splitting                     false
% 3.53/0.99  --sup_smt_interval                      50000
% 3.53/0.99  
% 3.53/0.99  ------ Superposition Simplification Setup
% 3.53/0.99  
% 3.53/0.99  --sup_indices_passive                   []
% 3.53/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.53/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.53/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.53/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 3.53/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.53/0.99  --sup_full_bw                           [BwDemod]
% 3.53/0.99  --sup_immed_triv                        [TrivRules]
% 3.53/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.53/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.53/0.99  --sup_immed_bw_main                     []
% 3.53/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.53/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 3.53/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.53/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.53/0.99  
% 3.53/0.99  ------ Combination Options
% 3.53/0.99  
% 3.53/0.99  --comb_res_mult                         3
% 3.53/0.99  --comb_sup_mult                         2
% 3.53/0.99  --comb_inst_mult                        10
% 3.53/0.99  
% 3.53/0.99  ------ Debug Options
% 3.53/0.99  
% 3.53/0.99  --dbg_backtrace                         false
% 3.53/0.99  --dbg_dump_prop_clauses                 false
% 3.53/0.99  --dbg_dump_prop_clauses_file            -
% 3.53/0.99  --dbg_out_stat                          false
% 3.53/0.99  
% 3.53/0.99  
% 3.53/0.99  
% 3.53/0.99  
% 3.53/0.99  ------ Proving...
% 3.53/0.99  
% 3.53/0.99  
% 3.53/0.99  % SZS status Theorem for theBenchmark.p
% 3.53/0.99  
% 3.53/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 3.53/0.99  
% 3.53/0.99  fof(f1,axiom,(
% 3.53/0.99    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 3.53/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.53/0.99  
% 3.53/0.99  fof(f10,plain,(
% 3.53/0.99    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 3.53/0.99    inference(ennf_transformation,[],[f1])).
% 3.53/0.99  
% 3.53/0.99  fof(f14,plain,(
% 3.53/0.99    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 3.53/0.99    inference(nnf_transformation,[],[f10])).
% 3.53/0.99  
% 3.53/0.99  fof(f15,plain,(
% 3.53/0.99    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 3.53/0.99    inference(rectify,[],[f14])).
% 3.53/0.99  
% 3.53/0.99  fof(f16,plain,(
% 3.53/0.99    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 3.53/0.99    introduced(choice_axiom,[])).
% 3.53/0.99  
% 3.53/0.99  fof(f17,plain,(
% 3.53/0.99    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 3.53/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f15,f16])).
% 3.53/0.99  
% 3.53/0.99  fof(f34,plain,(
% 3.53/0.99    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK0(X0,X1),X0)) )),
% 3.53/0.99    inference(cnf_transformation,[],[f17])).
% 3.53/0.99  
% 3.53/0.99  fof(f6,axiom,(
% 3.53/0.99    ! [X0,X1,X2,X3] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) <=> (r2_hidden(X1,X3) & r2_hidden(X0,X2)))),
% 3.53/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.53/0.99  
% 3.53/0.99  fof(f27,plain,(
% 3.53/0.99    ! [X0,X1,X2,X3] : ((r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | (~r2_hidden(X1,X3) | ~r2_hidden(X0,X2))) & ((r2_hidden(X1,X3) & r2_hidden(X0,X2)) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))))),
% 3.53/0.99    inference(nnf_transformation,[],[f6])).
% 3.53/0.99  
% 3.53/0.99  fof(f28,plain,(
% 3.53/0.99    ! [X0,X1,X2,X3] : ((r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | ~r2_hidden(X1,X3) | ~r2_hidden(X0,X2)) & ((r2_hidden(X1,X3) & r2_hidden(X0,X2)) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))))),
% 3.53/0.99    inference(flattening,[],[f27])).
% 3.53/0.99  
% 3.53/0.99  fof(f54,plain,(
% 3.53/0.99    ( ! [X2,X0,X3,X1] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | ~r2_hidden(X1,X3) | ~r2_hidden(X0,X2)) )),
% 3.53/0.99    inference(cnf_transformation,[],[f28])).
% 3.53/0.99  
% 3.53/0.99  fof(f8,conjecture,(
% 3.53/0.99    ! [X0,X1] : (k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X1,X0) => (X0 = X1 | k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 3.53/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.53/0.99  
% 3.53/0.99  fof(f9,negated_conjecture,(
% 3.53/0.99    ~! [X0,X1] : (k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X1,X0) => (X0 = X1 | k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 3.53/0.99    inference(negated_conjecture,[],[f8])).
% 3.53/0.99  
% 3.53/0.99  fof(f12,plain,(
% 3.53/0.99    ? [X0,X1] : ((X0 != X1 & k1_xboole_0 != X1 & k1_xboole_0 != X0) & k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X1,X0))),
% 3.53/0.99    inference(ennf_transformation,[],[f9])).
% 3.53/0.99  
% 3.53/0.99  fof(f13,plain,(
% 3.53/0.99    ? [X0,X1] : (X0 != X1 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X1,X0))),
% 3.53/0.99    inference(flattening,[],[f12])).
% 3.53/0.99  
% 3.53/0.99  fof(f31,plain,(
% 3.53/0.99    ? [X0,X1] : (X0 != X1 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X1,X0)) => (sK6 != sK7 & k1_xboole_0 != sK7 & k1_xboole_0 != sK6 & k2_zfmisc_1(sK6,sK7) = k2_zfmisc_1(sK7,sK6))),
% 3.53/0.99    introduced(choice_axiom,[])).
% 3.53/0.99  
% 3.53/0.99  fof(f32,plain,(
% 3.53/0.99    sK6 != sK7 & k1_xboole_0 != sK7 & k1_xboole_0 != sK6 & k2_zfmisc_1(sK6,sK7) = k2_zfmisc_1(sK7,sK6)),
% 3.53/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7])],[f13,f31])).
% 3.53/0.99  
% 3.53/0.99  fof(f58,plain,(
% 3.53/0.99    k2_zfmisc_1(sK6,sK7) = k2_zfmisc_1(sK7,sK6)),
% 3.53/0.99    inference(cnf_transformation,[],[f32])).
% 3.53/0.99  
% 3.53/0.99  fof(f53,plain,(
% 3.53/0.99    ( ! [X2,X0,X3,X1] : (r2_hidden(X1,X3) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))) )),
% 3.53/0.99    inference(cnf_transformation,[],[f28])).
% 3.53/0.99  
% 3.53/0.99  fof(f59,plain,(
% 3.53/0.99    k1_xboole_0 != sK6),
% 3.53/0.99    inference(cnf_transformation,[],[f32])).
% 3.53/0.99  
% 3.53/0.99  fof(f7,axiom,(
% 3.53/0.99    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 3.53/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.53/0.99  
% 3.53/0.99  fof(f29,plain,(
% 3.53/0.99    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 3.53/0.99    inference(nnf_transformation,[],[f7])).
% 3.53/0.99  
% 3.53/0.99  fof(f30,plain,(
% 3.53/0.99    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 3.53/0.99    inference(flattening,[],[f29])).
% 3.53/0.99  
% 3.53/0.99  fof(f55,plain,(
% 3.53/0.99    ( ! [X0,X1] : (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)) )),
% 3.53/0.99    inference(cnf_transformation,[],[f30])).
% 3.53/0.99  
% 3.53/0.99  fof(f56,plain,(
% 3.53/0.99    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X0) )),
% 3.53/0.99    inference(cnf_transformation,[],[f30])).
% 3.53/0.99  
% 3.53/0.99  fof(f70,plain,(
% 3.53/0.99    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 3.53/0.99    inference(equality_resolution,[],[f56])).
% 3.53/0.99  
% 3.53/0.99  fof(f5,axiom,(
% 3.53/0.99    ! [X0,X1,X2] : (k2_zfmisc_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4,X5] : (k4_tarski(X4,X5) = X3 & r2_hidden(X5,X1) & r2_hidden(X4,X0))))),
% 3.53/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.53/0.99  
% 3.53/0.99  fof(f21,plain,(
% 3.53/0.99    ! [X0,X1,X2] : ((k2_zfmisc_1(X0,X1) = X2 | ? [X3] : ((! [X4,X5] : (k4_tarski(X4,X5) != X3 | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X0)) | ~r2_hidden(X3,X2)) & (? [X4,X5] : (k4_tarski(X4,X5) = X3 & r2_hidden(X5,X1) & r2_hidden(X4,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ! [X4,X5] : (k4_tarski(X4,X5) != X3 | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X0))) & (? [X4,X5] : (k4_tarski(X4,X5) = X3 & r2_hidden(X5,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X3,X2))) | k2_zfmisc_1(X0,X1) != X2))),
% 3.53/0.99    inference(nnf_transformation,[],[f5])).
% 3.53/0.99  
% 3.53/0.99  fof(f22,plain,(
% 3.53/0.99    ! [X0,X1,X2] : ((k2_zfmisc_1(X0,X1) = X2 | ? [X3] : ((! [X4,X5] : (k4_tarski(X4,X5) != X3 | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X0)) | ~r2_hidden(X3,X2)) & (? [X6,X7] : (k4_tarski(X6,X7) = X3 & r2_hidden(X7,X1) & r2_hidden(X6,X0)) | r2_hidden(X3,X2)))) & (! [X8] : ((r2_hidden(X8,X2) | ! [X9,X10] : (k4_tarski(X9,X10) != X8 | ~r2_hidden(X10,X1) | ~r2_hidden(X9,X0))) & (? [X11,X12] : (k4_tarski(X11,X12) = X8 & r2_hidden(X12,X1) & r2_hidden(X11,X0)) | ~r2_hidden(X8,X2))) | k2_zfmisc_1(X0,X1) != X2))),
% 3.53/0.99    inference(rectify,[],[f21])).
% 3.53/0.99  
% 3.53/0.99  fof(f25,plain,(
% 3.53/0.99    ! [X8,X1,X0] : (? [X11,X12] : (k4_tarski(X11,X12) = X8 & r2_hidden(X12,X1) & r2_hidden(X11,X0)) => (k4_tarski(sK4(X0,X1,X8),sK5(X0,X1,X8)) = X8 & r2_hidden(sK5(X0,X1,X8),X1) & r2_hidden(sK4(X0,X1,X8),X0)))),
% 3.53/0.99    introduced(choice_axiom,[])).
% 3.53/0.99  
% 3.53/0.99  fof(f24,plain,(
% 3.53/0.99    ( ! [X3] : (! [X2,X1,X0] : (? [X6,X7] : (k4_tarski(X6,X7) = X3 & r2_hidden(X7,X1) & r2_hidden(X6,X0)) => (k4_tarski(sK2(X0,X1,X2),sK3(X0,X1,X2)) = X3 & r2_hidden(sK3(X0,X1,X2),X1) & r2_hidden(sK2(X0,X1,X2),X0)))) )),
% 3.53/0.99    introduced(choice_axiom,[])).
% 3.53/0.99  
% 3.53/0.99  fof(f23,plain,(
% 3.53/0.99    ! [X2,X1,X0] : (? [X3] : ((! [X4,X5] : (k4_tarski(X4,X5) != X3 | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X0)) | ~r2_hidden(X3,X2)) & (? [X6,X7] : (k4_tarski(X6,X7) = X3 & r2_hidden(X7,X1) & r2_hidden(X6,X0)) | r2_hidden(X3,X2))) => ((! [X5,X4] : (k4_tarski(X4,X5) != sK1(X0,X1,X2) | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X0)) | ~r2_hidden(sK1(X0,X1,X2),X2)) & (? [X7,X6] : (k4_tarski(X6,X7) = sK1(X0,X1,X2) & r2_hidden(X7,X1) & r2_hidden(X6,X0)) | r2_hidden(sK1(X0,X1,X2),X2))))),
% 3.53/0.99    introduced(choice_axiom,[])).
% 3.53/0.99  
% 3.53/0.99  fof(f26,plain,(
% 3.53/0.99    ! [X0,X1,X2] : ((k2_zfmisc_1(X0,X1) = X2 | ((! [X4,X5] : (k4_tarski(X4,X5) != sK1(X0,X1,X2) | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X0)) | ~r2_hidden(sK1(X0,X1,X2),X2)) & ((k4_tarski(sK2(X0,X1,X2),sK3(X0,X1,X2)) = sK1(X0,X1,X2) & r2_hidden(sK3(X0,X1,X2),X1) & r2_hidden(sK2(X0,X1,X2),X0)) | r2_hidden(sK1(X0,X1,X2),X2)))) & (! [X8] : ((r2_hidden(X8,X2) | ! [X9,X10] : (k4_tarski(X9,X10) != X8 | ~r2_hidden(X10,X1) | ~r2_hidden(X9,X0))) & ((k4_tarski(sK4(X0,X1,X8),sK5(X0,X1,X8)) = X8 & r2_hidden(sK5(X0,X1,X8),X1) & r2_hidden(sK4(X0,X1,X8),X0)) | ~r2_hidden(X8,X2))) | k2_zfmisc_1(X0,X1) != X2))),
% 3.53/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4,sK5])],[f22,f25,f24,f23])).
% 3.53/0.99  
% 3.53/0.99  fof(f49,plain,(
% 3.53/0.99    ( ! [X2,X0,X1] : (k2_zfmisc_1(X0,X1) = X2 | r2_hidden(sK3(X0,X1,X2),X1) | r2_hidden(sK1(X0,X1,X2),X2)) )),
% 3.53/0.99    inference(cnf_transformation,[],[f26])).
% 3.53/0.99  
% 3.53/0.99  fof(f4,axiom,(
% 3.53/0.99    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 3.53/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.53/0.99  
% 3.53/0.99  fof(f43,plain,(
% 3.53/0.99    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 3.53/0.99    inference(cnf_transformation,[],[f4])).
% 3.53/0.99  
% 3.53/0.99  fof(f2,axiom,(
% 3.53/0.99    ! [X0,X1,X2] : (r2_hidden(X0,k5_xboole_0(X1,X2)) <=> ~(r2_hidden(X0,X1) <=> r2_hidden(X0,X2)))),
% 3.53/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.53/0.99  
% 3.53/0.99  fof(f11,plain,(
% 3.53/0.99    ! [X0,X1,X2] : (r2_hidden(X0,k5_xboole_0(X1,X2)) <=> (r2_hidden(X0,X1) <~> r2_hidden(X0,X2)))),
% 3.53/0.99    inference(ennf_transformation,[],[f2])).
% 3.53/0.99  
% 3.53/0.99  fof(f18,plain,(
% 3.53/0.99    ! [X0,X1,X2] : ((r2_hidden(X0,k5_xboole_0(X1,X2)) | ((r2_hidden(X0,X1) | ~r2_hidden(X0,X2)) & (r2_hidden(X0,X2) | ~r2_hidden(X0,X1)))) & (((~r2_hidden(X0,X2) | ~r2_hidden(X0,X1)) & (r2_hidden(X0,X2) | r2_hidden(X0,X1))) | ~r2_hidden(X0,k5_xboole_0(X1,X2))))),
% 3.53/0.99    inference(nnf_transformation,[],[f11])).
% 3.53/0.99  
% 3.53/0.99  fof(f39,plain,(
% 3.53/0.99    ( ! [X2,X0,X1] : (r2_hidden(X0,k5_xboole_0(X1,X2)) | r2_hidden(X0,X1) | ~r2_hidden(X0,X2)) )),
% 3.53/0.99    inference(cnf_transformation,[],[f18])).
% 3.53/0.99  
% 3.53/0.99  fof(f57,plain,(
% 3.53/0.99    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X1) )),
% 3.53/0.99    inference(cnf_transformation,[],[f30])).
% 3.53/0.99  
% 3.53/0.99  fof(f69,plain,(
% 3.53/0.99    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 3.53/0.99    inference(equality_resolution,[],[f57])).
% 3.53/0.99  
% 3.53/0.99  fof(f37,plain,(
% 3.53/0.99    ( ! [X2,X0,X1] : (~r2_hidden(X0,X2) | ~r2_hidden(X0,X1) | ~r2_hidden(X0,k5_xboole_0(X1,X2))) )),
% 3.53/0.99    inference(cnf_transformation,[],[f18])).
% 3.53/0.99  
% 3.53/0.99  fof(f35,plain,(
% 3.53/0.99    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r2_hidden(sK0(X0,X1),X1)) )),
% 3.53/0.99    inference(cnf_transformation,[],[f17])).
% 3.53/0.99  
% 3.53/0.99  fof(f52,plain,(
% 3.53/0.99    ( ! [X2,X0,X3,X1] : (r2_hidden(X0,X2) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))) )),
% 3.53/0.99    inference(cnf_transformation,[],[f28])).
% 3.53/0.99  
% 3.53/0.99  fof(f60,plain,(
% 3.53/0.99    k1_xboole_0 != sK7),
% 3.53/0.99    inference(cnf_transformation,[],[f32])).
% 3.53/0.99  
% 3.53/0.99  fof(f48,plain,(
% 3.53/0.99    ( ! [X2,X0,X1] : (k2_zfmisc_1(X0,X1) = X2 | r2_hidden(sK2(X0,X1,X2),X0) | r2_hidden(sK1(X0,X1,X2),X2)) )),
% 3.53/0.99    inference(cnf_transformation,[],[f26])).
% 3.53/0.99  
% 3.53/0.99  fof(f3,axiom,(
% 3.53/0.99    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 3.53/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.53/0.99  
% 3.53/0.99  fof(f19,plain,(
% 3.53/0.99    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.53/0.99    inference(nnf_transformation,[],[f3])).
% 3.53/0.99  
% 3.53/0.99  fof(f20,plain,(
% 3.53/0.99    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.53/0.99    inference(flattening,[],[f19])).
% 3.53/0.99  
% 3.53/0.99  fof(f42,plain,(
% 3.53/0.99    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 3.53/0.99    inference(cnf_transformation,[],[f20])).
% 3.53/0.99  
% 3.53/0.99  fof(f61,plain,(
% 3.53/0.99    sK6 != sK7),
% 3.53/0.99    inference(cnf_transformation,[],[f32])).
% 3.53/0.99  
% 3.53/0.99  cnf(c_1,plain,
% 3.53/0.99      ( r2_hidden(sK0(X0,X1),X0) | r1_tarski(X0,X1) ),
% 3.53/0.99      inference(cnf_transformation,[],[f34]) ).
% 3.53/0.99  
% 3.53/0.99  cnf(c_598,plain,
% 3.53/0.99      ( r2_hidden(sK0(X0,X1),X0) = iProver_top
% 3.53/0.99      | r1_tarski(X0,X1) = iProver_top ),
% 3.53/0.99      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 3.53/0.99  
% 3.53/0.99  cnf(c_19,plain,
% 3.53/0.99      ( ~ r2_hidden(X0,X1)
% 3.53/0.99      | ~ r2_hidden(X2,X3)
% 3.53/0.99      | r2_hidden(k4_tarski(X0,X2),k2_zfmisc_1(X1,X3)) ),
% 3.53/0.99      inference(cnf_transformation,[],[f54]) ).
% 3.53/0.99  
% 3.53/0.99  cnf(c_582,plain,
% 3.53/0.99      ( r2_hidden(X0,X1) != iProver_top
% 3.53/0.99      | r2_hidden(X2,X3) != iProver_top
% 3.53/0.99      | r2_hidden(k4_tarski(X0,X2),k2_zfmisc_1(X1,X3)) = iProver_top ),
% 3.53/0.99      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 3.53/0.99  
% 3.53/0.99  cnf(c_28,negated_conjecture,
% 3.53/0.99      ( k2_zfmisc_1(sK6,sK7) = k2_zfmisc_1(sK7,sK6) ),
% 3.53/0.99      inference(cnf_transformation,[],[f58]) ).
% 3.53/0.99  
% 3.53/0.99  cnf(c_20,plain,
% 3.53/0.99      ( r2_hidden(X0,X1)
% 3.53/0.99      | ~ r2_hidden(k4_tarski(X2,X0),k2_zfmisc_1(X3,X1)) ),
% 3.53/0.99      inference(cnf_transformation,[],[f53]) ).
% 3.53/0.99  
% 3.53/0.99  cnf(c_581,plain,
% 3.53/0.99      ( r2_hidden(X0,X1) = iProver_top
% 3.53/0.99      | r2_hidden(k4_tarski(X2,X0),k2_zfmisc_1(X3,X1)) != iProver_top ),
% 3.53/0.99      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 3.53/0.99  
% 3.53/0.99  cnf(c_986,plain,
% 3.53/0.99      ( r2_hidden(X0,sK6) = iProver_top
% 3.53/0.99      | r2_hidden(k4_tarski(X1,X0),k2_zfmisc_1(sK6,sK7)) != iProver_top ),
% 3.53/0.99      inference(superposition,[status(thm)],[c_28,c_581]) ).
% 3.53/0.99  
% 3.53/0.99  cnf(c_1758,plain,
% 3.53/0.99      ( r2_hidden(X0,sK7) != iProver_top
% 3.53/0.99      | r2_hidden(X1,sK6) != iProver_top
% 3.53/0.99      | r2_hidden(X0,sK6) = iProver_top ),
% 3.53/0.99      inference(superposition,[status(thm)],[c_582,c_986]) ).
% 3.53/0.99  
% 3.53/0.99  cnf(c_4779,plain,
% 3.53/0.99      ( r2_hidden(X0,sK6) != iProver_top
% 3.53/0.99      | r2_hidden(sK0(sK7,X1),sK6) = iProver_top
% 3.53/0.99      | r1_tarski(sK7,X1) = iProver_top ),
% 3.53/0.99      inference(superposition,[status(thm)],[c_598,c_1758]) ).
% 3.53/0.99  
% 3.53/0.99  cnf(c_9278,plain,
% 3.53/0.99      ( r2_hidden(sK0(sK7,X0),sK6) = iProver_top
% 3.53/0.99      | r1_tarski(sK7,X0) = iProver_top
% 3.53/0.99      | r1_tarski(sK6,X1) = iProver_top ),
% 3.53/0.99      inference(superposition,[status(thm)],[c_598,c_4779]) ).
% 3.53/0.99  
% 3.53/0.99  cnf(c_27,negated_conjecture,
% 3.53/0.99      ( k1_xboole_0 != sK6 ),
% 3.53/0.99      inference(cnf_transformation,[],[f59]) ).
% 3.53/0.99  
% 3.53/0.99  cnf(c_24,plain,
% 3.53/0.99      ( k2_zfmisc_1(X0,X1) != k1_xboole_0
% 3.53/0.99      | k1_xboole_0 = X1
% 3.53/0.99      | k1_xboole_0 = X0 ),
% 3.53/0.99      inference(cnf_transformation,[],[f55]) ).
% 3.53/0.99  
% 3.53/0.99  cnf(c_29,plain,
% 3.53/0.99      ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) != k1_xboole_0
% 3.53/0.99      | k1_xboole_0 = k1_xboole_0 ),
% 3.53/0.99      inference(instantiation,[status(thm)],[c_24]) ).
% 3.53/0.99  
% 3.53/0.99  cnf(c_23,plain,
% 3.53/0.99      ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
% 3.53/0.99      inference(cnf_transformation,[],[f70]) ).
% 3.53/0.99  
% 3.53/0.99  cnf(c_30,plain,
% 3.53/0.99      ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
% 3.53/0.99      inference(instantiation,[status(thm)],[c_23]) ).
% 3.53/0.99  
% 3.53/0.99  cnf(c_283,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 3.53/0.99  
% 3.53/0.99  cnf(c_791,plain,
% 3.53/0.99      ( sK6 != X0 | k1_xboole_0 != X0 | k1_xboole_0 = sK6 ),
% 3.53/0.99      inference(instantiation,[status(thm)],[c_283]) ).
% 3.53/0.99  
% 3.53/0.99  cnf(c_792,plain,
% 3.53/0.99      ( sK6 != k1_xboole_0
% 3.53/0.99      | k1_xboole_0 = sK6
% 3.53/0.99      | k1_xboole_0 != k1_xboole_0 ),
% 3.53/0.99      inference(instantiation,[status(thm)],[c_791]) ).
% 3.53/0.99  
% 3.53/0.99  cnf(c_13,plain,
% 3.53/0.99      ( r2_hidden(sK3(X0,X1,X2),X1)
% 3.53/0.99      | r2_hidden(sK1(X0,X1,X2),X2)
% 3.53/0.99      | k2_zfmisc_1(X0,X1) = X2 ),
% 3.53/0.99      inference(cnf_transformation,[],[f49]) ).
% 3.53/0.99  
% 3.53/0.99  cnf(c_588,plain,
% 3.53/0.99      ( k2_zfmisc_1(X0,X1) = X2
% 3.53/0.99      | r2_hidden(sK3(X0,X1,X2),X1) = iProver_top
% 3.53/0.99      | r2_hidden(sK1(X0,X1,X2),X2) = iProver_top ),
% 3.53/0.99      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 3.53/0.99  
% 3.53/0.99  cnf(c_10,plain,
% 3.53/0.99      ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
% 3.53/0.99      inference(cnf_transformation,[],[f43]) ).
% 3.53/0.99  
% 3.53/0.99  cnf(c_3,plain,
% 3.53/0.99      ( ~ r2_hidden(X0,X1)
% 3.53/0.99      | r2_hidden(X0,X2)
% 3.53/0.99      | r2_hidden(X0,k5_xboole_0(X2,X1)) ),
% 3.53/0.99      inference(cnf_transformation,[],[f39]) ).
% 3.53/0.99  
% 3.53/0.99  cnf(c_596,plain,
% 3.53/0.99      ( r2_hidden(X0,X1) != iProver_top
% 3.53/0.99      | r2_hidden(X0,X2) = iProver_top
% 3.53/0.99      | r2_hidden(X0,k5_xboole_0(X2,X1)) = iProver_top ),
% 3.53/0.99      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 3.53/0.99  
% 3.53/0.99  cnf(c_2707,plain,
% 3.53/0.99      ( r2_hidden(X0,X1) = iProver_top
% 3.53/0.99      | r2_hidden(X0,k1_xboole_0) != iProver_top ),
% 3.53/0.99      inference(superposition,[status(thm)],[c_10,c_596]) ).
% 3.53/0.99  
% 3.53/0.99  cnf(c_3000,plain,
% 3.53/0.99      ( k2_zfmisc_1(X0,k1_xboole_0) = X1
% 3.53/0.99      | r2_hidden(sK3(X0,k1_xboole_0,X1),X2) = iProver_top
% 3.53/0.99      | r2_hidden(sK1(X0,k1_xboole_0,X1),X1) = iProver_top ),
% 3.53/0.99      inference(superposition,[status(thm)],[c_588,c_2707]) ).
% 3.53/0.99  
% 3.53/0.99  cnf(c_22,plain,
% 3.53/0.99      ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
% 3.53/0.99      inference(cnf_transformation,[],[f69]) ).
% 3.53/0.99  
% 3.53/0.99  cnf(c_3004,plain,
% 3.53/0.99      ( k1_xboole_0 = X0
% 3.53/0.99      | r2_hidden(sK3(X1,k1_xboole_0,X0),X2) = iProver_top
% 3.53/0.99      | r2_hidden(sK1(X1,k1_xboole_0,X0),X0) = iProver_top ),
% 3.53/0.99      inference(demodulation,[status(thm)],[c_3000,c_22]) ).
% 3.53/0.99  
% 3.53/0.99  cnf(c_5,plain,
% 3.53/0.99      ( ~ r2_hidden(X0,X1)
% 3.53/0.99      | ~ r2_hidden(X0,X2)
% 3.53/0.99      | ~ r2_hidden(X0,k5_xboole_0(X1,X2)) ),
% 3.53/0.99      inference(cnf_transformation,[],[f37]) ).
% 3.53/0.99  
% 3.53/0.99  cnf(c_594,plain,
% 3.53/0.99      ( r2_hidden(X0,X1) != iProver_top
% 3.53/0.99      | r2_hidden(X0,X2) != iProver_top
% 3.53/0.99      | r2_hidden(X0,k5_xboole_0(X1,X2)) != iProver_top ),
% 3.53/0.99      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 3.53/0.99  
% 3.53/0.99  cnf(c_4351,plain,
% 3.53/0.99      ( r2_hidden(X0,X1) != iProver_top
% 3.53/0.99      | r2_hidden(X0,k1_xboole_0) != iProver_top ),
% 3.53/0.99      inference(superposition,[status(thm)],[c_10,c_594]) ).
% 3.53/0.99  
% 3.53/0.99  cnf(c_4572,plain,
% 3.53/0.99      ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
% 3.53/0.99      inference(global_propositional_subsumption,
% 3.53/0.99                [status(thm)],
% 3.53/0.99                [c_4351,c_2707]) ).
% 3.53/0.99  
% 3.53/0.99  cnf(c_4587,plain,
% 3.53/0.99      ( k1_xboole_0 = X0
% 3.53/0.99      | r2_hidden(sK1(X1,k1_xboole_0,X0),X0) = iProver_top ),
% 3.53/0.99      inference(superposition,[status(thm)],[c_3004,c_4572]) ).
% 3.53/0.99  
% 3.53/0.99  cnf(c_9299,plain,
% 3.53/0.99      ( sK6 = k1_xboole_0
% 3.53/0.99      | r2_hidden(sK0(sK7,X0),sK6) = iProver_top
% 3.53/0.99      | r1_tarski(sK7,X0) = iProver_top ),
% 3.53/0.99      inference(superposition,[status(thm)],[c_4587,c_4779]) ).
% 3.53/0.99  
% 3.53/0.99  cnf(c_9688,plain,
% 3.53/0.99      ( r1_tarski(sK7,X0) = iProver_top
% 3.53/0.99      | r2_hidden(sK0(sK7,X0),sK6) = iProver_top ),
% 3.53/0.99      inference(global_propositional_subsumption,
% 3.53/0.99                [status(thm)],
% 3.53/0.99                [c_9278,c_27,c_29,c_30,c_792,c_9299]) ).
% 3.53/0.99  
% 3.53/0.99  cnf(c_9689,plain,
% 3.53/0.99      ( r2_hidden(sK0(sK7,X0),sK6) = iProver_top
% 3.53/0.99      | r1_tarski(sK7,X0) = iProver_top ),
% 3.53/0.99      inference(renaming,[status(thm)],[c_9688]) ).
% 3.53/0.99  
% 3.53/0.99  cnf(c_0,plain,
% 3.53/0.99      ( ~ r2_hidden(sK0(X0,X1),X1) | r1_tarski(X0,X1) ),
% 3.53/0.99      inference(cnf_transformation,[],[f35]) ).
% 3.53/0.99  
% 3.53/0.99  cnf(c_599,plain,
% 3.53/0.99      ( r2_hidden(sK0(X0,X1),X1) != iProver_top
% 3.53/0.99      | r1_tarski(X0,X1) = iProver_top ),
% 3.53/0.99      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 3.53/0.99  
% 3.53/0.99  cnf(c_9696,plain,
% 3.53/0.99      ( r1_tarski(sK7,sK6) = iProver_top ),
% 3.53/0.99      inference(superposition,[status(thm)],[c_9689,c_599]) ).
% 3.53/0.99  
% 3.53/0.99  cnf(c_21,plain,
% 3.53/0.99      ( r2_hidden(X0,X1)
% 3.53/0.99      | ~ r2_hidden(k4_tarski(X0,X2),k2_zfmisc_1(X1,X3)) ),
% 3.53/0.99      inference(cnf_transformation,[],[f52]) ).
% 3.53/0.99  
% 3.53/0.99  cnf(c_580,plain,
% 3.53/0.99      ( r2_hidden(X0,X1) = iProver_top
% 3.53/0.99      | r2_hidden(k4_tarski(X0,X2),k2_zfmisc_1(X1,X3)) != iProver_top ),
% 3.53/0.99      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 3.53/0.99  
% 3.53/0.99  cnf(c_987,plain,
% 3.53/0.99      ( r2_hidden(X0,sK7) = iProver_top
% 3.53/0.99      | r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(sK6,sK7)) != iProver_top ),
% 3.53/0.99      inference(superposition,[status(thm)],[c_28,c_580]) ).
% 3.53/0.99  
% 3.53/0.99  cnf(c_1763,plain,
% 3.53/0.99      ( r2_hidden(X0,sK7) != iProver_top
% 3.53/0.99      | r2_hidden(X1,sK7) = iProver_top
% 3.53/0.99      | r2_hidden(X1,sK6) != iProver_top ),
% 3.53/0.99      inference(superposition,[status(thm)],[c_582,c_987]) ).
% 3.53/0.99  
% 3.53/0.99  cnf(c_5740,plain,
% 3.53/0.99      ( r2_hidden(X0,sK7) = iProver_top
% 3.53/0.99      | r2_hidden(X0,sK6) != iProver_top
% 3.53/0.99      | r1_tarski(sK7,X1) = iProver_top ),
% 3.53/0.99      inference(superposition,[status(thm)],[c_598,c_1763]) ).
% 3.53/0.99  
% 3.53/0.99  cnf(c_26,negated_conjecture,
% 3.53/0.99      ( k1_xboole_0 != sK7 ),
% 3.53/0.99      inference(cnf_transformation,[],[f60]) ).
% 3.53/0.99  
% 3.53/0.99  cnf(c_789,plain,
% 3.53/0.99      ( sK7 != X0 | k1_xboole_0 != X0 | k1_xboole_0 = sK7 ),
% 3.53/0.99      inference(instantiation,[status(thm)],[c_283]) ).
% 3.53/0.99  
% 3.53/0.99  cnf(c_790,plain,
% 3.53/0.99      ( sK7 != k1_xboole_0
% 3.53/0.99      | k1_xboole_0 = sK7
% 3.53/0.99      | k1_xboole_0 != k1_xboole_0 ),
% 3.53/0.99      inference(instantiation,[status(thm)],[c_789]) ).
% 3.53/0.99  
% 3.53/0.99  cnf(c_14,plain,
% 3.53/0.99      ( r2_hidden(sK2(X0,X1,X2),X0)
% 3.53/0.99      | r2_hidden(sK1(X0,X1,X2),X2)
% 3.53/0.99      | k2_zfmisc_1(X0,X1) = X2 ),
% 3.53/0.99      inference(cnf_transformation,[],[f48]) ).
% 3.53/0.99  
% 3.53/0.99  cnf(c_587,plain,
% 3.53/0.99      ( k2_zfmisc_1(X0,X1) = X2
% 3.53/0.99      | r2_hidden(sK2(X0,X1,X2),X0) = iProver_top
% 3.53/0.99      | r2_hidden(sK1(X0,X1,X2),X2) = iProver_top ),
% 3.53/0.99      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 3.53/0.99  
% 3.53/0.99  cnf(c_2737,plain,
% 3.53/0.99      ( k2_zfmisc_1(k1_xboole_0,X0) = X1
% 3.53/0.99      | r2_hidden(sK2(k1_xboole_0,X0,X1),X2) = iProver_top
% 3.53/0.99      | r2_hidden(sK1(k1_xboole_0,X0,X1),X1) = iProver_top ),
% 3.53/0.99      inference(superposition,[status(thm)],[c_587,c_2707]) ).
% 3.53/0.99  
% 3.53/0.99  cnf(c_2753,plain,
% 3.53/0.99      ( k1_xboole_0 = X0
% 3.53/0.99      | r2_hidden(sK2(k1_xboole_0,X1,X0),X2) = iProver_top
% 3.53/0.99      | r2_hidden(sK1(k1_xboole_0,X1,X0),X0) = iProver_top ),
% 3.53/0.99      inference(demodulation,[status(thm)],[c_2737,c_23]) ).
% 3.53/0.99  
% 3.53/0.99  cnf(c_4585,plain,
% 3.53/0.99      ( k1_xboole_0 = X0
% 3.53/0.99      | r2_hidden(sK1(k1_xboole_0,X1,X0),X0) = iProver_top ),
% 3.53/0.99      inference(superposition,[status(thm)],[c_2753,c_4572]) ).
% 3.53/0.99  
% 3.53/0.99  cnf(c_6288,plain,
% 3.53/0.99      ( sK7 = k1_xboole_0
% 3.53/0.99      | r2_hidden(X0,sK7) = iProver_top
% 3.53/0.99      | r2_hidden(X0,sK6) != iProver_top ),
% 3.53/0.99      inference(superposition,[status(thm)],[c_4585,c_1763]) ).
% 3.53/0.99  
% 3.53/0.99  cnf(c_7549,plain,
% 3.53/0.99      ( r2_hidden(X0,sK6) != iProver_top
% 3.53/0.99      | r2_hidden(X0,sK7) = iProver_top ),
% 3.53/0.99      inference(global_propositional_subsumption,
% 3.53/0.99                [status(thm)],
% 3.53/0.99                [c_5740,c_26,c_29,c_30,c_790,c_6288]) ).
% 3.53/0.99  
% 3.53/0.99  cnf(c_7550,plain,
% 3.53/0.99      ( r2_hidden(X0,sK7) = iProver_top
% 3.53/0.99      | r2_hidden(X0,sK6) != iProver_top ),
% 3.53/0.99      inference(renaming,[status(thm)],[c_7549]) ).
% 3.53/0.99  
% 3.53/0.99  cnf(c_7557,plain,
% 3.53/0.99      ( r2_hidden(sK0(sK6,X0),sK7) = iProver_top
% 3.53/0.99      | r1_tarski(sK6,X0) = iProver_top ),
% 3.53/0.99      inference(superposition,[status(thm)],[c_598,c_7550]) ).
% 3.53/0.99  
% 3.53/0.99  cnf(c_7885,plain,
% 3.53/0.99      ( r1_tarski(sK6,sK7) = iProver_top ),
% 3.53/0.99      inference(superposition,[status(thm)],[c_7557,c_599]) ).
% 3.53/0.99  
% 3.53/0.99  cnf(c_7,plain,
% 3.53/0.99      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X1 = X0 ),
% 3.53/0.99      inference(cnf_transformation,[],[f42]) ).
% 3.53/0.99  
% 3.53/0.99  cnf(c_25,negated_conjecture,
% 3.53/0.99      ( sK6 != sK7 ),
% 3.53/0.99      inference(cnf_transformation,[],[f61]) ).
% 3.53/0.99  
% 3.53/0.99  cnf(c_1121,plain,
% 3.53/0.99      ( ~ r1_tarski(sK7,sK6) | ~ r1_tarski(sK6,sK7) ),
% 3.53/0.99      inference(resolution,[status(thm)],[c_7,c_25]) ).
% 3.53/0.99  
% 3.53/0.99  cnf(c_1122,plain,
% 3.53/0.99      ( r1_tarski(sK7,sK6) != iProver_top
% 3.53/0.99      | r1_tarski(sK6,sK7) != iProver_top ),
% 3.53/0.99      inference(predicate_to_equality,[status(thm)],[c_1121]) ).
% 3.53/0.99  
% 3.53/0.99  cnf(contradiction,plain,
% 3.53/0.99      ( $false ),
% 3.53/0.99      inference(minisat,[status(thm)],[c_9696,c_7885,c_1122]) ).
% 3.53/0.99  
% 3.53/0.99  
% 3.53/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 3.53/0.99  
% 3.53/0.99  ------                               Statistics
% 3.53/0.99  
% 3.53/0.99  ------ Selected
% 3.53/0.99  
% 3.53/0.99  total_time:                             0.34
% 3.53/0.99  
%------------------------------------------------------------------------------
