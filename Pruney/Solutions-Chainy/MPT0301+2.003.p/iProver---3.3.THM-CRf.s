%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:36:55 EST 2020

% Result     : Theorem 2.45s
% Output     : CNFRefutation 2.45s
% Verified   : 
% Statistics : Number of formulae       :   87 ( 613 expanded)
%              Number of clauses        :   42 ( 229 expanded)
%              Number of leaves         :   14 ( 150 expanded)
%              Depth                    :   21
%              Number of atoms          :  328 (2773 expanded)
%              Number of equality atoms :  162 (1021 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal clause size      :   18 (   2 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

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
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f14,plain,(
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
    inference(flattening,[],[f13])).

fof(f15,plain,(
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
    inference(rectify,[],[f14])).

fof(f16,plain,(
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

fof(f17,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f15,f16])).

fof(f32,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X0,X1) = X2
      | r2_hidden(sK0(X0,X1,X2),X0)
      | r2_hidden(sK0(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f3,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X2
      | r2_hidden(sK0(X0,X1,X2),X0)
      | r2_hidden(sK0(X0,X1,X2),X2) ) ),
    inference(definition_unfolding,[],[f32,f35])).

fof(f6,axiom,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f6])).

fof(f8,axiom,(
    ! [X0,X1] :
      ~ ( r2_hidden(X0,X1)
        & r1_xboole_0(k1_tarski(X0),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ r1_xboole_0(k1_tarski(X0),X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ r1_xboole_0(k1_tarski(X0),X1) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f4,axiom,(
    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f4])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f5,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f5])).

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

fof(f18,plain,(
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

fof(f19,plain,(
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
    inference(rectify,[],[f18])).

fof(f22,plain,(
    ! [X8,X1,X0] :
      ( ? [X11,X12] :
          ( k4_tarski(X11,X12) = X8
          & r2_hidden(X12,X1)
          & r2_hidden(X11,X0) )
     => ( k4_tarski(sK4(X0,X1,X8),sK5(X0,X1,X8)) = X8
        & r2_hidden(sK5(X0,X1,X8),X1)
        & r2_hidden(sK4(X0,X1,X8),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X6,X7] :
          ( k4_tarski(X6,X7) = X3
          & r2_hidden(X7,X1)
          & r2_hidden(X6,X0) )
     => ( k4_tarski(sK2(X0,X1,X2),sK3(X0,X1,X2)) = X3
        & r2_hidden(sK3(X0,X1,X2),X1)
        & r2_hidden(sK2(X0,X1,X2),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
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

fof(f23,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4,sK5])],[f19,f22,f21,f20])).

fof(f40,plain,(
    ! [X2,X0,X8,X1] :
      ( r2_hidden(sK5(X0,X1,X8),X1)
      | ~ r2_hidden(X8,X2)
      | k2_zfmisc_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f23])).

fof(f63,plain,(
    ! [X0,X8,X1] :
      ( r2_hidden(sK5(X0,X1,X8),X1)
      | ~ r2_hidden(X8,k2_zfmisc_1(X0,X1)) ) ),
    inference(equality_resolution,[],[f40])).

fof(f39,plain,(
    ! [X2,X0,X8,X1] :
      ( r2_hidden(sK4(X0,X1,X8),X0)
      | ~ r2_hidden(X8,X2)
      | k2_zfmisc_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f23])).

fof(f64,plain,(
    ! [X0,X8,X1] :
      ( r2_hidden(sK4(X0,X1,X8),X0)
      | ~ r2_hidden(X8,k2_zfmisc_1(X0,X1)) ) ),
    inference(equality_resolution,[],[f39])).

fof(f9,conjecture,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f10,negated_conjecture,(
    ~ ! [X0,X1] :
        ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      <=> ( k1_xboole_0 = X1
          | k1_xboole_0 = X0 ) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f12,plain,(
    ? [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <~> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f24,plain,(
    ? [X0,X1] :
      ( ( ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 )
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 = k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f12])).

fof(f25,plain,(
    ? [X0,X1] :
      ( ( ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 )
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 = k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f24])).

fof(f26,plain,
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

fof(f27,plain,
    ( ( ( k1_xboole_0 != sK7
        & k1_xboole_0 != sK6 )
      | k1_xboole_0 != k2_zfmisc_1(sK6,sK7) )
    & ( k1_xboole_0 = sK7
      | k1_xboole_0 = sK6
      | k1_xboole_0 = k2_zfmisc_1(sK6,sK7) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7])],[f25,f26])).

fof(f48,plain,
    ( k1_xboole_0 = sK7
    | k1_xboole_0 = sK6
    | k1_xboole_0 = k2_zfmisc_1(sK6,sK7) ),
    inference(cnf_transformation,[],[f27])).

fof(f42,plain,(
    ! [X2,X0,X10,X8,X1,X9] :
      ( r2_hidden(X8,X2)
      | k4_tarski(X9,X10) != X8
      | ~ r2_hidden(X10,X1)
      | ~ r2_hidden(X9,X0)
      | k2_zfmisc_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f23])).

fof(f60,plain,(
    ! [X2,X0,X10,X1,X9] :
      ( r2_hidden(k4_tarski(X9,X10),X2)
      | ~ r2_hidden(X10,X1)
      | ~ r2_hidden(X9,X0)
      | k2_zfmisc_1(X0,X1) != X2 ) ),
    inference(equality_resolution,[],[f42])).

fof(f61,plain,(
    ! [X0,X10,X1,X9] :
      ( r2_hidden(k4_tarski(X9,X10),k2_zfmisc_1(X0,X1))
      | ~ r2_hidden(X10,X1)
      | ~ r2_hidden(X9,X0) ) ),
    inference(equality_resolution,[],[f60])).

fof(f49,plain,
    ( k1_xboole_0 != sK6
    | k1_xboole_0 != k2_zfmisc_1(sK6,sK7) ),
    inference(cnf_transformation,[],[f27])).

fof(f50,plain,
    ( k1_xboole_0 != sK7
    | k1_xboole_0 != k2_zfmisc_1(sK6,sK7) ),
    inference(cnf_transformation,[],[f27])).

cnf(c_3,plain,
    ( r2_hidden(sK0(X0,X1,X2),X0)
    | r2_hidden(sK0(X0,X1,X2),X2)
    | k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X2 ),
    inference(cnf_transformation,[],[f53])).

cnf(c_567,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X2
    | r2_hidden(sK0(X0,X1,X2),X0) = iProver_top
    | r2_hidden(sK0(X0,X1,X2),X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_9,plain,
    ( r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_18,plain,
    ( ~ r1_xboole_0(k1_tarski(X0),X1)
    | ~ r2_hidden(X0,X1) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_194,plain,
    ( ~ r2_hidden(X0,X1)
    | k1_tarski(X0) != X2
    | k1_xboole_0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_18])).

cnf(c_195,plain,
    ( ~ r2_hidden(X0,k1_xboole_0) ),
    inference(unflattening,[status(thm)],[c_194])).

cnf(c_555,plain,
    ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_195])).

cnf(c_3342,plain,
    ( k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X0)) = X1
    | r2_hidden(sK0(k1_xboole_0,X0,X1),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_567,c_555])).

cnf(c_7,plain,
    ( k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f36])).

cnf(c_0,plain,
    ( k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f28])).

cnf(c_828,plain,
    ( k3_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_7,c_0])).

cnf(c_3494,plain,
    ( k5_xboole_0(k1_xboole_0,k1_xboole_0) = X0
    | r2_hidden(sK0(k1_xboole_0,X1,X0),X0) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3342,c_828])).

cnf(c_8,plain,
    ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f37])).

cnf(c_3495,plain,
    ( k1_xboole_0 = X0
    | r2_hidden(sK0(k1_xboole_0,X1,X0),X0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_3494,c_8])).

cnf(c_16,plain,
    ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
    | r2_hidden(sK5(X1,X2,X0),X2) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_557,plain,
    ( r2_hidden(X0,k2_zfmisc_1(X1,X2)) != iProver_top
    | r2_hidden(sK5(X1,X2,X0),X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_17,plain,
    ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
    | r2_hidden(sK4(X1,X2,X0),X1) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_556,plain,
    ( r2_hidden(X0,k2_zfmisc_1(X1,X2)) != iProver_top
    | r2_hidden(sK4(X1,X2,X0),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_874,plain,
    ( r2_hidden(X0,k2_zfmisc_1(k1_xboole_0,X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_556,c_555])).

cnf(c_1076,plain,
    ( r2_hidden(X0,k2_zfmisc_1(X1,k2_zfmisc_1(k1_xboole_0,X2))) != iProver_top ),
    inference(superposition,[status(thm)],[c_557,c_874])).

cnf(c_3776,plain,
    ( k2_zfmisc_1(X0,k2_zfmisc_1(k1_xboole_0,X1)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_3495,c_1076])).

cnf(c_1214,plain,
    ( r2_hidden(X0,k2_zfmisc_1(k2_zfmisc_1(X1,k2_zfmisc_1(k1_xboole_0,X2)),X3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_556,c_1076])).

cnf(c_3781,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(X0,k2_zfmisc_1(k1_xboole_0,X1)),X2) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_3495,c_1214])).

cnf(c_3864,plain,
    ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_3776,c_3781])).

cnf(c_3867,plain,
    ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_3864,c_3776])).

cnf(c_21,negated_conjecture,
    ( k1_xboole_0 = k2_zfmisc_1(sK6,sK7)
    | k1_xboole_0 = sK6
    | k1_xboole_0 = sK7 ),
    inference(cnf_transformation,[],[f48])).

cnf(c_14,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X2,X3)
    | r2_hidden(k4_tarski(X2,X0),k2_zfmisc_1(X3,X1)) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_559,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X2,X3) != iProver_top
    | r2_hidden(k4_tarski(X2,X0),k2_zfmisc_1(X3,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_1678,plain,
    ( sK6 = k1_xboole_0
    | sK7 = k1_xboole_0
    | r2_hidden(X0,sK6) != iProver_top
    | r2_hidden(X1,sK7) != iProver_top
    | r2_hidden(k4_tarski(X0,X1),k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_21,c_559])).

cnf(c_1903,plain,
    ( sK6 = k1_xboole_0
    | sK7 = k1_xboole_0
    | r2_hidden(X0,sK6) != iProver_top
    | r2_hidden(X1,sK7) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_1678,c_555])).

cnf(c_3782,plain,
    ( sK6 = k1_xboole_0
    | sK7 = k1_xboole_0
    | r2_hidden(X0,sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_3495,c_1903])).

cnf(c_4060,plain,
    ( sK6 = k1_xboole_0
    | sK7 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_3495,c_3782])).

cnf(c_20,negated_conjecture,
    ( k1_xboole_0 != k2_zfmisc_1(sK6,sK7)
    | k1_xboole_0 != sK6 ),
    inference(cnf_transformation,[],[f49])).

cnf(c_4201,plain,
    ( k2_zfmisc_1(k1_xboole_0,sK7) != k1_xboole_0
    | sK6 != k1_xboole_0
    | sK7 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_4060,c_20])).

cnf(c_4206,plain,
    ( k2_zfmisc_1(k1_xboole_0,sK7) != k1_xboole_0
    | sK7 = k1_xboole_0 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_4201,c_4060])).

cnf(c_8324,plain,
    ( sK7 = k1_xboole_0
    | k1_xboole_0 != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_3864,c_4206])).

cnf(c_8326,plain,
    ( sK7 = k1_xboole_0 ),
    inference(equality_resolution_simp,[status(thm)],[c_8324])).

cnf(c_19,negated_conjecture,
    ( k1_xboole_0 != k2_zfmisc_1(sK6,sK7)
    | k1_xboole_0 != sK7 ),
    inference(cnf_transformation,[],[f50])).

cnf(c_8388,plain,
    ( k2_zfmisc_1(sK6,k1_xboole_0) != k1_xboole_0
    | k1_xboole_0 != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_8326,c_19])).

cnf(c_8389,plain,
    ( k2_zfmisc_1(sK6,k1_xboole_0) != k1_xboole_0 ),
    inference(equality_resolution_simp,[status(thm)],[c_8388])).

cnf(c_8601,plain,
    ( k1_xboole_0 != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_3867,c_8389])).

cnf(c_8602,plain,
    ( $false ),
    inference(equality_resolution_simp,[status(thm)],[c_8601])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 19:15:38 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  % Running in FOF mode
% 2.45/1.04  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.45/1.04  
% 2.45/1.04  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.45/1.04  
% 2.45/1.04  ------  iProver source info
% 2.45/1.04  
% 2.45/1.04  git: date: 2020-06-30 10:37:57 +0100
% 2.45/1.04  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.45/1.04  git: non_committed_changes: false
% 2.45/1.04  git: last_make_outside_of_git: false
% 2.45/1.04  
% 2.45/1.04  ------ 
% 2.45/1.04  
% 2.45/1.04  ------ Input Options
% 2.45/1.04  
% 2.45/1.04  --out_options                           all
% 2.45/1.04  --tptp_safe_out                         true
% 2.45/1.04  --problem_path                          ""
% 2.45/1.04  --include_path                          ""
% 2.45/1.04  --clausifier                            res/vclausify_rel
% 2.45/1.04  --clausifier_options                    --mode clausify
% 2.45/1.04  --stdin                                 false
% 2.45/1.04  --stats_out                             all
% 2.45/1.04  
% 2.45/1.04  ------ General Options
% 2.45/1.04  
% 2.45/1.04  --fof                                   false
% 2.45/1.04  --time_out_real                         305.
% 2.45/1.04  --time_out_virtual                      -1.
% 2.45/1.04  --symbol_type_check                     false
% 2.45/1.04  --clausify_out                          false
% 2.45/1.04  --sig_cnt_out                           false
% 2.45/1.04  --trig_cnt_out                          false
% 2.45/1.04  --trig_cnt_out_tolerance                1.
% 2.45/1.04  --trig_cnt_out_sk_spl                   false
% 2.45/1.04  --abstr_cl_out                          false
% 2.45/1.04  
% 2.45/1.04  ------ Global Options
% 2.45/1.04  
% 2.45/1.04  --schedule                              default
% 2.45/1.04  --add_important_lit                     false
% 2.45/1.04  --prop_solver_per_cl                    1000
% 2.45/1.04  --min_unsat_core                        false
% 2.45/1.04  --soft_assumptions                      false
% 2.45/1.04  --soft_lemma_size                       3
% 2.45/1.04  --prop_impl_unit_size                   0
% 2.45/1.04  --prop_impl_unit                        []
% 2.45/1.04  --share_sel_clauses                     true
% 2.45/1.04  --reset_solvers                         false
% 2.45/1.04  --bc_imp_inh                            [conj_cone]
% 2.45/1.04  --conj_cone_tolerance                   3.
% 2.45/1.04  --extra_neg_conj                        none
% 2.45/1.04  --large_theory_mode                     true
% 2.45/1.04  --prolific_symb_bound                   200
% 2.45/1.04  --lt_threshold                          2000
% 2.45/1.04  --clause_weak_htbl                      true
% 2.45/1.04  --gc_record_bc_elim                     false
% 2.45/1.04  
% 2.45/1.04  ------ Preprocessing Options
% 2.45/1.04  
% 2.45/1.04  --preprocessing_flag                    true
% 2.45/1.04  --time_out_prep_mult                    0.1
% 2.45/1.04  --splitting_mode                        input
% 2.45/1.04  --splitting_grd                         true
% 2.45/1.04  --splitting_cvd                         false
% 2.45/1.04  --splitting_cvd_svl                     false
% 2.45/1.04  --splitting_nvd                         32
% 2.45/1.04  --sub_typing                            true
% 2.45/1.04  --prep_gs_sim                           true
% 2.45/1.04  --prep_unflatten                        true
% 2.45/1.04  --prep_res_sim                          true
% 2.45/1.04  --prep_upred                            true
% 2.45/1.04  --prep_sem_filter                       exhaustive
% 2.45/1.04  --prep_sem_filter_out                   false
% 2.45/1.04  --pred_elim                             true
% 2.45/1.04  --res_sim_input                         true
% 2.45/1.04  --eq_ax_congr_red                       true
% 2.45/1.04  --pure_diseq_elim                       true
% 2.45/1.04  --brand_transform                       false
% 2.45/1.04  --non_eq_to_eq                          false
% 2.45/1.04  --prep_def_merge                        true
% 2.45/1.04  --prep_def_merge_prop_impl              false
% 2.45/1.04  --prep_def_merge_mbd                    true
% 2.45/1.04  --prep_def_merge_tr_red                 false
% 2.45/1.04  --prep_def_merge_tr_cl                  false
% 2.45/1.04  --smt_preprocessing                     true
% 2.45/1.04  --smt_ac_axioms                         fast
% 2.45/1.04  --preprocessed_out                      false
% 2.45/1.04  --preprocessed_stats                    false
% 2.45/1.04  
% 2.45/1.04  ------ Abstraction refinement Options
% 2.45/1.04  
% 2.45/1.04  --abstr_ref                             []
% 2.45/1.04  --abstr_ref_prep                        false
% 2.45/1.04  --abstr_ref_until_sat                   false
% 2.45/1.04  --abstr_ref_sig_restrict                funpre
% 2.45/1.04  --abstr_ref_af_restrict_to_split_sk     false
% 2.45/1.04  --abstr_ref_under                       []
% 2.45/1.04  
% 2.45/1.04  ------ SAT Options
% 2.45/1.04  
% 2.45/1.04  --sat_mode                              false
% 2.45/1.04  --sat_fm_restart_options                ""
% 2.45/1.04  --sat_gr_def                            false
% 2.45/1.04  --sat_epr_types                         true
% 2.45/1.04  --sat_non_cyclic_types                  false
% 2.45/1.04  --sat_finite_models                     false
% 2.45/1.04  --sat_fm_lemmas                         false
% 2.45/1.04  --sat_fm_prep                           false
% 2.45/1.04  --sat_fm_uc_incr                        true
% 2.45/1.04  --sat_out_model                         small
% 2.45/1.04  --sat_out_clauses                       false
% 2.45/1.04  
% 2.45/1.04  ------ QBF Options
% 2.45/1.04  
% 2.45/1.04  --qbf_mode                              false
% 2.45/1.04  --qbf_elim_univ                         false
% 2.45/1.04  --qbf_dom_inst                          none
% 2.45/1.04  --qbf_dom_pre_inst                      false
% 2.45/1.04  --qbf_sk_in                             false
% 2.45/1.04  --qbf_pred_elim                         true
% 2.45/1.04  --qbf_split                             512
% 2.45/1.04  
% 2.45/1.04  ------ BMC1 Options
% 2.45/1.04  
% 2.45/1.04  --bmc1_incremental                      false
% 2.45/1.04  --bmc1_axioms                           reachable_all
% 2.45/1.04  --bmc1_min_bound                        0
% 2.45/1.04  --bmc1_max_bound                        -1
% 2.45/1.04  --bmc1_max_bound_default                -1
% 2.45/1.04  --bmc1_symbol_reachability              true
% 2.45/1.04  --bmc1_property_lemmas                  false
% 2.45/1.04  --bmc1_k_induction                      false
% 2.45/1.04  --bmc1_non_equiv_states                 false
% 2.45/1.04  --bmc1_deadlock                         false
% 2.45/1.04  --bmc1_ucm                              false
% 2.45/1.04  --bmc1_add_unsat_core                   none
% 2.45/1.04  --bmc1_unsat_core_children              false
% 2.45/1.04  --bmc1_unsat_core_extrapolate_axioms    false
% 2.45/1.04  --bmc1_out_stat                         full
% 2.45/1.04  --bmc1_ground_init                      false
% 2.45/1.04  --bmc1_pre_inst_next_state              false
% 2.45/1.04  --bmc1_pre_inst_state                   false
% 2.45/1.04  --bmc1_pre_inst_reach_state             false
% 2.45/1.04  --bmc1_out_unsat_core                   false
% 2.45/1.04  --bmc1_aig_witness_out                  false
% 2.45/1.04  --bmc1_verbose                          false
% 2.45/1.04  --bmc1_dump_clauses_tptp                false
% 2.45/1.04  --bmc1_dump_unsat_core_tptp             false
% 2.45/1.04  --bmc1_dump_file                        -
% 2.45/1.04  --bmc1_ucm_expand_uc_limit              128
% 2.45/1.04  --bmc1_ucm_n_expand_iterations          6
% 2.45/1.04  --bmc1_ucm_extend_mode                  1
% 2.45/1.04  --bmc1_ucm_init_mode                    2
% 2.45/1.04  --bmc1_ucm_cone_mode                    none
% 2.45/1.04  --bmc1_ucm_reduced_relation_type        0
% 2.45/1.04  --bmc1_ucm_relax_model                  4
% 2.45/1.04  --bmc1_ucm_full_tr_after_sat            true
% 2.45/1.04  --bmc1_ucm_expand_neg_assumptions       false
% 2.45/1.04  --bmc1_ucm_layered_model                none
% 2.45/1.04  --bmc1_ucm_max_lemma_size               10
% 2.45/1.04  
% 2.45/1.04  ------ AIG Options
% 2.45/1.04  
% 2.45/1.04  --aig_mode                              false
% 2.45/1.04  
% 2.45/1.04  ------ Instantiation Options
% 2.45/1.04  
% 2.45/1.04  --instantiation_flag                    true
% 2.45/1.04  --inst_sos_flag                         false
% 2.45/1.04  --inst_sos_phase                        true
% 2.45/1.04  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.45/1.04  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.45/1.04  --inst_lit_sel_side                     num_symb
% 2.45/1.04  --inst_solver_per_active                1400
% 2.45/1.04  --inst_solver_calls_frac                1.
% 2.45/1.04  --inst_passive_queue_type               priority_queues
% 2.45/1.04  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.45/1.04  --inst_passive_queues_freq              [25;2]
% 2.45/1.04  --inst_dismatching                      true
% 2.45/1.04  --inst_eager_unprocessed_to_passive     true
% 2.45/1.04  --inst_prop_sim_given                   true
% 2.45/1.04  --inst_prop_sim_new                     false
% 2.45/1.04  --inst_subs_new                         false
% 2.45/1.04  --inst_eq_res_simp                      false
% 2.45/1.04  --inst_subs_given                       false
% 2.45/1.04  --inst_orphan_elimination               true
% 2.45/1.04  --inst_learning_loop_flag               true
% 2.45/1.04  --inst_learning_start                   3000
% 2.45/1.04  --inst_learning_factor                  2
% 2.45/1.04  --inst_start_prop_sim_after_learn       3
% 2.45/1.04  --inst_sel_renew                        solver
% 2.45/1.04  --inst_lit_activity_flag                true
% 2.45/1.04  --inst_restr_to_given                   false
% 2.45/1.04  --inst_activity_threshold               500
% 2.45/1.04  --inst_out_proof                        true
% 2.45/1.04  
% 2.45/1.04  ------ Resolution Options
% 2.45/1.04  
% 2.45/1.04  --resolution_flag                       true
% 2.45/1.04  --res_lit_sel                           adaptive
% 2.45/1.04  --res_lit_sel_side                      none
% 2.45/1.04  --res_ordering                          kbo
% 2.45/1.04  --res_to_prop_solver                    active
% 2.45/1.04  --res_prop_simpl_new                    false
% 2.45/1.04  --res_prop_simpl_given                  true
% 2.45/1.04  --res_passive_queue_type                priority_queues
% 2.45/1.04  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.45/1.04  --res_passive_queues_freq               [15;5]
% 2.45/1.04  --res_forward_subs                      full
% 2.45/1.04  --res_backward_subs                     full
% 2.45/1.04  --res_forward_subs_resolution           true
% 2.45/1.04  --res_backward_subs_resolution          true
% 2.45/1.04  --res_orphan_elimination                true
% 2.45/1.04  --res_time_limit                        2.
% 2.45/1.04  --res_out_proof                         true
% 2.45/1.04  
% 2.45/1.04  ------ Superposition Options
% 2.45/1.04  
% 2.45/1.04  --superposition_flag                    true
% 2.45/1.04  --sup_passive_queue_type                priority_queues
% 2.45/1.04  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.45/1.04  --sup_passive_queues_freq               [8;1;4]
% 2.45/1.04  --demod_completeness_check              fast
% 2.45/1.04  --demod_use_ground                      true
% 2.45/1.04  --sup_to_prop_solver                    passive
% 2.45/1.04  --sup_prop_simpl_new                    true
% 2.45/1.04  --sup_prop_simpl_given                  true
% 2.45/1.04  --sup_fun_splitting                     false
% 2.45/1.04  --sup_smt_interval                      50000
% 2.45/1.04  
% 2.45/1.04  ------ Superposition Simplification Setup
% 2.45/1.04  
% 2.45/1.04  --sup_indices_passive                   []
% 2.45/1.04  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.45/1.04  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.45/1.04  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.45/1.04  --sup_full_triv                         [TrivRules;PropSubs]
% 2.45/1.04  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.45/1.04  --sup_full_bw                           [BwDemod]
% 2.45/1.04  --sup_immed_triv                        [TrivRules]
% 2.45/1.04  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.45/1.04  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.45/1.04  --sup_immed_bw_main                     []
% 2.45/1.04  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.45/1.04  --sup_input_triv                        [Unflattening;TrivRules]
% 2.45/1.04  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.45/1.04  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.45/1.04  
% 2.45/1.04  ------ Combination Options
% 2.45/1.04  
% 2.45/1.04  --comb_res_mult                         3
% 2.45/1.04  --comb_sup_mult                         2
% 2.45/1.04  --comb_inst_mult                        10
% 2.45/1.04  
% 2.45/1.04  ------ Debug Options
% 2.45/1.04  
% 2.45/1.04  --dbg_backtrace                         false
% 2.45/1.04  --dbg_dump_prop_clauses                 false
% 2.45/1.04  --dbg_dump_prop_clauses_file            -
% 2.45/1.04  --dbg_out_stat                          false
% 2.45/1.04  ------ Parsing...
% 2.45/1.04  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.45/1.04  
% 2.45/1.04  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 2.45/1.04  
% 2.45/1.04  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.45/1.04  
% 2.45/1.04  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.45/1.04  ------ Proving...
% 2.45/1.04  ------ Problem Properties 
% 2.45/1.04  
% 2.45/1.04  
% 2.45/1.04  clauses                                 21
% 2.45/1.04  conjectures                             3
% 2.45/1.04  EPR                                     1
% 2.45/1.04  Horn                                    13
% 2.45/1.04  unary                                   4
% 2.45/1.04  binary                                  7
% 2.45/1.04  lits                                    51
% 2.45/1.04  lits eq                                 20
% 2.45/1.04  fd_pure                                 0
% 2.45/1.04  fd_pseudo                               0
% 2.45/1.04  fd_cond                                 0
% 2.45/1.04  fd_pseudo_cond                          7
% 2.45/1.04  AC symbols                              0
% 2.45/1.04  
% 2.45/1.04  ------ Schedule dynamic 5 is on 
% 2.45/1.04  
% 2.45/1.04  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.45/1.04  
% 2.45/1.04  
% 2.45/1.04  ------ 
% 2.45/1.04  Current options:
% 2.45/1.04  ------ 
% 2.45/1.04  
% 2.45/1.04  ------ Input Options
% 2.45/1.04  
% 2.45/1.04  --out_options                           all
% 2.45/1.04  --tptp_safe_out                         true
% 2.45/1.04  --problem_path                          ""
% 2.45/1.04  --include_path                          ""
% 2.45/1.04  --clausifier                            res/vclausify_rel
% 2.45/1.04  --clausifier_options                    --mode clausify
% 2.45/1.04  --stdin                                 false
% 2.45/1.04  --stats_out                             all
% 2.45/1.04  
% 2.45/1.04  ------ General Options
% 2.45/1.04  
% 2.45/1.04  --fof                                   false
% 2.45/1.04  --time_out_real                         305.
% 2.45/1.04  --time_out_virtual                      -1.
% 2.45/1.04  --symbol_type_check                     false
% 2.45/1.04  --clausify_out                          false
% 2.45/1.04  --sig_cnt_out                           false
% 2.45/1.04  --trig_cnt_out                          false
% 2.45/1.04  --trig_cnt_out_tolerance                1.
% 2.45/1.04  --trig_cnt_out_sk_spl                   false
% 2.45/1.04  --abstr_cl_out                          false
% 2.45/1.04  
% 2.45/1.04  ------ Global Options
% 2.45/1.04  
% 2.45/1.04  --schedule                              default
% 2.45/1.04  --add_important_lit                     false
% 2.45/1.04  --prop_solver_per_cl                    1000
% 2.45/1.04  --min_unsat_core                        false
% 2.45/1.04  --soft_assumptions                      false
% 2.45/1.04  --soft_lemma_size                       3
% 2.45/1.04  --prop_impl_unit_size                   0
% 2.45/1.04  --prop_impl_unit                        []
% 2.45/1.04  --share_sel_clauses                     true
% 2.45/1.04  --reset_solvers                         false
% 2.45/1.04  --bc_imp_inh                            [conj_cone]
% 2.45/1.04  --conj_cone_tolerance                   3.
% 2.45/1.04  --extra_neg_conj                        none
% 2.45/1.04  --large_theory_mode                     true
% 2.45/1.04  --prolific_symb_bound                   200
% 2.45/1.04  --lt_threshold                          2000
% 2.45/1.04  --clause_weak_htbl                      true
% 2.45/1.04  --gc_record_bc_elim                     false
% 2.45/1.04  
% 2.45/1.04  ------ Preprocessing Options
% 2.45/1.04  
% 2.45/1.04  --preprocessing_flag                    true
% 2.45/1.04  --time_out_prep_mult                    0.1
% 2.45/1.04  --splitting_mode                        input
% 2.45/1.04  --splitting_grd                         true
% 2.45/1.04  --splitting_cvd                         false
% 2.45/1.04  --splitting_cvd_svl                     false
% 2.45/1.04  --splitting_nvd                         32
% 2.45/1.04  --sub_typing                            true
% 2.45/1.04  --prep_gs_sim                           true
% 2.45/1.04  --prep_unflatten                        true
% 2.45/1.04  --prep_res_sim                          true
% 2.45/1.04  --prep_upred                            true
% 2.45/1.04  --prep_sem_filter                       exhaustive
% 2.45/1.04  --prep_sem_filter_out                   false
% 2.45/1.04  --pred_elim                             true
% 2.45/1.04  --res_sim_input                         true
% 2.45/1.04  --eq_ax_congr_red                       true
% 2.45/1.04  --pure_diseq_elim                       true
% 2.45/1.04  --brand_transform                       false
% 2.45/1.04  --non_eq_to_eq                          false
% 2.45/1.04  --prep_def_merge                        true
% 2.45/1.04  --prep_def_merge_prop_impl              false
% 2.45/1.04  --prep_def_merge_mbd                    true
% 2.45/1.04  --prep_def_merge_tr_red                 false
% 2.45/1.04  --prep_def_merge_tr_cl                  false
% 2.45/1.04  --smt_preprocessing                     true
% 2.45/1.04  --smt_ac_axioms                         fast
% 2.45/1.04  --preprocessed_out                      false
% 2.45/1.04  --preprocessed_stats                    false
% 2.45/1.04  
% 2.45/1.04  ------ Abstraction refinement Options
% 2.45/1.04  
% 2.45/1.04  --abstr_ref                             []
% 2.45/1.04  --abstr_ref_prep                        false
% 2.45/1.04  --abstr_ref_until_sat                   false
% 2.45/1.04  --abstr_ref_sig_restrict                funpre
% 2.45/1.04  --abstr_ref_af_restrict_to_split_sk     false
% 2.45/1.04  --abstr_ref_under                       []
% 2.45/1.04  
% 2.45/1.04  ------ SAT Options
% 2.45/1.04  
% 2.45/1.04  --sat_mode                              false
% 2.45/1.04  --sat_fm_restart_options                ""
% 2.45/1.04  --sat_gr_def                            false
% 2.45/1.04  --sat_epr_types                         true
% 2.45/1.04  --sat_non_cyclic_types                  false
% 2.45/1.04  --sat_finite_models                     false
% 2.45/1.04  --sat_fm_lemmas                         false
% 2.45/1.04  --sat_fm_prep                           false
% 2.45/1.04  --sat_fm_uc_incr                        true
% 2.45/1.04  --sat_out_model                         small
% 2.45/1.04  --sat_out_clauses                       false
% 2.45/1.04  
% 2.45/1.04  ------ QBF Options
% 2.45/1.04  
% 2.45/1.04  --qbf_mode                              false
% 2.45/1.04  --qbf_elim_univ                         false
% 2.45/1.04  --qbf_dom_inst                          none
% 2.45/1.04  --qbf_dom_pre_inst                      false
% 2.45/1.04  --qbf_sk_in                             false
% 2.45/1.04  --qbf_pred_elim                         true
% 2.45/1.04  --qbf_split                             512
% 2.45/1.04  
% 2.45/1.04  ------ BMC1 Options
% 2.45/1.04  
% 2.45/1.04  --bmc1_incremental                      false
% 2.45/1.04  --bmc1_axioms                           reachable_all
% 2.45/1.04  --bmc1_min_bound                        0
% 2.45/1.04  --bmc1_max_bound                        -1
% 2.45/1.04  --bmc1_max_bound_default                -1
% 2.45/1.04  --bmc1_symbol_reachability              true
% 2.45/1.04  --bmc1_property_lemmas                  false
% 2.45/1.04  --bmc1_k_induction                      false
% 2.45/1.04  --bmc1_non_equiv_states                 false
% 2.45/1.04  --bmc1_deadlock                         false
% 2.45/1.04  --bmc1_ucm                              false
% 2.45/1.04  --bmc1_add_unsat_core                   none
% 2.45/1.04  --bmc1_unsat_core_children              false
% 2.45/1.04  --bmc1_unsat_core_extrapolate_axioms    false
% 2.45/1.04  --bmc1_out_stat                         full
% 2.45/1.04  --bmc1_ground_init                      false
% 2.45/1.04  --bmc1_pre_inst_next_state              false
% 2.45/1.04  --bmc1_pre_inst_state                   false
% 2.45/1.04  --bmc1_pre_inst_reach_state             false
% 2.45/1.04  --bmc1_out_unsat_core                   false
% 2.45/1.04  --bmc1_aig_witness_out                  false
% 2.45/1.04  --bmc1_verbose                          false
% 2.45/1.04  --bmc1_dump_clauses_tptp                false
% 2.45/1.04  --bmc1_dump_unsat_core_tptp             false
% 2.45/1.04  --bmc1_dump_file                        -
% 2.45/1.04  --bmc1_ucm_expand_uc_limit              128
% 2.45/1.04  --bmc1_ucm_n_expand_iterations          6
% 2.45/1.04  --bmc1_ucm_extend_mode                  1
% 2.45/1.04  --bmc1_ucm_init_mode                    2
% 2.45/1.04  --bmc1_ucm_cone_mode                    none
% 2.45/1.04  --bmc1_ucm_reduced_relation_type        0
% 2.45/1.04  --bmc1_ucm_relax_model                  4
% 2.45/1.04  --bmc1_ucm_full_tr_after_sat            true
% 2.45/1.04  --bmc1_ucm_expand_neg_assumptions       false
% 2.45/1.04  --bmc1_ucm_layered_model                none
% 2.45/1.04  --bmc1_ucm_max_lemma_size               10
% 2.45/1.04  
% 2.45/1.04  ------ AIG Options
% 2.45/1.04  
% 2.45/1.04  --aig_mode                              false
% 2.45/1.04  
% 2.45/1.04  ------ Instantiation Options
% 2.45/1.04  
% 2.45/1.04  --instantiation_flag                    true
% 2.45/1.04  --inst_sos_flag                         false
% 2.45/1.04  --inst_sos_phase                        true
% 2.45/1.04  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.45/1.04  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.45/1.04  --inst_lit_sel_side                     none
% 2.45/1.04  --inst_solver_per_active                1400
% 2.45/1.04  --inst_solver_calls_frac                1.
% 2.45/1.04  --inst_passive_queue_type               priority_queues
% 2.45/1.04  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.45/1.04  --inst_passive_queues_freq              [25;2]
% 2.45/1.04  --inst_dismatching                      true
% 2.45/1.04  --inst_eager_unprocessed_to_passive     true
% 2.45/1.04  --inst_prop_sim_given                   true
% 2.45/1.04  --inst_prop_sim_new                     false
% 2.45/1.04  --inst_subs_new                         false
% 2.45/1.04  --inst_eq_res_simp                      false
% 2.45/1.04  --inst_subs_given                       false
% 2.45/1.04  --inst_orphan_elimination               true
% 2.45/1.04  --inst_learning_loop_flag               true
% 2.45/1.04  --inst_learning_start                   3000
% 2.45/1.04  --inst_learning_factor                  2
% 2.45/1.04  --inst_start_prop_sim_after_learn       3
% 2.45/1.04  --inst_sel_renew                        solver
% 2.45/1.04  --inst_lit_activity_flag                true
% 2.45/1.04  --inst_restr_to_given                   false
% 2.45/1.04  --inst_activity_threshold               500
% 2.45/1.04  --inst_out_proof                        true
% 2.45/1.04  
% 2.45/1.04  ------ Resolution Options
% 2.45/1.04  
% 2.45/1.04  --resolution_flag                       false
% 2.45/1.04  --res_lit_sel                           adaptive
% 2.45/1.04  --res_lit_sel_side                      none
% 2.45/1.04  --res_ordering                          kbo
% 2.45/1.04  --res_to_prop_solver                    active
% 2.45/1.04  --res_prop_simpl_new                    false
% 2.45/1.04  --res_prop_simpl_given                  true
% 2.45/1.04  --res_passive_queue_type                priority_queues
% 2.45/1.04  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.45/1.04  --res_passive_queues_freq               [15;5]
% 2.45/1.04  --res_forward_subs                      full
% 2.45/1.04  --res_backward_subs                     full
% 2.45/1.04  --res_forward_subs_resolution           true
% 2.45/1.04  --res_backward_subs_resolution          true
% 2.45/1.04  --res_orphan_elimination                true
% 2.45/1.04  --res_time_limit                        2.
% 2.45/1.04  --res_out_proof                         true
% 2.45/1.04  
% 2.45/1.04  ------ Superposition Options
% 2.45/1.04  
% 2.45/1.04  --superposition_flag                    true
% 2.45/1.04  --sup_passive_queue_type                priority_queues
% 2.45/1.04  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.45/1.04  --sup_passive_queues_freq               [8;1;4]
% 2.45/1.04  --demod_completeness_check              fast
% 2.45/1.04  --demod_use_ground                      true
% 2.45/1.04  --sup_to_prop_solver                    passive
% 2.45/1.04  --sup_prop_simpl_new                    true
% 2.45/1.04  --sup_prop_simpl_given                  true
% 2.45/1.04  --sup_fun_splitting                     false
% 2.45/1.04  --sup_smt_interval                      50000
% 2.45/1.04  
% 2.45/1.04  ------ Superposition Simplification Setup
% 2.45/1.04  
% 2.45/1.04  --sup_indices_passive                   []
% 2.45/1.04  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.45/1.04  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.45/1.04  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.45/1.04  --sup_full_triv                         [TrivRules;PropSubs]
% 2.45/1.04  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.45/1.04  --sup_full_bw                           [BwDemod]
% 2.45/1.04  --sup_immed_triv                        [TrivRules]
% 2.45/1.04  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.45/1.04  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.45/1.04  --sup_immed_bw_main                     []
% 2.45/1.04  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.45/1.04  --sup_input_triv                        [Unflattening;TrivRules]
% 2.45/1.04  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.45/1.04  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.45/1.04  
% 2.45/1.04  ------ Combination Options
% 2.45/1.04  
% 2.45/1.04  --comb_res_mult                         3
% 2.45/1.04  --comb_sup_mult                         2
% 2.45/1.04  --comb_inst_mult                        10
% 2.45/1.04  
% 2.45/1.04  ------ Debug Options
% 2.45/1.04  
% 2.45/1.04  --dbg_backtrace                         false
% 2.45/1.04  --dbg_dump_prop_clauses                 false
% 2.45/1.04  --dbg_dump_prop_clauses_file            -
% 2.45/1.04  --dbg_out_stat                          false
% 2.45/1.04  
% 2.45/1.04  
% 2.45/1.04  
% 2.45/1.04  
% 2.45/1.04  ------ Proving...
% 2.45/1.04  
% 2.45/1.04  
% 2.45/1.04  % SZS status Theorem for theBenchmark.p
% 2.45/1.04  
% 2.45/1.04   Resolution empty clause
% 2.45/1.04  
% 2.45/1.04  % SZS output start CNFRefutation for theBenchmark.p
% 2.45/1.04  
% 2.45/1.04  fof(f2,axiom,(
% 2.45/1.04    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 2.45/1.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.45/1.04  
% 2.45/1.04  fof(f13,plain,(
% 2.45/1.04    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : (((r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 2.45/1.04    inference(nnf_transformation,[],[f2])).
% 2.45/1.04  
% 2.45/1.04  fof(f14,plain,(
% 2.45/1.04    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 2.45/1.04    inference(flattening,[],[f13])).
% 2.45/1.04  
% 2.45/1.04  fof(f15,plain,(
% 2.45/1.04    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 2.45/1.04    inference(rectify,[],[f14])).
% 2.45/1.04  
% 2.45/1.04  fof(f16,plain,(
% 2.45/1.04    ! [X2,X1,X0] : (? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((r2_hidden(sK0(X0,X1,X2),X1) | ~r2_hidden(sK0(X0,X1,X2),X0) | ~r2_hidden(sK0(X0,X1,X2),X2)) & ((~r2_hidden(sK0(X0,X1,X2),X1) & r2_hidden(sK0(X0,X1,X2),X0)) | r2_hidden(sK0(X0,X1,X2),X2))))),
% 2.45/1.04    introduced(choice_axiom,[])).
% 2.45/1.04  
% 2.45/1.04  fof(f17,plain,(
% 2.45/1.04    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ((r2_hidden(sK0(X0,X1,X2),X1) | ~r2_hidden(sK0(X0,X1,X2),X0) | ~r2_hidden(sK0(X0,X1,X2),X2)) & ((~r2_hidden(sK0(X0,X1,X2),X1) & r2_hidden(sK0(X0,X1,X2),X0)) | r2_hidden(sK0(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 2.45/1.04    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f15,f16])).
% 2.45/1.04  
% 2.45/1.04  fof(f32,plain,(
% 2.45/1.04    ( ! [X2,X0,X1] : (k4_xboole_0(X0,X1) = X2 | r2_hidden(sK0(X0,X1,X2),X0) | r2_hidden(sK0(X0,X1,X2),X2)) )),
% 2.45/1.04    inference(cnf_transformation,[],[f17])).
% 2.45/1.04  
% 2.45/1.04  fof(f3,axiom,(
% 2.45/1.04    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 2.45/1.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.45/1.04  
% 2.45/1.04  fof(f35,plain,(
% 2.45/1.04    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 2.45/1.04    inference(cnf_transformation,[],[f3])).
% 2.45/1.04  
% 2.45/1.04  fof(f53,plain,(
% 2.45/1.04    ( ! [X2,X0,X1] : (k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X2 | r2_hidden(sK0(X0,X1,X2),X0) | r2_hidden(sK0(X0,X1,X2),X2)) )),
% 2.45/1.04    inference(definition_unfolding,[],[f32,f35])).
% 2.45/1.04  
% 2.45/1.04  fof(f6,axiom,(
% 2.45/1.04    ! [X0] : r1_xboole_0(X0,k1_xboole_0)),
% 2.45/1.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.45/1.04  
% 2.45/1.04  fof(f38,plain,(
% 2.45/1.04    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) )),
% 2.45/1.04    inference(cnf_transformation,[],[f6])).
% 2.45/1.04  
% 2.45/1.04  fof(f8,axiom,(
% 2.45/1.04    ! [X0,X1] : ~(r2_hidden(X0,X1) & r1_xboole_0(k1_tarski(X0),X1))),
% 2.45/1.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.45/1.04  
% 2.45/1.04  fof(f11,plain,(
% 2.45/1.04    ! [X0,X1] : (~r2_hidden(X0,X1) | ~r1_xboole_0(k1_tarski(X0),X1))),
% 2.45/1.04    inference(ennf_transformation,[],[f8])).
% 2.45/1.04  
% 2.45/1.04  fof(f47,plain,(
% 2.45/1.04    ( ! [X0,X1] : (~r2_hidden(X0,X1) | ~r1_xboole_0(k1_tarski(X0),X1)) )),
% 2.45/1.04    inference(cnf_transformation,[],[f11])).
% 2.45/1.04  
% 2.45/1.04  fof(f4,axiom,(
% 2.45/1.04    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0),
% 2.45/1.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.45/1.04  
% 2.45/1.04  fof(f36,plain,(
% 2.45/1.04    ( ! [X0] : (k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0) )),
% 2.45/1.04    inference(cnf_transformation,[],[f4])).
% 2.45/1.04  
% 2.45/1.04  fof(f1,axiom,(
% 2.45/1.04    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 2.45/1.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.45/1.04  
% 2.45/1.04  fof(f28,plain,(
% 2.45/1.04    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 2.45/1.04    inference(cnf_transformation,[],[f1])).
% 2.45/1.04  
% 2.45/1.04  fof(f5,axiom,(
% 2.45/1.04    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 2.45/1.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.45/1.04  
% 2.45/1.04  fof(f37,plain,(
% 2.45/1.04    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 2.45/1.04    inference(cnf_transformation,[],[f5])).
% 2.45/1.04  
% 2.45/1.04  fof(f7,axiom,(
% 2.45/1.04    ! [X0,X1,X2] : (k2_zfmisc_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4,X5] : (k4_tarski(X4,X5) = X3 & r2_hidden(X5,X1) & r2_hidden(X4,X0))))),
% 2.45/1.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.45/1.04  
% 2.45/1.04  fof(f18,plain,(
% 2.45/1.04    ! [X0,X1,X2] : ((k2_zfmisc_1(X0,X1) = X2 | ? [X3] : ((! [X4,X5] : (k4_tarski(X4,X5) != X3 | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X0)) | ~r2_hidden(X3,X2)) & (? [X4,X5] : (k4_tarski(X4,X5) = X3 & r2_hidden(X5,X1) & r2_hidden(X4,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ! [X4,X5] : (k4_tarski(X4,X5) != X3 | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X0))) & (? [X4,X5] : (k4_tarski(X4,X5) = X3 & r2_hidden(X5,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X3,X2))) | k2_zfmisc_1(X0,X1) != X2))),
% 2.45/1.04    inference(nnf_transformation,[],[f7])).
% 2.45/1.04  
% 2.45/1.04  fof(f19,plain,(
% 2.45/1.04    ! [X0,X1,X2] : ((k2_zfmisc_1(X0,X1) = X2 | ? [X3] : ((! [X4,X5] : (k4_tarski(X4,X5) != X3 | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X0)) | ~r2_hidden(X3,X2)) & (? [X6,X7] : (k4_tarski(X6,X7) = X3 & r2_hidden(X7,X1) & r2_hidden(X6,X0)) | r2_hidden(X3,X2)))) & (! [X8] : ((r2_hidden(X8,X2) | ! [X9,X10] : (k4_tarski(X9,X10) != X8 | ~r2_hidden(X10,X1) | ~r2_hidden(X9,X0))) & (? [X11,X12] : (k4_tarski(X11,X12) = X8 & r2_hidden(X12,X1) & r2_hidden(X11,X0)) | ~r2_hidden(X8,X2))) | k2_zfmisc_1(X0,X1) != X2))),
% 2.45/1.04    inference(rectify,[],[f18])).
% 2.45/1.04  
% 2.45/1.04  fof(f22,plain,(
% 2.45/1.04    ! [X8,X1,X0] : (? [X11,X12] : (k4_tarski(X11,X12) = X8 & r2_hidden(X12,X1) & r2_hidden(X11,X0)) => (k4_tarski(sK4(X0,X1,X8),sK5(X0,X1,X8)) = X8 & r2_hidden(sK5(X0,X1,X8),X1) & r2_hidden(sK4(X0,X1,X8),X0)))),
% 2.45/1.04    introduced(choice_axiom,[])).
% 2.45/1.04  
% 2.45/1.04  fof(f21,plain,(
% 2.45/1.04    ( ! [X3] : (! [X2,X1,X0] : (? [X6,X7] : (k4_tarski(X6,X7) = X3 & r2_hidden(X7,X1) & r2_hidden(X6,X0)) => (k4_tarski(sK2(X0,X1,X2),sK3(X0,X1,X2)) = X3 & r2_hidden(sK3(X0,X1,X2),X1) & r2_hidden(sK2(X0,X1,X2),X0)))) )),
% 2.45/1.04    introduced(choice_axiom,[])).
% 2.45/1.04  
% 2.45/1.04  fof(f20,plain,(
% 2.45/1.04    ! [X2,X1,X0] : (? [X3] : ((! [X4,X5] : (k4_tarski(X4,X5) != X3 | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X0)) | ~r2_hidden(X3,X2)) & (? [X6,X7] : (k4_tarski(X6,X7) = X3 & r2_hidden(X7,X1) & r2_hidden(X6,X0)) | r2_hidden(X3,X2))) => ((! [X5,X4] : (k4_tarski(X4,X5) != sK1(X0,X1,X2) | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X0)) | ~r2_hidden(sK1(X0,X1,X2),X2)) & (? [X7,X6] : (k4_tarski(X6,X7) = sK1(X0,X1,X2) & r2_hidden(X7,X1) & r2_hidden(X6,X0)) | r2_hidden(sK1(X0,X1,X2),X2))))),
% 2.45/1.04    introduced(choice_axiom,[])).
% 2.45/1.04  
% 2.45/1.04  fof(f23,plain,(
% 2.45/1.04    ! [X0,X1,X2] : ((k2_zfmisc_1(X0,X1) = X2 | ((! [X4,X5] : (k4_tarski(X4,X5) != sK1(X0,X1,X2) | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X0)) | ~r2_hidden(sK1(X0,X1,X2),X2)) & ((k4_tarski(sK2(X0,X1,X2),sK3(X0,X1,X2)) = sK1(X0,X1,X2) & r2_hidden(sK3(X0,X1,X2),X1) & r2_hidden(sK2(X0,X1,X2),X0)) | r2_hidden(sK1(X0,X1,X2),X2)))) & (! [X8] : ((r2_hidden(X8,X2) | ! [X9,X10] : (k4_tarski(X9,X10) != X8 | ~r2_hidden(X10,X1) | ~r2_hidden(X9,X0))) & ((k4_tarski(sK4(X0,X1,X8),sK5(X0,X1,X8)) = X8 & r2_hidden(sK5(X0,X1,X8),X1) & r2_hidden(sK4(X0,X1,X8),X0)) | ~r2_hidden(X8,X2))) | k2_zfmisc_1(X0,X1) != X2))),
% 2.45/1.04    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4,sK5])],[f19,f22,f21,f20])).
% 2.45/1.04  
% 2.45/1.04  fof(f40,plain,(
% 2.45/1.04    ( ! [X2,X0,X8,X1] : (r2_hidden(sK5(X0,X1,X8),X1) | ~r2_hidden(X8,X2) | k2_zfmisc_1(X0,X1) != X2) )),
% 2.45/1.04    inference(cnf_transformation,[],[f23])).
% 2.45/1.04  
% 2.45/1.04  fof(f63,plain,(
% 2.45/1.04    ( ! [X0,X8,X1] : (r2_hidden(sK5(X0,X1,X8),X1) | ~r2_hidden(X8,k2_zfmisc_1(X0,X1))) )),
% 2.45/1.04    inference(equality_resolution,[],[f40])).
% 2.45/1.04  
% 2.45/1.04  fof(f39,plain,(
% 2.45/1.04    ( ! [X2,X0,X8,X1] : (r2_hidden(sK4(X0,X1,X8),X0) | ~r2_hidden(X8,X2) | k2_zfmisc_1(X0,X1) != X2) )),
% 2.45/1.04    inference(cnf_transformation,[],[f23])).
% 2.45/1.04  
% 2.45/1.04  fof(f64,plain,(
% 2.45/1.04    ( ! [X0,X8,X1] : (r2_hidden(sK4(X0,X1,X8),X0) | ~r2_hidden(X8,k2_zfmisc_1(X0,X1))) )),
% 2.45/1.04    inference(equality_resolution,[],[f39])).
% 2.45/1.04  
% 2.45/1.04  fof(f9,conjecture,(
% 2.45/1.04    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 2.45/1.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.45/1.04  
% 2.45/1.04  fof(f10,negated_conjecture,(
% 2.45/1.04    ~! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 2.45/1.04    inference(negated_conjecture,[],[f9])).
% 2.45/1.04  
% 2.45/1.04  fof(f12,plain,(
% 2.45/1.04    ? [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <~> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 2.45/1.04    inference(ennf_transformation,[],[f10])).
% 2.45/1.04  
% 2.45/1.04  fof(f24,plain,(
% 2.45/1.04    ? [X0,X1] : (((k1_xboole_0 != X1 & k1_xboole_0 != X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 = k2_zfmisc_1(X0,X1)))),
% 2.45/1.04    inference(nnf_transformation,[],[f12])).
% 2.45/1.04  
% 2.45/1.04  fof(f25,plain,(
% 2.45/1.04    ? [X0,X1] : (((k1_xboole_0 != X1 & k1_xboole_0 != X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 = k2_zfmisc_1(X0,X1)))),
% 2.45/1.04    inference(flattening,[],[f24])).
% 2.45/1.04  
% 2.45/1.04  fof(f26,plain,(
% 2.45/1.04    ? [X0,X1] : (((k1_xboole_0 != X1 & k1_xboole_0 != X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 = k2_zfmisc_1(X0,X1))) => (((k1_xboole_0 != sK7 & k1_xboole_0 != sK6) | k1_xboole_0 != k2_zfmisc_1(sK6,sK7)) & (k1_xboole_0 = sK7 | k1_xboole_0 = sK6 | k1_xboole_0 = k2_zfmisc_1(sK6,sK7)))),
% 2.45/1.04    introduced(choice_axiom,[])).
% 2.45/1.04  
% 2.45/1.04  fof(f27,plain,(
% 2.45/1.04    ((k1_xboole_0 != sK7 & k1_xboole_0 != sK6) | k1_xboole_0 != k2_zfmisc_1(sK6,sK7)) & (k1_xboole_0 = sK7 | k1_xboole_0 = sK6 | k1_xboole_0 = k2_zfmisc_1(sK6,sK7))),
% 2.45/1.04    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7])],[f25,f26])).
% 2.45/1.04  
% 2.45/1.04  fof(f48,plain,(
% 2.45/1.04    k1_xboole_0 = sK7 | k1_xboole_0 = sK6 | k1_xboole_0 = k2_zfmisc_1(sK6,sK7)),
% 2.45/1.04    inference(cnf_transformation,[],[f27])).
% 2.45/1.04  
% 2.45/1.04  fof(f42,plain,(
% 2.45/1.04    ( ! [X2,X0,X10,X8,X1,X9] : (r2_hidden(X8,X2) | k4_tarski(X9,X10) != X8 | ~r2_hidden(X10,X1) | ~r2_hidden(X9,X0) | k2_zfmisc_1(X0,X1) != X2) )),
% 2.45/1.04    inference(cnf_transformation,[],[f23])).
% 2.45/1.04  
% 2.45/1.04  fof(f60,plain,(
% 2.45/1.04    ( ! [X2,X0,X10,X1,X9] : (r2_hidden(k4_tarski(X9,X10),X2) | ~r2_hidden(X10,X1) | ~r2_hidden(X9,X0) | k2_zfmisc_1(X0,X1) != X2) )),
% 2.45/1.04    inference(equality_resolution,[],[f42])).
% 2.45/1.04  
% 2.45/1.04  fof(f61,plain,(
% 2.45/1.04    ( ! [X0,X10,X1,X9] : (r2_hidden(k4_tarski(X9,X10),k2_zfmisc_1(X0,X1)) | ~r2_hidden(X10,X1) | ~r2_hidden(X9,X0)) )),
% 2.45/1.04    inference(equality_resolution,[],[f60])).
% 2.45/1.04  
% 2.45/1.04  fof(f49,plain,(
% 2.45/1.04    k1_xboole_0 != sK6 | k1_xboole_0 != k2_zfmisc_1(sK6,sK7)),
% 2.45/1.04    inference(cnf_transformation,[],[f27])).
% 2.45/1.04  
% 2.45/1.04  fof(f50,plain,(
% 2.45/1.04    k1_xboole_0 != sK7 | k1_xboole_0 != k2_zfmisc_1(sK6,sK7)),
% 2.45/1.04    inference(cnf_transformation,[],[f27])).
% 2.45/1.04  
% 2.45/1.04  cnf(c_3,plain,
% 2.45/1.04      ( r2_hidden(sK0(X0,X1,X2),X0)
% 2.45/1.04      | r2_hidden(sK0(X0,X1,X2),X2)
% 2.45/1.04      | k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X2 ),
% 2.45/1.04      inference(cnf_transformation,[],[f53]) ).
% 2.45/1.04  
% 2.45/1.04  cnf(c_567,plain,
% 2.45/1.04      ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X2
% 2.45/1.04      | r2_hidden(sK0(X0,X1,X2),X0) = iProver_top
% 2.45/1.04      | r2_hidden(sK0(X0,X1,X2),X2) = iProver_top ),
% 2.45/1.04      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 2.45/1.04  
% 2.45/1.04  cnf(c_9,plain,
% 2.45/1.04      ( r1_xboole_0(X0,k1_xboole_0) ),
% 2.45/1.04      inference(cnf_transformation,[],[f38]) ).
% 2.45/1.04  
% 2.45/1.04  cnf(c_18,plain,
% 2.45/1.04      ( ~ r1_xboole_0(k1_tarski(X0),X1) | ~ r2_hidden(X0,X1) ),
% 2.45/1.04      inference(cnf_transformation,[],[f47]) ).
% 2.45/1.04  
% 2.45/1.04  cnf(c_194,plain,
% 2.45/1.04      ( ~ r2_hidden(X0,X1) | k1_tarski(X0) != X2 | k1_xboole_0 != X1 ),
% 2.45/1.04      inference(resolution_lifted,[status(thm)],[c_9,c_18]) ).
% 2.45/1.04  
% 2.45/1.04  cnf(c_195,plain,
% 2.45/1.04      ( ~ r2_hidden(X0,k1_xboole_0) ),
% 2.45/1.04      inference(unflattening,[status(thm)],[c_194]) ).
% 2.45/1.04  
% 2.45/1.04  cnf(c_555,plain,
% 2.45/1.04      ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
% 2.45/1.04      inference(predicate_to_equality,[status(thm)],[c_195]) ).
% 2.45/1.04  
% 2.45/1.04  cnf(c_3342,plain,
% 2.45/1.04      ( k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X0)) = X1
% 2.45/1.04      | r2_hidden(sK0(k1_xboole_0,X0,X1),X1) = iProver_top ),
% 2.45/1.04      inference(superposition,[status(thm)],[c_567,c_555]) ).
% 2.45/1.04  
% 2.45/1.04  cnf(c_7,plain,
% 2.45/1.04      ( k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
% 2.45/1.04      inference(cnf_transformation,[],[f36]) ).
% 2.45/1.04  
% 2.45/1.04  cnf(c_0,plain,
% 2.45/1.04      ( k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
% 2.45/1.04      inference(cnf_transformation,[],[f28]) ).
% 2.45/1.04  
% 2.45/1.04  cnf(c_828,plain,
% 2.45/1.04      ( k3_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
% 2.45/1.04      inference(superposition,[status(thm)],[c_7,c_0]) ).
% 2.45/1.04  
% 2.45/1.04  cnf(c_3494,plain,
% 2.45/1.04      ( k5_xboole_0(k1_xboole_0,k1_xboole_0) = X0
% 2.45/1.04      | r2_hidden(sK0(k1_xboole_0,X1,X0),X0) = iProver_top ),
% 2.45/1.04      inference(light_normalisation,[status(thm)],[c_3342,c_828]) ).
% 2.45/1.04  
% 2.45/1.04  cnf(c_8,plain,
% 2.45/1.04      ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
% 2.45/1.04      inference(cnf_transformation,[],[f37]) ).
% 2.45/1.04  
% 2.45/1.04  cnf(c_3495,plain,
% 2.45/1.04      ( k1_xboole_0 = X0 | r2_hidden(sK0(k1_xboole_0,X1,X0),X0) = iProver_top ),
% 2.45/1.04      inference(demodulation,[status(thm)],[c_3494,c_8]) ).
% 2.45/1.04  
% 2.45/1.04  cnf(c_16,plain,
% 2.45/1.04      ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) | r2_hidden(sK5(X1,X2,X0),X2) ),
% 2.45/1.04      inference(cnf_transformation,[],[f63]) ).
% 2.45/1.04  
% 2.45/1.04  cnf(c_557,plain,
% 2.45/1.04      ( r2_hidden(X0,k2_zfmisc_1(X1,X2)) != iProver_top
% 2.45/1.04      | r2_hidden(sK5(X1,X2,X0),X2) = iProver_top ),
% 2.45/1.04      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 2.45/1.04  
% 2.45/1.04  cnf(c_17,plain,
% 2.45/1.04      ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) | r2_hidden(sK4(X1,X2,X0),X1) ),
% 2.45/1.04      inference(cnf_transformation,[],[f64]) ).
% 2.45/1.04  
% 2.45/1.04  cnf(c_556,plain,
% 2.45/1.04      ( r2_hidden(X0,k2_zfmisc_1(X1,X2)) != iProver_top
% 2.45/1.04      | r2_hidden(sK4(X1,X2,X0),X1) = iProver_top ),
% 2.45/1.04      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 2.45/1.04  
% 2.45/1.04  cnf(c_874,plain,
% 2.45/1.04      ( r2_hidden(X0,k2_zfmisc_1(k1_xboole_0,X1)) != iProver_top ),
% 2.45/1.04      inference(superposition,[status(thm)],[c_556,c_555]) ).
% 2.45/1.04  
% 2.45/1.04  cnf(c_1076,plain,
% 2.45/1.04      ( r2_hidden(X0,k2_zfmisc_1(X1,k2_zfmisc_1(k1_xboole_0,X2))) != iProver_top ),
% 2.45/1.04      inference(superposition,[status(thm)],[c_557,c_874]) ).
% 2.45/1.04  
% 2.45/1.04  cnf(c_3776,plain,
% 2.45/1.04      ( k2_zfmisc_1(X0,k2_zfmisc_1(k1_xboole_0,X1)) = k1_xboole_0 ),
% 2.45/1.04      inference(superposition,[status(thm)],[c_3495,c_1076]) ).
% 2.45/1.04  
% 2.45/1.04  cnf(c_1214,plain,
% 2.45/1.04      ( r2_hidden(X0,k2_zfmisc_1(k2_zfmisc_1(X1,k2_zfmisc_1(k1_xboole_0,X2)),X3)) != iProver_top ),
% 2.45/1.04      inference(superposition,[status(thm)],[c_556,c_1076]) ).
% 2.45/1.04  
% 2.45/1.04  cnf(c_3781,plain,
% 2.45/1.04      ( k2_zfmisc_1(k2_zfmisc_1(X0,k2_zfmisc_1(k1_xboole_0,X1)),X2) = k1_xboole_0 ),
% 2.45/1.04      inference(superposition,[status(thm)],[c_3495,c_1214]) ).
% 2.45/1.04  
% 2.45/1.04  cnf(c_3864,plain,
% 2.45/1.04      ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
% 2.45/1.04      inference(demodulation,[status(thm)],[c_3776,c_3781]) ).
% 2.45/1.04  
% 2.45/1.04  cnf(c_3867,plain,
% 2.45/1.04      ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
% 2.45/1.04      inference(demodulation,[status(thm)],[c_3864,c_3776]) ).
% 2.45/1.04  
% 2.45/1.04  cnf(c_21,negated_conjecture,
% 2.45/1.04      ( k1_xboole_0 = k2_zfmisc_1(sK6,sK7)
% 2.45/1.04      | k1_xboole_0 = sK6
% 2.45/1.04      | k1_xboole_0 = sK7 ),
% 2.45/1.04      inference(cnf_transformation,[],[f48]) ).
% 2.45/1.04  
% 2.45/1.04  cnf(c_14,plain,
% 2.45/1.04      ( ~ r2_hidden(X0,X1)
% 2.45/1.04      | ~ r2_hidden(X2,X3)
% 2.45/1.04      | r2_hidden(k4_tarski(X2,X0),k2_zfmisc_1(X3,X1)) ),
% 2.45/1.04      inference(cnf_transformation,[],[f61]) ).
% 2.45/1.04  
% 2.45/1.04  cnf(c_559,plain,
% 2.45/1.04      ( r2_hidden(X0,X1) != iProver_top
% 2.45/1.04      | r2_hidden(X2,X3) != iProver_top
% 2.45/1.04      | r2_hidden(k4_tarski(X2,X0),k2_zfmisc_1(X3,X1)) = iProver_top ),
% 2.45/1.04      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 2.45/1.04  
% 2.45/1.04  cnf(c_1678,plain,
% 2.45/1.04      ( sK6 = k1_xboole_0
% 2.45/1.04      | sK7 = k1_xboole_0
% 2.45/1.04      | r2_hidden(X0,sK6) != iProver_top
% 2.45/1.04      | r2_hidden(X1,sK7) != iProver_top
% 2.45/1.04      | r2_hidden(k4_tarski(X0,X1),k1_xboole_0) = iProver_top ),
% 2.45/1.04      inference(superposition,[status(thm)],[c_21,c_559]) ).
% 2.45/1.04  
% 2.45/1.04  cnf(c_1903,plain,
% 2.45/1.04      ( sK6 = k1_xboole_0
% 2.45/1.04      | sK7 = k1_xboole_0
% 2.45/1.04      | r2_hidden(X0,sK6) != iProver_top
% 2.45/1.04      | r2_hidden(X1,sK7) != iProver_top ),
% 2.45/1.04      inference(forward_subsumption_resolution,[status(thm)],[c_1678,c_555]) ).
% 2.45/1.04  
% 2.45/1.04  cnf(c_3782,plain,
% 2.45/1.04      ( sK6 = k1_xboole_0
% 2.45/1.04      | sK7 = k1_xboole_0
% 2.45/1.04      | r2_hidden(X0,sK6) != iProver_top ),
% 2.45/1.04      inference(superposition,[status(thm)],[c_3495,c_1903]) ).
% 2.45/1.04  
% 2.45/1.04  cnf(c_4060,plain,
% 2.45/1.04      ( sK6 = k1_xboole_0 | sK7 = k1_xboole_0 ),
% 2.45/1.04      inference(superposition,[status(thm)],[c_3495,c_3782]) ).
% 2.45/1.04  
% 2.45/1.04  cnf(c_20,negated_conjecture,
% 2.45/1.04      ( k1_xboole_0 != k2_zfmisc_1(sK6,sK7) | k1_xboole_0 != sK6 ),
% 2.45/1.04      inference(cnf_transformation,[],[f49]) ).
% 2.45/1.04  
% 2.45/1.04  cnf(c_4201,plain,
% 2.45/1.04      ( k2_zfmisc_1(k1_xboole_0,sK7) != k1_xboole_0
% 2.45/1.04      | sK6 != k1_xboole_0
% 2.45/1.04      | sK7 = k1_xboole_0 ),
% 2.45/1.04      inference(superposition,[status(thm)],[c_4060,c_20]) ).
% 2.45/1.04  
% 2.45/1.04  cnf(c_4206,plain,
% 2.45/1.04      ( k2_zfmisc_1(k1_xboole_0,sK7) != k1_xboole_0 | sK7 = k1_xboole_0 ),
% 2.45/1.04      inference(forward_subsumption_resolution,[status(thm)],[c_4201,c_4060]) ).
% 2.45/1.04  
% 2.45/1.04  cnf(c_8324,plain,
% 2.45/1.04      ( sK7 = k1_xboole_0 | k1_xboole_0 != k1_xboole_0 ),
% 2.45/1.04      inference(demodulation,[status(thm)],[c_3864,c_4206]) ).
% 2.45/1.04  
% 2.45/1.04  cnf(c_8326,plain,
% 2.45/1.04      ( sK7 = k1_xboole_0 ),
% 2.45/1.04      inference(equality_resolution_simp,[status(thm)],[c_8324]) ).
% 2.45/1.04  
% 2.45/1.04  cnf(c_19,negated_conjecture,
% 2.45/1.04      ( k1_xboole_0 != k2_zfmisc_1(sK6,sK7) | k1_xboole_0 != sK7 ),
% 2.45/1.04      inference(cnf_transformation,[],[f50]) ).
% 2.45/1.04  
% 2.45/1.04  cnf(c_8388,plain,
% 2.45/1.04      ( k2_zfmisc_1(sK6,k1_xboole_0) != k1_xboole_0
% 2.45/1.04      | k1_xboole_0 != k1_xboole_0 ),
% 2.45/1.04      inference(demodulation,[status(thm)],[c_8326,c_19]) ).
% 2.45/1.04  
% 2.45/1.04  cnf(c_8389,plain,
% 2.45/1.04      ( k2_zfmisc_1(sK6,k1_xboole_0) != k1_xboole_0 ),
% 2.45/1.04      inference(equality_resolution_simp,[status(thm)],[c_8388]) ).
% 2.45/1.04  
% 2.45/1.04  cnf(c_8601,plain,
% 2.45/1.04      ( k1_xboole_0 != k1_xboole_0 ),
% 2.45/1.04      inference(demodulation,[status(thm)],[c_3867,c_8389]) ).
% 2.45/1.04  
% 2.45/1.04  cnf(c_8602,plain,
% 2.45/1.04      ( $false ),
% 2.45/1.04      inference(equality_resolution_simp,[status(thm)],[c_8601]) ).
% 2.45/1.04  
% 2.45/1.04  
% 2.45/1.04  % SZS output end CNFRefutation for theBenchmark.p
% 2.45/1.04  
% 2.45/1.04  ------                               Statistics
% 2.45/1.04  
% 2.45/1.04  ------ General
% 2.45/1.04  
% 2.45/1.04  abstr_ref_over_cycles:                  0
% 2.45/1.04  abstr_ref_under_cycles:                 0
% 2.45/1.04  gc_basic_clause_elim:                   0
% 2.45/1.04  forced_gc_time:                         0
% 2.45/1.04  parsing_time:                           0.011
% 2.45/1.04  unif_index_cands_time:                  0.
% 2.45/1.04  unif_index_add_time:                    0.
% 2.45/1.04  orderings_time:                         0.
% 2.45/1.04  out_proof_time:                         0.012
% 2.45/1.04  total_time:                             0.266
% 2.45/1.04  num_of_symbols:                         47
% 2.45/1.04  num_of_terms:                           9664
% 2.45/1.04  
% 2.45/1.04  ------ Preprocessing
% 2.45/1.04  
% 2.45/1.04  num_of_splits:                          0
% 2.45/1.04  num_of_split_atoms:                     0
% 2.45/1.04  num_of_reused_defs:                     0
% 2.45/1.04  num_eq_ax_congr_red:                    61
% 2.45/1.04  num_of_sem_filtered_clauses:            1
% 2.45/1.04  num_of_subtypes:                        0
% 2.45/1.04  monotx_restored_types:                  0
% 2.45/1.04  sat_num_of_epr_types:                   0
% 2.45/1.04  sat_num_of_non_cyclic_types:            0
% 2.45/1.04  sat_guarded_non_collapsed_types:        0
% 2.45/1.04  num_pure_diseq_elim:                    0
% 2.45/1.04  simp_replaced_by:                       0
% 2.45/1.04  res_preprocessed:                       100
% 2.45/1.04  prep_upred:                             0
% 2.45/1.04  prep_unflattend:                        2
% 2.45/1.04  smt_new_axioms:                         0
% 2.45/1.04  pred_elim_cands:                        1
% 2.45/1.04  pred_elim:                              1
% 2.45/1.04  pred_elim_cl:                           1
% 2.45/1.04  pred_elim_cycles:                       3
% 2.45/1.04  merged_defs:                            0
% 2.45/1.04  merged_defs_ncl:                        0
% 2.45/1.04  bin_hyper_res:                          0
% 2.45/1.04  prep_cycles:                            4
% 2.45/1.04  pred_elim_time:                         0.001
% 2.45/1.04  splitting_time:                         0.
% 2.45/1.04  sem_filter_time:                        0.
% 2.45/1.04  monotx_time:                            0.
% 2.45/1.04  subtype_inf_time:                       0.
% 2.45/1.04  
% 2.45/1.04  ------ Problem properties
% 2.45/1.04  
% 2.45/1.04  clauses:                                21
% 2.45/1.04  conjectures:                            3
% 2.45/1.04  epr:                                    1
% 2.45/1.04  horn:                                   13
% 2.45/1.04  ground:                                 3
% 2.45/1.04  unary:                                  4
% 2.45/1.04  binary:                                 7
% 2.45/1.04  lits:                                   51
% 2.45/1.04  lits_eq:                                20
% 2.45/1.04  fd_pure:                                0
% 2.45/1.04  fd_pseudo:                              0
% 2.45/1.04  fd_cond:                                0
% 2.45/1.04  fd_pseudo_cond:                         7
% 2.45/1.04  ac_symbols:                             0
% 2.45/1.04  
% 2.45/1.04  ------ Propositional Solver
% 2.45/1.04  
% 2.45/1.04  prop_solver_calls:                      29
% 2.45/1.04  prop_fast_solver_calls:                 983
% 2.45/1.04  smt_solver_calls:                       0
% 2.45/1.04  smt_fast_solver_calls:                  0
% 2.45/1.04  prop_num_of_clauses:                    2584
% 2.45/1.04  prop_preprocess_simplified:             6261
% 2.45/1.04  prop_fo_subsumed:                       144
% 2.45/1.04  prop_solver_time:                       0.
% 2.45/1.04  smt_solver_time:                        0.
% 2.45/1.04  smt_fast_solver_time:                   0.
% 2.45/1.04  prop_fast_solver_time:                  0.
% 2.45/1.04  prop_unsat_core_time:                   0.
% 2.45/1.04  
% 2.45/1.04  ------ QBF
% 2.45/1.04  
% 2.45/1.04  qbf_q_res:                              0
% 2.45/1.04  qbf_num_tautologies:                    0
% 2.45/1.04  qbf_prep_cycles:                        0
% 2.45/1.04  
% 2.45/1.04  ------ BMC1
% 2.45/1.04  
% 2.45/1.04  bmc1_current_bound:                     -1
% 2.45/1.04  bmc1_last_solved_bound:                 -1
% 2.45/1.04  bmc1_unsat_core_size:                   -1
% 2.45/1.04  bmc1_unsat_core_parents_size:           -1
% 2.45/1.04  bmc1_merge_next_fun:                    0
% 2.45/1.04  bmc1_unsat_core_clauses_time:           0.
% 2.45/1.04  
% 2.45/1.04  ------ Instantiation
% 2.45/1.04  
% 2.45/1.04  inst_num_of_clauses:                    739
% 2.45/1.04  inst_num_in_passive:                    171
% 2.45/1.04  inst_num_in_active:                     326
% 2.45/1.04  inst_num_in_unprocessed:                242
% 2.45/1.04  inst_num_of_loops:                      400
% 2.45/1.04  inst_num_of_learning_restarts:          0
% 2.45/1.04  inst_num_moves_active_passive:          69
% 2.45/1.04  inst_lit_activity:                      0
% 2.45/1.04  inst_lit_activity_moves:                0
% 2.45/1.04  inst_num_tautologies:                   0
% 2.45/1.04  inst_num_prop_implied:                  0
% 2.45/1.04  inst_num_existing_simplified:           0
% 2.45/1.04  inst_num_eq_res_simplified:             0
% 2.45/1.04  inst_num_child_elim:                    0
% 2.45/1.04  inst_num_of_dismatching_blockings:      389
% 2.45/1.04  inst_num_of_non_proper_insts:           568
% 2.45/1.04  inst_num_of_duplicates:                 0
% 2.45/1.04  inst_inst_num_from_inst_to_res:         0
% 2.45/1.04  inst_dismatching_checking_time:         0.
% 2.45/1.04  
% 2.45/1.04  ------ Resolution
% 2.45/1.04  
% 2.45/1.04  res_num_of_clauses:                     0
% 2.45/1.04  res_num_in_passive:                     0
% 2.45/1.04  res_num_in_active:                      0
% 2.45/1.04  res_num_of_loops:                       104
% 2.45/1.04  res_forward_subset_subsumed:            78
% 2.45/1.04  res_backward_subset_subsumed:           0
% 2.45/1.04  res_forward_subsumed:                   0
% 2.45/1.04  res_backward_subsumed:                  0
% 2.45/1.04  res_forward_subsumption_resolution:     0
% 2.45/1.04  res_backward_subsumption_resolution:    0
% 2.45/1.04  res_clause_to_clause_subsumption:       1673
% 2.45/1.04  res_orphan_elimination:                 0
% 2.45/1.04  res_tautology_del:                      65
% 2.45/1.04  res_num_eq_res_simplified:              0
% 2.45/1.04  res_num_sel_changes:                    0
% 2.45/1.04  res_moves_from_active_to_pass:          0
% 2.45/1.04  
% 2.45/1.04  ------ Superposition
% 2.45/1.04  
% 2.45/1.04  sup_time_total:                         0.
% 2.45/1.04  sup_time_generating:                    0.
% 2.45/1.04  sup_time_sim_full:                      0.
% 2.45/1.04  sup_time_sim_immed:                     0.
% 2.45/1.04  
% 2.45/1.04  sup_num_of_clauses:                     271
% 2.45/1.04  sup_num_in_active:                      39
% 2.45/1.04  sup_num_in_passive:                     232
% 2.45/1.04  sup_num_of_loops:                       79
% 2.45/1.04  sup_fw_superposition:                   510
% 2.45/1.04  sup_bw_superposition:                   487
% 2.45/1.04  sup_immediate_simplified:               212
% 2.45/1.04  sup_given_eliminated:                   10
% 2.45/1.04  comparisons_done:                       0
% 2.45/1.04  comparisons_avoided:                    2
% 2.45/1.04  
% 2.45/1.04  ------ Simplifications
% 2.45/1.04  
% 2.45/1.04  
% 2.45/1.04  sim_fw_subset_subsumed:                 17
% 2.45/1.04  sim_bw_subset_subsumed:                 20
% 2.45/1.04  sim_fw_subsumed:                        55
% 2.45/1.04  sim_bw_subsumed:                        7
% 2.45/1.04  sim_fw_subsumption_res:                 2
% 2.45/1.04  sim_bw_subsumption_res:                 0
% 2.45/1.04  sim_tautology_del:                      14
% 2.45/1.04  sim_eq_tautology_del:                   3
% 2.45/1.04  sim_eq_res_simp:                        3
% 2.45/1.04  sim_fw_demodulated:                     105
% 2.45/1.04  sim_bw_demodulated:                     37
% 2.45/1.04  sim_light_normalised:                   38
% 2.45/1.04  sim_joinable_taut:                      0
% 2.45/1.04  sim_joinable_simp:                      0
% 2.45/1.04  sim_ac_normalised:                      0
% 2.45/1.04  sim_smt_subsumption:                    0
% 2.45/1.04  
%------------------------------------------------------------------------------
