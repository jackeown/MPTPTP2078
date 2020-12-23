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

% Result     : Theorem 11.51s
% Output     : CNFRefutation 11.51s
% Verified   : 
% Statistics : Number of formulae       :   82 ( 693 expanded)
%              Number of clauses        :   45 ( 231 expanded)
%              Number of leaves         :    9 ( 156 expanded)
%              Depth                    :   25
%              Number of atoms          :  342 (4215 expanded)
%              Number of equality atoms :  179 (1291 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal clause size      :   18 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2,axiom,(
    ! [X0] : k4_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0] : k4_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f2])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f7,plain,(
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
    inference(nnf_transformation,[],[f1])).

fof(f8,plain,(
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
    inference(flattening,[],[f7])).

fof(f9,plain,(
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
    inference(rectify,[],[f8])).

fof(f10,plain,(
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

fof(f11,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f9,f10])).

fof(f25,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X0,X1) = X2
      | r2_hidden(sK0(X0,X1,X2),X0)
      | r2_hidden(sK0(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f23,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f11])).

fof(f41,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,k4_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f23])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( k2_zfmisc_1(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ? [X4,X5] :
              ( k4_tarski(X4,X5) = X3
              & r2_hidden(X5,X1)
              & r2_hidden(X4,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
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
    inference(nnf_transformation,[],[f3])).

fof(f13,plain,(
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
    inference(rectify,[],[f12])).

fof(f16,plain,(
    ! [X8,X1,X0] :
      ( ? [X11,X12] :
          ( k4_tarski(X11,X12) = X8
          & r2_hidden(X12,X1)
          & r2_hidden(X11,X0) )
     => ( k4_tarski(sK4(X0,X1,X8),sK5(X0,X1,X8)) = X8
        & r2_hidden(sK5(X0,X1,X8),X1)
        & r2_hidden(sK4(X0,X1,X8),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X6,X7] :
          ( k4_tarski(X6,X7) = X3
          & r2_hidden(X7,X1)
          & r2_hidden(X6,X0) )
     => ( k4_tarski(sK2(X0,X1,X2),sK3(X0,X1,X2)) = X3
        & r2_hidden(sK3(X0,X1,X2),X1)
        & r2_hidden(sK2(X0,X1,X2),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f14,plain,(
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

fof(f17,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4,sK5])],[f13,f16,f15,f14])).

fof(f29,plain,(
    ! [X2,X0,X8,X1] :
      ( r2_hidden(sK4(X0,X1,X8),X0)
      | ~ r2_hidden(X8,X2)
      | k2_zfmisc_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f17])).

fof(f47,plain,(
    ! [X0,X8,X1] :
      ( r2_hidden(sK4(X0,X1,X8),X0)
      | ~ r2_hidden(X8,k2_zfmisc_1(X0,X1)) ) ),
    inference(equality_resolution,[],[f29])).

fof(f22,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f11])).

fof(f42,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,k4_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f22])).

fof(f4,conjecture,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f5,negated_conjecture,(
    ~ ! [X0,X1] :
        ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      <=> ( k1_xboole_0 = X1
          | k1_xboole_0 = X0 ) ) ),
    inference(negated_conjecture,[],[f4])).

fof(f6,plain,(
    ? [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <~> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f18,plain,(
    ? [X0,X1] :
      ( ( ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 )
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 = k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f19,plain,(
    ? [X0,X1] :
      ( ( ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 )
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 = k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f18])).

fof(f20,plain,
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

fof(f21,plain,
    ( ( ( k1_xboole_0 != sK7
        & k1_xboole_0 != sK6 )
      | k1_xboole_0 != k2_zfmisc_1(sK6,sK7) )
    & ( k1_xboole_0 = sK7
      | k1_xboole_0 = sK6
      | k1_xboole_0 = k2_zfmisc_1(sK6,sK7) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7])],[f19,f20])).

fof(f37,plain,
    ( k1_xboole_0 = sK7
    | k1_xboole_0 = sK6
    | k1_xboole_0 = k2_zfmisc_1(sK6,sK7) ),
    inference(cnf_transformation,[],[f21])).

fof(f32,plain,(
    ! [X2,X0,X10,X8,X1,X9] :
      ( r2_hidden(X8,X2)
      | k4_tarski(X9,X10) != X8
      | ~ r2_hidden(X10,X1)
      | ~ r2_hidden(X9,X0)
      | k2_zfmisc_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f17])).

fof(f43,plain,(
    ! [X2,X0,X10,X1,X9] :
      ( r2_hidden(k4_tarski(X9,X10),X2)
      | ~ r2_hidden(X10,X1)
      | ~ r2_hidden(X9,X0)
      | k2_zfmisc_1(X0,X1) != X2 ) ),
    inference(equality_resolution,[],[f32])).

fof(f44,plain,(
    ! [X0,X10,X1,X9] :
      ( r2_hidden(k4_tarski(X9,X10),k2_zfmisc_1(X0,X1))
      | ~ r2_hidden(X10,X1)
      | ~ r2_hidden(X9,X0) ) ),
    inference(equality_resolution,[],[f43])).

fof(f38,plain,
    ( k1_xboole_0 != sK6
    | k1_xboole_0 != k2_zfmisc_1(sK6,sK7) ),
    inference(cnf_transformation,[],[f21])).

fof(f39,plain,
    ( k1_xboole_0 != sK7
    | k1_xboole_0 != k2_zfmisc_1(sK6,sK7) ),
    inference(cnf_transformation,[],[f21])).

fof(f30,plain,(
    ! [X2,X0,X8,X1] :
      ( r2_hidden(sK5(X0,X1,X8),X1)
      | ~ r2_hidden(X8,X2)
      | k2_zfmisc_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f17])).

fof(f46,plain,(
    ! [X0,X8,X1] :
      ( r2_hidden(sK5(X0,X1,X8),X1)
      | ~ r2_hidden(X8,k2_zfmisc_1(X0,X1)) ) ),
    inference(equality_resolution,[],[f30])).

cnf(c_6,plain,
    ( k4_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f28])).

cnf(c_2,plain,
    ( r2_hidden(sK0(X0,X1,X2),X0)
    | r2_hidden(sK0(X0,X1,X2),X2)
    | k4_xboole_0(X0,X1) = X2 ),
    inference(cnf_transformation,[],[f25])).

cnf(c_824,plain,
    ( k4_xboole_0(X0,X1) = X2
    | r2_hidden(sK0(X0,X1,X2),X0) = iProver_top
    | r2_hidden(sK0(X0,X1,X2),X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_4,negated_conjecture,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k4_xboole_0(X2,X1)) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_822,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,k4_xboole_0(X2,X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_1802,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),X2) = X3
    | r2_hidden(sK0(k4_xboole_0(X0,X1),X2,X3),X1) != iProver_top
    | r2_hidden(sK0(k4_xboole_0(X0,X1),X2,X3),X3) = iProver_top ),
    inference(superposition,[status(thm)],[c_824,c_822])).

cnf(c_2145,plain,
    ( k4_xboole_0(k4_xboole_0(k1_xboole_0,X0),X1) = X2
    | r2_hidden(sK0(k4_xboole_0(k1_xboole_0,X0),X1,X2),X2) = iProver_top
    | r2_hidden(sK0(k1_xboole_0,X1,X2),X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_6,c_1802])).

cnf(c_2149,plain,
    ( k4_xboole_0(k1_xboole_0,X0) = X1
    | r2_hidden(sK0(k1_xboole_0,X0,X1),X2) != iProver_top
    | r2_hidden(sK0(k1_xboole_0,X0,X1),X1) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2145,c_6])).

cnf(c_2150,plain,
    ( k1_xboole_0 = X0
    | r2_hidden(sK0(k1_xboole_0,X1,X0),X2) != iProver_top
    | r2_hidden(sK0(k1_xboole_0,X1,X0),X0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_2149,c_6])).

cnf(c_2487,plain,
    ( k4_xboole_0(k1_xboole_0,X0) = X1
    | k1_xboole_0 = X1
    | r2_hidden(sK0(k1_xboole_0,X0,X1),X1) = iProver_top
    | r2_hidden(sK0(k1_xboole_0,X0,X1),k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_824,c_2150])).

cnf(c_2493,plain,
    ( k4_xboole_0(k1_xboole_0,X0) = X1
    | k1_xboole_0 = X1
    | r2_hidden(sK0(k1_xboole_0,X0,X1),X1) = iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_2487,c_2150])).

cnf(c_2494,plain,
    ( k1_xboole_0 = X0
    | r2_hidden(sK0(k1_xboole_0,X1,X0),X0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_2493,c_6])).

cnf(c_14,plain,
    ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
    | r2_hidden(sK4(X1,X2,X0),X1) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_813,plain,
    ( r2_hidden(X0,k2_zfmisc_1(X1,X2)) != iProver_top
    | r2_hidden(sK4(X1,X2,X0),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_5,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k4_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_821,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r2_hidden(X0,k4_xboole_0(X1,X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_1003,plain,
    ( r2_hidden(X0,k2_zfmisc_1(k4_xboole_0(X1,X2),X3)) != iProver_top
    | r2_hidden(sK4(k4_xboole_0(X1,X2),X3,X0),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_813,c_821])).

cnf(c_1004,plain,
    ( r2_hidden(X0,k2_zfmisc_1(k4_xboole_0(X1,X2),X3)) != iProver_top
    | r2_hidden(sK4(k4_xboole_0(X1,X2),X3,X0),X2) != iProver_top ),
    inference(superposition,[status(thm)],[c_813,c_822])).

cnf(c_3773,plain,
    ( r2_hidden(X0,k2_zfmisc_1(k4_xboole_0(X1,X1),X2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1003,c_1004])).

cnf(c_3884,plain,
    ( k2_zfmisc_1(k4_xboole_0(X0,X0),X1) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2494,c_3773])).

cnf(c_4085,plain,
    ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_6,c_3884])).

cnf(c_17,negated_conjecture,
    ( k1_xboole_0 = k2_zfmisc_1(sK6,sK7)
    | k1_xboole_0 = sK6
    | k1_xboole_0 = sK7 ),
    inference(cnf_transformation,[],[f37])).

cnf(c_11,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X2,X3)
    | r2_hidden(k4_tarski(X2,X0),k2_zfmisc_1(X3,X1)) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_816,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X2,X3) != iProver_top
    | r2_hidden(k4_tarski(X2,X0),k2_zfmisc_1(X3,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_1111,plain,
    ( sK6 = k1_xboole_0
    | sK7 = k1_xboole_0
    | r2_hidden(X0,sK6) != iProver_top
    | r2_hidden(X1,sK7) != iProver_top
    | r2_hidden(k4_tarski(X0,X1),k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_17,c_816])).

cnf(c_985,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_6,c_822])).

cnf(c_1112,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X2,X3) != iProver_top
    | r2_hidden(k4_tarski(X2,X0),k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_816,c_985])).

cnf(c_1131,plain,
    ( sK6 = k1_xboole_0
    | sK7 = k1_xboole_0
    | r2_hidden(X0,sK6) != iProver_top
    | r2_hidden(X1,sK7) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_1111,c_1112])).

cnf(c_2510,plain,
    ( sK6 = k1_xboole_0
    | sK7 = k1_xboole_0
    | r2_hidden(X0,sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_2494,c_1131])).

cnf(c_3710,plain,
    ( sK6 = k1_xboole_0
    | sK7 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2494,c_2510])).

cnf(c_16,negated_conjecture,
    ( k1_xboole_0 != k2_zfmisc_1(sK6,sK7)
    | k1_xboole_0 != sK6 ),
    inference(cnf_transformation,[],[f38])).

cnf(c_3836,plain,
    ( k2_zfmisc_1(k1_xboole_0,sK7) != k1_xboole_0
    | sK6 != k1_xboole_0
    | sK7 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_3710,c_16])).

cnf(c_3841,plain,
    ( k2_zfmisc_1(k1_xboole_0,sK7) != k1_xboole_0
    | sK7 = k1_xboole_0 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_3836,c_3710])).

cnf(c_4105,plain,
    ( sK7 = k1_xboole_0
    | k1_xboole_0 != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_4085,c_3841])).

cnf(c_4106,plain,
    ( sK7 = k1_xboole_0 ),
    inference(equality_resolution_simp,[status(thm)],[c_4105])).

cnf(c_15,negated_conjecture,
    ( k1_xboole_0 != k2_zfmisc_1(sK6,sK7)
    | k1_xboole_0 != sK7 ),
    inference(cnf_transformation,[],[f39])).

cnf(c_45733,plain,
    ( k2_zfmisc_1(sK6,k1_xboole_0) != k1_xboole_0
    | k1_xboole_0 != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_4106,c_15])).

cnf(c_45734,plain,
    ( k2_zfmisc_1(sK6,k1_xboole_0) != k1_xboole_0 ),
    inference(equality_resolution_simp,[status(thm)],[c_45733])).

cnf(c_13,plain,
    ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
    | r2_hidden(sK5(X1,X2,X0),X2) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_814,plain,
    ( r2_hidden(X0,k2_zfmisc_1(X1,X2)) != iProver_top
    | r2_hidden(sK5(X1,X2,X0),X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_1035,plain,
    ( r2_hidden(X0,k2_zfmisc_1(X1,X2)) != iProver_top
    | r2_hidden(sK5(X1,X2,X0),k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_814,c_985])).

cnf(c_1371,plain,
    ( r2_hidden(X0,k2_zfmisc_1(X1,k1_xboole_0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_814,c_1035])).

cnf(c_4148,plain,
    ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2494,c_1371])).

cnf(c_45736,plain,
    ( k1_xboole_0 != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_45734,c_4148])).

cnf(c_45737,plain,
    ( $false ),
    inference(equality_resolution_simp,[status(thm)],[c_45736])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n004.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 12:59:23 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 11.51/2.00  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 11.51/2.00  
% 11.51/2.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 11.51/2.00  
% 11.51/2.00  ------  iProver source info
% 11.51/2.00  
% 11.51/2.00  git: date: 2020-06-30 10:37:57 +0100
% 11.51/2.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 11.51/2.00  git: non_committed_changes: false
% 11.51/2.00  git: last_make_outside_of_git: false
% 11.51/2.00  
% 11.51/2.00  ------ 
% 11.51/2.00  ------ Parsing...
% 11.51/2.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 11.51/2.00  
% 11.51/2.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 11.51/2.00  
% 11.51/2.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 11.51/2.00  
% 11.51/2.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 11.51/2.00  ------ Proving...
% 11.51/2.00  ------ Problem Properties 
% 11.51/2.00  
% 11.51/2.00  
% 11.51/2.00  clauses                                 18
% 11.51/2.00  conjectures                             4
% 11.51/2.00  EPR                                     0
% 11.51/2.00  Horn                                    10
% 11.51/2.00  unary                                   1
% 11.51/2.00  binary                                  7
% 11.51/2.00  lits                                    48
% 11.51/2.00  lits eq                                 18
% 11.51/2.00  fd_pure                                 0
% 11.51/2.00  fd_pseudo                               0
% 11.51/2.00  fd_cond                                 0
% 11.51/2.00  fd_pseudo_cond                          7
% 11.51/2.00  AC symbols                              0
% 11.51/2.00  
% 11.51/2.00  ------ Input Options Time Limit: Unbounded
% 11.51/2.00  
% 11.51/2.00  
% 11.51/2.00  
% 11.51/2.00  
% 11.51/2.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e ------ 
% 11.51/2.00  Current options:
% 11.51/2.00  ------ 
% 11.51/2.00  
% 11.51/2.00  
% 11.51/2.00  
% 11.51/2.00  
% 11.51/2.00  ------ Proving...
% 11.51/2.00  
% 11.51/2.00  
% 11.51/2.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 11.51/2.00  
% 11.51/2.00  ------ Proving...
% 11.51/2.00  
% 11.51/2.00  
% 11.51/2.00  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 11.51/2.00  
% 11.51/2.00  ------ Proving...
% 11.51/2.00  
% 11.51/2.00  
% 11.51/2.00  % SZS status Theorem for theBenchmark.p
% 11.51/2.00  
% 11.51/2.00   Resolution empty clause
% 11.51/2.00  
% 11.51/2.00  % SZS output start CNFRefutation for theBenchmark.p
% 11.51/2.00  
% 11.51/2.00  fof(f2,axiom,(
% 11.51/2.00    ! [X0] : k4_xboole_0(k1_xboole_0,X0) = k1_xboole_0),
% 11.51/2.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.51/2.00  
% 11.51/2.00  fof(f28,plain,(
% 11.51/2.00    ( ! [X0] : (k4_xboole_0(k1_xboole_0,X0) = k1_xboole_0) )),
% 11.51/2.00    inference(cnf_transformation,[],[f2])).
% 11.51/2.00  
% 11.51/2.00  fof(f1,axiom,(
% 11.51/2.00    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 11.51/2.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.51/2.00  
% 11.51/2.00  fof(f7,plain,(
% 11.51/2.00    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : (((r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 11.51/2.00    inference(nnf_transformation,[],[f1])).
% 11.51/2.00  
% 11.51/2.00  fof(f8,plain,(
% 11.51/2.00    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 11.51/2.00    inference(flattening,[],[f7])).
% 11.51/2.00  
% 11.51/2.00  fof(f9,plain,(
% 11.51/2.00    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 11.51/2.00    inference(rectify,[],[f8])).
% 11.51/2.00  
% 11.51/2.00  fof(f10,plain,(
% 11.51/2.00    ! [X2,X1,X0] : (? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((r2_hidden(sK0(X0,X1,X2),X1) | ~r2_hidden(sK0(X0,X1,X2),X0) | ~r2_hidden(sK0(X0,X1,X2),X2)) & ((~r2_hidden(sK0(X0,X1,X2),X1) & r2_hidden(sK0(X0,X1,X2),X0)) | r2_hidden(sK0(X0,X1,X2),X2))))),
% 11.51/2.00    introduced(choice_axiom,[])).
% 11.51/2.00  
% 11.51/2.00  fof(f11,plain,(
% 11.51/2.00    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ((r2_hidden(sK0(X0,X1,X2),X1) | ~r2_hidden(sK0(X0,X1,X2),X0) | ~r2_hidden(sK0(X0,X1,X2),X2)) & ((~r2_hidden(sK0(X0,X1,X2),X1) & r2_hidden(sK0(X0,X1,X2),X0)) | r2_hidden(sK0(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 11.51/2.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f9,f10])).
% 11.51/2.00  
% 11.51/2.00  fof(f25,plain,(
% 11.51/2.00    ( ! [X2,X0,X1] : (k4_xboole_0(X0,X1) = X2 | r2_hidden(sK0(X0,X1,X2),X0) | r2_hidden(sK0(X0,X1,X2),X2)) )),
% 11.51/2.00    inference(cnf_transformation,[],[f11])).
% 11.51/2.00  
% 11.51/2.00  fof(f23,plain,(
% 11.51/2.00    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 11.51/2.00    inference(cnf_transformation,[],[f11])).
% 11.51/2.00  
% 11.51/2.00  fof(f41,plain,(
% 11.51/2.00    ( ! [X4,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,k4_xboole_0(X0,X1))) )),
% 11.51/2.00    inference(equality_resolution,[],[f23])).
% 11.51/2.00  
% 11.51/2.00  fof(f3,axiom,(
% 11.51/2.00    ! [X0,X1,X2] : (k2_zfmisc_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4,X5] : (k4_tarski(X4,X5) = X3 & r2_hidden(X5,X1) & r2_hidden(X4,X0))))),
% 11.51/2.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.51/2.00  
% 11.51/2.00  fof(f12,plain,(
% 11.51/2.00    ! [X0,X1,X2] : ((k2_zfmisc_1(X0,X1) = X2 | ? [X3] : ((! [X4,X5] : (k4_tarski(X4,X5) != X3 | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X0)) | ~r2_hidden(X3,X2)) & (? [X4,X5] : (k4_tarski(X4,X5) = X3 & r2_hidden(X5,X1) & r2_hidden(X4,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ! [X4,X5] : (k4_tarski(X4,X5) != X3 | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X0))) & (? [X4,X5] : (k4_tarski(X4,X5) = X3 & r2_hidden(X5,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X3,X2))) | k2_zfmisc_1(X0,X1) != X2))),
% 11.51/2.00    inference(nnf_transformation,[],[f3])).
% 11.51/2.00  
% 11.51/2.00  fof(f13,plain,(
% 11.51/2.00    ! [X0,X1,X2] : ((k2_zfmisc_1(X0,X1) = X2 | ? [X3] : ((! [X4,X5] : (k4_tarski(X4,X5) != X3 | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X0)) | ~r2_hidden(X3,X2)) & (? [X6,X7] : (k4_tarski(X6,X7) = X3 & r2_hidden(X7,X1) & r2_hidden(X6,X0)) | r2_hidden(X3,X2)))) & (! [X8] : ((r2_hidden(X8,X2) | ! [X9,X10] : (k4_tarski(X9,X10) != X8 | ~r2_hidden(X10,X1) | ~r2_hidden(X9,X0))) & (? [X11,X12] : (k4_tarski(X11,X12) = X8 & r2_hidden(X12,X1) & r2_hidden(X11,X0)) | ~r2_hidden(X8,X2))) | k2_zfmisc_1(X0,X1) != X2))),
% 11.51/2.00    inference(rectify,[],[f12])).
% 11.51/2.00  
% 11.51/2.00  fof(f16,plain,(
% 11.51/2.00    ! [X8,X1,X0] : (? [X11,X12] : (k4_tarski(X11,X12) = X8 & r2_hidden(X12,X1) & r2_hidden(X11,X0)) => (k4_tarski(sK4(X0,X1,X8),sK5(X0,X1,X8)) = X8 & r2_hidden(sK5(X0,X1,X8),X1) & r2_hidden(sK4(X0,X1,X8),X0)))),
% 11.51/2.00    introduced(choice_axiom,[])).
% 11.51/2.00  
% 11.51/2.00  fof(f15,plain,(
% 11.51/2.00    ( ! [X3] : (! [X2,X1,X0] : (? [X6,X7] : (k4_tarski(X6,X7) = X3 & r2_hidden(X7,X1) & r2_hidden(X6,X0)) => (k4_tarski(sK2(X0,X1,X2),sK3(X0,X1,X2)) = X3 & r2_hidden(sK3(X0,X1,X2),X1) & r2_hidden(sK2(X0,X1,X2),X0)))) )),
% 11.51/2.00    introduced(choice_axiom,[])).
% 11.51/2.00  
% 11.51/2.00  fof(f14,plain,(
% 11.51/2.00    ! [X2,X1,X0] : (? [X3] : ((! [X4,X5] : (k4_tarski(X4,X5) != X3 | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X0)) | ~r2_hidden(X3,X2)) & (? [X6,X7] : (k4_tarski(X6,X7) = X3 & r2_hidden(X7,X1) & r2_hidden(X6,X0)) | r2_hidden(X3,X2))) => ((! [X5,X4] : (k4_tarski(X4,X5) != sK1(X0,X1,X2) | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X0)) | ~r2_hidden(sK1(X0,X1,X2),X2)) & (? [X7,X6] : (k4_tarski(X6,X7) = sK1(X0,X1,X2) & r2_hidden(X7,X1) & r2_hidden(X6,X0)) | r2_hidden(sK1(X0,X1,X2),X2))))),
% 11.51/2.00    introduced(choice_axiom,[])).
% 11.51/2.00  
% 11.51/2.00  fof(f17,plain,(
% 11.51/2.00    ! [X0,X1,X2] : ((k2_zfmisc_1(X0,X1) = X2 | ((! [X4,X5] : (k4_tarski(X4,X5) != sK1(X0,X1,X2) | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X0)) | ~r2_hidden(sK1(X0,X1,X2),X2)) & ((k4_tarski(sK2(X0,X1,X2),sK3(X0,X1,X2)) = sK1(X0,X1,X2) & r2_hidden(sK3(X0,X1,X2),X1) & r2_hidden(sK2(X0,X1,X2),X0)) | r2_hidden(sK1(X0,X1,X2),X2)))) & (! [X8] : ((r2_hidden(X8,X2) | ! [X9,X10] : (k4_tarski(X9,X10) != X8 | ~r2_hidden(X10,X1) | ~r2_hidden(X9,X0))) & ((k4_tarski(sK4(X0,X1,X8),sK5(X0,X1,X8)) = X8 & r2_hidden(sK5(X0,X1,X8),X1) & r2_hidden(sK4(X0,X1,X8),X0)) | ~r2_hidden(X8,X2))) | k2_zfmisc_1(X0,X1) != X2))),
% 11.51/2.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4,sK5])],[f13,f16,f15,f14])).
% 11.51/2.00  
% 11.51/2.00  fof(f29,plain,(
% 11.51/2.00    ( ! [X2,X0,X8,X1] : (r2_hidden(sK4(X0,X1,X8),X0) | ~r2_hidden(X8,X2) | k2_zfmisc_1(X0,X1) != X2) )),
% 11.51/2.00    inference(cnf_transformation,[],[f17])).
% 11.51/2.00  
% 11.51/2.00  fof(f47,plain,(
% 11.51/2.00    ( ! [X0,X8,X1] : (r2_hidden(sK4(X0,X1,X8),X0) | ~r2_hidden(X8,k2_zfmisc_1(X0,X1))) )),
% 11.51/2.00    inference(equality_resolution,[],[f29])).
% 11.51/2.00  
% 11.51/2.00  fof(f22,plain,(
% 11.51/2.00    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 11.51/2.00    inference(cnf_transformation,[],[f11])).
% 11.51/2.00  
% 11.51/2.00  fof(f42,plain,(
% 11.51/2.00    ( ! [X4,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,k4_xboole_0(X0,X1))) )),
% 11.51/2.00    inference(equality_resolution,[],[f22])).
% 11.51/2.00  
% 11.51/2.00  fof(f4,conjecture,(
% 11.51/2.00    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 11.51/2.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.51/2.00  
% 11.51/2.00  fof(f5,negated_conjecture,(
% 11.51/2.00    ~! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 11.51/2.00    inference(negated_conjecture,[],[f4])).
% 11.51/2.00  
% 11.51/2.00  fof(f6,plain,(
% 11.51/2.00    ? [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <~> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 11.51/2.00    inference(ennf_transformation,[],[f5])).
% 11.51/2.00  
% 11.51/2.00  fof(f18,plain,(
% 11.51/2.00    ? [X0,X1] : (((k1_xboole_0 != X1 & k1_xboole_0 != X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 = k2_zfmisc_1(X0,X1)))),
% 11.51/2.00    inference(nnf_transformation,[],[f6])).
% 11.51/2.00  
% 11.51/2.00  fof(f19,plain,(
% 11.51/2.00    ? [X0,X1] : (((k1_xboole_0 != X1 & k1_xboole_0 != X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 = k2_zfmisc_1(X0,X1)))),
% 11.51/2.00    inference(flattening,[],[f18])).
% 11.51/2.00  
% 11.51/2.00  fof(f20,plain,(
% 11.51/2.00    ? [X0,X1] : (((k1_xboole_0 != X1 & k1_xboole_0 != X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 = k2_zfmisc_1(X0,X1))) => (((k1_xboole_0 != sK7 & k1_xboole_0 != sK6) | k1_xboole_0 != k2_zfmisc_1(sK6,sK7)) & (k1_xboole_0 = sK7 | k1_xboole_0 = sK6 | k1_xboole_0 = k2_zfmisc_1(sK6,sK7)))),
% 11.51/2.00    introduced(choice_axiom,[])).
% 11.51/2.00  
% 11.51/2.00  fof(f21,plain,(
% 11.51/2.00    ((k1_xboole_0 != sK7 & k1_xboole_0 != sK6) | k1_xboole_0 != k2_zfmisc_1(sK6,sK7)) & (k1_xboole_0 = sK7 | k1_xboole_0 = sK6 | k1_xboole_0 = k2_zfmisc_1(sK6,sK7))),
% 11.51/2.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7])],[f19,f20])).
% 11.51/2.00  
% 11.51/2.00  fof(f37,plain,(
% 11.51/2.00    k1_xboole_0 = sK7 | k1_xboole_0 = sK6 | k1_xboole_0 = k2_zfmisc_1(sK6,sK7)),
% 11.51/2.00    inference(cnf_transformation,[],[f21])).
% 11.51/2.00  
% 11.51/2.00  fof(f32,plain,(
% 11.51/2.00    ( ! [X2,X0,X10,X8,X1,X9] : (r2_hidden(X8,X2) | k4_tarski(X9,X10) != X8 | ~r2_hidden(X10,X1) | ~r2_hidden(X9,X0) | k2_zfmisc_1(X0,X1) != X2) )),
% 11.51/2.00    inference(cnf_transformation,[],[f17])).
% 11.51/2.00  
% 11.51/2.00  fof(f43,plain,(
% 11.51/2.00    ( ! [X2,X0,X10,X1,X9] : (r2_hidden(k4_tarski(X9,X10),X2) | ~r2_hidden(X10,X1) | ~r2_hidden(X9,X0) | k2_zfmisc_1(X0,X1) != X2) )),
% 11.51/2.00    inference(equality_resolution,[],[f32])).
% 11.51/2.00  
% 11.51/2.00  fof(f44,plain,(
% 11.51/2.00    ( ! [X0,X10,X1,X9] : (r2_hidden(k4_tarski(X9,X10),k2_zfmisc_1(X0,X1)) | ~r2_hidden(X10,X1) | ~r2_hidden(X9,X0)) )),
% 11.51/2.00    inference(equality_resolution,[],[f43])).
% 11.51/2.00  
% 11.51/2.00  fof(f38,plain,(
% 11.51/2.00    k1_xboole_0 != sK6 | k1_xboole_0 != k2_zfmisc_1(sK6,sK7)),
% 11.51/2.00    inference(cnf_transformation,[],[f21])).
% 11.51/2.00  
% 11.51/2.00  fof(f39,plain,(
% 11.51/2.00    k1_xboole_0 != sK7 | k1_xboole_0 != k2_zfmisc_1(sK6,sK7)),
% 11.51/2.00    inference(cnf_transformation,[],[f21])).
% 11.51/2.00  
% 11.51/2.00  fof(f30,plain,(
% 11.51/2.00    ( ! [X2,X0,X8,X1] : (r2_hidden(sK5(X0,X1,X8),X1) | ~r2_hidden(X8,X2) | k2_zfmisc_1(X0,X1) != X2) )),
% 11.51/2.00    inference(cnf_transformation,[],[f17])).
% 11.51/2.00  
% 11.51/2.00  fof(f46,plain,(
% 11.51/2.00    ( ! [X0,X8,X1] : (r2_hidden(sK5(X0,X1,X8),X1) | ~r2_hidden(X8,k2_zfmisc_1(X0,X1))) )),
% 11.51/2.00    inference(equality_resolution,[],[f30])).
% 11.51/2.00  
% 11.51/2.00  cnf(c_6,plain,
% 11.51/2.00      ( k4_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
% 11.51/2.00      inference(cnf_transformation,[],[f28]) ).
% 11.51/2.00  
% 11.51/2.00  cnf(c_2,plain,
% 11.51/2.00      ( r2_hidden(sK0(X0,X1,X2),X0)
% 11.51/2.00      | r2_hidden(sK0(X0,X1,X2),X2)
% 11.51/2.00      | k4_xboole_0(X0,X1) = X2 ),
% 11.51/2.00      inference(cnf_transformation,[],[f25]) ).
% 11.51/2.00  
% 11.51/2.00  cnf(c_824,plain,
% 11.51/2.00      ( k4_xboole_0(X0,X1) = X2
% 11.51/2.00      | r2_hidden(sK0(X0,X1,X2),X0) = iProver_top
% 11.51/2.00      | r2_hidden(sK0(X0,X1,X2),X2) = iProver_top ),
% 11.51/2.00      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 11.51/2.00  
% 11.51/2.00  cnf(c_4,negated_conjecture,
% 11.51/2.00      ( ~ r2_hidden(X0,X1) | ~ r2_hidden(X0,k4_xboole_0(X2,X1)) ),
% 11.51/2.00      inference(cnf_transformation,[],[f41]) ).
% 11.51/2.00  
% 11.51/2.00  cnf(c_822,plain,
% 11.51/2.00      ( r2_hidden(X0,X1) != iProver_top
% 11.51/2.00      | r2_hidden(X0,k4_xboole_0(X2,X1)) != iProver_top ),
% 11.51/2.00      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 11.51/2.00  
% 11.51/2.00  cnf(c_1802,plain,
% 11.51/2.00      ( k4_xboole_0(k4_xboole_0(X0,X1),X2) = X3
% 11.51/2.00      | r2_hidden(sK0(k4_xboole_0(X0,X1),X2,X3),X1) != iProver_top
% 11.51/2.00      | r2_hidden(sK0(k4_xboole_0(X0,X1),X2,X3),X3) = iProver_top ),
% 11.51/2.00      inference(superposition,[status(thm)],[c_824,c_822]) ).
% 11.51/2.00  
% 11.51/2.00  cnf(c_2145,plain,
% 11.51/2.00      ( k4_xboole_0(k4_xboole_0(k1_xboole_0,X0),X1) = X2
% 11.51/2.00      | r2_hidden(sK0(k4_xboole_0(k1_xboole_0,X0),X1,X2),X2) = iProver_top
% 11.51/2.00      | r2_hidden(sK0(k1_xboole_0,X1,X2),X0) != iProver_top ),
% 11.51/2.00      inference(superposition,[status(thm)],[c_6,c_1802]) ).
% 11.51/2.00  
% 11.51/2.00  cnf(c_2149,plain,
% 11.51/2.00      ( k4_xboole_0(k1_xboole_0,X0) = X1
% 11.51/2.00      | r2_hidden(sK0(k1_xboole_0,X0,X1),X2) != iProver_top
% 11.51/2.00      | r2_hidden(sK0(k1_xboole_0,X0,X1),X1) = iProver_top ),
% 11.51/2.00      inference(light_normalisation,[status(thm)],[c_2145,c_6]) ).
% 11.51/2.00  
% 11.51/2.00  cnf(c_2150,plain,
% 11.51/2.00      ( k1_xboole_0 = X0
% 11.51/2.00      | r2_hidden(sK0(k1_xboole_0,X1,X0),X2) != iProver_top
% 11.51/2.00      | r2_hidden(sK0(k1_xboole_0,X1,X0),X0) = iProver_top ),
% 11.51/2.00      inference(demodulation,[status(thm)],[c_2149,c_6]) ).
% 11.51/2.00  
% 11.51/2.00  cnf(c_2487,plain,
% 11.51/2.00      ( k4_xboole_0(k1_xboole_0,X0) = X1
% 11.51/2.00      | k1_xboole_0 = X1
% 11.51/2.00      | r2_hidden(sK0(k1_xboole_0,X0,X1),X1) = iProver_top
% 11.51/2.00      | r2_hidden(sK0(k1_xboole_0,X0,X1),k1_xboole_0) = iProver_top ),
% 11.51/2.00      inference(superposition,[status(thm)],[c_824,c_2150]) ).
% 11.51/2.00  
% 11.51/2.00  cnf(c_2493,plain,
% 11.51/2.00      ( k4_xboole_0(k1_xboole_0,X0) = X1
% 11.51/2.00      | k1_xboole_0 = X1
% 11.51/2.00      | r2_hidden(sK0(k1_xboole_0,X0,X1),X1) = iProver_top ),
% 11.51/2.00      inference(forward_subsumption_resolution,[status(thm)],[c_2487,c_2150]) ).
% 11.51/2.00  
% 11.51/2.00  cnf(c_2494,plain,
% 11.51/2.00      ( k1_xboole_0 = X0 | r2_hidden(sK0(k1_xboole_0,X1,X0),X0) = iProver_top ),
% 11.51/2.00      inference(demodulation,[status(thm)],[c_2493,c_6]) ).
% 11.51/2.00  
% 11.51/2.00  cnf(c_14,plain,
% 11.51/2.00      ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) | r2_hidden(sK4(X1,X2,X0),X1) ),
% 11.51/2.00      inference(cnf_transformation,[],[f47]) ).
% 11.51/2.00  
% 11.51/2.00  cnf(c_813,plain,
% 11.51/2.00      ( r2_hidden(X0,k2_zfmisc_1(X1,X2)) != iProver_top
% 11.51/2.00      | r2_hidden(sK4(X1,X2,X0),X1) = iProver_top ),
% 11.51/2.00      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 11.51/2.00  
% 11.51/2.00  cnf(c_5,plain,
% 11.51/2.00      ( r2_hidden(X0,X1) | ~ r2_hidden(X0,k4_xboole_0(X1,X2)) ),
% 11.51/2.00      inference(cnf_transformation,[],[f42]) ).
% 11.51/2.00  
% 11.51/2.00  cnf(c_821,plain,
% 11.51/2.00      ( r2_hidden(X0,X1) = iProver_top
% 11.51/2.00      | r2_hidden(X0,k4_xboole_0(X1,X2)) != iProver_top ),
% 11.51/2.00      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 11.51/2.00  
% 11.51/2.00  cnf(c_1003,plain,
% 11.51/2.00      ( r2_hidden(X0,k2_zfmisc_1(k4_xboole_0(X1,X2),X3)) != iProver_top
% 11.51/2.00      | r2_hidden(sK4(k4_xboole_0(X1,X2),X3,X0),X1) = iProver_top ),
% 11.51/2.00      inference(superposition,[status(thm)],[c_813,c_821]) ).
% 11.51/2.00  
% 11.51/2.00  cnf(c_1004,plain,
% 11.51/2.00      ( r2_hidden(X0,k2_zfmisc_1(k4_xboole_0(X1,X2),X3)) != iProver_top
% 11.51/2.00      | r2_hidden(sK4(k4_xboole_0(X1,X2),X3,X0),X2) != iProver_top ),
% 11.51/2.00      inference(superposition,[status(thm)],[c_813,c_822]) ).
% 11.51/2.00  
% 11.51/2.00  cnf(c_3773,plain,
% 11.51/2.00      ( r2_hidden(X0,k2_zfmisc_1(k4_xboole_0(X1,X1),X2)) != iProver_top ),
% 11.51/2.00      inference(superposition,[status(thm)],[c_1003,c_1004]) ).
% 11.51/2.00  
% 11.51/2.00  cnf(c_3884,plain,
% 11.51/2.00      ( k2_zfmisc_1(k4_xboole_0(X0,X0),X1) = k1_xboole_0 ),
% 11.51/2.00      inference(superposition,[status(thm)],[c_2494,c_3773]) ).
% 11.51/2.00  
% 11.51/2.00  cnf(c_4085,plain,
% 11.51/2.00      ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
% 11.51/2.00      inference(superposition,[status(thm)],[c_6,c_3884]) ).
% 11.51/2.00  
% 11.51/2.00  cnf(c_17,negated_conjecture,
% 11.51/2.00      ( k1_xboole_0 = k2_zfmisc_1(sK6,sK7)
% 11.51/2.00      | k1_xboole_0 = sK6
% 11.51/2.00      | k1_xboole_0 = sK7 ),
% 11.51/2.00      inference(cnf_transformation,[],[f37]) ).
% 11.51/2.00  
% 11.51/2.00  cnf(c_11,plain,
% 11.51/2.00      ( ~ r2_hidden(X0,X1)
% 11.51/2.00      | ~ r2_hidden(X2,X3)
% 11.51/2.00      | r2_hidden(k4_tarski(X2,X0),k2_zfmisc_1(X3,X1)) ),
% 11.51/2.00      inference(cnf_transformation,[],[f44]) ).
% 11.51/2.00  
% 11.51/2.00  cnf(c_816,plain,
% 11.51/2.00      ( r2_hidden(X0,X1) != iProver_top
% 11.51/2.00      | r2_hidden(X2,X3) != iProver_top
% 11.51/2.00      | r2_hidden(k4_tarski(X2,X0),k2_zfmisc_1(X3,X1)) = iProver_top ),
% 11.51/2.00      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 11.51/2.00  
% 11.51/2.00  cnf(c_1111,plain,
% 11.51/2.00      ( sK6 = k1_xboole_0
% 11.51/2.00      | sK7 = k1_xboole_0
% 11.51/2.00      | r2_hidden(X0,sK6) != iProver_top
% 11.51/2.00      | r2_hidden(X1,sK7) != iProver_top
% 11.51/2.00      | r2_hidden(k4_tarski(X0,X1),k1_xboole_0) = iProver_top ),
% 11.51/2.00      inference(superposition,[status(thm)],[c_17,c_816]) ).
% 11.51/2.00  
% 11.51/2.00  cnf(c_985,plain,
% 11.51/2.00      ( r2_hidden(X0,X1) != iProver_top
% 11.51/2.00      | r2_hidden(X0,k1_xboole_0) != iProver_top ),
% 11.51/2.00      inference(superposition,[status(thm)],[c_6,c_822]) ).
% 11.51/2.00  
% 11.51/2.00  cnf(c_1112,plain,
% 11.51/2.00      ( r2_hidden(X0,X1) != iProver_top
% 11.51/2.00      | r2_hidden(X2,X3) != iProver_top
% 11.51/2.00      | r2_hidden(k4_tarski(X2,X0),k1_xboole_0) != iProver_top ),
% 11.51/2.00      inference(superposition,[status(thm)],[c_816,c_985]) ).
% 11.51/2.00  
% 11.51/2.00  cnf(c_1131,plain,
% 11.51/2.00      ( sK6 = k1_xboole_0
% 11.51/2.00      | sK7 = k1_xboole_0
% 11.51/2.00      | r2_hidden(X0,sK6) != iProver_top
% 11.51/2.00      | r2_hidden(X1,sK7) != iProver_top ),
% 11.51/2.00      inference(forward_subsumption_resolution,[status(thm)],[c_1111,c_1112]) ).
% 11.51/2.00  
% 11.51/2.00  cnf(c_2510,plain,
% 11.51/2.00      ( sK6 = k1_xboole_0
% 11.51/2.00      | sK7 = k1_xboole_0
% 11.51/2.00      | r2_hidden(X0,sK6) != iProver_top ),
% 11.51/2.00      inference(superposition,[status(thm)],[c_2494,c_1131]) ).
% 11.51/2.00  
% 11.51/2.00  cnf(c_3710,plain,
% 11.51/2.00      ( sK6 = k1_xboole_0 | sK7 = k1_xboole_0 ),
% 11.51/2.00      inference(superposition,[status(thm)],[c_2494,c_2510]) ).
% 11.51/2.00  
% 11.51/2.00  cnf(c_16,negated_conjecture,
% 11.51/2.00      ( k1_xboole_0 != k2_zfmisc_1(sK6,sK7) | k1_xboole_0 != sK6 ),
% 11.51/2.00      inference(cnf_transformation,[],[f38]) ).
% 11.51/2.00  
% 11.51/2.00  cnf(c_3836,plain,
% 11.51/2.00      ( k2_zfmisc_1(k1_xboole_0,sK7) != k1_xboole_0
% 11.51/2.00      | sK6 != k1_xboole_0
% 11.51/2.00      | sK7 = k1_xboole_0 ),
% 11.51/2.00      inference(superposition,[status(thm)],[c_3710,c_16]) ).
% 11.51/2.00  
% 11.51/2.00  cnf(c_3841,plain,
% 11.51/2.00      ( k2_zfmisc_1(k1_xboole_0,sK7) != k1_xboole_0 | sK7 = k1_xboole_0 ),
% 11.51/2.00      inference(forward_subsumption_resolution,[status(thm)],[c_3836,c_3710]) ).
% 11.51/2.00  
% 11.51/2.00  cnf(c_4105,plain,
% 11.51/2.00      ( sK7 = k1_xboole_0 | k1_xboole_0 != k1_xboole_0 ),
% 11.51/2.00      inference(demodulation,[status(thm)],[c_4085,c_3841]) ).
% 11.51/2.00  
% 11.51/2.00  cnf(c_4106,plain,
% 11.51/2.00      ( sK7 = k1_xboole_0 ),
% 11.51/2.00      inference(equality_resolution_simp,[status(thm)],[c_4105]) ).
% 11.51/2.00  
% 11.51/2.00  cnf(c_15,negated_conjecture,
% 11.51/2.00      ( k1_xboole_0 != k2_zfmisc_1(sK6,sK7) | k1_xboole_0 != sK7 ),
% 11.51/2.00      inference(cnf_transformation,[],[f39]) ).
% 11.51/2.00  
% 11.51/2.00  cnf(c_45733,plain,
% 11.51/2.00      ( k2_zfmisc_1(sK6,k1_xboole_0) != k1_xboole_0
% 11.51/2.00      | k1_xboole_0 != k1_xboole_0 ),
% 11.51/2.00      inference(demodulation,[status(thm)],[c_4106,c_15]) ).
% 11.51/2.00  
% 11.51/2.00  cnf(c_45734,plain,
% 11.51/2.00      ( k2_zfmisc_1(sK6,k1_xboole_0) != k1_xboole_0 ),
% 11.51/2.00      inference(equality_resolution_simp,[status(thm)],[c_45733]) ).
% 11.51/2.00  
% 11.51/2.00  cnf(c_13,plain,
% 11.51/2.00      ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) | r2_hidden(sK5(X1,X2,X0),X2) ),
% 11.51/2.00      inference(cnf_transformation,[],[f46]) ).
% 11.51/2.00  
% 11.51/2.00  cnf(c_814,plain,
% 11.51/2.00      ( r2_hidden(X0,k2_zfmisc_1(X1,X2)) != iProver_top
% 11.51/2.00      | r2_hidden(sK5(X1,X2,X0),X2) = iProver_top ),
% 11.51/2.00      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 11.51/2.00  
% 11.51/2.00  cnf(c_1035,plain,
% 11.51/2.00      ( r2_hidden(X0,k2_zfmisc_1(X1,X2)) != iProver_top
% 11.51/2.00      | r2_hidden(sK5(X1,X2,X0),k1_xboole_0) != iProver_top ),
% 11.51/2.00      inference(superposition,[status(thm)],[c_814,c_985]) ).
% 11.51/2.00  
% 11.51/2.00  cnf(c_1371,plain,
% 11.51/2.00      ( r2_hidden(X0,k2_zfmisc_1(X1,k1_xboole_0)) != iProver_top ),
% 11.51/2.00      inference(superposition,[status(thm)],[c_814,c_1035]) ).
% 11.51/2.00  
% 11.51/2.00  cnf(c_4148,plain,
% 11.51/2.00      ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
% 11.51/2.00      inference(superposition,[status(thm)],[c_2494,c_1371]) ).
% 11.51/2.00  
% 11.51/2.00  cnf(c_45736,plain,
% 11.51/2.00      ( k1_xboole_0 != k1_xboole_0 ),
% 11.51/2.00      inference(demodulation,[status(thm)],[c_45734,c_4148]) ).
% 11.51/2.00  
% 11.51/2.00  cnf(c_45737,plain,
% 11.51/2.00      ( $false ),
% 11.51/2.00      inference(equality_resolution_simp,[status(thm)],[c_45736]) ).
% 11.51/2.00  
% 11.51/2.00  
% 11.51/2.00  % SZS output end CNFRefutation for theBenchmark.p
% 11.51/2.00  
% 11.51/2.00  ------                               Statistics
% 11.51/2.00  
% 11.51/2.00  ------ Selected
% 11.51/2.00  
% 11.51/2.00  total_time:                             1.298
% 11.51/2.00  
%------------------------------------------------------------------------------
