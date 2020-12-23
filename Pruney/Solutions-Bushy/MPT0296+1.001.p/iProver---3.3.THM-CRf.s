%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0296+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:42:57 EST 2020

% Result     : Theorem 2.43s
% Output     : CNFRefutation 2.43s
% Verified   : 
% Statistics : Number of formulae       :   78 ( 297 expanded)
%              Number of clauses        :   42 (  82 expanded)
%              Number of leaves         :    9 (  74 expanded)
%              Depth                    :   15
%              Number of atoms          :  309 (1965 expanded)
%              Number of equality atoms :  118 ( 526 expanded)
%              Maximal formula depth    :   14 (   6 average)
%              Maximal clause size      :   18 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f4,conjecture,(
    ! [X0,X1,X2,X3,X4] :
      ~ ( ! [X5,X6] :
            ~ ( r2_hidden(X6,k3_xboole_0(X2,X4))
              & r2_hidden(X5,k3_xboole_0(X1,X3))
              & k4_tarski(X5,X6) = X0 )
        & r2_hidden(X0,k3_xboole_0(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X3,X4))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f5,negated_conjecture,(
    ~ ! [X0,X1,X2,X3,X4] :
        ~ ( ! [X5,X6] :
              ~ ( r2_hidden(X6,k3_xboole_0(X2,X4))
                & r2_hidden(X5,k3_xboole_0(X1,X3))
                & k4_tarski(X5,X6) = X0 )
          & r2_hidden(X0,k3_xboole_0(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X3,X4))) ) ),
    inference(negated_conjecture,[],[f4])).

fof(f7,plain,(
    ? [X0,X1,X2,X3,X4] :
      ( ! [X5,X6] :
          ( ~ r2_hidden(X6,k3_xboole_0(X2,X4))
          | ~ r2_hidden(X5,k3_xboole_0(X1,X3))
          | k4_tarski(X5,X6) != X0 )
      & r2_hidden(X0,k3_xboole_0(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X3,X4))) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f19,plain,
    ( ? [X0,X1,X2,X3,X4] :
        ( ! [X5,X6] :
            ( ~ r2_hidden(X6,k3_xboole_0(X2,X4))
            | ~ r2_hidden(X5,k3_xboole_0(X1,X3))
            | k4_tarski(X5,X6) != X0 )
        & r2_hidden(X0,k3_xboole_0(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X3,X4))) )
   => ( ! [X6,X5] :
          ( ~ r2_hidden(X6,k3_xboole_0(sK8,sK10))
          | ~ r2_hidden(X5,k3_xboole_0(sK7,sK9))
          | k4_tarski(X5,X6) != sK6 )
      & r2_hidden(sK6,k3_xboole_0(k2_zfmisc_1(sK7,sK8),k2_zfmisc_1(sK9,sK10))) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,
    ( ! [X5,X6] :
        ( ~ r2_hidden(X6,k3_xboole_0(sK8,sK10))
        | ~ r2_hidden(X5,k3_xboole_0(sK7,sK9))
        | k4_tarski(X5,X6) != sK6 )
    & r2_hidden(sK6,k3_xboole_0(k2_zfmisc_1(sK7,sK8),k2_zfmisc_1(sK9,sK10))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7,sK8,sK9,sK10])],[f7,f19])).

fof(f37,plain,(
    r2_hidden(sK6,k3_xboole_0(k2_zfmisc_1(sK7,sK8),k2_zfmisc_1(sK9,sK10))) ),
    inference(cnf_transformation,[],[f20])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
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
    inference(nnf_transformation,[],[f2])).

fof(f15,plain,(
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
    inference(flattening,[],[f14])).

fof(f16,plain,(
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
    inference(rectify,[],[f15])).

fof(f17,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ~ r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( ~ r2_hidden(sK5(X0,X1,X2),X1)
          | ~ r2_hidden(sK5(X0,X1,X2),X0)
          | ~ r2_hidden(sK5(X0,X1,X2),X2) )
        & ( ( r2_hidden(sK5(X0,X1,X2),X1)
            & r2_hidden(sK5(X0,X1,X2),X0) )
          | r2_hidden(sK5(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ( ( ~ r2_hidden(sK5(X0,X1,X2),X1)
            | ~ r2_hidden(sK5(X0,X1,X2),X0)
            | ~ r2_hidden(sK5(X0,X1,X2),X2) )
          & ( ( r2_hidden(sK5(X0,X1,X2),X1)
              & r2_hidden(sK5(X0,X1,X2),X0) )
            | r2_hidden(sK5(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f16,f17])).

fof(f30,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f18])).

fof(f45,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X1)
      | ~ r2_hidden(X4,k3_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f30])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( k2_zfmisc_1(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ? [X4,X5] :
              ( k4_tarski(X4,X5) = X3
              & r2_hidden(X5,X1)
              & r2_hidden(X4,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f8,plain,(
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
    inference(nnf_transformation,[],[f1])).

fof(f9,plain,(
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
    inference(rectify,[],[f8])).

fof(f12,plain,(
    ! [X8,X1,X0] :
      ( ? [X11,X12] :
          ( k4_tarski(X11,X12) = X8
          & r2_hidden(X12,X1)
          & r2_hidden(X11,X0) )
     => ( k4_tarski(sK3(X0,X1,X8),sK4(X0,X1,X8)) = X8
        & r2_hidden(sK4(X0,X1,X8),X1)
        & r2_hidden(sK3(X0,X1,X8),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f11,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X6,X7] :
          ( k4_tarski(X6,X7) = X3
          & r2_hidden(X7,X1)
          & r2_hidden(X6,X0) )
     => ( k4_tarski(sK1(X0,X1,X2),sK2(X0,X1,X2)) = X3
        & r2_hidden(sK2(X0,X1,X2),X1)
        & r2_hidden(sK1(X0,X1,X2),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f10,plain,(
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
              ( k4_tarski(X4,X5) != sK0(X0,X1,X2)
              | ~ r2_hidden(X5,X1)
              | ~ r2_hidden(X4,X0) )
          | ~ r2_hidden(sK0(X0,X1,X2),X2) )
        & ( ? [X7,X6] :
              ( k4_tarski(X6,X7) = sK0(X0,X1,X2)
              & r2_hidden(X7,X1)
              & r2_hidden(X6,X0) )
          | r2_hidden(sK0(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( ( k2_zfmisc_1(X0,X1) = X2
        | ( ( ! [X4,X5] :
                ( k4_tarski(X4,X5) != sK0(X0,X1,X2)
                | ~ r2_hidden(X5,X1)
                | ~ r2_hidden(X4,X0) )
            | ~ r2_hidden(sK0(X0,X1,X2),X2) )
          & ( ( k4_tarski(sK1(X0,X1,X2),sK2(X0,X1,X2)) = sK0(X0,X1,X2)
              & r2_hidden(sK2(X0,X1,X2),X1)
              & r2_hidden(sK1(X0,X1,X2),X0) )
            | r2_hidden(sK0(X0,X1,X2),X2) ) ) )
      & ( ! [X8] :
            ( ( r2_hidden(X8,X2)
              | ! [X9,X10] :
                  ( k4_tarski(X9,X10) != X8
                  | ~ r2_hidden(X10,X1)
                  | ~ r2_hidden(X9,X0) ) )
            & ( ( k4_tarski(sK3(X0,X1,X8),sK4(X0,X1,X8)) = X8
                & r2_hidden(sK4(X0,X1,X8),X1)
                & r2_hidden(sK3(X0,X1,X8),X0) )
              | ~ r2_hidden(X8,X2) ) )
        | k2_zfmisc_1(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f9,f12,f11,f10])).

fof(f23,plain,(
    ! [X2,X0,X8,X1] :
      ( k4_tarski(sK3(X0,X1,X8),sK4(X0,X1,X8)) = X8
      | ~ r2_hidden(X8,X2)
      | k2_zfmisc_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f13])).

fof(f41,plain,(
    ! [X0,X8,X1] :
      ( k4_tarski(sK3(X0,X1,X8),sK4(X0,X1,X8)) = X8
      | ~ r2_hidden(X8,k2_zfmisc_1(X0,X1)) ) ),
    inference(equality_resolution,[],[f23])).

fof(f29,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f18])).

fof(f46,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,k3_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f29])).

fof(f3,axiom,(
    ! [X0,X1,X2,X3] :
      ( k4_tarski(X0,X1) = k4_tarski(X2,X3)
     => ( X1 = X3
        & X0 = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f6,plain,(
    ! [X0,X1,X2,X3] :
      ( ( X1 = X3
        & X0 = X2 )
      | k4_tarski(X0,X1) != k4_tarski(X2,X3) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f35,plain,(
    ! [X2,X0,X3,X1] :
      ( X0 = X2
      | k4_tarski(X0,X1) != k4_tarski(X2,X3) ) ),
    inference(cnf_transformation,[],[f6])).

fof(f21,plain,(
    ! [X2,X0,X8,X1] :
      ( r2_hidden(sK3(X0,X1,X8),X0)
      | ~ r2_hidden(X8,X2)
      | k2_zfmisc_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f13])).

fof(f43,plain,(
    ! [X0,X8,X1] :
      ( r2_hidden(sK3(X0,X1,X8),X0)
      | ~ r2_hidden(X8,k2_zfmisc_1(X0,X1)) ) ),
    inference(equality_resolution,[],[f21])).

fof(f36,plain,(
    ! [X2,X0,X3,X1] :
      ( X1 = X3
      | k4_tarski(X0,X1) != k4_tarski(X2,X3) ) ),
    inference(cnf_transformation,[],[f6])).

fof(f22,plain,(
    ! [X2,X0,X8,X1] :
      ( r2_hidden(sK4(X0,X1,X8),X1)
      | ~ r2_hidden(X8,X2)
      | k2_zfmisc_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f13])).

fof(f42,plain,(
    ! [X0,X8,X1] :
      ( r2_hidden(sK4(X0,X1,X8),X1)
      | ~ r2_hidden(X8,k2_zfmisc_1(X0,X1)) ) ),
    inference(equality_resolution,[],[f22])).

fof(f31,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f18])).

fof(f44,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k3_xboole_0(X0,X1))
      | ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f31])).

fof(f38,plain,(
    ! [X6,X5] :
      ( ~ r2_hidden(X6,k3_xboole_0(sK8,sK10))
      | ~ r2_hidden(X5,k3_xboole_0(sK7,sK9))
      | k4_tarski(X5,X6) != sK6 ) ),
    inference(cnf_transformation,[],[f20])).

cnf(c_17,negated_conjecture,
    ( r2_hidden(sK6,k3_xboole_0(k2_zfmisc_1(sK7,sK8),k2_zfmisc_1(sK9,sK10))) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_445,plain,
    ( r2_hidden(sK6,k3_xboole_0(k2_zfmisc_1(sK7,sK8),k2_zfmisc_1(sK9,sK10))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_12,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k3_xboole_0(X2,X1)) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_448,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r2_hidden(X0,k3_xboole_0(X2,X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_900,plain,
    ( r2_hidden(sK6,k2_zfmisc_1(sK9,sK10)) = iProver_top ),
    inference(superposition,[status(thm)],[c_445,c_448])).

cnf(c_5,plain,
    ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
    | k4_tarski(sK3(X1,X2,X0),sK4(X1,X2,X0)) = X0 ),
    inference(cnf_transformation,[],[f41])).

cnf(c_455,plain,
    ( k4_tarski(sK3(X0,X1,X2),sK4(X0,X1,X2)) = X2
    | r2_hidden(X2,k2_zfmisc_1(X0,X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_1841,plain,
    ( k4_tarski(sK3(sK9,sK10,sK6),sK4(sK9,sK10,sK6)) = sK6 ),
    inference(superposition,[status(thm)],[c_900,c_455])).

cnf(c_13,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k3_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_447,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r2_hidden(X0,k3_xboole_0(X1,X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_798,plain,
    ( r2_hidden(sK6,k2_zfmisc_1(sK7,sK8)) = iProver_top ),
    inference(superposition,[status(thm)],[c_445,c_447])).

cnf(c_1460,plain,
    ( k4_tarski(sK3(sK7,sK8,sK6),sK4(sK7,sK8,sK6)) = sK6 ),
    inference(superposition,[status(thm)],[c_798,c_455])).

cnf(c_15,plain,
    ( X0 = X1
    | k4_tarski(X0,X2) != k4_tarski(X1,X3) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_1846,plain,
    ( sK3(sK7,sK8,sK6) = X0
    | k4_tarski(X0,X1) != sK6 ),
    inference(superposition,[status(thm)],[c_1460,c_15])).

cnf(c_2942,plain,
    ( sK3(sK7,sK8,sK6) = sK3(sK9,sK10,sK6) ),
    inference(superposition,[status(thm)],[c_1841,c_1846])).

cnf(c_7,plain,
    ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
    | r2_hidden(sK3(X1,X2,X0),X1) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_453,plain,
    ( r2_hidden(X0,k2_zfmisc_1(X1,X2)) != iProver_top
    | r2_hidden(sK3(X1,X2,X0),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_3731,plain,
    ( r2_hidden(sK3(sK7,sK8,sK6),sK9) = iProver_top
    | r2_hidden(sK6,k2_zfmisc_1(sK9,sK10)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2942,c_453])).

cnf(c_14,plain,
    ( X0 = X1
    | k4_tarski(X2,X0) != k4_tarski(X3,X1) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_1845,plain,
    ( sK4(sK7,sK8,sK6) = X0
    | k4_tarski(X1,X0) != sK6 ),
    inference(superposition,[status(thm)],[c_1460,c_14])).

cnf(c_2526,plain,
    ( sK4(sK7,sK8,sK6) = sK4(sK9,sK10,sK6) ),
    inference(superposition,[status(thm)],[c_1841,c_1845])).

cnf(c_6,plain,
    ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
    | r2_hidden(sK4(X1,X2,X0),X2) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_454,plain,
    ( r2_hidden(X0,k2_zfmisc_1(X1,X2)) != iProver_top
    | r2_hidden(sK4(X1,X2,X0),X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_3311,plain,
    ( r2_hidden(sK4(sK7,sK8,sK6),sK10) = iProver_top
    | r2_hidden(sK6,k2_zfmisc_1(sK9,sK10)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2526,c_454])).

cnf(c_11,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X0,X2)
    | r2_hidden(X0,k3_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_449,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,X2) != iProver_top
    | r2_hidden(X0,k3_xboole_0(X1,X2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_16,negated_conjecture,
    ( ~ r2_hidden(X0,k3_xboole_0(sK7,sK9))
    | ~ r2_hidden(X1,k3_xboole_0(sK8,sK10))
    | k4_tarski(X0,X1) != sK6 ),
    inference(cnf_transformation,[],[f38])).

cnf(c_446,plain,
    ( k4_tarski(X0,X1) != sK6
    | r2_hidden(X0,k3_xboole_0(sK7,sK9)) != iProver_top
    | r2_hidden(X1,k3_xboole_0(sK8,sK10)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_1844,plain,
    ( r2_hidden(sK4(sK7,sK8,sK6),k3_xboole_0(sK8,sK10)) != iProver_top
    | r2_hidden(sK3(sK7,sK8,sK6),k3_xboole_0(sK7,sK9)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1460,c_446])).

cnf(c_2115,plain,
    ( r2_hidden(sK4(sK7,sK8,sK6),sK10) != iProver_top
    | r2_hidden(sK4(sK7,sK8,sK6),sK8) != iProver_top
    | r2_hidden(sK3(sK7,sK8,sK6),k3_xboole_0(sK7,sK9)) != iProver_top ),
    inference(superposition,[status(thm)],[c_449,c_1844])).

cnf(c_18,plain,
    ( r2_hidden(sK6,k3_xboole_0(k2_zfmisc_1(sK7,sK8),k2_zfmisc_1(sK9,sK10))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_593,plain,
    ( ~ r2_hidden(sK6,k3_xboole_0(k2_zfmisc_1(sK7,sK8),k2_zfmisc_1(sK9,sK10)))
    | r2_hidden(sK6,k2_zfmisc_1(sK7,sK8)) ),
    inference(instantiation,[status(thm)],[c_13])).

cnf(c_594,plain,
    ( r2_hidden(sK6,k3_xboole_0(k2_zfmisc_1(sK7,sK8),k2_zfmisc_1(sK9,sK10))) != iProver_top
    | r2_hidden(sK6,k2_zfmisc_1(sK7,sK8)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_593])).

cnf(c_664,plain,
    ( r2_hidden(sK4(sK7,sK8,sK6),sK8)
    | ~ r2_hidden(sK6,k2_zfmisc_1(sK7,sK8)) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_665,plain,
    ( r2_hidden(sK4(sK7,sK8,sK6),sK8) = iProver_top
    | r2_hidden(sK6,k2_zfmisc_1(sK7,sK8)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_664])).

cnf(c_2332,plain,
    ( r2_hidden(sK4(sK7,sK8,sK6),sK10) != iProver_top
    | r2_hidden(sK3(sK7,sK8,sK6),k3_xboole_0(sK7,sK9)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2115,c_18,c_594,c_665])).

cnf(c_2338,plain,
    ( r2_hidden(sK4(sK7,sK8,sK6),sK10) != iProver_top
    | r2_hidden(sK3(sK7,sK8,sK6),sK9) != iProver_top
    | r2_hidden(sK3(sK7,sK8,sK6),sK7) != iProver_top ),
    inference(superposition,[status(thm)],[c_449,c_2332])).

cnf(c_663,plain,
    ( r2_hidden(sK3(sK7,sK8,sK6),sK7)
    | ~ r2_hidden(sK6,k2_zfmisc_1(sK7,sK8)) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_667,plain,
    ( r2_hidden(sK3(sK7,sK8,sK6),sK7) = iProver_top
    | r2_hidden(sK6,k2_zfmisc_1(sK7,sK8)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_663])).

cnf(c_590,plain,
    ( ~ r2_hidden(sK6,k3_xboole_0(k2_zfmisc_1(sK7,sK8),k2_zfmisc_1(sK9,sK10)))
    | r2_hidden(sK6,k2_zfmisc_1(sK9,sK10)) ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_591,plain,
    ( r2_hidden(sK6,k3_xboole_0(k2_zfmisc_1(sK7,sK8),k2_zfmisc_1(sK9,sK10))) != iProver_top
    | r2_hidden(sK6,k2_zfmisc_1(sK9,sK10)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_590])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_3731,c_3311,c_2338,c_667,c_594,c_591,c_18])).


%------------------------------------------------------------------------------
