%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:36:52 EST 2020

% Result     : Theorem 2.14s
% Output     : CNFRefutation 2.14s
% Verified   : 
% Statistics : Number of formulae       :   89 ( 399 expanded)
%              Number of clauses        :   46 ( 129 expanded)
%              Number of leaves         :   11 (  86 expanded)
%              Depth                    :   19
%              Number of atoms          :  324 (1794 expanded)
%              Number of equality atoms :  124 ( 541 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal clause size      :   18 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
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

fof(f19,plain,(
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

fof(f20,plain,(
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
    inference(rectify,[],[f19])).

fof(f23,plain,(
    ! [X8,X1,X0] :
      ( ? [X11,X12] :
          ( k4_tarski(X11,X12) = X8
          & r2_hidden(X12,X1)
          & r2_hidden(X11,X0) )
     => ( k4_tarski(sK5(X0,X1,X8),sK6(X0,X1,X8)) = X8
        & r2_hidden(sK6(X0,X1,X8),X1)
        & r2_hidden(sK5(X0,X1,X8),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X6,X7] :
          ( k4_tarski(X6,X7) = X3
          & r2_hidden(X7,X1)
          & r2_hidden(X6,X0) )
     => ( k4_tarski(sK3(X0,X1,X2),sK4(X0,X1,X2)) = X3
        & r2_hidden(sK4(X0,X1,X2),X1)
        & r2_hidden(sK3(X0,X1,X2),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
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

fof(f24,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5,sK6])],[f20,f23,f22,f21])).

fof(f36,plain,(
    ! [X2,X0,X8,X1] :
      ( r2_hidden(sK6(X0,X1,X8),X1)
      | ~ r2_hidden(X8,X2)
      | k2_zfmisc_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f24])).

fof(f52,plain,(
    ! [X0,X8,X1] :
      ( r2_hidden(sK6(X0,X1,X8),X1)
      | ~ r2_hidden(X8,k2_zfmisc_1(X0,X1)) ) ),
    inference(equality_resolution,[],[f36])).

fof(f35,plain,(
    ! [X2,X0,X8,X1] :
      ( r2_hidden(sK5(X0,X1,X8),X0)
      | ~ r2_hidden(X8,X2)
      | k2_zfmisc_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f24])).

fof(f53,plain,(
    ! [X0,X8,X1] :
      ( r2_hidden(sK5(X0,X1,X8),X0)
      | ~ r2_hidden(X8,k2_zfmisc_1(X0,X1)) ) ),
    inference(equality_resolution,[],[f35])).

fof(f6,conjecture,(
    ! [X0,X1,X2,X3] :
      ~ ( ! [X4,X5] :
            ~ ( k4_tarski(X4,X5) = X3
              & r2_hidden(X5,X2)
              & r2_hidden(X4,X1) )
        & r2_hidden(X3,X0)
        & r1_tarski(X0,k2_zfmisc_1(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f7,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ~ ( ! [X4,X5] :
              ~ ( k4_tarski(X4,X5) = X3
                & r2_hidden(X5,X2)
                & r2_hidden(X4,X1) )
          & r2_hidden(X3,X0)
          & r1_tarski(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f12,plain,(
    ? [X0,X1,X2,X3] :
      ( ! [X4,X5] :
          ( k4_tarski(X4,X5) != X3
          | ~ r2_hidden(X5,X2)
          | ~ r2_hidden(X4,X1) )
      & r2_hidden(X3,X0)
      & r1_tarski(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f25,plain,
    ( ? [X0,X1,X2,X3] :
        ( ! [X4,X5] :
            ( k4_tarski(X4,X5) != X3
            | ~ r2_hidden(X5,X2)
            | ~ r2_hidden(X4,X1) )
        & r2_hidden(X3,X0)
        & r1_tarski(X0,k2_zfmisc_1(X1,X2)) )
   => ( ! [X5,X4] :
          ( k4_tarski(X4,X5) != sK10
          | ~ r2_hidden(X5,sK9)
          | ~ r2_hidden(X4,sK8) )
      & r2_hidden(sK10,sK7)
      & r1_tarski(sK7,k2_zfmisc_1(sK8,sK9)) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,
    ( ! [X4,X5] :
        ( k4_tarski(X4,X5) != sK10
        | ~ r2_hidden(X5,sK9)
        | ~ r2_hidden(X4,sK8) )
    & r2_hidden(sK10,sK7)
    & r1_tarski(sK7,k2_zfmisc_1(sK8,sK9)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7,sK8,sK9,sK10])],[f12,f25])).

fof(f44,plain,(
    r2_hidden(sK10,sK7) ),
    inference(cnf_transformation,[],[f26])).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f8,plain,(
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

fof(f9,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f13,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
     => ( r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f14,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ( r2_hidden(sK0(X0,X1),X1)
          & r2_hidden(sK0(X0,X1),X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f9,f13])).

fof(f28,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK0(X0,X1),X1)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ? [X2] :
            ( ( X0 != X2
              | ~ r2_hidden(X2,X1) )
            & ( X0 = X2
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | X0 != X2 )
            & ( X0 = X2
              | ~ r2_hidden(X2,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ? [X2] :
            ( ( X0 != X2
              | ~ r2_hidden(X2,X1) )
            & ( X0 = X2
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(rectify,[],[f15])).

fof(f17,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( X0 != X2
            | ~ r2_hidden(X2,X1) )
          & ( X0 = X2
            | r2_hidden(X2,X1) ) )
     => ( ( sK1(X0,X1) != X0
          | ~ r2_hidden(sK1(X0,X1),X1) )
        & ( sK1(X0,X1) = X0
          | r2_hidden(sK1(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ( ( sK1(X0,X1) != X0
            | ~ r2_hidden(sK1(X0,X1),X1) )
          & ( sK1(X0,X1) = X0
            | r2_hidden(sK1(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f16,f17])).

fof(f31,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f18])).

fof(f48,plain,(
    ! [X0,X3] :
      ( X0 = X3
      | ~ r2_hidden(X3,k1_tarski(X0)) ) ),
    inference(equality_resolution,[],[f31])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_xboole_0(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f10,plain,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f11,plain,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f10])).

fof(f30,plain,(
    ! [X2,X0,X1] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f43,plain,(
    r1_tarski(sK7,k2_zfmisc_1(sK8,sK9)) ),
    inference(cnf_transformation,[],[f26])).

fof(f32,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | X0 != X3
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f18])).

fof(f46,plain,(
    ! [X3,X1] :
      ( r2_hidden(X3,X1)
      | k1_tarski(X3) != X1 ) ),
    inference(equality_resolution,[],[f32])).

fof(f47,plain,(
    ! [X3] : r2_hidden(X3,k1_tarski(X3)) ),
    inference(equality_resolution,[],[f46])).

fof(f29,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f27,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK0(X0,X1),X0)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f37,plain,(
    ! [X2,X0,X8,X1] :
      ( k4_tarski(sK5(X0,X1,X8),sK6(X0,X1,X8)) = X8
      | ~ r2_hidden(X8,X2)
      | k2_zfmisc_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f24])).

fof(f51,plain,(
    ! [X0,X8,X1] :
      ( k4_tarski(sK5(X0,X1,X8),sK6(X0,X1,X8)) = X8
      | ~ r2_hidden(X8,k2_zfmisc_1(X0,X1)) ) ),
    inference(equality_resolution,[],[f37])).

fof(f45,plain,(
    ! [X4,X5] :
      ( k4_tarski(X4,X5) != sK10
      | ~ r2_hidden(X5,sK9)
      | ~ r2_hidden(X4,sK8) ) ),
    inference(cnf_transformation,[],[f26])).

cnf(c_14,plain,
    ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
    | r2_hidden(sK6(X1,X2,X0),X2) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_660,plain,
    ( r2_hidden(X0,k2_zfmisc_1(X1,X2)) != iProver_top
    | r2_hidden(sK6(X1,X2,X0),X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_15,plain,
    ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
    | r2_hidden(sK5(X1,X2,X0),X1) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_659,plain,
    ( r2_hidden(X0,k2_zfmisc_1(X1,X2)) != iProver_top
    | r2_hidden(sK5(X1,X2,X0),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_17,negated_conjecture,
    ( r2_hidden(sK10,sK7) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_657,plain,
    ( r2_hidden(sK10,sK7) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_1,plain,
    ( r2_hidden(sK0(X0,X1),X1)
    | r1_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f28])).

cnf(c_672,plain,
    ( r2_hidden(sK0(X0,X1),X1) = iProver_top
    | r1_xboole_0(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_7,plain,
    ( ~ r2_hidden(X0,k1_tarski(X1))
    | X0 = X1 ),
    inference(cnf_transformation,[],[f48])).

cnf(c_667,plain,
    ( X0 = X1
    | r2_hidden(X0,k1_tarski(X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_1252,plain,
    ( sK0(X0,k1_tarski(X1)) = X1
    | r1_xboole_0(X0,k1_tarski(X1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_672,c_667])).

cnf(c_3,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_xboole_0(X1,X2)
    | r1_xboole_0(X0,X2) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_18,negated_conjecture,
    ( r1_tarski(sK7,k2_zfmisc_1(sK8,sK9)) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_214,plain,
    ( ~ r1_xboole_0(X0,X1)
    | r1_xboole_0(X2,X1)
    | k2_zfmisc_1(sK8,sK9) != X0
    | sK7 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_3,c_18])).

cnf(c_215,plain,
    ( ~ r1_xboole_0(k2_zfmisc_1(sK8,sK9),X0)
    | r1_xboole_0(sK7,X0) ),
    inference(unflattening,[status(thm)],[c_214])).

cnf(c_656,plain,
    ( r1_xboole_0(k2_zfmisc_1(sK8,sK9),X0) != iProver_top
    | r1_xboole_0(sK7,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_215])).

cnf(c_5577,plain,
    ( sK0(k2_zfmisc_1(sK8,sK9),k1_tarski(X0)) = X0
    | r1_xboole_0(sK7,k1_tarski(X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1252,c_656])).

cnf(c_6,plain,
    ( r2_hidden(X0,k1_tarski(X0)) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_668,plain,
    ( r2_hidden(X0,k1_tarski(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_0,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X0,X2)
    | ~ r1_xboole_0(X2,X1) ),
    inference(cnf_transformation,[],[f29])).

cnf(c_673,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,X2) != iProver_top
    | r1_xboole_0(X2,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_1911,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r1_xboole_0(X1,k1_tarski(X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_668,c_673])).

cnf(c_5911,plain,
    ( sK0(k2_zfmisc_1(sK8,sK9),k1_tarski(X0)) = X0
    | r2_hidden(X0,sK7) != iProver_top ),
    inference(superposition,[status(thm)],[c_5577,c_1911])).

cnf(c_6038,plain,
    ( sK0(k2_zfmisc_1(sK8,sK9),k1_tarski(sK10)) = sK10 ),
    inference(superposition,[status(thm)],[c_657,c_5911])).

cnf(c_2,plain,
    ( r2_hidden(sK0(X0,X1),X0)
    | r1_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f27])).

cnf(c_671,plain,
    ( r2_hidden(sK0(X0,X1),X0) = iProver_top
    | r1_xboole_0(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_6125,plain,
    ( r2_hidden(sK10,k2_zfmisc_1(sK8,sK9)) = iProver_top
    | r1_xboole_0(k2_zfmisc_1(sK8,sK9),k1_tarski(sK10)) = iProver_top ),
    inference(superposition,[status(thm)],[c_6038,c_671])).

cnf(c_20,plain,
    ( r2_hidden(sK10,sK7) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_51,plain,
    ( r2_hidden(X0,k1_tarski(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_53,plain,
    ( r2_hidden(sK10,k1_tarski(sK10)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_51])).

cnf(c_812,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k1_tarski(X0))
    | ~ r1_xboole_0(X1,k1_tarski(X0)) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_872,plain,
    ( ~ r2_hidden(sK10,k1_tarski(sK10))
    | ~ r2_hidden(sK10,sK7)
    | ~ r1_xboole_0(sK7,k1_tarski(sK10)) ),
    inference(instantiation,[status(thm)],[c_812])).

cnf(c_873,plain,
    ( r2_hidden(sK10,k1_tarski(sK10)) != iProver_top
    | r2_hidden(sK10,sK7) != iProver_top
    | r1_xboole_0(sK7,k1_tarski(sK10)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_872])).

cnf(c_1023,plain,
    ( ~ r1_xboole_0(k2_zfmisc_1(sK8,sK9),k1_tarski(sK10))
    | r1_xboole_0(sK7,k1_tarski(sK10)) ),
    inference(instantiation,[status(thm)],[c_215])).

cnf(c_1024,plain,
    ( r1_xboole_0(k2_zfmisc_1(sK8,sK9),k1_tarski(sK10)) != iProver_top
    | r1_xboole_0(sK7,k1_tarski(sK10)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1023])).

cnf(c_6423,plain,
    ( r2_hidden(sK10,k2_zfmisc_1(sK8,sK9)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6125,c_20,c_53,c_873,c_1024])).

cnf(c_13,plain,
    ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
    | k4_tarski(sK5(X1,X2,X0),sK6(X1,X2,X0)) = X0 ),
    inference(cnf_transformation,[],[f51])).

cnf(c_661,plain,
    ( k4_tarski(sK5(X0,X1,X2),sK6(X0,X1,X2)) = X2
    | r2_hidden(X2,k2_zfmisc_1(X0,X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_6430,plain,
    ( k4_tarski(sK5(sK8,sK9,sK10),sK6(sK8,sK9,sK10)) = sK10 ),
    inference(superposition,[status(thm)],[c_6423,c_661])).

cnf(c_16,negated_conjecture,
    ( ~ r2_hidden(X0,sK8)
    | ~ r2_hidden(X1,sK9)
    | k4_tarski(X0,X1) != sK10 ),
    inference(cnf_transformation,[],[f45])).

cnf(c_658,plain,
    ( k4_tarski(X0,X1) != sK10
    | r2_hidden(X0,sK8) != iProver_top
    | r2_hidden(X1,sK9) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_6729,plain,
    ( r2_hidden(sK6(sK8,sK9,sK10),sK9) != iProver_top
    | r2_hidden(sK5(sK8,sK9,sK10),sK8) != iProver_top ),
    inference(superposition,[status(thm)],[c_6430,c_658])).

cnf(c_7094,plain,
    ( r2_hidden(sK6(sK8,sK9,sK10),sK9) != iProver_top
    | r2_hidden(sK10,k2_zfmisc_1(sK8,sK9)) != iProver_top ),
    inference(superposition,[status(thm)],[c_659,c_6729])).

cnf(c_7515,plain,
    ( r2_hidden(sK6(sK8,sK9,sK10),sK9) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_7094,c_20,c_53,c_873,c_1024,c_6125])).

cnf(c_7520,plain,
    ( r2_hidden(sK10,k2_zfmisc_1(sK8,sK9)) != iProver_top ),
    inference(superposition,[status(thm)],[c_660,c_7515])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_7520,c_6125,c_1024,c_873,c_53,c_20])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n006.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 13:55:37 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 2.14/0.97  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.14/0.97  
% 2.14/0.97  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.14/0.97  
% 2.14/0.97  ------  iProver source info
% 2.14/0.97  
% 2.14/0.97  git: date: 2020-06-30 10:37:57 +0100
% 2.14/0.97  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.14/0.97  git: non_committed_changes: false
% 2.14/0.97  git: last_make_outside_of_git: false
% 2.14/0.97  
% 2.14/0.97  ------ 
% 2.14/0.97  
% 2.14/0.97  ------ Input Options
% 2.14/0.97  
% 2.14/0.97  --out_options                           all
% 2.14/0.97  --tptp_safe_out                         true
% 2.14/0.97  --problem_path                          ""
% 2.14/0.97  --include_path                          ""
% 2.14/0.97  --clausifier                            res/vclausify_rel
% 2.14/0.97  --clausifier_options                    --mode clausify
% 2.14/0.97  --stdin                                 false
% 2.14/0.97  --stats_out                             all
% 2.14/0.97  
% 2.14/0.97  ------ General Options
% 2.14/0.97  
% 2.14/0.97  --fof                                   false
% 2.14/0.97  --time_out_real                         305.
% 2.14/0.97  --time_out_virtual                      -1.
% 2.14/0.97  --symbol_type_check                     false
% 2.14/0.97  --clausify_out                          false
% 2.14/0.97  --sig_cnt_out                           false
% 2.14/0.97  --trig_cnt_out                          false
% 2.14/0.97  --trig_cnt_out_tolerance                1.
% 2.14/0.97  --trig_cnt_out_sk_spl                   false
% 2.14/0.97  --abstr_cl_out                          false
% 2.14/0.97  
% 2.14/0.97  ------ Global Options
% 2.14/0.97  
% 2.14/0.97  --schedule                              default
% 2.14/0.97  --add_important_lit                     false
% 2.14/0.97  --prop_solver_per_cl                    1000
% 2.14/0.97  --min_unsat_core                        false
% 2.14/0.97  --soft_assumptions                      false
% 2.14/0.97  --soft_lemma_size                       3
% 2.14/0.97  --prop_impl_unit_size                   0
% 2.14/0.97  --prop_impl_unit                        []
% 2.14/0.97  --share_sel_clauses                     true
% 2.14/0.97  --reset_solvers                         false
% 2.14/0.97  --bc_imp_inh                            [conj_cone]
% 2.14/0.97  --conj_cone_tolerance                   3.
% 2.14/0.97  --extra_neg_conj                        none
% 2.14/0.97  --large_theory_mode                     true
% 2.14/0.97  --prolific_symb_bound                   200
% 2.14/0.97  --lt_threshold                          2000
% 2.14/0.97  --clause_weak_htbl                      true
% 2.14/0.97  --gc_record_bc_elim                     false
% 2.14/0.97  
% 2.14/0.97  ------ Preprocessing Options
% 2.14/0.97  
% 2.14/0.97  --preprocessing_flag                    true
% 2.14/0.97  --time_out_prep_mult                    0.1
% 2.14/0.97  --splitting_mode                        input
% 2.14/0.97  --splitting_grd                         true
% 2.14/0.97  --splitting_cvd                         false
% 2.14/0.97  --splitting_cvd_svl                     false
% 2.14/0.97  --splitting_nvd                         32
% 2.14/0.97  --sub_typing                            true
% 2.14/0.97  --prep_gs_sim                           true
% 2.14/0.97  --prep_unflatten                        true
% 2.14/0.97  --prep_res_sim                          true
% 2.14/0.97  --prep_upred                            true
% 2.14/0.97  --prep_sem_filter                       exhaustive
% 2.14/0.97  --prep_sem_filter_out                   false
% 2.14/0.97  --pred_elim                             true
% 2.14/0.97  --res_sim_input                         true
% 2.14/0.97  --eq_ax_congr_red                       true
% 2.14/0.97  --pure_diseq_elim                       true
% 2.14/0.97  --brand_transform                       false
% 2.14/0.97  --non_eq_to_eq                          false
% 2.14/0.97  --prep_def_merge                        true
% 2.14/0.97  --prep_def_merge_prop_impl              false
% 2.14/0.97  --prep_def_merge_mbd                    true
% 2.14/0.97  --prep_def_merge_tr_red                 false
% 2.14/0.97  --prep_def_merge_tr_cl                  false
% 2.14/0.97  --smt_preprocessing                     true
% 2.14/0.97  --smt_ac_axioms                         fast
% 2.14/0.97  --preprocessed_out                      false
% 2.14/0.97  --preprocessed_stats                    false
% 2.14/0.97  
% 2.14/0.97  ------ Abstraction refinement Options
% 2.14/0.97  
% 2.14/0.97  --abstr_ref                             []
% 2.14/0.97  --abstr_ref_prep                        false
% 2.14/0.97  --abstr_ref_until_sat                   false
% 2.14/0.97  --abstr_ref_sig_restrict                funpre
% 2.14/0.97  --abstr_ref_af_restrict_to_split_sk     false
% 2.14/0.97  --abstr_ref_under                       []
% 2.14/0.97  
% 2.14/0.97  ------ SAT Options
% 2.14/0.97  
% 2.14/0.97  --sat_mode                              false
% 2.14/0.97  --sat_fm_restart_options                ""
% 2.14/0.97  --sat_gr_def                            false
% 2.14/0.97  --sat_epr_types                         true
% 2.14/0.97  --sat_non_cyclic_types                  false
% 2.14/0.97  --sat_finite_models                     false
% 2.14/0.97  --sat_fm_lemmas                         false
% 2.14/0.97  --sat_fm_prep                           false
% 2.14/0.97  --sat_fm_uc_incr                        true
% 2.14/0.97  --sat_out_model                         small
% 2.14/0.97  --sat_out_clauses                       false
% 2.14/0.97  
% 2.14/0.97  ------ QBF Options
% 2.14/0.97  
% 2.14/0.97  --qbf_mode                              false
% 2.14/0.97  --qbf_elim_univ                         false
% 2.14/0.97  --qbf_dom_inst                          none
% 2.14/0.97  --qbf_dom_pre_inst                      false
% 2.14/0.97  --qbf_sk_in                             false
% 2.14/0.97  --qbf_pred_elim                         true
% 2.14/0.97  --qbf_split                             512
% 2.14/0.97  
% 2.14/0.97  ------ BMC1 Options
% 2.14/0.97  
% 2.14/0.97  --bmc1_incremental                      false
% 2.14/0.97  --bmc1_axioms                           reachable_all
% 2.14/0.97  --bmc1_min_bound                        0
% 2.14/0.97  --bmc1_max_bound                        -1
% 2.14/0.97  --bmc1_max_bound_default                -1
% 2.14/0.97  --bmc1_symbol_reachability              true
% 2.14/0.97  --bmc1_property_lemmas                  false
% 2.14/0.97  --bmc1_k_induction                      false
% 2.14/0.97  --bmc1_non_equiv_states                 false
% 2.14/0.97  --bmc1_deadlock                         false
% 2.14/0.97  --bmc1_ucm                              false
% 2.14/0.97  --bmc1_add_unsat_core                   none
% 2.14/0.97  --bmc1_unsat_core_children              false
% 2.14/0.97  --bmc1_unsat_core_extrapolate_axioms    false
% 2.14/0.97  --bmc1_out_stat                         full
% 2.14/0.97  --bmc1_ground_init                      false
% 2.14/0.97  --bmc1_pre_inst_next_state              false
% 2.14/0.97  --bmc1_pre_inst_state                   false
% 2.14/0.97  --bmc1_pre_inst_reach_state             false
% 2.14/0.97  --bmc1_out_unsat_core                   false
% 2.14/0.97  --bmc1_aig_witness_out                  false
% 2.14/0.97  --bmc1_verbose                          false
% 2.14/0.97  --bmc1_dump_clauses_tptp                false
% 2.14/0.97  --bmc1_dump_unsat_core_tptp             false
% 2.14/0.97  --bmc1_dump_file                        -
% 2.14/0.97  --bmc1_ucm_expand_uc_limit              128
% 2.14/0.97  --bmc1_ucm_n_expand_iterations          6
% 2.14/0.97  --bmc1_ucm_extend_mode                  1
% 2.14/0.97  --bmc1_ucm_init_mode                    2
% 2.14/0.97  --bmc1_ucm_cone_mode                    none
% 2.14/0.97  --bmc1_ucm_reduced_relation_type        0
% 2.14/0.97  --bmc1_ucm_relax_model                  4
% 2.14/0.97  --bmc1_ucm_full_tr_after_sat            true
% 2.14/0.97  --bmc1_ucm_expand_neg_assumptions       false
% 2.14/0.97  --bmc1_ucm_layered_model                none
% 2.14/0.97  --bmc1_ucm_max_lemma_size               10
% 2.14/0.97  
% 2.14/0.97  ------ AIG Options
% 2.14/0.97  
% 2.14/0.97  --aig_mode                              false
% 2.14/0.97  
% 2.14/0.97  ------ Instantiation Options
% 2.14/0.97  
% 2.14/0.97  --instantiation_flag                    true
% 2.14/0.97  --inst_sos_flag                         false
% 2.14/0.97  --inst_sos_phase                        true
% 2.14/0.97  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.14/0.97  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.14/0.97  --inst_lit_sel_side                     num_symb
% 2.14/0.97  --inst_solver_per_active                1400
% 2.14/0.97  --inst_solver_calls_frac                1.
% 2.14/0.97  --inst_passive_queue_type               priority_queues
% 2.14/0.97  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.14/0.97  --inst_passive_queues_freq              [25;2]
% 2.14/0.97  --inst_dismatching                      true
% 2.14/0.97  --inst_eager_unprocessed_to_passive     true
% 2.14/0.97  --inst_prop_sim_given                   true
% 2.14/0.97  --inst_prop_sim_new                     false
% 2.14/0.97  --inst_subs_new                         false
% 2.14/0.97  --inst_eq_res_simp                      false
% 2.14/0.97  --inst_subs_given                       false
% 2.14/0.97  --inst_orphan_elimination               true
% 2.14/0.97  --inst_learning_loop_flag               true
% 2.14/0.97  --inst_learning_start                   3000
% 2.14/0.97  --inst_learning_factor                  2
% 2.14/0.97  --inst_start_prop_sim_after_learn       3
% 2.14/0.97  --inst_sel_renew                        solver
% 2.14/0.97  --inst_lit_activity_flag                true
% 2.14/0.97  --inst_restr_to_given                   false
% 2.14/0.97  --inst_activity_threshold               500
% 2.14/0.97  --inst_out_proof                        true
% 2.14/0.97  
% 2.14/0.97  ------ Resolution Options
% 2.14/0.97  
% 2.14/0.97  --resolution_flag                       true
% 2.14/0.97  --res_lit_sel                           adaptive
% 2.14/0.97  --res_lit_sel_side                      none
% 2.14/0.97  --res_ordering                          kbo
% 2.14/0.97  --res_to_prop_solver                    active
% 2.14/0.97  --res_prop_simpl_new                    false
% 2.14/0.97  --res_prop_simpl_given                  true
% 2.14/0.97  --res_passive_queue_type                priority_queues
% 2.14/0.97  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.14/0.97  --res_passive_queues_freq               [15;5]
% 2.14/0.97  --res_forward_subs                      full
% 2.14/0.97  --res_backward_subs                     full
% 2.14/0.97  --res_forward_subs_resolution           true
% 2.14/0.97  --res_backward_subs_resolution          true
% 2.14/0.97  --res_orphan_elimination                true
% 2.14/0.97  --res_time_limit                        2.
% 2.14/0.97  --res_out_proof                         true
% 2.14/0.97  
% 2.14/0.97  ------ Superposition Options
% 2.14/0.97  
% 2.14/0.97  --superposition_flag                    true
% 2.14/0.97  --sup_passive_queue_type                priority_queues
% 2.14/0.97  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.14/0.97  --sup_passive_queues_freq               [8;1;4]
% 2.14/0.97  --demod_completeness_check              fast
% 2.14/0.97  --demod_use_ground                      true
% 2.14/0.97  --sup_to_prop_solver                    passive
% 2.14/0.97  --sup_prop_simpl_new                    true
% 2.14/0.97  --sup_prop_simpl_given                  true
% 2.14/0.97  --sup_fun_splitting                     false
% 2.14/0.97  --sup_smt_interval                      50000
% 2.14/0.97  
% 2.14/0.97  ------ Superposition Simplification Setup
% 2.14/0.97  
% 2.14/0.97  --sup_indices_passive                   []
% 2.14/0.97  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.14/0.97  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.14/0.97  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.14/0.97  --sup_full_triv                         [TrivRules;PropSubs]
% 2.14/0.97  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.14/0.97  --sup_full_bw                           [BwDemod]
% 2.14/0.97  --sup_immed_triv                        [TrivRules]
% 2.14/0.97  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.14/0.97  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.14/0.97  --sup_immed_bw_main                     []
% 2.14/0.97  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.14/0.97  --sup_input_triv                        [Unflattening;TrivRules]
% 2.14/0.97  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.14/0.97  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.14/0.97  
% 2.14/0.97  ------ Combination Options
% 2.14/0.97  
% 2.14/0.97  --comb_res_mult                         3
% 2.14/0.97  --comb_sup_mult                         2
% 2.14/0.97  --comb_inst_mult                        10
% 2.14/0.97  
% 2.14/0.97  ------ Debug Options
% 2.14/0.97  
% 2.14/0.97  --dbg_backtrace                         false
% 2.14/0.97  --dbg_dump_prop_clauses                 false
% 2.14/0.97  --dbg_dump_prop_clauses_file            -
% 2.14/0.97  --dbg_out_stat                          false
% 2.14/0.97  ------ Parsing...
% 2.14/0.97  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.14/0.97  
% 2.14/0.97  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 2.14/0.97  
% 2.14/0.97  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.14/0.97  
% 2.14/0.97  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.14/0.97  ------ Proving...
% 2.14/0.97  ------ Problem Properties 
% 2.14/0.97  
% 2.14/0.97  
% 2.14/0.97  clauses                                 18
% 2.14/0.97  conjectures                             2
% 2.14/0.97  EPR                                     2
% 2.14/0.97  Horn                                    12
% 2.14/0.97  unary                                   2
% 2.14/0.97  binary                                  7
% 2.14/0.97  lits                                    45
% 2.14/0.97  lits eq                                 13
% 2.14/0.97  fd_pure                                 0
% 2.14/0.97  fd_pseudo                               0
% 2.14/0.97  fd_cond                                 0
% 2.14/0.97  fd_pseudo_cond                          6
% 2.14/0.97  AC symbols                              0
% 2.14/0.97  
% 2.14/0.97  ------ Schedule dynamic 5 is on 
% 2.14/0.97  
% 2.14/0.97  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.14/0.97  
% 2.14/0.97  
% 2.14/0.97  ------ 
% 2.14/0.97  Current options:
% 2.14/0.97  ------ 
% 2.14/0.97  
% 2.14/0.97  ------ Input Options
% 2.14/0.97  
% 2.14/0.97  --out_options                           all
% 2.14/0.97  --tptp_safe_out                         true
% 2.14/0.97  --problem_path                          ""
% 2.14/0.97  --include_path                          ""
% 2.14/0.97  --clausifier                            res/vclausify_rel
% 2.14/0.97  --clausifier_options                    --mode clausify
% 2.14/0.97  --stdin                                 false
% 2.14/0.97  --stats_out                             all
% 2.14/0.97  
% 2.14/0.97  ------ General Options
% 2.14/0.97  
% 2.14/0.97  --fof                                   false
% 2.14/0.97  --time_out_real                         305.
% 2.14/0.97  --time_out_virtual                      -1.
% 2.14/0.97  --symbol_type_check                     false
% 2.14/0.97  --clausify_out                          false
% 2.14/0.97  --sig_cnt_out                           false
% 2.14/0.97  --trig_cnt_out                          false
% 2.14/0.97  --trig_cnt_out_tolerance                1.
% 2.14/0.97  --trig_cnt_out_sk_spl                   false
% 2.14/0.97  --abstr_cl_out                          false
% 2.14/0.97  
% 2.14/0.97  ------ Global Options
% 2.14/0.97  
% 2.14/0.97  --schedule                              default
% 2.14/0.97  --add_important_lit                     false
% 2.14/0.97  --prop_solver_per_cl                    1000
% 2.14/0.97  --min_unsat_core                        false
% 2.14/0.97  --soft_assumptions                      false
% 2.14/0.97  --soft_lemma_size                       3
% 2.14/0.97  --prop_impl_unit_size                   0
% 2.14/0.97  --prop_impl_unit                        []
% 2.14/0.97  --share_sel_clauses                     true
% 2.14/0.97  --reset_solvers                         false
% 2.14/0.97  --bc_imp_inh                            [conj_cone]
% 2.14/0.97  --conj_cone_tolerance                   3.
% 2.14/0.97  --extra_neg_conj                        none
% 2.14/0.97  --large_theory_mode                     true
% 2.14/0.97  --prolific_symb_bound                   200
% 2.14/0.97  --lt_threshold                          2000
% 2.14/0.97  --clause_weak_htbl                      true
% 2.14/0.97  --gc_record_bc_elim                     false
% 2.14/0.97  
% 2.14/0.97  ------ Preprocessing Options
% 2.14/0.97  
% 2.14/0.97  --preprocessing_flag                    true
% 2.14/0.97  --time_out_prep_mult                    0.1
% 2.14/0.97  --splitting_mode                        input
% 2.14/0.97  --splitting_grd                         true
% 2.14/0.97  --splitting_cvd                         false
% 2.14/0.97  --splitting_cvd_svl                     false
% 2.14/0.97  --splitting_nvd                         32
% 2.14/0.97  --sub_typing                            true
% 2.14/0.97  --prep_gs_sim                           true
% 2.14/0.97  --prep_unflatten                        true
% 2.14/0.97  --prep_res_sim                          true
% 2.14/0.97  --prep_upred                            true
% 2.14/0.97  --prep_sem_filter                       exhaustive
% 2.14/0.97  --prep_sem_filter_out                   false
% 2.14/0.97  --pred_elim                             true
% 2.14/0.97  --res_sim_input                         true
% 2.14/0.97  --eq_ax_congr_red                       true
% 2.14/0.97  --pure_diseq_elim                       true
% 2.14/0.97  --brand_transform                       false
% 2.14/0.97  --non_eq_to_eq                          false
% 2.14/0.97  --prep_def_merge                        true
% 2.14/0.97  --prep_def_merge_prop_impl              false
% 2.14/0.97  --prep_def_merge_mbd                    true
% 2.14/0.97  --prep_def_merge_tr_red                 false
% 2.14/0.97  --prep_def_merge_tr_cl                  false
% 2.14/0.97  --smt_preprocessing                     true
% 2.14/0.97  --smt_ac_axioms                         fast
% 2.14/0.97  --preprocessed_out                      false
% 2.14/0.97  --preprocessed_stats                    false
% 2.14/0.97  
% 2.14/0.97  ------ Abstraction refinement Options
% 2.14/0.97  
% 2.14/0.97  --abstr_ref                             []
% 2.14/0.97  --abstr_ref_prep                        false
% 2.14/0.97  --abstr_ref_until_sat                   false
% 2.14/0.97  --abstr_ref_sig_restrict                funpre
% 2.14/0.97  --abstr_ref_af_restrict_to_split_sk     false
% 2.14/0.97  --abstr_ref_under                       []
% 2.14/0.97  
% 2.14/0.97  ------ SAT Options
% 2.14/0.97  
% 2.14/0.97  --sat_mode                              false
% 2.14/0.97  --sat_fm_restart_options                ""
% 2.14/0.97  --sat_gr_def                            false
% 2.14/0.97  --sat_epr_types                         true
% 2.14/0.97  --sat_non_cyclic_types                  false
% 2.14/0.97  --sat_finite_models                     false
% 2.14/0.97  --sat_fm_lemmas                         false
% 2.14/0.97  --sat_fm_prep                           false
% 2.14/0.97  --sat_fm_uc_incr                        true
% 2.14/0.97  --sat_out_model                         small
% 2.14/0.97  --sat_out_clauses                       false
% 2.14/0.97  
% 2.14/0.97  ------ QBF Options
% 2.14/0.97  
% 2.14/0.97  --qbf_mode                              false
% 2.14/0.97  --qbf_elim_univ                         false
% 2.14/0.97  --qbf_dom_inst                          none
% 2.14/0.97  --qbf_dom_pre_inst                      false
% 2.14/0.97  --qbf_sk_in                             false
% 2.14/0.97  --qbf_pred_elim                         true
% 2.14/0.97  --qbf_split                             512
% 2.14/0.97  
% 2.14/0.97  ------ BMC1 Options
% 2.14/0.97  
% 2.14/0.97  --bmc1_incremental                      false
% 2.14/0.97  --bmc1_axioms                           reachable_all
% 2.14/0.97  --bmc1_min_bound                        0
% 2.14/0.97  --bmc1_max_bound                        -1
% 2.14/0.97  --bmc1_max_bound_default                -1
% 2.14/0.97  --bmc1_symbol_reachability              true
% 2.14/0.97  --bmc1_property_lemmas                  false
% 2.14/0.97  --bmc1_k_induction                      false
% 2.14/0.97  --bmc1_non_equiv_states                 false
% 2.14/0.97  --bmc1_deadlock                         false
% 2.14/0.97  --bmc1_ucm                              false
% 2.14/0.97  --bmc1_add_unsat_core                   none
% 2.14/0.97  --bmc1_unsat_core_children              false
% 2.14/0.97  --bmc1_unsat_core_extrapolate_axioms    false
% 2.14/0.97  --bmc1_out_stat                         full
% 2.14/0.97  --bmc1_ground_init                      false
% 2.14/0.97  --bmc1_pre_inst_next_state              false
% 2.14/0.97  --bmc1_pre_inst_state                   false
% 2.14/0.97  --bmc1_pre_inst_reach_state             false
% 2.14/0.97  --bmc1_out_unsat_core                   false
% 2.14/0.97  --bmc1_aig_witness_out                  false
% 2.14/0.97  --bmc1_verbose                          false
% 2.14/0.97  --bmc1_dump_clauses_tptp                false
% 2.14/0.97  --bmc1_dump_unsat_core_tptp             false
% 2.14/0.97  --bmc1_dump_file                        -
% 2.14/0.97  --bmc1_ucm_expand_uc_limit              128
% 2.14/0.97  --bmc1_ucm_n_expand_iterations          6
% 2.14/0.97  --bmc1_ucm_extend_mode                  1
% 2.14/0.97  --bmc1_ucm_init_mode                    2
% 2.14/0.97  --bmc1_ucm_cone_mode                    none
% 2.14/0.97  --bmc1_ucm_reduced_relation_type        0
% 2.14/0.97  --bmc1_ucm_relax_model                  4
% 2.14/0.97  --bmc1_ucm_full_tr_after_sat            true
% 2.14/0.97  --bmc1_ucm_expand_neg_assumptions       false
% 2.14/0.97  --bmc1_ucm_layered_model                none
% 2.14/0.97  --bmc1_ucm_max_lemma_size               10
% 2.14/0.97  
% 2.14/0.97  ------ AIG Options
% 2.14/0.97  
% 2.14/0.97  --aig_mode                              false
% 2.14/0.97  
% 2.14/0.97  ------ Instantiation Options
% 2.14/0.97  
% 2.14/0.97  --instantiation_flag                    true
% 2.14/0.97  --inst_sos_flag                         false
% 2.14/0.97  --inst_sos_phase                        true
% 2.14/0.97  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.14/0.97  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.14/0.97  --inst_lit_sel_side                     none
% 2.14/0.97  --inst_solver_per_active                1400
% 2.14/0.97  --inst_solver_calls_frac                1.
% 2.14/0.97  --inst_passive_queue_type               priority_queues
% 2.14/0.97  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.14/0.97  --inst_passive_queues_freq              [25;2]
% 2.14/0.97  --inst_dismatching                      true
% 2.14/0.97  --inst_eager_unprocessed_to_passive     true
% 2.14/0.97  --inst_prop_sim_given                   true
% 2.14/0.97  --inst_prop_sim_new                     false
% 2.14/0.97  --inst_subs_new                         false
% 2.14/0.97  --inst_eq_res_simp                      false
% 2.14/0.97  --inst_subs_given                       false
% 2.14/0.97  --inst_orphan_elimination               true
% 2.14/0.97  --inst_learning_loop_flag               true
% 2.14/0.97  --inst_learning_start                   3000
% 2.14/0.97  --inst_learning_factor                  2
% 2.14/0.97  --inst_start_prop_sim_after_learn       3
% 2.14/0.97  --inst_sel_renew                        solver
% 2.14/0.97  --inst_lit_activity_flag                true
% 2.14/0.97  --inst_restr_to_given                   false
% 2.14/0.97  --inst_activity_threshold               500
% 2.14/0.97  --inst_out_proof                        true
% 2.14/0.97  
% 2.14/0.97  ------ Resolution Options
% 2.14/0.97  
% 2.14/0.97  --resolution_flag                       false
% 2.14/0.97  --res_lit_sel                           adaptive
% 2.14/0.97  --res_lit_sel_side                      none
% 2.14/0.97  --res_ordering                          kbo
% 2.14/0.97  --res_to_prop_solver                    active
% 2.14/0.97  --res_prop_simpl_new                    false
% 2.14/0.97  --res_prop_simpl_given                  true
% 2.14/0.97  --res_passive_queue_type                priority_queues
% 2.14/0.97  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.14/0.97  --res_passive_queues_freq               [15;5]
% 2.14/0.97  --res_forward_subs                      full
% 2.14/0.97  --res_backward_subs                     full
% 2.14/0.97  --res_forward_subs_resolution           true
% 2.14/0.97  --res_backward_subs_resolution          true
% 2.14/0.97  --res_orphan_elimination                true
% 2.14/0.97  --res_time_limit                        2.
% 2.14/0.97  --res_out_proof                         true
% 2.14/0.97  
% 2.14/0.97  ------ Superposition Options
% 2.14/0.97  
% 2.14/0.97  --superposition_flag                    true
% 2.14/0.97  --sup_passive_queue_type                priority_queues
% 2.14/0.97  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.14/0.97  --sup_passive_queues_freq               [8;1;4]
% 2.14/0.97  --demod_completeness_check              fast
% 2.14/0.97  --demod_use_ground                      true
% 2.14/0.97  --sup_to_prop_solver                    passive
% 2.14/0.97  --sup_prop_simpl_new                    true
% 2.14/0.97  --sup_prop_simpl_given                  true
% 2.14/0.97  --sup_fun_splitting                     false
% 2.14/0.97  --sup_smt_interval                      50000
% 2.14/0.97  
% 2.14/0.97  ------ Superposition Simplification Setup
% 2.14/0.97  
% 2.14/0.97  --sup_indices_passive                   []
% 2.14/0.97  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.14/0.97  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.14/0.97  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.14/0.97  --sup_full_triv                         [TrivRules;PropSubs]
% 2.14/0.97  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.14/0.97  --sup_full_bw                           [BwDemod]
% 2.14/0.97  --sup_immed_triv                        [TrivRules]
% 2.14/0.97  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.14/0.97  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.14/0.97  --sup_immed_bw_main                     []
% 2.14/0.97  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.14/0.97  --sup_input_triv                        [Unflattening;TrivRules]
% 2.14/0.97  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.14/0.97  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.14/0.97  
% 2.14/0.97  ------ Combination Options
% 2.14/0.97  
% 2.14/0.97  --comb_res_mult                         3
% 2.14/0.97  --comb_sup_mult                         2
% 2.14/0.97  --comb_inst_mult                        10
% 2.14/0.97  
% 2.14/0.97  ------ Debug Options
% 2.14/0.97  
% 2.14/0.97  --dbg_backtrace                         false
% 2.14/0.97  --dbg_dump_prop_clauses                 false
% 2.14/0.97  --dbg_dump_prop_clauses_file            -
% 2.14/0.97  --dbg_out_stat                          false
% 2.14/0.97  
% 2.14/0.97  
% 2.14/0.97  
% 2.14/0.97  
% 2.14/0.97  ------ Proving...
% 2.14/0.97  
% 2.14/0.97  
% 2.14/0.97  % SZS status Theorem for theBenchmark.p
% 2.14/0.97  
% 2.14/0.97  % SZS output start CNFRefutation for theBenchmark.p
% 2.14/0.97  
% 2.14/0.97  fof(f5,axiom,(
% 2.14/0.97    ! [X0,X1,X2] : (k2_zfmisc_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4,X5] : (k4_tarski(X4,X5) = X3 & r2_hidden(X5,X1) & r2_hidden(X4,X0))))),
% 2.14/0.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.14/0.97  
% 2.14/0.97  fof(f19,plain,(
% 2.14/0.97    ! [X0,X1,X2] : ((k2_zfmisc_1(X0,X1) = X2 | ? [X3] : ((! [X4,X5] : (k4_tarski(X4,X5) != X3 | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X0)) | ~r2_hidden(X3,X2)) & (? [X4,X5] : (k4_tarski(X4,X5) = X3 & r2_hidden(X5,X1) & r2_hidden(X4,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ! [X4,X5] : (k4_tarski(X4,X5) != X3 | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X0))) & (? [X4,X5] : (k4_tarski(X4,X5) = X3 & r2_hidden(X5,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X3,X2))) | k2_zfmisc_1(X0,X1) != X2))),
% 2.14/0.97    inference(nnf_transformation,[],[f5])).
% 2.14/0.97  
% 2.14/0.97  fof(f20,plain,(
% 2.14/0.97    ! [X0,X1,X2] : ((k2_zfmisc_1(X0,X1) = X2 | ? [X3] : ((! [X4,X5] : (k4_tarski(X4,X5) != X3 | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X0)) | ~r2_hidden(X3,X2)) & (? [X6,X7] : (k4_tarski(X6,X7) = X3 & r2_hidden(X7,X1) & r2_hidden(X6,X0)) | r2_hidden(X3,X2)))) & (! [X8] : ((r2_hidden(X8,X2) | ! [X9,X10] : (k4_tarski(X9,X10) != X8 | ~r2_hidden(X10,X1) | ~r2_hidden(X9,X0))) & (? [X11,X12] : (k4_tarski(X11,X12) = X8 & r2_hidden(X12,X1) & r2_hidden(X11,X0)) | ~r2_hidden(X8,X2))) | k2_zfmisc_1(X0,X1) != X2))),
% 2.14/0.97    inference(rectify,[],[f19])).
% 2.14/0.97  
% 2.14/0.97  fof(f23,plain,(
% 2.14/0.97    ! [X8,X1,X0] : (? [X11,X12] : (k4_tarski(X11,X12) = X8 & r2_hidden(X12,X1) & r2_hidden(X11,X0)) => (k4_tarski(sK5(X0,X1,X8),sK6(X0,X1,X8)) = X8 & r2_hidden(sK6(X0,X1,X8),X1) & r2_hidden(sK5(X0,X1,X8),X0)))),
% 2.14/0.97    introduced(choice_axiom,[])).
% 2.14/0.97  
% 2.14/0.97  fof(f22,plain,(
% 2.14/0.97    ( ! [X3] : (! [X2,X1,X0] : (? [X6,X7] : (k4_tarski(X6,X7) = X3 & r2_hidden(X7,X1) & r2_hidden(X6,X0)) => (k4_tarski(sK3(X0,X1,X2),sK4(X0,X1,X2)) = X3 & r2_hidden(sK4(X0,X1,X2),X1) & r2_hidden(sK3(X0,X1,X2),X0)))) )),
% 2.14/0.97    introduced(choice_axiom,[])).
% 2.14/0.97  
% 2.14/0.97  fof(f21,plain,(
% 2.14/0.97    ! [X2,X1,X0] : (? [X3] : ((! [X4,X5] : (k4_tarski(X4,X5) != X3 | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X0)) | ~r2_hidden(X3,X2)) & (? [X6,X7] : (k4_tarski(X6,X7) = X3 & r2_hidden(X7,X1) & r2_hidden(X6,X0)) | r2_hidden(X3,X2))) => ((! [X5,X4] : (k4_tarski(X4,X5) != sK2(X0,X1,X2) | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X0)) | ~r2_hidden(sK2(X0,X1,X2),X2)) & (? [X7,X6] : (k4_tarski(X6,X7) = sK2(X0,X1,X2) & r2_hidden(X7,X1) & r2_hidden(X6,X0)) | r2_hidden(sK2(X0,X1,X2),X2))))),
% 2.14/0.97    introduced(choice_axiom,[])).
% 2.14/0.97  
% 2.14/0.97  fof(f24,plain,(
% 2.14/0.97    ! [X0,X1,X2] : ((k2_zfmisc_1(X0,X1) = X2 | ((! [X4,X5] : (k4_tarski(X4,X5) != sK2(X0,X1,X2) | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X0)) | ~r2_hidden(sK2(X0,X1,X2),X2)) & ((k4_tarski(sK3(X0,X1,X2),sK4(X0,X1,X2)) = sK2(X0,X1,X2) & r2_hidden(sK4(X0,X1,X2),X1) & r2_hidden(sK3(X0,X1,X2),X0)) | r2_hidden(sK2(X0,X1,X2),X2)))) & (! [X8] : ((r2_hidden(X8,X2) | ! [X9,X10] : (k4_tarski(X9,X10) != X8 | ~r2_hidden(X10,X1) | ~r2_hidden(X9,X0))) & ((k4_tarski(sK5(X0,X1,X8),sK6(X0,X1,X8)) = X8 & r2_hidden(sK6(X0,X1,X8),X1) & r2_hidden(sK5(X0,X1,X8),X0)) | ~r2_hidden(X8,X2))) | k2_zfmisc_1(X0,X1) != X2))),
% 2.14/0.97    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5,sK6])],[f20,f23,f22,f21])).
% 2.14/0.97  
% 2.14/0.97  fof(f36,plain,(
% 2.14/0.97    ( ! [X2,X0,X8,X1] : (r2_hidden(sK6(X0,X1,X8),X1) | ~r2_hidden(X8,X2) | k2_zfmisc_1(X0,X1) != X2) )),
% 2.14/0.97    inference(cnf_transformation,[],[f24])).
% 2.14/0.97  
% 2.14/0.97  fof(f52,plain,(
% 2.14/0.97    ( ! [X0,X8,X1] : (r2_hidden(sK6(X0,X1,X8),X1) | ~r2_hidden(X8,k2_zfmisc_1(X0,X1))) )),
% 2.14/0.97    inference(equality_resolution,[],[f36])).
% 2.14/0.97  
% 2.14/0.97  fof(f35,plain,(
% 2.14/0.97    ( ! [X2,X0,X8,X1] : (r2_hidden(sK5(X0,X1,X8),X0) | ~r2_hidden(X8,X2) | k2_zfmisc_1(X0,X1) != X2) )),
% 2.14/0.97    inference(cnf_transformation,[],[f24])).
% 2.14/0.97  
% 2.14/0.97  fof(f53,plain,(
% 2.14/0.97    ( ! [X0,X8,X1] : (r2_hidden(sK5(X0,X1,X8),X0) | ~r2_hidden(X8,k2_zfmisc_1(X0,X1))) )),
% 2.14/0.97    inference(equality_resolution,[],[f35])).
% 2.14/0.97  
% 2.14/0.97  fof(f6,conjecture,(
% 2.14/0.97    ! [X0,X1,X2,X3] : ~(! [X4,X5] : ~(k4_tarski(X4,X5) = X3 & r2_hidden(X5,X2) & r2_hidden(X4,X1)) & r2_hidden(X3,X0) & r1_tarski(X0,k2_zfmisc_1(X1,X2)))),
% 2.14/0.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.14/0.97  
% 2.14/0.97  fof(f7,negated_conjecture,(
% 2.14/0.97    ~! [X0,X1,X2,X3] : ~(! [X4,X5] : ~(k4_tarski(X4,X5) = X3 & r2_hidden(X5,X2) & r2_hidden(X4,X1)) & r2_hidden(X3,X0) & r1_tarski(X0,k2_zfmisc_1(X1,X2)))),
% 2.14/0.97    inference(negated_conjecture,[],[f6])).
% 2.14/0.97  
% 2.14/0.97  fof(f12,plain,(
% 2.14/0.97    ? [X0,X1,X2,X3] : (! [X4,X5] : (k4_tarski(X4,X5) != X3 | ~r2_hidden(X5,X2) | ~r2_hidden(X4,X1)) & r2_hidden(X3,X0) & r1_tarski(X0,k2_zfmisc_1(X1,X2)))),
% 2.14/0.97    inference(ennf_transformation,[],[f7])).
% 2.14/0.97  
% 2.14/0.97  fof(f25,plain,(
% 2.14/0.97    ? [X0,X1,X2,X3] : (! [X4,X5] : (k4_tarski(X4,X5) != X3 | ~r2_hidden(X5,X2) | ~r2_hidden(X4,X1)) & r2_hidden(X3,X0) & r1_tarski(X0,k2_zfmisc_1(X1,X2))) => (! [X5,X4] : (k4_tarski(X4,X5) != sK10 | ~r2_hidden(X5,sK9) | ~r2_hidden(X4,sK8)) & r2_hidden(sK10,sK7) & r1_tarski(sK7,k2_zfmisc_1(sK8,sK9)))),
% 2.14/0.97    introduced(choice_axiom,[])).
% 2.14/0.97  
% 2.14/0.97  fof(f26,plain,(
% 2.14/0.97    ! [X4,X5] : (k4_tarski(X4,X5) != sK10 | ~r2_hidden(X5,sK9) | ~r2_hidden(X4,sK8)) & r2_hidden(sK10,sK7) & r1_tarski(sK7,k2_zfmisc_1(sK8,sK9))),
% 2.14/0.97    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7,sK8,sK9,sK10])],[f12,f25])).
% 2.14/0.97  
% 2.14/0.97  fof(f44,plain,(
% 2.14/0.97    r2_hidden(sK10,sK7)),
% 2.14/0.97    inference(cnf_transformation,[],[f26])).
% 2.14/0.97  
% 2.14/0.97  fof(f2,axiom,(
% 2.14/0.97    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 2.14/0.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.14/0.97  
% 2.14/0.97  fof(f8,plain,(
% 2.14/0.97    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 2.14/0.97    inference(rectify,[],[f2])).
% 2.14/0.97  
% 2.14/0.97  fof(f9,plain,(
% 2.14/0.97    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 2.14/0.97    inference(ennf_transformation,[],[f8])).
% 2.14/0.97  
% 2.14/0.97  fof(f13,plain,(
% 2.14/0.97    ! [X1,X0] : (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) => (r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 2.14/0.97    introduced(choice_axiom,[])).
% 2.14/0.97  
% 2.14/0.97  fof(f14,plain,(
% 2.14/0.97    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & ((r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)) | r1_xboole_0(X0,X1)))),
% 2.14/0.97    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f9,f13])).
% 2.14/0.97  
% 2.14/0.97  fof(f28,plain,(
% 2.14/0.97    ( ! [X0,X1] : (r2_hidden(sK0(X0,X1),X1) | r1_xboole_0(X0,X1)) )),
% 2.14/0.97    inference(cnf_transformation,[],[f14])).
% 2.14/0.97  
% 2.14/0.97  fof(f4,axiom,(
% 2.14/0.97    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 2.14/0.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.14/0.97  
% 2.14/0.97  fof(f15,plain,(
% 2.14/0.97    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | X0 != X2) & (X0 = X2 | ~r2_hidden(X2,X1))) | k1_tarski(X0) != X1))),
% 2.14/0.97    inference(nnf_transformation,[],[f4])).
% 2.14/0.97  
% 2.14/0.97  fof(f16,plain,(
% 2.14/0.97    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 2.14/0.97    inference(rectify,[],[f15])).
% 2.14/0.97  
% 2.14/0.97  fof(f17,plain,(
% 2.14/0.97    ! [X1,X0] : (? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1))) => ((sK1(X0,X1) != X0 | ~r2_hidden(sK1(X0,X1),X1)) & (sK1(X0,X1) = X0 | r2_hidden(sK1(X0,X1),X1))))),
% 2.14/0.97    introduced(choice_axiom,[])).
% 2.14/0.97  
% 2.14/0.97  fof(f18,plain,(
% 2.14/0.97    ! [X0,X1] : ((k1_tarski(X0) = X1 | ((sK1(X0,X1) != X0 | ~r2_hidden(sK1(X0,X1),X1)) & (sK1(X0,X1) = X0 | r2_hidden(sK1(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 2.14/0.97    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f16,f17])).
% 2.14/0.97  
% 2.14/0.97  fof(f31,plain,(
% 2.14/0.97    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k1_tarski(X0) != X1) )),
% 2.14/0.97    inference(cnf_transformation,[],[f18])).
% 2.14/0.97  
% 2.14/0.97  fof(f48,plain,(
% 2.14/0.97    ( ! [X0,X3] : (X0 = X3 | ~r2_hidden(X3,k1_tarski(X0))) )),
% 2.14/0.97    inference(equality_resolution,[],[f31])).
% 2.14/0.97  
% 2.14/0.97  fof(f3,axiom,(
% 2.14/0.97    ! [X0,X1,X2] : ((r1_xboole_0(X1,X2) & r1_tarski(X0,X1)) => r1_xboole_0(X0,X2))),
% 2.14/0.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.14/0.97  
% 2.14/0.97  fof(f10,plain,(
% 2.14/0.97    ! [X0,X1,X2] : (r1_xboole_0(X0,X2) | (~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X1)))),
% 2.14/0.97    inference(ennf_transformation,[],[f3])).
% 2.14/0.97  
% 2.14/0.97  fof(f11,plain,(
% 2.14/0.97    ! [X0,X1,X2] : (r1_xboole_0(X0,X2) | ~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X1))),
% 2.14/0.97    inference(flattening,[],[f10])).
% 2.14/0.97  
% 2.14/0.97  fof(f30,plain,(
% 2.14/0.97    ( ! [X2,X0,X1] : (r1_xboole_0(X0,X2) | ~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X1)) )),
% 2.14/0.97    inference(cnf_transformation,[],[f11])).
% 2.14/0.97  
% 2.14/0.97  fof(f43,plain,(
% 2.14/0.97    r1_tarski(sK7,k2_zfmisc_1(sK8,sK9))),
% 2.14/0.97    inference(cnf_transformation,[],[f26])).
% 2.14/0.97  
% 2.14/0.97  fof(f32,plain,(
% 2.14/0.97    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | X0 != X3 | k1_tarski(X0) != X1) )),
% 2.14/0.97    inference(cnf_transformation,[],[f18])).
% 2.14/0.97  
% 2.14/0.97  fof(f46,plain,(
% 2.14/0.97    ( ! [X3,X1] : (r2_hidden(X3,X1) | k1_tarski(X3) != X1) )),
% 2.14/0.97    inference(equality_resolution,[],[f32])).
% 2.14/0.97  
% 2.14/0.97  fof(f47,plain,(
% 2.14/0.97    ( ! [X3] : (r2_hidden(X3,k1_tarski(X3))) )),
% 2.14/0.97    inference(equality_resolution,[],[f46])).
% 2.14/0.97  
% 2.14/0.97  fof(f29,plain,(
% 2.14/0.97    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) )),
% 2.14/0.97    inference(cnf_transformation,[],[f14])).
% 2.14/0.97  
% 2.14/0.97  fof(f27,plain,(
% 2.14/0.97    ( ! [X0,X1] : (r2_hidden(sK0(X0,X1),X0) | r1_xboole_0(X0,X1)) )),
% 2.14/0.97    inference(cnf_transformation,[],[f14])).
% 2.14/0.97  
% 2.14/0.97  fof(f37,plain,(
% 2.14/0.97    ( ! [X2,X0,X8,X1] : (k4_tarski(sK5(X0,X1,X8),sK6(X0,X1,X8)) = X8 | ~r2_hidden(X8,X2) | k2_zfmisc_1(X0,X1) != X2) )),
% 2.14/0.97    inference(cnf_transformation,[],[f24])).
% 2.14/0.97  
% 2.14/0.97  fof(f51,plain,(
% 2.14/0.97    ( ! [X0,X8,X1] : (k4_tarski(sK5(X0,X1,X8),sK6(X0,X1,X8)) = X8 | ~r2_hidden(X8,k2_zfmisc_1(X0,X1))) )),
% 2.14/0.97    inference(equality_resolution,[],[f37])).
% 2.14/0.97  
% 2.14/0.97  fof(f45,plain,(
% 2.14/0.97    ( ! [X4,X5] : (k4_tarski(X4,X5) != sK10 | ~r2_hidden(X5,sK9) | ~r2_hidden(X4,sK8)) )),
% 2.14/0.97    inference(cnf_transformation,[],[f26])).
% 2.14/0.97  
% 2.14/0.97  cnf(c_14,plain,
% 2.14/0.97      ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
% 2.14/0.97      | r2_hidden(sK6(X1,X2,X0),X2) ),
% 2.14/0.97      inference(cnf_transformation,[],[f52]) ).
% 2.14/0.97  
% 2.14/0.97  cnf(c_660,plain,
% 2.14/0.97      ( r2_hidden(X0,k2_zfmisc_1(X1,X2)) != iProver_top
% 2.14/0.97      | r2_hidden(sK6(X1,X2,X0),X2) = iProver_top ),
% 2.14/0.97      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 2.14/0.97  
% 2.14/0.97  cnf(c_15,plain,
% 2.14/0.97      ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
% 2.14/0.97      | r2_hidden(sK5(X1,X2,X0),X1) ),
% 2.14/0.97      inference(cnf_transformation,[],[f53]) ).
% 2.14/0.97  
% 2.14/0.97  cnf(c_659,plain,
% 2.14/0.97      ( r2_hidden(X0,k2_zfmisc_1(X1,X2)) != iProver_top
% 2.14/0.97      | r2_hidden(sK5(X1,X2,X0),X1) = iProver_top ),
% 2.14/0.97      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 2.14/0.97  
% 2.14/0.97  cnf(c_17,negated_conjecture,
% 2.14/0.97      ( r2_hidden(sK10,sK7) ),
% 2.14/0.97      inference(cnf_transformation,[],[f44]) ).
% 2.14/0.97  
% 2.14/0.97  cnf(c_657,plain,
% 2.14/0.97      ( r2_hidden(sK10,sK7) = iProver_top ),
% 2.14/0.97      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 2.14/0.97  
% 2.14/0.97  cnf(c_1,plain,
% 2.14/0.97      ( r2_hidden(sK0(X0,X1),X1) | r1_xboole_0(X0,X1) ),
% 2.14/0.97      inference(cnf_transformation,[],[f28]) ).
% 2.14/0.97  
% 2.14/0.97  cnf(c_672,plain,
% 2.14/0.97      ( r2_hidden(sK0(X0,X1),X1) = iProver_top
% 2.14/0.97      | r1_xboole_0(X0,X1) = iProver_top ),
% 2.14/0.97      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 2.14/0.97  
% 2.14/0.97  cnf(c_7,plain,
% 2.14/0.97      ( ~ r2_hidden(X0,k1_tarski(X1)) | X0 = X1 ),
% 2.14/0.97      inference(cnf_transformation,[],[f48]) ).
% 2.14/0.97  
% 2.14/0.97  cnf(c_667,plain,
% 2.14/0.97      ( X0 = X1 | r2_hidden(X0,k1_tarski(X1)) != iProver_top ),
% 2.14/0.97      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 2.14/0.97  
% 2.14/0.97  cnf(c_1252,plain,
% 2.14/0.97      ( sK0(X0,k1_tarski(X1)) = X1
% 2.14/0.97      | r1_xboole_0(X0,k1_tarski(X1)) = iProver_top ),
% 2.14/0.97      inference(superposition,[status(thm)],[c_672,c_667]) ).
% 2.14/0.97  
% 2.14/0.97  cnf(c_3,plain,
% 2.14/0.97      ( ~ r1_tarski(X0,X1) | ~ r1_xboole_0(X1,X2) | r1_xboole_0(X0,X2) ),
% 2.14/0.97      inference(cnf_transformation,[],[f30]) ).
% 2.14/0.97  
% 2.14/0.97  cnf(c_18,negated_conjecture,
% 2.14/0.97      ( r1_tarski(sK7,k2_zfmisc_1(sK8,sK9)) ),
% 2.14/0.97      inference(cnf_transformation,[],[f43]) ).
% 2.14/0.97  
% 2.14/0.97  cnf(c_214,plain,
% 2.14/0.97      ( ~ r1_xboole_0(X0,X1)
% 2.14/0.97      | r1_xboole_0(X2,X1)
% 2.14/0.97      | k2_zfmisc_1(sK8,sK9) != X0
% 2.14/0.97      | sK7 != X2 ),
% 2.14/0.97      inference(resolution_lifted,[status(thm)],[c_3,c_18]) ).
% 2.14/0.97  
% 2.14/0.97  cnf(c_215,plain,
% 2.14/0.97      ( ~ r1_xboole_0(k2_zfmisc_1(sK8,sK9),X0) | r1_xboole_0(sK7,X0) ),
% 2.14/0.97      inference(unflattening,[status(thm)],[c_214]) ).
% 2.14/0.97  
% 2.14/0.97  cnf(c_656,plain,
% 2.14/0.97      ( r1_xboole_0(k2_zfmisc_1(sK8,sK9),X0) != iProver_top
% 2.14/0.97      | r1_xboole_0(sK7,X0) = iProver_top ),
% 2.14/0.97      inference(predicate_to_equality,[status(thm)],[c_215]) ).
% 2.14/0.97  
% 2.14/0.97  cnf(c_5577,plain,
% 2.14/0.97      ( sK0(k2_zfmisc_1(sK8,sK9),k1_tarski(X0)) = X0
% 2.14/0.97      | r1_xboole_0(sK7,k1_tarski(X0)) = iProver_top ),
% 2.14/0.97      inference(superposition,[status(thm)],[c_1252,c_656]) ).
% 2.14/0.97  
% 2.14/0.97  cnf(c_6,plain,
% 2.14/0.97      ( r2_hidden(X0,k1_tarski(X0)) ),
% 2.14/0.97      inference(cnf_transformation,[],[f47]) ).
% 2.14/0.97  
% 2.14/0.97  cnf(c_668,plain,
% 2.14/0.97      ( r2_hidden(X0,k1_tarski(X0)) = iProver_top ),
% 2.14/0.97      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 2.14/0.97  
% 2.14/0.97  cnf(c_0,plain,
% 2.14/0.97      ( ~ r2_hidden(X0,X1) | ~ r2_hidden(X0,X2) | ~ r1_xboole_0(X2,X1) ),
% 2.14/0.97      inference(cnf_transformation,[],[f29]) ).
% 2.14/0.97  
% 2.14/0.97  cnf(c_673,plain,
% 2.14/0.97      ( r2_hidden(X0,X1) != iProver_top
% 2.14/0.97      | r2_hidden(X0,X2) != iProver_top
% 2.14/0.97      | r1_xboole_0(X2,X1) != iProver_top ),
% 2.14/0.97      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 2.14/0.97  
% 2.14/0.97  cnf(c_1911,plain,
% 2.14/0.97      ( r2_hidden(X0,X1) != iProver_top
% 2.14/0.97      | r1_xboole_0(X1,k1_tarski(X0)) != iProver_top ),
% 2.14/0.97      inference(superposition,[status(thm)],[c_668,c_673]) ).
% 2.14/0.97  
% 2.14/0.97  cnf(c_5911,plain,
% 2.14/0.97      ( sK0(k2_zfmisc_1(sK8,sK9),k1_tarski(X0)) = X0
% 2.14/0.97      | r2_hidden(X0,sK7) != iProver_top ),
% 2.14/0.97      inference(superposition,[status(thm)],[c_5577,c_1911]) ).
% 2.14/0.97  
% 2.14/0.97  cnf(c_6038,plain,
% 2.14/0.97      ( sK0(k2_zfmisc_1(sK8,sK9),k1_tarski(sK10)) = sK10 ),
% 2.14/0.97      inference(superposition,[status(thm)],[c_657,c_5911]) ).
% 2.14/0.97  
% 2.14/0.97  cnf(c_2,plain,
% 2.14/0.97      ( r2_hidden(sK0(X0,X1),X0) | r1_xboole_0(X0,X1) ),
% 2.14/0.97      inference(cnf_transformation,[],[f27]) ).
% 2.14/0.97  
% 2.14/0.97  cnf(c_671,plain,
% 2.14/0.97      ( r2_hidden(sK0(X0,X1),X0) = iProver_top
% 2.14/0.97      | r1_xboole_0(X0,X1) = iProver_top ),
% 2.14/0.97      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 2.14/0.97  
% 2.14/0.97  cnf(c_6125,plain,
% 2.14/0.97      ( r2_hidden(sK10,k2_zfmisc_1(sK8,sK9)) = iProver_top
% 2.14/0.97      | r1_xboole_0(k2_zfmisc_1(sK8,sK9),k1_tarski(sK10)) = iProver_top ),
% 2.14/0.97      inference(superposition,[status(thm)],[c_6038,c_671]) ).
% 2.14/0.97  
% 2.14/0.97  cnf(c_20,plain,
% 2.14/0.97      ( r2_hidden(sK10,sK7) = iProver_top ),
% 2.14/0.97      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 2.14/0.97  
% 2.14/0.97  cnf(c_51,plain,
% 2.14/0.97      ( r2_hidden(X0,k1_tarski(X0)) = iProver_top ),
% 2.14/0.97      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 2.14/0.97  
% 2.14/0.97  cnf(c_53,plain,
% 2.14/0.97      ( r2_hidden(sK10,k1_tarski(sK10)) = iProver_top ),
% 2.14/0.97      inference(instantiation,[status(thm)],[c_51]) ).
% 2.14/0.97  
% 2.14/0.97  cnf(c_812,plain,
% 2.14/0.97      ( ~ r2_hidden(X0,X1)
% 2.14/0.97      | ~ r2_hidden(X0,k1_tarski(X0))
% 2.14/0.97      | ~ r1_xboole_0(X1,k1_tarski(X0)) ),
% 2.14/0.97      inference(instantiation,[status(thm)],[c_0]) ).
% 2.14/0.97  
% 2.14/0.97  cnf(c_872,plain,
% 2.14/0.97      ( ~ r2_hidden(sK10,k1_tarski(sK10))
% 2.14/0.97      | ~ r2_hidden(sK10,sK7)
% 2.14/0.97      | ~ r1_xboole_0(sK7,k1_tarski(sK10)) ),
% 2.14/0.97      inference(instantiation,[status(thm)],[c_812]) ).
% 2.14/0.97  
% 2.14/0.97  cnf(c_873,plain,
% 2.14/0.97      ( r2_hidden(sK10,k1_tarski(sK10)) != iProver_top
% 2.14/0.97      | r2_hidden(sK10,sK7) != iProver_top
% 2.14/0.97      | r1_xboole_0(sK7,k1_tarski(sK10)) != iProver_top ),
% 2.14/0.97      inference(predicate_to_equality,[status(thm)],[c_872]) ).
% 2.14/0.97  
% 2.14/0.97  cnf(c_1023,plain,
% 2.14/0.97      ( ~ r1_xboole_0(k2_zfmisc_1(sK8,sK9),k1_tarski(sK10))
% 2.14/0.97      | r1_xboole_0(sK7,k1_tarski(sK10)) ),
% 2.14/0.97      inference(instantiation,[status(thm)],[c_215]) ).
% 2.14/0.97  
% 2.14/0.97  cnf(c_1024,plain,
% 2.14/0.97      ( r1_xboole_0(k2_zfmisc_1(sK8,sK9),k1_tarski(sK10)) != iProver_top
% 2.14/0.97      | r1_xboole_0(sK7,k1_tarski(sK10)) = iProver_top ),
% 2.14/0.97      inference(predicate_to_equality,[status(thm)],[c_1023]) ).
% 2.14/0.97  
% 2.14/0.97  cnf(c_6423,plain,
% 2.14/0.97      ( r2_hidden(sK10,k2_zfmisc_1(sK8,sK9)) = iProver_top ),
% 2.14/0.97      inference(global_propositional_subsumption,
% 2.14/0.97                [status(thm)],
% 2.14/0.97                [c_6125,c_20,c_53,c_873,c_1024]) ).
% 2.14/0.97  
% 2.14/0.97  cnf(c_13,plain,
% 2.14/0.97      ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
% 2.14/0.97      | k4_tarski(sK5(X1,X2,X0),sK6(X1,X2,X0)) = X0 ),
% 2.14/0.97      inference(cnf_transformation,[],[f51]) ).
% 2.14/0.97  
% 2.14/0.97  cnf(c_661,plain,
% 2.14/0.97      ( k4_tarski(sK5(X0,X1,X2),sK6(X0,X1,X2)) = X2
% 2.14/0.97      | r2_hidden(X2,k2_zfmisc_1(X0,X1)) != iProver_top ),
% 2.14/0.97      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 2.14/0.97  
% 2.14/0.97  cnf(c_6430,plain,
% 2.14/0.97      ( k4_tarski(sK5(sK8,sK9,sK10),sK6(sK8,sK9,sK10)) = sK10 ),
% 2.14/0.97      inference(superposition,[status(thm)],[c_6423,c_661]) ).
% 2.14/0.97  
% 2.14/0.97  cnf(c_16,negated_conjecture,
% 2.14/0.97      ( ~ r2_hidden(X0,sK8)
% 2.14/0.97      | ~ r2_hidden(X1,sK9)
% 2.14/0.97      | k4_tarski(X0,X1) != sK10 ),
% 2.14/0.97      inference(cnf_transformation,[],[f45]) ).
% 2.14/0.97  
% 2.14/0.97  cnf(c_658,plain,
% 2.14/0.97      ( k4_tarski(X0,X1) != sK10
% 2.14/0.97      | r2_hidden(X0,sK8) != iProver_top
% 2.14/0.97      | r2_hidden(X1,sK9) != iProver_top ),
% 2.14/0.97      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 2.14/0.97  
% 2.14/0.97  cnf(c_6729,plain,
% 2.14/0.97      ( r2_hidden(sK6(sK8,sK9,sK10),sK9) != iProver_top
% 2.14/0.97      | r2_hidden(sK5(sK8,sK9,sK10),sK8) != iProver_top ),
% 2.14/0.97      inference(superposition,[status(thm)],[c_6430,c_658]) ).
% 2.14/0.97  
% 2.14/0.97  cnf(c_7094,plain,
% 2.14/0.97      ( r2_hidden(sK6(sK8,sK9,sK10),sK9) != iProver_top
% 2.14/0.97      | r2_hidden(sK10,k2_zfmisc_1(sK8,sK9)) != iProver_top ),
% 2.14/0.97      inference(superposition,[status(thm)],[c_659,c_6729]) ).
% 2.14/0.97  
% 2.14/0.97  cnf(c_7515,plain,
% 2.14/0.97      ( r2_hidden(sK6(sK8,sK9,sK10),sK9) != iProver_top ),
% 2.14/0.97      inference(global_propositional_subsumption,
% 2.14/0.97                [status(thm)],
% 2.14/0.97                [c_7094,c_20,c_53,c_873,c_1024,c_6125]) ).
% 2.14/0.97  
% 2.14/0.97  cnf(c_7520,plain,
% 2.14/0.97      ( r2_hidden(sK10,k2_zfmisc_1(sK8,sK9)) != iProver_top ),
% 2.14/0.97      inference(superposition,[status(thm)],[c_660,c_7515]) ).
% 2.14/0.97  
% 2.14/0.97  cnf(contradiction,plain,
% 2.14/0.97      ( $false ),
% 2.14/0.97      inference(minisat,
% 2.14/0.97                [status(thm)],
% 2.14/0.97                [c_7520,c_6125,c_1024,c_873,c_53,c_20]) ).
% 2.14/0.97  
% 2.14/0.97  
% 2.14/0.97  % SZS output end CNFRefutation for theBenchmark.p
% 2.14/0.97  
% 2.14/0.97  ------                               Statistics
% 2.14/0.97  
% 2.14/0.97  ------ General
% 2.14/0.97  
% 2.14/0.97  abstr_ref_over_cycles:                  0
% 2.14/0.97  abstr_ref_under_cycles:                 0
% 2.14/0.97  gc_basic_clause_elim:                   0
% 2.14/0.97  forced_gc_time:                         0
% 2.14/0.97  parsing_time:                           0.007
% 2.14/0.97  unif_index_cands_time:                  0.
% 2.14/0.97  unif_index_add_time:                    0.
% 2.14/0.97  orderings_time:                         0.
% 2.14/0.97  out_proof_time:                         0.006
% 2.14/0.97  total_time:                             0.214
% 2.14/0.97  num_of_symbols:                         48
% 2.14/0.97  num_of_terms:                           13088
% 2.14/0.97  
% 2.14/0.97  ------ Preprocessing
% 2.14/0.97  
% 2.14/0.97  num_of_splits:                          0
% 2.14/0.97  num_of_split_atoms:                     0
% 2.14/0.97  num_of_reused_defs:                     0
% 2.14/0.97  num_eq_ax_congr_red:                    64
% 2.14/0.97  num_of_sem_filtered_clauses:            1
% 2.14/0.97  num_of_subtypes:                        0
% 2.14/0.97  monotx_restored_types:                  0
% 2.14/0.97  sat_num_of_epr_types:                   0
% 2.14/0.97  sat_num_of_non_cyclic_types:            0
% 2.14/0.97  sat_guarded_non_collapsed_types:        0
% 2.14/0.97  num_pure_diseq_elim:                    0
% 2.14/0.97  simp_replaced_by:                       0
% 2.14/0.97  res_preprocessed:                       86
% 2.14/0.97  prep_upred:                             0
% 2.14/0.97  prep_unflattend:                        2
% 2.14/0.97  smt_new_axioms:                         0
% 2.14/0.97  pred_elim_cands:                        2
% 2.14/0.97  pred_elim:                              1
% 2.14/0.97  pred_elim_cl:                           1
% 2.14/0.97  pred_elim_cycles:                       3
% 2.14/0.97  merged_defs:                            0
% 2.14/0.97  merged_defs_ncl:                        0
% 2.14/0.97  bin_hyper_res:                          0
% 2.14/0.97  prep_cycles:                            4
% 2.14/0.97  pred_elim_time:                         0.
% 2.14/0.97  splitting_time:                         0.
% 2.14/0.97  sem_filter_time:                        0.
% 2.14/0.97  monotx_time:                            0.
% 2.14/0.97  subtype_inf_time:                       0.
% 2.14/0.97  
% 2.14/0.97  ------ Problem properties
% 2.14/0.97  
% 2.14/0.97  clauses:                                18
% 2.14/0.97  conjectures:                            2
% 2.14/0.97  epr:                                    2
% 2.14/0.97  horn:                                   12
% 2.14/0.97  ground:                                 1
% 2.14/0.97  unary:                                  2
% 2.14/0.97  binary:                                 7
% 2.14/0.97  lits:                                   45
% 2.14/0.97  lits_eq:                                13
% 2.14/0.97  fd_pure:                                0
% 2.14/0.97  fd_pseudo:                              0
% 2.14/0.97  fd_cond:                                0
% 2.14/0.97  fd_pseudo_cond:                         6
% 2.14/0.97  ac_symbols:                             0
% 2.14/0.97  
% 2.14/0.97  ------ Propositional Solver
% 2.14/0.97  
% 2.14/0.97  prop_solver_calls:                      27
% 2.14/0.97  prop_fast_solver_calls:                 552
% 2.14/0.97  smt_solver_calls:                       0
% 2.14/0.97  smt_fast_solver_calls:                  0
% 2.14/0.97  prop_num_of_clauses:                    3144
% 2.14/0.97  prop_preprocess_simplified:             7567
% 2.14/0.97  prop_fo_subsumed:                       3
% 2.14/0.97  prop_solver_time:                       0.
% 2.14/0.97  smt_solver_time:                        0.
% 2.14/0.97  smt_fast_solver_time:                   0.
% 2.14/0.97  prop_fast_solver_time:                  0.
% 2.14/0.97  prop_unsat_core_time:                   0.
% 2.14/0.97  
% 2.14/0.97  ------ QBF
% 2.14/0.97  
% 2.14/0.97  qbf_q_res:                              0
% 2.14/0.97  qbf_num_tautologies:                    0
% 2.14/0.97  qbf_prep_cycles:                        0
% 2.14/0.97  
% 2.14/0.97  ------ BMC1
% 2.14/0.97  
% 2.14/0.97  bmc1_current_bound:                     -1
% 2.14/0.97  bmc1_last_solved_bound:                 -1
% 2.14/0.97  bmc1_unsat_core_size:                   -1
% 2.14/0.97  bmc1_unsat_core_parents_size:           -1
% 2.14/0.97  bmc1_merge_next_fun:                    0
% 2.14/0.97  bmc1_unsat_core_clauses_time:           0.
% 2.14/0.97  
% 2.14/0.97  ------ Instantiation
% 2.14/0.97  
% 2.14/0.97  inst_num_of_clauses:                    817
% 2.14/0.97  inst_num_in_passive:                    260
% 2.14/0.97  inst_num_in_active:                     240
% 2.14/0.97  inst_num_in_unprocessed:                317
% 2.14/0.97  inst_num_of_loops:                      280
% 2.14/0.97  inst_num_of_learning_restarts:          0
% 2.14/0.97  inst_num_moves_active_passive:          39
% 2.14/0.97  inst_lit_activity:                      0
% 2.14/0.97  inst_lit_activity_moves:                0
% 2.14/0.97  inst_num_tautologies:                   0
% 2.14/0.97  inst_num_prop_implied:                  0
% 2.14/0.97  inst_num_existing_simplified:           0
% 2.14/0.97  inst_num_eq_res_simplified:             0
% 2.14/0.97  inst_num_child_elim:                    0
% 2.14/0.97  inst_num_of_dismatching_blockings:      1081
% 2.14/0.97  inst_num_of_non_proper_insts:           498
% 2.14/0.97  inst_num_of_duplicates:                 0
% 2.14/0.97  inst_inst_num_from_inst_to_res:         0
% 2.14/0.97  inst_dismatching_checking_time:         0.
% 2.14/0.97  
% 2.14/0.97  ------ Resolution
% 2.14/0.97  
% 2.14/0.97  res_num_of_clauses:                     0
% 2.14/0.97  res_num_in_passive:                     0
% 2.14/0.97  res_num_in_active:                      0
% 2.14/0.97  res_num_of_loops:                       90
% 2.14/0.97  res_forward_subset_subsumed:            9
% 2.14/0.97  res_backward_subset_subsumed:           0
% 2.14/0.97  res_forward_subsumed:                   0
% 2.14/0.97  res_backward_subsumed:                  0
% 2.14/0.97  res_forward_subsumption_resolution:     0
% 2.14/0.97  res_backward_subsumption_resolution:    0
% 2.14/0.97  res_clause_to_clause_subsumption:       498
% 2.14/0.97  res_orphan_elimination:                 0
% 2.14/0.97  res_tautology_del:                      14
% 2.14/0.97  res_num_eq_res_simplified:              0
% 2.14/0.97  res_num_sel_changes:                    0
% 2.14/0.97  res_moves_from_active_to_pass:          0
% 2.14/0.97  
% 2.14/0.97  ------ Superposition
% 2.14/0.97  
% 2.14/0.97  sup_time_total:                         0.
% 2.14/0.97  sup_time_generating:                    0.
% 2.14/0.97  sup_time_sim_full:                      0.
% 2.14/0.97  sup_time_sim_immed:                     0.
% 2.14/0.97  
% 2.14/0.97  sup_num_of_clauses:                     188
% 2.14/0.97  sup_num_in_active:                      54
% 2.14/0.97  sup_num_in_passive:                     134
% 2.14/0.97  sup_num_of_loops:                       54
% 2.14/0.97  sup_fw_superposition:                   88
% 2.14/0.97  sup_bw_superposition:                   114
% 2.14/0.97  sup_immediate_simplified:               23
% 2.14/0.97  sup_given_eliminated:                   0
% 2.14/0.97  comparisons_done:                       0
% 2.14/0.97  comparisons_avoided:                    3
% 2.14/0.97  
% 2.14/0.97  ------ Simplifications
% 2.14/0.97  
% 2.14/0.97  
% 2.14/0.97  sim_fw_subset_subsumed:                 7
% 2.14/0.97  sim_bw_subset_subsumed:                 3
% 2.14/0.97  sim_fw_subsumed:                        12
% 2.14/0.97  sim_bw_subsumed:                        0
% 2.14/0.97  sim_fw_subsumption_res:                 0
% 2.14/0.97  sim_bw_subsumption_res:                 0
% 2.14/0.97  sim_tautology_del:                      2
% 2.14/0.97  sim_eq_tautology_del:                   3
% 2.14/0.97  sim_eq_res_simp:                        0
% 2.14/0.97  sim_fw_demodulated:                     0
% 2.14/0.97  sim_bw_demodulated:                     0
% 2.14/0.97  sim_light_normalised:                   3
% 2.14/0.97  sim_joinable_taut:                      0
% 2.14/0.97  sim_joinable_simp:                      0
% 2.14/0.97  sim_ac_normalised:                      0
% 2.14/0.97  sim_smt_subsumption:                    0
% 2.14/0.97  
%------------------------------------------------------------------------------
