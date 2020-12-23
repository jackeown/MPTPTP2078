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
% DateTime   : Thu Dec  3 11:57:17 EST 2020

% Result     : Theorem 3.28s
% Output     : CNFRefutation 3.28s
% Verified   : 
% Statistics : Number of formulae       :   82 ( 176 expanded)
%              Number of clauses        :   44 (  68 expanded)
%              Number of leaves         :   12 (  39 expanded)
%              Depth                    :   17
%              Number of atoms          :  293 ( 705 expanded)
%              Number of equality atoms :  120 ( 222 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal clause size      :   18 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( k2_zfmisc_1(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ? [X4,X5] :
              ( k4_tarski(X4,X5) = X3
              & r2_hidden(X5,X1)
              & r2_hidden(X4,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
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

fof(f15,plain,(
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
    inference(rectify,[],[f14])).

fof(f18,plain,(
    ! [X8,X1,X0] :
      ( ? [X11,X12] :
          ( k4_tarski(X11,X12) = X8
          & r2_hidden(X12,X1)
          & r2_hidden(X11,X0) )
     => ( k4_tarski(sK4(X0,X1,X8),sK5(X0,X1,X8)) = X8
        & r2_hidden(sK5(X0,X1,X8),X1)
        & r2_hidden(sK4(X0,X1,X8),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X6,X7] :
          ( k4_tarski(X6,X7) = X3
          & r2_hidden(X7,X1)
          & r2_hidden(X6,X0) )
     => ( k4_tarski(sK2(X0,X1,X2),sK3(X0,X1,X2)) = X3
        & r2_hidden(sK3(X0,X1,X2),X1)
        & r2_hidden(sK2(X0,X1,X2),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
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

fof(f19,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4,sK5])],[f15,f18,f17,f16])).

fof(f33,plain,(
    ! [X2,X0,X1] :
      ( k2_zfmisc_1(X0,X1) = X2
      | r2_hidden(sK2(X0,X1,X2),X0)
      | r2_hidden(sK1(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) = k1_xboole_0
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( k2_zfmisc_1(X0,X1) = k1_xboole_0
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k2_zfmisc_1(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( k2_zfmisc_1(X0,X1) = k1_xboole_0
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k2_zfmisc_1(X0,X1) != k1_xboole_0 ) ) ),
    inference(flattening,[],[f20])).

fof(f39,plain,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) = k1_xboole_0
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f21])).

fof(f49,plain,(
    ! [X0] : k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(equality_resolution,[],[f39])).

fof(f29,plain,(
    ! [X2,X0,X8,X1] :
      ( r2_hidden(sK4(X0,X1,X8),X0)
      | ~ r2_hidden(X8,X2)
      | k2_zfmisc_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f19])).

fof(f48,plain,(
    ! [X0,X8,X1] :
      ( r2_hidden(sK4(X0,X1,X8),X0)
      | ~ r2_hidden(X8,k2_zfmisc_1(X0,X1)) ) ),
    inference(equality_resolution,[],[f29])).

fof(f5,axiom,(
    ! [X0,X1] :
      ~ ( ! [X2] :
            ~ ( ! [X3] :
                  ~ ( r2_hidden(X3,X2)
                    & r2_hidden(X3,X1) )
              & r2_hidden(X2,X1) )
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f10,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ! [X3] :
              ( ~ r2_hidden(X3,X2)
              | ~ r2_hidden(X3,X1) )
          & r2_hidden(X2,X1) )
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f22,plain,(
    ! [X1] :
      ( ? [X2] :
          ( ! [X3] :
              ( ~ r2_hidden(X3,X2)
              | ~ r2_hidden(X3,X1) )
          & r2_hidden(X2,X1) )
     => ( ! [X3] :
            ( ~ r2_hidden(X3,sK6(X1))
            | ~ r2_hidden(X3,X1) )
        & r2_hidden(sK6(X1),X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( ! [X3] :
            ( ~ r2_hidden(X3,sK6(X1))
            | ~ r2_hidden(X3,X1) )
        & r2_hidden(sK6(X1),X1) )
      | ~ r2_hidden(X0,X1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f10,f22])).

fof(f40,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK6(X1),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f38,plain,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) = k1_xboole_0
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f21])).

fof(f50,plain,(
    ! [X1] : k2_zfmisc_1(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(equality_resolution,[],[f38])).

fof(f6,conjecture,(
    ! [X0] :
      ~ ( ! [X1] :
            ~ ( r1_xboole_0(X1,X0)
              & r2_hidden(X1,X0) )
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f7,negated_conjecture,(
    ~ ! [X0] :
        ~ ( ! [X1] :
              ~ ( r1_xboole_0(X1,X0)
                & r2_hidden(X1,X0) )
          & k1_xboole_0 != X0 ) ),
    inference(negated_conjecture,[],[f6])).

fof(f11,plain,(
    ? [X0] :
      ( ! [X1] :
          ( ~ r1_xboole_0(X1,X0)
          | ~ r2_hidden(X1,X0) )
      & k1_xboole_0 != X0 ) ),
    inference(ennf_transformation,[],[f7])).

fof(f24,plain,
    ( ? [X0] :
        ( ! [X1] :
            ( ~ r1_xboole_0(X1,X0)
            | ~ r2_hidden(X1,X0) )
        & k1_xboole_0 != X0 )
   => ( ! [X1] :
          ( ~ r1_xboole_0(X1,sK7)
          | ~ r2_hidden(X1,sK7) )
      & k1_xboole_0 != sK7 ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,
    ( ! [X1] :
        ( ~ r1_xboole_0(X1,sK7)
        | ~ r2_hidden(X1,sK7) )
    & k1_xboole_0 != sK7 ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f11,f24])).

fof(f43,plain,(
    ! [X1] :
      ( ~ r1_xboole_0(X1,sK7)
      | ~ r2_hidden(X1,sK7) ) ),
    inference(cnf_transformation,[],[f25])).

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

fof(f12,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
     => ( r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ( r2_hidden(sK0(X0,X1),X1)
          & r2_hidden(sK0(X0,X1),X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f9,f12])).

fof(f27,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK0(X0,X1),X1)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f41,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,sK6(X1))
      | ~ r2_hidden(X3,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f26,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK0(X0,X1),X0)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f37,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | k2_zfmisc_1(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f21])).

fof(f42,plain,(
    k1_xboole_0 != sK7 ),
    inference(cnf_transformation,[],[f25])).

cnf(c_6,plain,
    ( r2_hidden(sK2(X0,X1,X2),X0)
    | r2_hidden(sK1(X0,X1,X2),X2)
    | k2_zfmisc_1(X0,X1) = X2 ),
    inference(cnf_transformation,[],[f33])).

cnf(c_498,plain,
    ( k2_zfmisc_1(X0,X1) = X2
    | r2_hidden(sK2(X0,X1,X2),X0) = iProver_top
    | r2_hidden(sK1(X0,X1,X2),X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_11,plain,
    ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f49])).

cnf(c_10,plain,
    ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
    | r2_hidden(sK4(X1,X2,X0),X1) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_494,plain,
    ( r2_hidden(X0,k2_zfmisc_1(X1,X2)) != iProver_top
    | r2_hidden(sK4(X1,X2,X0),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_15,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(sK6(X1),X1) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_492,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(sK6(X1),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_786,plain,
    ( r2_hidden(X0,k2_zfmisc_1(X1,X2)) != iProver_top
    | r2_hidden(sK6(X1),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_494,c_492])).

cnf(c_964,plain,
    ( r2_hidden(X0,k1_xboole_0) != iProver_top
    | r2_hidden(sK6(X1),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_11,c_786])).

cnf(c_3515,plain,
    ( k2_zfmisc_1(k1_xboole_0,X0) = X1
    | r2_hidden(sK1(k1_xboole_0,X0,X1),X1) = iProver_top
    | r2_hidden(sK6(X2),X2) = iProver_top ),
    inference(superposition,[status(thm)],[c_498,c_964])).

cnf(c_12,plain,
    ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f50])).

cnf(c_3591,plain,
    ( k1_xboole_0 = X0
    | r2_hidden(sK1(k1_xboole_0,X1,X0),X0) = iProver_top
    | r2_hidden(sK6(X2),X2) = iProver_top ),
    inference(demodulation,[status(thm)],[c_3515,c_12])).

cnf(c_16,negated_conjecture,
    ( ~ r2_hidden(X0,sK7)
    | ~ r1_xboole_0(X0,sK7) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_491,plain,
    ( r2_hidden(X0,sK7) != iProver_top
    | r1_xboole_0(X0,sK7) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_3920,plain,
    ( k1_xboole_0 = X0
    | r2_hidden(sK1(k1_xboole_0,X1,X0),X0) = iProver_top
    | r1_xboole_0(sK6(sK7),sK7) != iProver_top ),
    inference(superposition,[status(thm)],[c_3591,c_491])).

cnf(c_4842,plain,
    ( k1_xboole_0 = X0
    | r2_hidden(sK6(X0),X0) = iProver_top
    | r1_xboole_0(sK6(sK7),sK7) != iProver_top ),
    inference(superposition,[status(thm)],[c_3920,c_492])).

cnf(c_1,plain,
    ( r2_hidden(sK0(X0,X1),X1)
    | r1_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f27])).

cnf(c_1007,plain,
    ( r2_hidden(sK0(sK6(X0),X0),X0)
    | r1_xboole_0(sK6(X0),X0) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_1584,plain,
    ( r2_hidden(sK0(sK6(sK7),sK7),sK7)
    | r1_xboole_0(sK6(sK7),sK7) ),
    inference(instantiation,[status(thm)],[c_1007])).

cnf(c_1586,plain,
    ( r2_hidden(sK0(sK6(sK7),sK7),sK7) = iProver_top
    | r1_xboole_0(sK6(sK7),sK7) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1584])).

cnf(c_14,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X2,X1)
    | ~ r2_hidden(X2,sK6(X1)) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_650,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(sK0(X2,X1),X1)
    | ~ r2_hidden(sK0(X2,X1),sK6(X1)) ),
    inference(instantiation,[status(thm)],[c_14])).

cnf(c_770,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(sK0(sK6(X1),X1),X1)
    | ~ r2_hidden(sK0(sK6(X1),X1),sK6(X1)) ),
    inference(instantiation,[status(thm)],[c_650])).

cnf(c_6358,plain,
    ( ~ r2_hidden(sK0(sK6(sK7),sK7),sK6(sK7))
    | ~ r2_hidden(sK0(sK6(sK7),sK7),sK7)
    | ~ r2_hidden(sK6(sK7),sK7) ),
    inference(instantiation,[status(thm)],[c_770])).

cnf(c_6364,plain,
    ( r2_hidden(sK0(sK6(sK7),sK7),sK6(sK7)) != iProver_top
    | r2_hidden(sK0(sK6(sK7),sK7),sK7) != iProver_top
    | r2_hidden(sK6(sK7),sK7) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6358])).

cnf(c_2,plain,
    ( r2_hidden(sK0(X0,X1),X0)
    | r1_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f26])).

cnf(c_771,plain,
    ( r2_hidden(sK0(sK6(X0),X0),sK6(X0))
    | r1_xboole_0(sK6(X0),X0) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_7555,plain,
    ( r2_hidden(sK0(sK6(sK7),sK7),sK6(sK7))
    | r1_xboole_0(sK6(sK7),sK7) ),
    inference(instantiation,[status(thm)],[c_771])).

cnf(c_7556,plain,
    ( r2_hidden(sK0(sK6(sK7),sK7),sK6(sK7)) = iProver_top
    | r1_xboole_0(sK6(sK7),sK7) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7555])).

cnf(c_632,plain,
    ( ~ r2_hidden(sK0(X0,X1),X1)
    | r2_hidden(sK6(X1),X1) ),
    inference(instantiation,[status(thm)],[c_15])).

cnf(c_1590,plain,
    ( ~ r2_hidden(sK0(sK6(X0),X0),X0)
    | r2_hidden(sK6(X0),X0) ),
    inference(instantiation,[status(thm)],[c_632])).

cnf(c_7575,plain,
    ( ~ r2_hidden(sK0(sK6(sK7),sK7),sK7)
    | r2_hidden(sK6(sK7),sK7) ),
    inference(instantiation,[status(thm)],[c_1590])).

cnf(c_7576,plain,
    ( r2_hidden(sK0(sK6(sK7),sK7),sK7) != iProver_top
    | r2_hidden(sK6(sK7),sK7) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7575])).

cnf(c_8756,plain,
    ( r2_hidden(sK6(X0),X0) = iProver_top
    | k1_xboole_0 = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_4842,c_1586,c_6364,c_7556,c_7576])).

cnf(c_8757,plain,
    ( k1_xboole_0 = X0
    | r2_hidden(sK6(X0),X0) = iProver_top ),
    inference(renaming,[status(thm)],[c_8756])).

cnf(c_8769,plain,
    ( sK7 = k1_xboole_0
    | r1_xboole_0(sK6(sK7),sK7) != iProver_top ),
    inference(superposition,[status(thm)],[c_8757,c_491])).

cnf(c_228,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_658,plain,
    ( sK7 != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = sK7 ),
    inference(instantiation,[status(thm)],[c_228])).

cnf(c_659,plain,
    ( sK7 != k1_xboole_0
    | k1_xboole_0 = sK7
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_658])).

cnf(c_28,plain,
    ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_13,plain,
    ( k2_zfmisc_1(X0,X1) != k1_xboole_0
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f37])).

cnf(c_27,plain,
    ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) != k1_xboole_0
    | k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_13])).

cnf(c_17,negated_conjecture,
    ( k1_xboole_0 != sK7 ),
    inference(cnf_transformation,[],[f42])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_8769,c_7576,c_7556,c_6364,c_1586,c_659,c_28,c_27,c_17])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : iproveropt_run.sh %d %s
% 0.14/0.34  % Computer   : n012.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 10:36:52 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running in FOF mode
% 3.28/1.02  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.28/1.02  
% 3.28/1.02  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.28/1.02  
% 3.28/1.02  ------  iProver source info
% 3.28/1.02  
% 3.28/1.02  git: date: 2020-06-30 10:37:57 +0100
% 3.28/1.02  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.28/1.02  git: non_committed_changes: false
% 3.28/1.02  git: last_make_outside_of_git: false
% 3.28/1.02  
% 3.28/1.02  ------ 
% 3.28/1.02  ------ Parsing...
% 3.28/1.02  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.28/1.02  
% 3.28/1.02  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 3.28/1.02  
% 3.28/1.02  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.28/1.02  
% 3.28/1.02  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.28/1.02  ------ Proving...
% 3.28/1.02  ------ Problem Properties 
% 3.28/1.02  
% 3.28/1.02  
% 3.28/1.02  clauses                                 18
% 3.28/1.02  conjectures                             2
% 3.28/1.02  EPR                                     3
% 3.28/1.02  Horn                                    12
% 3.28/1.02  unary                                   3
% 3.28/1.02  binary                                  7
% 3.28/1.02  lits                                    43
% 3.28/1.02  lits eq                                 13
% 3.28/1.02  fd_pure                                 0
% 3.28/1.02  fd_pseudo                               0
% 3.28/1.02  fd_cond                                 1
% 3.28/1.02  fd_pseudo_cond                          4
% 3.28/1.02  AC symbols                              0
% 3.28/1.02  
% 3.28/1.02  ------ Input Options Time Limit: Unbounded
% 3.28/1.02  
% 3.28/1.02  
% 3.28/1.02  ------ 
% 3.28/1.02  Current options:
% 3.28/1.02  ------ 
% 3.28/1.02  
% 3.28/1.02  
% 3.28/1.02  
% 3.28/1.02  
% 3.28/1.02  ------ Proving...
% 3.28/1.02  
% 3.28/1.02  
% 3.28/1.02  % SZS status Theorem for theBenchmark.p
% 3.28/1.02  
% 3.28/1.02  % SZS output start CNFRefutation for theBenchmark.p
% 3.28/1.02  
% 3.28/1.02  fof(f3,axiom,(
% 3.28/1.02    ! [X0,X1,X2] : (k2_zfmisc_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4,X5] : (k4_tarski(X4,X5) = X3 & r2_hidden(X5,X1) & r2_hidden(X4,X0))))),
% 3.28/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.28/1.02  
% 3.28/1.02  fof(f14,plain,(
% 3.28/1.02    ! [X0,X1,X2] : ((k2_zfmisc_1(X0,X1) = X2 | ? [X3] : ((! [X4,X5] : (k4_tarski(X4,X5) != X3 | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X0)) | ~r2_hidden(X3,X2)) & (? [X4,X5] : (k4_tarski(X4,X5) = X3 & r2_hidden(X5,X1) & r2_hidden(X4,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ! [X4,X5] : (k4_tarski(X4,X5) != X3 | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X0))) & (? [X4,X5] : (k4_tarski(X4,X5) = X3 & r2_hidden(X5,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X3,X2))) | k2_zfmisc_1(X0,X1) != X2))),
% 3.28/1.02    inference(nnf_transformation,[],[f3])).
% 3.28/1.02  
% 3.28/1.02  fof(f15,plain,(
% 3.28/1.02    ! [X0,X1,X2] : ((k2_zfmisc_1(X0,X1) = X2 | ? [X3] : ((! [X4,X5] : (k4_tarski(X4,X5) != X3 | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X0)) | ~r2_hidden(X3,X2)) & (? [X6,X7] : (k4_tarski(X6,X7) = X3 & r2_hidden(X7,X1) & r2_hidden(X6,X0)) | r2_hidden(X3,X2)))) & (! [X8] : ((r2_hidden(X8,X2) | ! [X9,X10] : (k4_tarski(X9,X10) != X8 | ~r2_hidden(X10,X1) | ~r2_hidden(X9,X0))) & (? [X11,X12] : (k4_tarski(X11,X12) = X8 & r2_hidden(X12,X1) & r2_hidden(X11,X0)) | ~r2_hidden(X8,X2))) | k2_zfmisc_1(X0,X1) != X2))),
% 3.28/1.02    inference(rectify,[],[f14])).
% 3.28/1.02  
% 3.28/1.02  fof(f18,plain,(
% 3.28/1.02    ! [X8,X1,X0] : (? [X11,X12] : (k4_tarski(X11,X12) = X8 & r2_hidden(X12,X1) & r2_hidden(X11,X0)) => (k4_tarski(sK4(X0,X1,X8),sK5(X0,X1,X8)) = X8 & r2_hidden(sK5(X0,X1,X8),X1) & r2_hidden(sK4(X0,X1,X8),X0)))),
% 3.28/1.02    introduced(choice_axiom,[])).
% 3.28/1.02  
% 3.28/1.02  fof(f17,plain,(
% 3.28/1.02    ( ! [X3] : (! [X2,X1,X0] : (? [X6,X7] : (k4_tarski(X6,X7) = X3 & r2_hidden(X7,X1) & r2_hidden(X6,X0)) => (k4_tarski(sK2(X0,X1,X2),sK3(X0,X1,X2)) = X3 & r2_hidden(sK3(X0,X1,X2),X1) & r2_hidden(sK2(X0,X1,X2),X0)))) )),
% 3.28/1.02    introduced(choice_axiom,[])).
% 3.28/1.02  
% 3.28/1.02  fof(f16,plain,(
% 3.28/1.02    ! [X2,X1,X0] : (? [X3] : ((! [X4,X5] : (k4_tarski(X4,X5) != X3 | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X0)) | ~r2_hidden(X3,X2)) & (? [X6,X7] : (k4_tarski(X6,X7) = X3 & r2_hidden(X7,X1) & r2_hidden(X6,X0)) | r2_hidden(X3,X2))) => ((! [X5,X4] : (k4_tarski(X4,X5) != sK1(X0,X1,X2) | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X0)) | ~r2_hidden(sK1(X0,X1,X2),X2)) & (? [X7,X6] : (k4_tarski(X6,X7) = sK1(X0,X1,X2) & r2_hidden(X7,X1) & r2_hidden(X6,X0)) | r2_hidden(sK1(X0,X1,X2),X2))))),
% 3.28/1.02    introduced(choice_axiom,[])).
% 3.28/1.02  
% 3.28/1.02  fof(f19,plain,(
% 3.28/1.02    ! [X0,X1,X2] : ((k2_zfmisc_1(X0,X1) = X2 | ((! [X4,X5] : (k4_tarski(X4,X5) != sK1(X0,X1,X2) | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X0)) | ~r2_hidden(sK1(X0,X1,X2),X2)) & ((k4_tarski(sK2(X0,X1,X2),sK3(X0,X1,X2)) = sK1(X0,X1,X2) & r2_hidden(sK3(X0,X1,X2),X1) & r2_hidden(sK2(X0,X1,X2),X0)) | r2_hidden(sK1(X0,X1,X2),X2)))) & (! [X8] : ((r2_hidden(X8,X2) | ! [X9,X10] : (k4_tarski(X9,X10) != X8 | ~r2_hidden(X10,X1) | ~r2_hidden(X9,X0))) & ((k4_tarski(sK4(X0,X1,X8),sK5(X0,X1,X8)) = X8 & r2_hidden(sK5(X0,X1,X8),X1) & r2_hidden(sK4(X0,X1,X8),X0)) | ~r2_hidden(X8,X2))) | k2_zfmisc_1(X0,X1) != X2))),
% 3.28/1.02    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4,sK5])],[f15,f18,f17,f16])).
% 3.28/1.02  
% 3.28/1.02  fof(f33,plain,(
% 3.28/1.02    ( ! [X2,X0,X1] : (k2_zfmisc_1(X0,X1) = X2 | r2_hidden(sK2(X0,X1,X2),X0) | r2_hidden(sK1(X0,X1,X2),X2)) )),
% 3.28/1.02    inference(cnf_transformation,[],[f19])).
% 3.28/1.02  
% 3.28/1.02  fof(f4,axiom,(
% 3.28/1.02    ! [X0,X1] : (k2_zfmisc_1(X0,X1) = k1_xboole_0 <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 3.28/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.28/1.02  
% 3.28/1.02  fof(f20,plain,(
% 3.28/1.02    ! [X0,X1] : ((k2_zfmisc_1(X0,X1) = k1_xboole_0 | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k2_zfmisc_1(X0,X1) != k1_xboole_0))),
% 3.28/1.02    inference(nnf_transformation,[],[f4])).
% 3.28/1.02  
% 3.28/1.02  fof(f21,plain,(
% 3.28/1.02    ! [X0,X1] : ((k2_zfmisc_1(X0,X1) = k1_xboole_0 | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k2_zfmisc_1(X0,X1) != k1_xboole_0))),
% 3.28/1.02    inference(flattening,[],[f20])).
% 3.28/1.02  
% 3.28/1.02  fof(f39,plain,(
% 3.28/1.02    ( ! [X0,X1] : (k2_zfmisc_1(X0,X1) = k1_xboole_0 | k1_xboole_0 != X1) )),
% 3.28/1.02    inference(cnf_transformation,[],[f21])).
% 3.28/1.02  
% 3.28/1.02  fof(f49,plain,(
% 3.28/1.02    ( ! [X0] : (k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0) )),
% 3.28/1.02    inference(equality_resolution,[],[f39])).
% 3.28/1.02  
% 3.28/1.02  fof(f29,plain,(
% 3.28/1.02    ( ! [X2,X0,X8,X1] : (r2_hidden(sK4(X0,X1,X8),X0) | ~r2_hidden(X8,X2) | k2_zfmisc_1(X0,X1) != X2) )),
% 3.28/1.02    inference(cnf_transformation,[],[f19])).
% 3.28/1.02  
% 3.28/1.02  fof(f48,plain,(
% 3.28/1.02    ( ! [X0,X8,X1] : (r2_hidden(sK4(X0,X1,X8),X0) | ~r2_hidden(X8,k2_zfmisc_1(X0,X1))) )),
% 3.28/1.02    inference(equality_resolution,[],[f29])).
% 3.28/1.02  
% 3.28/1.02  fof(f5,axiom,(
% 3.28/1.02    ! [X0,X1] : ~(! [X2] : ~(! [X3] : ~(r2_hidden(X3,X2) & r2_hidden(X3,X1)) & r2_hidden(X2,X1)) & r2_hidden(X0,X1))),
% 3.28/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.28/1.02  
% 3.28/1.02  fof(f10,plain,(
% 3.28/1.02    ! [X0,X1] : (? [X2] : (! [X3] : (~r2_hidden(X3,X2) | ~r2_hidden(X3,X1)) & r2_hidden(X2,X1)) | ~r2_hidden(X0,X1))),
% 3.28/1.02    inference(ennf_transformation,[],[f5])).
% 3.28/1.02  
% 3.28/1.02  fof(f22,plain,(
% 3.28/1.02    ! [X1] : (? [X2] : (! [X3] : (~r2_hidden(X3,X2) | ~r2_hidden(X3,X1)) & r2_hidden(X2,X1)) => (! [X3] : (~r2_hidden(X3,sK6(X1)) | ~r2_hidden(X3,X1)) & r2_hidden(sK6(X1),X1)))),
% 3.28/1.02    introduced(choice_axiom,[])).
% 3.28/1.02  
% 3.28/1.02  fof(f23,plain,(
% 3.28/1.02    ! [X0,X1] : ((! [X3] : (~r2_hidden(X3,sK6(X1)) | ~r2_hidden(X3,X1)) & r2_hidden(sK6(X1),X1)) | ~r2_hidden(X0,X1))),
% 3.28/1.02    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f10,f22])).
% 3.28/1.02  
% 3.28/1.02  fof(f40,plain,(
% 3.28/1.02    ( ! [X0,X1] : (r2_hidden(sK6(X1),X1) | ~r2_hidden(X0,X1)) )),
% 3.28/1.02    inference(cnf_transformation,[],[f23])).
% 3.28/1.02  
% 3.28/1.02  fof(f38,plain,(
% 3.28/1.02    ( ! [X0,X1] : (k2_zfmisc_1(X0,X1) = k1_xboole_0 | k1_xboole_0 != X0) )),
% 3.28/1.02    inference(cnf_transformation,[],[f21])).
% 3.28/1.02  
% 3.28/1.02  fof(f50,plain,(
% 3.28/1.02    ( ! [X1] : (k2_zfmisc_1(k1_xboole_0,X1) = k1_xboole_0) )),
% 3.28/1.02    inference(equality_resolution,[],[f38])).
% 3.28/1.02  
% 3.28/1.02  fof(f6,conjecture,(
% 3.28/1.02    ! [X0] : ~(! [X1] : ~(r1_xboole_0(X1,X0) & r2_hidden(X1,X0)) & k1_xboole_0 != X0)),
% 3.28/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.28/1.02  
% 3.28/1.02  fof(f7,negated_conjecture,(
% 3.28/1.02    ~! [X0] : ~(! [X1] : ~(r1_xboole_0(X1,X0) & r2_hidden(X1,X0)) & k1_xboole_0 != X0)),
% 3.28/1.02    inference(negated_conjecture,[],[f6])).
% 3.28/1.02  
% 3.28/1.02  fof(f11,plain,(
% 3.28/1.02    ? [X0] : (! [X1] : (~r1_xboole_0(X1,X0) | ~r2_hidden(X1,X0)) & k1_xboole_0 != X0)),
% 3.28/1.02    inference(ennf_transformation,[],[f7])).
% 3.28/1.02  
% 3.28/1.02  fof(f24,plain,(
% 3.28/1.02    ? [X0] : (! [X1] : (~r1_xboole_0(X1,X0) | ~r2_hidden(X1,X0)) & k1_xboole_0 != X0) => (! [X1] : (~r1_xboole_0(X1,sK7) | ~r2_hidden(X1,sK7)) & k1_xboole_0 != sK7)),
% 3.28/1.02    introduced(choice_axiom,[])).
% 3.28/1.02  
% 3.28/1.02  fof(f25,plain,(
% 3.28/1.02    ! [X1] : (~r1_xboole_0(X1,sK7) | ~r2_hidden(X1,sK7)) & k1_xboole_0 != sK7),
% 3.28/1.02    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f11,f24])).
% 3.28/1.02  
% 3.28/1.02  fof(f43,plain,(
% 3.28/1.02    ( ! [X1] : (~r1_xboole_0(X1,sK7) | ~r2_hidden(X1,sK7)) )),
% 3.28/1.02    inference(cnf_transformation,[],[f25])).
% 3.28/1.02  
% 3.28/1.02  fof(f2,axiom,(
% 3.28/1.02    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 3.28/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.28/1.02  
% 3.28/1.02  fof(f8,plain,(
% 3.28/1.02    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 3.28/1.02    inference(rectify,[],[f2])).
% 3.28/1.02  
% 3.28/1.02  fof(f9,plain,(
% 3.28/1.02    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 3.28/1.02    inference(ennf_transformation,[],[f8])).
% 3.28/1.02  
% 3.28/1.02  fof(f12,plain,(
% 3.28/1.02    ! [X1,X0] : (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) => (r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 3.28/1.02    introduced(choice_axiom,[])).
% 3.28/1.02  
% 3.28/1.02  fof(f13,plain,(
% 3.28/1.02    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & ((r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)) | r1_xboole_0(X0,X1)))),
% 3.28/1.02    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f9,f12])).
% 3.28/1.02  
% 3.28/1.02  fof(f27,plain,(
% 3.28/1.02    ( ! [X0,X1] : (r2_hidden(sK0(X0,X1),X1) | r1_xboole_0(X0,X1)) )),
% 3.28/1.02    inference(cnf_transformation,[],[f13])).
% 3.28/1.02  
% 3.28/1.02  fof(f41,plain,(
% 3.28/1.02    ( ! [X0,X3,X1] : (~r2_hidden(X3,sK6(X1)) | ~r2_hidden(X3,X1) | ~r2_hidden(X0,X1)) )),
% 3.28/1.02    inference(cnf_transformation,[],[f23])).
% 3.28/1.02  
% 3.28/1.02  fof(f26,plain,(
% 3.28/1.02    ( ! [X0,X1] : (r2_hidden(sK0(X0,X1),X0) | r1_xboole_0(X0,X1)) )),
% 3.28/1.02    inference(cnf_transformation,[],[f13])).
% 3.28/1.02  
% 3.28/1.02  fof(f37,plain,(
% 3.28/1.02    ( ! [X0,X1] : (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k2_zfmisc_1(X0,X1) != k1_xboole_0) )),
% 3.28/1.02    inference(cnf_transformation,[],[f21])).
% 3.28/1.02  
% 3.28/1.02  fof(f42,plain,(
% 3.28/1.02    k1_xboole_0 != sK7),
% 3.28/1.02    inference(cnf_transformation,[],[f25])).
% 3.28/1.02  
% 3.28/1.02  cnf(c_6,plain,
% 3.28/1.02      ( r2_hidden(sK2(X0,X1,X2),X0)
% 3.28/1.02      | r2_hidden(sK1(X0,X1,X2),X2)
% 3.28/1.02      | k2_zfmisc_1(X0,X1) = X2 ),
% 3.28/1.02      inference(cnf_transformation,[],[f33]) ).
% 3.28/1.02  
% 3.28/1.02  cnf(c_498,plain,
% 3.28/1.02      ( k2_zfmisc_1(X0,X1) = X2
% 3.28/1.02      | r2_hidden(sK2(X0,X1,X2),X0) = iProver_top
% 3.28/1.02      | r2_hidden(sK1(X0,X1,X2),X2) = iProver_top ),
% 3.28/1.02      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 3.28/1.02  
% 3.28/1.02  cnf(c_11,plain,
% 3.28/1.02      ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
% 3.28/1.02      inference(cnf_transformation,[],[f49]) ).
% 3.28/1.02  
% 3.28/1.02  cnf(c_10,plain,
% 3.28/1.02      ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
% 3.28/1.02      | r2_hidden(sK4(X1,X2,X0),X1) ),
% 3.28/1.02      inference(cnf_transformation,[],[f48]) ).
% 3.28/1.02  
% 3.28/1.02  cnf(c_494,plain,
% 3.28/1.02      ( r2_hidden(X0,k2_zfmisc_1(X1,X2)) != iProver_top
% 3.28/1.02      | r2_hidden(sK4(X1,X2,X0),X1) = iProver_top ),
% 3.28/1.02      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 3.28/1.02  
% 3.28/1.02  cnf(c_15,plain,
% 3.28/1.02      ( ~ r2_hidden(X0,X1) | r2_hidden(sK6(X1),X1) ),
% 3.28/1.02      inference(cnf_transformation,[],[f40]) ).
% 3.28/1.02  
% 3.28/1.02  cnf(c_492,plain,
% 3.28/1.02      ( r2_hidden(X0,X1) != iProver_top
% 3.28/1.02      | r2_hidden(sK6(X1),X1) = iProver_top ),
% 3.28/1.02      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 3.28/1.02  
% 3.28/1.02  cnf(c_786,plain,
% 3.28/1.02      ( r2_hidden(X0,k2_zfmisc_1(X1,X2)) != iProver_top
% 3.28/1.02      | r2_hidden(sK6(X1),X1) = iProver_top ),
% 3.28/1.02      inference(superposition,[status(thm)],[c_494,c_492]) ).
% 3.28/1.02  
% 3.28/1.02  cnf(c_964,plain,
% 3.28/1.02      ( r2_hidden(X0,k1_xboole_0) != iProver_top
% 3.28/1.02      | r2_hidden(sK6(X1),X1) = iProver_top ),
% 3.28/1.02      inference(superposition,[status(thm)],[c_11,c_786]) ).
% 3.28/1.02  
% 3.28/1.02  cnf(c_3515,plain,
% 3.28/1.02      ( k2_zfmisc_1(k1_xboole_0,X0) = X1
% 3.28/1.02      | r2_hidden(sK1(k1_xboole_0,X0,X1),X1) = iProver_top
% 3.28/1.02      | r2_hidden(sK6(X2),X2) = iProver_top ),
% 3.28/1.02      inference(superposition,[status(thm)],[c_498,c_964]) ).
% 3.28/1.02  
% 3.28/1.02  cnf(c_12,plain,
% 3.28/1.02      ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
% 3.28/1.02      inference(cnf_transformation,[],[f50]) ).
% 3.28/1.02  
% 3.28/1.02  cnf(c_3591,plain,
% 3.28/1.02      ( k1_xboole_0 = X0
% 3.28/1.02      | r2_hidden(sK1(k1_xboole_0,X1,X0),X0) = iProver_top
% 3.28/1.02      | r2_hidden(sK6(X2),X2) = iProver_top ),
% 3.28/1.02      inference(demodulation,[status(thm)],[c_3515,c_12]) ).
% 3.28/1.02  
% 3.28/1.02  cnf(c_16,negated_conjecture,
% 3.28/1.02      ( ~ r2_hidden(X0,sK7) | ~ r1_xboole_0(X0,sK7) ),
% 3.28/1.02      inference(cnf_transformation,[],[f43]) ).
% 3.28/1.02  
% 3.28/1.02  cnf(c_491,plain,
% 3.28/1.02      ( r2_hidden(X0,sK7) != iProver_top
% 3.28/1.02      | r1_xboole_0(X0,sK7) != iProver_top ),
% 3.28/1.02      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 3.28/1.02  
% 3.28/1.02  cnf(c_3920,plain,
% 3.28/1.02      ( k1_xboole_0 = X0
% 3.28/1.02      | r2_hidden(sK1(k1_xboole_0,X1,X0),X0) = iProver_top
% 3.28/1.02      | r1_xboole_0(sK6(sK7),sK7) != iProver_top ),
% 3.28/1.02      inference(superposition,[status(thm)],[c_3591,c_491]) ).
% 3.28/1.02  
% 3.28/1.02  cnf(c_4842,plain,
% 3.28/1.02      ( k1_xboole_0 = X0
% 3.28/1.02      | r2_hidden(sK6(X0),X0) = iProver_top
% 3.28/1.02      | r1_xboole_0(sK6(sK7),sK7) != iProver_top ),
% 3.28/1.02      inference(superposition,[status(thm)],[c_3920,c_492]) ).
% 3.28/1.02  
% 3.28/1.02  cnf(c_1,plain,
% 3.28/1.02      ( r2_hidden(sK0(X0,X1),X1) | r1_xboole_0(X0,X1) ),
% 3.28/1.02      inference(cnf_transformation,[],[f27]) ).
% 3.28/1.02  
% 3.28/1.02  cnf(c_1007,plain,
% 3.28/1.02      ( r2_hidden(sK0(sK6(X0),X0),X0) | r1_xboole_0(sK6(X0),X0) ),
% 3.28/1.02      inference(instantiation,[status(thm)],[c_1]) ).
% 3.28/1.02  
% 3.28/1.02  cnf(c_1584,plain,
% 3.28/1.02      ( r2_hidden(sK0(sK6(sK7),sK7),sK7) | r1_xboole_0(sK6(sK7),sK7) ),
% 3.28/1.02      inference(instantiation,[status(thm)],[c_1007]) ).
% 3.28/1.02  
% 3.28/1.02  cnf(c_1586,plain,
% 3.28/1.02      ( r2_hidden(sK0(sK6(sK7),sK7),sK7) = iProver_top
% 3.28/1.02      | r1_xboole_0(sK6(sK7),sK7) = iProver_top ),
% 3.28/1.02      inference(predicate_to_equality,[status(thm)],[c_1584]) ).
% 3.28/1.02  
% 3.28/1.02  cnf(c_14,plain,
% 3.28/1.02      ( ~ r2_hidden(X0,X1)
% 3.28/1.02      | ~ r2_hidden(X2,X1)
% 3.28/1.02      | ~ r2_hidden(X2,sK6(X1)) ),
% 3.28/1.02      inference(cnf_transformation,[],[f41]) ).
% 3.28/1.02  
% 3.28/1.02  cnf(c_650,plain,
% 3.28/1.02      ( ~ r2_hidden(X0,X1)
% 3.28/1.02      | ~ r2_hidden(sK0(X2,X1),X1)
% 3.28/1.02      | ~ r2_hidden(sK0(X2,X1),sK6(X1)) ),
% 3.28/1.02      inference(instantiation,[status(thm)],[c_14]) ).
% 3.28/1.02  
% 3.28/1.02  cnf(c_770,plain,
% 3.28/1.02      ( ~ r2_hidden(X0,X1)
% 3.28/1.02      | ~ r2_hidden(sK0(sK6(X1),X1),X1)
% 3.28/1.02      | ~ r2_hidden(sK0(sK6(X1),X1),sK6(X1)) ),
% 3.28/1.02      inference(instantiation,[status(thm)],[c_650]) ).
% 3.28/1.02  
% 3.28/1.02  cnf(c_6358,plain,
% 3.28/1.02      ( ~ r2_hidden(sK0(sK6(sK7),sK7),sK6(sK7))
% 3.28/1.02      | ~ r2_hidden(sK0(sK6(sK7),sK7),sK7)
% 3.28/1.02      | ~ r2_hidden(sK6(sK7),sK7) ),
% 3.28/1.02      inference(instantiation,[status(thm)],[c_770]) ).
% 3.28/1.02  
% 3.28/1.02  cnf(c_6364,plain,
% 3.28/1.02      ( r2_hidden(sK0(sK6(sK7),sK7),sK6(sK7)) != iProver_top
% 3.28/1.02      | r2_hidden(sK0(sK6(sK7),sK7),sK7) != iProver_top
% 3.28/1.02      | r2_hidden(sK6(sK7),sK7) != iProver_top ),
% 3.28/1.02      inference(predicate_to_equality,[status(thm)],[c_6358]) ).
% 3.28/1.02  
% 3.28/1.02  cnf(c_2,plain,
% 3.28/1.02      ( r2_hidden(sK0(X0,X1),X0) | r1_xboole_0(X0,X1) ),
% 3.28/1.02      inference(cnf_transformation,[],[f26]) ).
% 3.28/1.02  
% 3.28/1.02  cnf(c_771,plain,
% 3.28/1.02      ( r2_hidden(sK0(sK6(X0),X0),sK6(X0)) | r1_xboole_0(sK6(X0),X0) ),
% 3.28/1.02      inference(instantiation,[status(thm)],[c_2]) ).
% 3.28/1.02  
% 3.28/1.02  cnf(c_7555,plain,
% 3.28/1.02      ( r2_hidden(sK0(sK6(sK7),sK7),sK6(sK7))
% 3.28/1.02      | r1_xboole_0(sK6(sK7),sK7) ),
% 3.28/1.02      inference(instantiation,[status(thm)],[c_771]) ).
% 3.28/1.02  
% 3.28/1.02  cnf(c_7556,plain,
% 3.28/1.02      ( r2_hidden(sK0(sK6(sK7),sK7),sK6(sK7)) = iProver_top
% 3.28/1.02      | r1_xboole_0(sK6(sK7),sK7) = iProver_top ),
% 3.28/1.02      inference(predicate_to_equality,[status(thm)],[c_7555]) ).
% 3.28/1.02  
% 3.28/1.02  cnf(c_632,plain,
% 3.28/1.02      ( ~ r2_hidden(sK0(X0,X1),X1) | r2_hidden(sK6(X1),X1) ),
% 3.28/1.02      inference(instantiation,[status(thm)],[c_15]) ).
% 3.28/1.02  
% 3.28/1.02  cnf(c_1590,plain,
% 3.28/1.02      ( ~ r2_hidden(sK0(sK6(X0),X0),X0) | r2_hidden(sK6(X0),X0) ),
% 3.28/1.02      inference(instantiation,[status(thm)],[c_632]) ).
% 3.28/1.02  
% 3.28/1.02  cnf(c_7575,plain,
% 3.28/1.02      ( ~ r2_hidden(sK0(sK6(sK7),sK7),sK7) | r2_hidden(sK6(sK7),sK7) ),
% 3.28/1.02      inference(instantiation,[status(thm)],[c_1590]) ).
% 3.28/1.02  
% 3.28/1.02  cnf(c_7576,plain,
% 3.28/1.02      ( r2_hidden(sK0(sK6(sK7),sK7),sK7) != iProver_top
% 3.28/1.02      | r2_hidden(sK6(sK7),sK7) = iProver_top ),
% 3.28/1.02      inference(predicate_to_equality,[status(thm)],[c_7575]) ).
% 3.28/1.02  
% 3.28/1.02  cnf(c_8756,plain,
% 3.28/1.02      ( r2_hidden(sK6(X0),X0) = iProver_top | k1_xboole_0 = X0 ),
% 3.28/1.02      inference(global_propositional_subsumption,
% 3.28/1.02                [status(thm)],
% 3.28/1.02                [c_4842,c_1586,c_6364,c_7556,c_7576]) ).
% 3.28/1.02  
% 3.28/1.02  cnf(c_8757,plain,
% 3.28/1.02      ( k1_xboole_0 = X0 | r2_hidden(sK6(X0),X0) = iProver_top ),
% 3.28/1.02      inference(renaming,[status(thm)],[c_8756]) ).
% 3.28/1.02  
% 3.28/1.02  cnf(c_8769,plain,
% 3.28/1.02      ( sK7 = k1_xboole_0 | r1_xboole_0(sK6(sK7),sK7) != iProver_top ),
% 3.28/1.02      inference(superposition,[status(thm)],[c_8757,c_491]) ).
% 3.28/1.02  
% 3.28/1.02  cnf(c_228,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 3.28/1.02  
% 3.28/1.02  cnf(c_658,plain,
% 3.28/1.02      ( sK7 != X0 | k1_xboole_0 != X0 | k1_xboole_0 = sK7 ),
% 3.28/1.02      inference(instantiation,[status(thm)],[c_228]) ).
% 3.28/1.02  
% 3.28/1.02  cnf(c_659,plain,
% 3.28/1.02      ( sK7 != k1_xboole_0
% 3.28/1.02      | k1_xboole_0 = sK7
% 3.28/1.02      | k1_xboole_0 != k1_xboole_0 ),
% 3.28/1.02      inference(instantiation,[status(thm)],[c_658]) ).
% 3.28/1.02  
% 3.28/1.02  cnf(c_28,plain,
% 3.28/1.02      ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
% 3.28/1.02      inference(instantiation,[status(thm)],[c_12]) ).
% 3.28/1.02  
% 3.28/1.02  cnf(c_13,plain,
% 3.28/1.02      ( k2_zfmisc_1(X0,X1) != k1_xboole_0
% 3.28/1.02      | k1_xboole_0 = X1
% 3.28/1.02      | k1_xboole_0 = X0 ),
% 3.28/1.02      inference(cnf_transformation,[],[f37]) ).
% 3.28/1.02  
% 3.28/1.02  cnf(c_27,plain,
% 3.28/1.02      ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) != k1_xboole_0
% 3.28/1.02      | k1_xboole_0 = k1_xboole_0 ),
% 3.28/1.02      inference(instantiation,[status(thm)],[c_13]) ).
% 3.28/1.02  
% 3.28/1.02  cnf(c_17,negated_conjecture,
% 3.28/1.02      ( k1_xboole_0 != sK7 ),
% 3.28/1.02      inference(cnf_transformation,[],[f42]) ).
% 3.28/1.02  
% 3.28/1.02  cnf(contradiction,plain,
% 3.28/1.02      ( $false ),
% 3.28/1.02      inference(minisat,
% 3.28/1.02                [status(thm)],
% 3.28/1.02                [c_8769,c_7576,c_7556,c_6364,c_1586,c_659,c_28,c_27,c_17]) ).
% 3.28/1.02  
% 3.28/1.02  
% 3.28/1.02  % SZS output end CNFRefutation for theBenchmark.p
% 3.28/1.02  
% 3.28/1.02  ------                               Statistics
% 3.28/1.02  
% 3.28/1.02  ------ Selected
% 3.28/1.02  
% 3.28/1.02  total_time:                             0.277
% 3.28/1.02  
%------------------------------------------------------------------------------
