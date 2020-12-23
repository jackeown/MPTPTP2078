%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:57:21 EST 2020

% Result     : Theorem 3.19s
% Output     : CNFRefutation 3.19s
% Verified   : 
% Statistics : Number of formulae       :   96 ( 248 expanded)
%              Number of clauses        :   57 (  90 expanded)
%              Number of leaves         :   13 (  59 expanded)
%              Depth                    :   14
%              Number of atoms          :  322 (1061 expanded)
%              Number of equality atoms :  143 ( 336 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal clause size      :   18 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1,axiom,(
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
    inference(rectify,[],[f1])).

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

fof(f26,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK0(X0,X1),X0)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f4,axiom,(
    ! [X0,X1] :
      ~ ( ! [X2] :
            ~ ( ! [X3] :
                  ~ ( r2_hidden(X3,X2)
                    & r2_hidden(X3,X1) )
              & r2_hidden(X2,X1) )
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f10,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ! [X3] :
              ( ~ r2_hidden(X3,X2)
              | ~ r2_hidden(X3,X1) )
          & r2_hidden(X2,X1) )
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f16,plain,(
    ! [X1] :
      ( ? [X2] :
          ( ! [X3] :
              ( ~ r2_hidden(X3,X2)
              | ~ r2_hidden(X3,X1) )
          & r2_hidden(X2,X1) )
     => ( ! [X3] :
            ( ~ r2_hidden(X3,sK1(X1))
            | ~ r2_hidden(X3,X1) )
        & r2_hidden(sK1(X1),X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ( ! [X3] :
            ( ~ r2_hidden(X3,sK1(X1))
            | ~ r2_hidden(X3,X1) )
        & r2_hidden(sK1(X1),X1) )
      | ~ r2_hidden(X0,X1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f10,f16])).

fof(f33,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK1(X1),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( k3_setfam_1(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ? [X4,X5] :
              ( k3_xboole_0(X4,X5) = X3
              & r2_hidden(X5,X1)
              & r2_hidden(X4,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( ( k3_setfam_1(X0,X1) = X2
        | ? [X3] :
            ( ( ! [X4,X5] :
                  ( k3_xboole_0(X4,X5) != X3
                  | ~ r2_hidden(X5,X1)
                  | ~ r2_hidden(X4,X0) )
              | ~ r2_hidden(X3,X2) )
            & ( ? [X4,X5] :
                  ( k3_xboole_0(X4,X5) = X3
                  & r2_hidden(X5,X1)
                  & r2_hidden(X4,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ! [X4,X5] :
                  ( k3_xboole_0(X4,X5) != X3
                  | ~ r2_hidden(X5,X1)
                  | ~ r2_hidden(X4,X0) ) )
            & ( ? [X4,X5] :
                  ( k3_xboole_0(X4,X5) = X3
                  & r2_hidden(X5,X1)
                  & r2_hidden(X4,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k3_setfam_1(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( ( k3_setfam_1(X0,X1) = X2
        | ? [X3] :
            ( ( ! [X4,X5] :
                  ( k3_xboole_0(X4,X5) != X3
                  | ~ r2_hidden(X5,X1)
                  | ~ r2_hidden(X4,X0) )
              | ~ r2_hidden(X3,X2) )
            & ( ? [X6,X7] :
                  ( k3_xboole_0(X6,X7) = X3
                  & r2_hidden(X7,X1)
                  & r2_hidden(X6,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X8] :
            ( ( r2_hidden(X8,X2)
              | ! [X9,X10] :
                  ( k3_xboole_0(X9,X10) != X8
                  | ~ r2_hidden(X10,X1)
                  | ~ r2_hidden(X9,X0) ) )
            & ( ? [X11,X12] :
                  ( k3_xboole_0(X11,X12) = X8
                  & r2_hidden(X12,X1)
                  & r2_hidden(X11,X0) )
              | ~ r2_hidden(X8,X2) ) )
        | k3_setfam_1(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f18])).

fof(f22,plain,(
    ! [X8,X1,X0] :
      ( ? [X11,X12] :
          ( k3_xboole_0(X11,X12) = X8
          & r2_hidden(X12,X1)
          & r2_hidden(X11,X0) )
     => ( k3_xboole_0(sK5(X0,X1,X8),sK6(X0,X1,X8)) = X8
        & r2_hidden(sK6(X0,X1,X8),X1)
        & r2_hidden(sK5(X0,X1,X8),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X6,X7] :
          ( k3_xboole_0(X6,X7) = X3
          & r2_hidden(X7,X1)
          & r2_hidden(X6,X0) )
     => ( k3_xboole_0(sK3(X0,X1,X2),sK4(X0,X1,X2)) = X3
        & r2_hidden(sK4(X0,X1,X2),X1)
        & r2_hidden(sK3(X0,X1,X2),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ! [X4,X5] :
                ( k3_xboole_0(X4,X5) != X3
                | ~ r2_hidden(X5,X1)
                | ~ r2_hidden(X4,X0) )
            | ~ r2_hidden(X3,X2) )
          & ( ? [X6,X7] :
                ( k3_xboole_0(X6,X7) = X3
                & r2_hidden(X7,X1)
                & r2_hidden(X6,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( ! [X5,X4] :
              ( k3_xboole_0(X4,X5) != sK2(X0,X1,X2)
              | ~ r2_hidden(X5,X1)
              | ~ r2_hidden(X4,X0) )
          | ~ r2_hidden(sK2(X0,X1,X2),X2) )
        & ( ? [X7,X6] :
              ( k3_xboole_0(X6,X7) = sK2(X0,X1,X2)
              & r2_hidden(X7,X1)
              & r2_hidden(X6,X0) )
          | r2_hidden(sK2(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( ( k3_setfam_1(X0,X1) = X2
        | ( ( ! [X4,X5] :
                ( k3_xboole_0(X4,X5) != sK2(X0,X1,X2)
                | ~ r2_hidden(X5,X1)
                | ~ r2_hidden(X4,X0) )
            | ~ r2_hidden(sK2(X0,X1,X2),X2) )
          & ( ( k3_xboole_0(sK3(X0,X1,X2),sK4(X0,X1,X2)) = sK2(X0,X1,X2)
              & r2_hidden(sK4(X0,X1,X2),X1)
              & r2_hidden(sK3(X0,X1,X2),X0) )
            | r2_hidden(sK2(X0,X1,X2),X2) ) ) )
      & ( ! [X8] :
            ( ( r2_hidden(X8,X2)
              | ! [X9,X10] :
                  ( k3_xboole_0(X9,X10) != X8
                  | ~ r2_hidden(X10,X1)
                  | ~ r2_hidden(X9,X0) ) )
            & ( ( k3_xboole_0(sK5(X0,X1,X8),sK6(X0,X1,X8)) = X8
                & r2_hidden(sK6(X0,X1,X8),X1)
                & r2_hidden(sK5(X0,X1,X8),X0) )
              | ~ r2_hidden(X8,X2) ) )
        | k3_setfam_1(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5,sK6])],[f19,f22,f21,f20])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( k3_setfam_1(X0,X1) = X2
      | r2_hidden(sK4(X0,X1,X2),X1)
      | r2_hidden(sK2(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f6,conjecture,(
    ! [X0] :
      ~ ( ! [X1] :
            ~ ( r1_xboole_0(X1,X0)
              & r2_hidden(X1,X0) )
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

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

fof(f44,plain,(
    ! [X1] :
      ( ~ r1_xboole_0(X1,sK7)
      | ~ r2_hidden(X1,sK7) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f27,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK0(X0,X1),X1)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f34,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,sK1(X1))
      | ~ r2_hidden(X3,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) = k1_xboole_0
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1] :
      ( ( k2_zfmisc_1(X0,X1) = k1_xboole_0
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k2_zfmisc_1(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ( k2_zfmisc_1(X0,X1) = k1_xboole_0
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k2_zfmisc_1(X0,X1) != k1_xboole_0 ) ) ),
    inference(flattening,[],[f14])).

fof(f31,plain,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) = k1_xboole_0
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f15])).

fof(f45,plain,(
    ! [X0] : k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(equality_resolution,[],[f31])).

fof(f3,axiom,(
    ! [X0,X1] : ~ r2_hidden(X0,k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1] : ~ r2_hidden(X0,k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( k3_setfam_1(X0,X1) = X2
      | r2_hidden(sK3(X0,X1,X2),X0)
      | r2_hidden(sK2(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f30,plain,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) = k1_xboole_0
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f15])).

fof(f46,plain,(
    ! [X1] : k2_zfmisc_1(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(equality_resolution,[],[f30])).

fof(f29,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | k2_zfmisc_1(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f15])).

fof(f43,plain,(
    k1_xboole_0 != sK7 ),
    inference(cnf_transformation,[],[f25])).

cnf(c_2,plain,
    ( r2_hidden(sK0(X0,X1),X0)
    | r1_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f26])).

cnf(c_520,plain,
    ( r2_hidden(sK0(X0,X1),X0) = iProver_top
    | r1_xboole_0(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_8,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(sK1(X1),X1) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_517,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(sK1(X1),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_1203,plain,
    ( r2_hidden(sK1(X0),X0) = iProver_top
    | r1_xboole_0(X0,X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_520,c_517])).

cnf(c_11,plain,
    ( r2_hidden(sK4(X0,X1,X2),X1)
    | r2_hidden(sK2(X0,X1,X2),X2)
    | k3_setfam_1(X0,X1) = X2 ),
    inference(cnf_transformation,[],[f40])).

cnf(c_514,plain,
    ( k3_setfam_1(X0,X1) = X2
    | r2_hidden(sK4(X0,X1,X2),X1) = iProver_top
    | r2_hidden(sK2(X0,X1,X2),X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_17,negated_conjecture,
    ( ~ r2_hidden(X0,sK7)
    | ~ r1_xboole_0(X0,sK7) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_508,plain,
    ( r2_hidden(X0,sK7) != iProver_top
    | r1_xboole_0(X0,sK7) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_2393,plain,
    ( k3_setfam_1(X0,sK7) = X1
    | r2_hidden(sK2(X0,sK7,X1),X1) = iProver_top
    | r1_xboole_0(sK4(X0,sK7,X1),sK7) != iProver_top ),
    inference(superposition,[status(thm)],[c_514,c_508])).

cnf(c_3196,plain,
    ( k3_setfam_1(X0,sK7) = X1
    | r2_hidden(sK2(X0,sK7,X1),X1) = iProver_top
    | r2_hidden(sK1(sK4(X0,sK7,X1)),sK4(X0,sK7,X1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1203,c_2393])).

cnf(c_815,plain,
    ( ~ r2_hidden(sK1(sK7),sK7)
    | ~ r1_xboole_0(sK1(sK7),sK7) ),
    inference(instantiation,[status(thm)],[c_17])).

cnf(c_820,plain,
    ( r2_hidden(sK1(sK7),sK7) != iProver_top
    | r1_xboole_0(sK1(sK7),sK7) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_815])).

cnf(c_3692,plain,
    ( r2_hidden(sK0(sK1(sK7),sK7),sK1(sK7))
    | r1_xboole_0(sK1(sK7),sK7) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_3694,plain,
    ( r2_hidden(sK0(sK1(sK7),sK7),sK1(sK7)) = iProver_top
    | r1_xboole_0(sK1(sK7),sK7) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3692])).

cnf(c_1,plain,
    ( r2_hidden(sK0(X0,X1),X1)
    | r1_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f27])).

cnf(c_649,plain,
    ( r2_hidden(sK0(X0,sK7),sK7)
    | r1_xboole_0(X0,sK7) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_3700,plain,
    ( r2_hidden(sK0(sK1(sK7),sK7),sK7)
    | r1_xboole_0(sK1(sK7),sK7) ),
    inference(instantiation,[status(thm)],[c_649])).

cnf(c_3701,plain,
    ( r2_hidden(sK0(sK1(sK7),sK7),sK7) = iProver_top
    | r1_xboole_0(sK1(sK7),sK7) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3700])).

cnf(c_521,plain,
    ( r2_hidden(sK0(X0,X1),X1) = iProver_top
    | r1_xboole_0(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_1228,plain,
    ( r2_hidden(sK1(X0),X0) = iProver_top
    | r1_xboole_0(X1,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_521,c_517])).

cnf(c_3880,plain,
    ( k3_setfam_1(X0,sK7) = X1
    | r2_hidden(sK2(X0,sK7,X1),X1) = iProver_top
    | r2_hidden(sK1(sK7),sK7) = iProver_top ),
    inference(superposition,[status(thm)],[c_1228,c_2393])).

cnf(c_7,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X2,X1)
    | ~ r2_hidden(X2,sK1(X1)) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_779,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X0,sK1(X1))
    | ~ r2_hidden(sK1(X1),X1) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_934,plain,
    ( ~ r2_hidden(sK0(X0,X1),X1)
    | ~ r2_hidden(sK0(X0,X1),sK1(X1))
    | ~ r2_hidden(sK1(X1),X1) ),
    inference(instantiation,[status(thm)],[c_779])).

cnf(c_3601,plain,
    ( ~ r2_hidden(sK0(X0,sK7),sK1(sK7))
    | ~ r2_hidden(sK0(X0,sK7),sK7)
    | ~ r2_hidden(sK1(sK7),sK7) ),
    inference(instantiation,[status(thm)],[c_934])).

cnf(c_7804,plain,
    ( ~ r2_hidden(sK0(sK1(sK7),sK7),sK1(sK7))
    | ~ r2_hidden(sK0(sK1(sK7),sK7),sK7)
    | ~ r2_hidden(sK1(sK7),sK7) ),
    inference(instantiation,[status(thm)],[c_3601])).

cnf(c_7805,plain,
    ( r2_hidden(sK0(sK1(sK7),sK7),sK1(sK7)) != iProver_top
    | r2_hidden(sK0(sK1(sK7),sK7),sK7) != iProver_top
    | r2_hidden(sK1(sK7),sK7) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7804])).

cnf(c_7860,plain,
    ( r2_hidden(sK2(X0,sK7,X1),X1) = iProver_top
    | k3_setfam_1(X0,sK7) = X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3196,c_820,c_3694,c_3701,c_3880,c_7805])).

cnf(c_7861,plain,
    ( k3_setfam_1(X0,sK7) = X1
    | r2_hidden(sK2(X0,sK7,X1),X1) = iProver_top ),
    inference(renaming,[status(thm)],[c_7860])).

cnf(c_3,plain,
    ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f45])).

cnf(c_6,plain,
    ( ~ r2_hidden(X0,k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_519,plain,
    ( r2_hidden(X0,k2_zfmisc_1(X0,X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_759,plain,
    ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_3,c_519])).

cnf(c_7874,plain,
    ( k3_setfam_1(X0,sK7) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_7861,c_759])).

cnf(c_12,plain,
    ( r2_hidden(sK3(X0,X1,X2),X0)
    | r2_hidden(sK2(X0,X1,X2),X2)
    | k3_setfam_1(X0,X1) = X2 ),
    inference(cnf_transformation,[],[f39])).

cnf(c_513,plain,
    ( k3_setfam_1(X0,X1) = X2
    | r2_hidden(sK3(X0,X1,X2),X0) = iProver_top
    | r2_hidden(sK2(X0,X1,X2),X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_2042,plain,
    ( k3_setfam_1(X0,X1) = sK7
    | r2_hidden(sK3(X0,X1,sK7),X0) = iProver_top
    | r1_xboole_0(sK2(X0,X1,sK7),sK7) != iProver_top ),
    inference(superposition,[status(thm)],[c_513,c_508])).

cnf(c_3878,plain,
    ( k3_setfam_1(X0,X1) = sK7
    | r2_hidden(sK3(X0,X1,sK7),X0) = iProver_top
    | r2_hidden(sK1(sK7),sK7) = iProver_top ),
    inference(superposition,[status(thm)],[c_1228,c_2042])).

cnf(c_894,plain,
    ( r2_hidden(sK3(X0,X1,sK7),X0)
    | r2_hidden(sK2(X0,X1,sK7),sK7)
    | k3_setfam_1(X0,X1) = sK7 ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_904,plain,
    ( k3_setfam_1(X0,X1) = sK7
    | r2_hidden(sK3(X0,X1,sK7),X0) = iProver_top
    | r2_hidden(sK2(X0,X1,sK7),sK7) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_894])).

cnf(c_2602,plain,
    ( ~ r2_hidden(X0,sK1(sK7))
    | ~ r2_hidden(X0,sK7)
    | ~ r2_hidden(sK2(X1,X2,sK7),sK7) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_5471,plain,
    ( ~ r2_hidden(sK2(X0,X1,sK7),sK7)
    | ~ r2_hidden(sK0(sK1(sK7),sK7),sK1(sK7))
    | ~ r2_hidden(sK0(sK1(sK7),sK7),sK7) ),
    inference(instantiation,[status(thm)],[c_2602])).

cnf(c_5473,plain,
    ( r2_hidden(sK2(X0,X1,sK7),sK7) != iProver_top
    | r2_hidden(sK0(sK1(sK7),sK7),sK1(sK7)) != iProver_top
    | r2_hidden(sK0(sK1(sK7),sK7),sK7) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5471])).

cnf(c_6460,plain,
    ( r2_hidden(sK3(X0,X1,sK7),X0) = iProver_top
    | k3_setfam_1(X0,X1) = sK7 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3878,c_820,c_904,c_3694,c_3701,c_5473])).

cnf(c_6461,plain,
    ( k3_setfam_1(X0,X1) = sK7
    | r2_hidden(sK3(X0,X1,sK7),X0) = iProver_top ),
    inference(renaming,[status(thm)],[c_6460])).

cnf(c_6475,plain,
    ( k3_setfam_1(k1_xboole_0,X0) = sK7 ),
    inference(superposition,[status(thm)],[c_6461,c_759])).

cnf(c_7991,plain,
    ( sK7 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_7874,c_6475])).

cnf(c_247,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_690,plain,
    ( sK7 != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = sK7 ),
    inference(instantiation,[status(thm)],[c_247])).

cnf(c_691,plain,
    ( sK7 != k1_xboole_0
    | k1_xboole_0 = sK7
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_690])).

cnf(c_4,plain,
    ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f46])).

cnf(c_56,plain,
    ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_5,plain,
    ( k2_zfmisc_1(X0,X1) != k1_xboole_0
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f29])).

cnf(c_55,plain,
    ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) != k1_xboole_0
    | k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_18,negated_conjecture,
    ( k1_xboole_0 != sK7 ),
    inference(cnf_transformation,[],[f43])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_7991,c_691,c_56,c_55,c_18])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n024.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 09:35:36 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 3.19/0.95  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.19/0.95  
% 3.19/0.95  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.19/0.95  
% 3.19/0.95  ------  iProver source info
% 3.19/0.95  
% 3.19/0.95  git: date: 2020-06-30 10:37:57 +0100
% 3.19/0.95  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.19/0.95  git: non_committed_changes: false
% 3.19/0.95  git: last_make_outside_of_git: false
% 3.19/0.95  
% 3.19/0.95  ------ 
% 3.19/0.95  
% 3.19/0.95  ------ Input Options
% 3.19/0.95  
% 3.19/0.95  --out_options                           all
% 3.19/0.95  --tptp_safe_out                         true
% 3.19/0.95  --problem_path                          ""
% 3.19/0.95  --include_path                          ""
% 3.19/0.95  --clausifier                            res/vclausify_rel
% 3.19/0.95  --clausifier_options                    --mode clausify
% 3.19/0.95  --stdin                                 false
% 3.19/0.95  --stats_out                             all
% 3.19/0.95  
% 3.19/0.95  ------ General Options
% 3.19/0.95  
% 3.19/0.95  --fof                                   false
% 3.19/0.95  --time_out_real                         305.
% 3.19/0.95  --time_out_virtual                      -1.
% 3.19/0.95  --symbol_type_check                     false
% 3.19/0.95  --clausify_out                          false
% 3.19/0.95  --sig_cnt_out                           false
% 3.19/0.95  --trig_cnt_out                          false
% 3.19/0.95  --trig_cnt_out_tolerance                1.
% 3.19/0.95  --trig_cnt_out_sk_spl                   false
% 3.19/0.95  --abstr_cl_out                          false
% 3.19/0.95  
% 3.19/0.95  ------ Global Options
% 3.19/0.95  
% 3.19/0.95  --schedule                              default
% 3.19/0.95  --add_important_lit                     false
% 3.19/0.95  --prop_solver_per_cl                    1000
% 3.19/0.95  --min_unsat_core                        false
% 3.19/0.95  --soft_assumptions                      false
% 3.19/0.95  --soft_lemma_size                       3
% 3.19/0.95  --prop_impl_unit_size                   0
% 3.19/0.95  --prop_impl_unit                        []
% 3.19/0.95  --share_sel_clauses                     true
% 3.19/0.95  --reset_solvers                         false
% 3.19/0.95  --bc_imp_inh                            [conj_cone]
% 3.19/0.95  --conj_cone_tolerance                   3.
% 3.19/0.95  --extra_neg_conj                        none
% 3.19/0.95  --large_theory_mode                     true
% 3.19/0.95  --prolific_symb_bound                   200
% 3.19/0.95  --lt_threshold                          2000
% 3.19/0.95  --clause_weak_htbl                      true
% 3.19/0.95  --gc_record_bc_elim                     false
% 3.19/0.95  
% 3.19/0.95  ------ Preprocessing Options
% 3.19/0.95  
% 3.19/0.95  --preprocessing_flag                    true
% 3.19/0.95  --time_out_prep_mult                    0.1
% 3.19/0.95  --splitting_mode                        input
% 3.19/0.95  --splitting_grd                         true
% 3.19/0.95  --splitting_cvd                         false
% 3.19/0.95  --splitting_cvd_svl                     false
% 3.19/0.95  --splitting_nvd                         32
% 3.19/0.95  --sub_typing                            true
% 3.19/0.95  --prep_gs_sim                           true
% 3.19/0.95  --prep_unflatten                        true
% 3.19/0.95  --prep_res_sim                          true
% 3.19/0.95  --prep_upred                            true
% 3.19/0.95  --prep_sem_filter                       exhaustive
% 3.19/0.95  --prep_sem_filter_out                   false
% 3.19/0.95  --pred_elim                             true
% 3.19/0.95  --res_sim_input                         true
% 3.19/0.95  --eq_ax_congr_red                       true
% 3.19/0.95  --pure_diseq_elim                       true
% 3.19/0.95  --brand_transform                       false
% 3.19/0.95  --non_eq_to_eq                          false
% 3.19/0.95  --prep_def_merge                        true
% 3.19/0.95  --prep_def_merge_prop_impl              false
% 3.19/0.95  --prep_def_merge_mbd                    true
% 3.19/0.95  --prep_def_merge_tr_red                 false
% 3.19/0.95  --prep_def_merge_tr_cl                  false
% 3.19/0.95  --smt_preprocessing                     true
% 3.19/0.95  --smt_ac_axioms                         fast
% 3.19/0.95  --preprocessed_out                      false
% 3.19/0.95  --preprocessed_stats                    false
% 3.19/0.95  
% 3.19/0.95  ------ Abstraction refinement Options
% 3.19/0.95  
% 3.19/0.95  --abstr_ref                             []
% 3.19/0.95  --abstr_ref_prep                        false
% 3.19/0.95  --abstr_ref_until_sat                   false
% 3.19/0.95  --abstr_ref_sig_restrict                funpre
% 3.19/0.95  --abstr_ref_af_restrict_to_split_sk     false
% 3.19/0.95  --abstr_ref_under                       []
% 3.19/0.95  
% 3.19/0.95  ------ SAT Options
% 3.19/0.95  
% 3.19/0.95  --sat_mode                              false
% 3.19/0.95  --sat_fm_restart_options                ""
% 3.19/0.95  --sat_gr_def                            false
% 3.19/0.95  --sat_epr_types                         true
% 3.19/0.95  --sat_non_cyclic_types                  false
% 3.19/0.95  --sat_finite_models                     false
% 3.19/0.95  --sat_fm_lemmas                         false
% 3.19/0.95  --sat_fm_prep                           false
% 3.19/0.95  --sat_fm_uc_incr                        true
% 3.19/0.95  --sat_out_model                         small
% 3.19/0.95  --sat_out_clauses                       false
% 3.19/0.95  
% 3.19/0.95  ------ QBF Options
% 3.19/0.95  
% 3.19/0.95  --qbf_mode                              false
% 3.19/0.95  --qbf_elim_univ                         false
% 3.19/0.95  --qbf_dom_inst                          none
% 3.19/0.95  --qbf_dom_pre_inst                      false
% 3.19/0.95  --qbf_sk_in                             false
% 3.19/0.95  --qbf_pred_elim                         true
% 3.19/0.95  --qbf_split                             512
% 3.19/0.95  
% 3.19/0.95  ------ BMC1 Options
% 3.19/0.95  
% 3.19/0.95  --bmc1_incremental                      false
% 3.19/0.95  --bmc1_axioms                           reachable_all
% 3.19/0.95  --bmc1_min_bound                        0
% 3.19/0.95  --bmc1_max_bound                        -1
% 3.19/0.95  --bmc1_max_bound_default                -1
% 3.19/0.95  --bmc1_symbol_reachability              true
% 3.19/0.95  --bmc1_property_lemmas                  false
% 3.19/0.95  --bmc1_k_induction                      false
% 3.19/0.95  --bmc1_non_equiv_states                 false
% 3.19/0.95  --bmc1_deadlock                         false
% 3.19/0.95  --bmc1_ucm                              false
% 3.19/0.95  --bmc1_add_unsat_core                   none
% 3.19/0.95  --bmc1_unsat_core_children              false
% 3.19/0.95  --bmc1_unsat_core_extrapolate_axioms    false
% 3.19/0.95  --bmc1_out_stat                         full
% 3.19/0.95  --bmc1_ground_init                      false
% 3.19/0.95  --bmc1_pre_inst_next_state              false
% 3.19/0.95  --bmc1_pre_inst_state                   false
% 3.19/0.95  --bmc1_pre_inst_reach_state             false
% 3.19/0.95  --bmc1_out_unsat_core                   false
% 3.19/0.95  --bmc1_aig_witness_out                  false
% 3.19/0.95  --bmc1_verbose                          false
% 3.19/0.95  --bmc1_dump_clauses_tptp                false
% 3.19/0.95  --bmc1_dump_unsat_core_tptp             false
% 3.19/0.95  --bmc1_dump_file                        -
% 3.19/0.95  --bmc1_ucm_expand_uc_limit              128
% 3.19/0.95  --bmc1_ucm_n_expand_iterations          6
% 3.19/0.95  --bmc1_ucm_extend_mode                  1
% 3.19/0.95  --bmc1_ucm_init_mode                    2
% 3.19/0.95  --bmc1_ucm_cone_mode                    none
% 3.19/0.95  --bmc1_ucm_reduced_relation_type        0
% 3.19/0.95  --bmc1_ucm_relax_model                  4
% 3.19/0.95  --bmc1_ucm_full_tr_after_sat            true
% 3.19/0.95  --bmc1_ucm_expand_neg_assumptions       false
% 3.19/0.95  --bmc1_ucm_layered_model                none
% 3.19/0.95  --bmc1_ucm_max_lemma_size               10
% 3.19/0.95  
% 3.19/0.95  ------ AIG Options
% 3.19/0.95  
% 3.19/0.95  --aig_mode                              false
% 3.19/0.95  
% 3.19/0.95  ------ Instantiation Options
% 3.19/0.95  
% 3.19/0.95  --instantiation_flag                    true
% 3.19/0.95  --inst_sos_flag                         false
% 3.19/0.95  --inst_sos_phase                        true
% 3.19/0.95  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.19/0.95  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.19/0.95  --inst_lit_sel_side                     num_symb
% 3.19/0.95  --inst_solver_per_active                1400
% 3.19/0.95  --inst_solver_calls_frac                1.
% 3.19/0.95  --inst_passive_queue_type               priority_queues
% 3.19/0.95  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.19/0.95  --inst_passive_queues_freq              [25;2]
% 3.19/0.95  --inst_dismatching                      true
% 3.19/0.95  --inst_eager_unprocessed_to_passive     true
% 3.19/0.95  --inst_prop_sim_given                   true
% 3.19/0.95  --inst_prop_sim_new                     false
% 3.19/0.95  --inst_subs_new                         false
% 3.19/0.95  --inst_eq_res_simp                      false
% 3.19/0.95  --inst_subs_given                       false
% 3.19/0.95  --inst_orphan_elimination               true
% 3.19/0.95  --inst_learning_loop_flag               true
% 3.19/0.95  --inst_learning_start                   3000
% 3.19/0.95  --inst_learning_factor                  2
% 3.19/0.95  --inst_start_prop_sim_after_learn       3
% 3.19/0.95  --inst_sel_renew                        solver
% 3.19/0.95  --inst_lit_activity_flag                true
% 3.19/0.95  --inst_restr_to_given                   false
% 3.19/0.95  --inst_activity_threshold               500
% 3.19/0.95  --inst_out_proof                        true
% 3.19/0.95  
% 3.19/0.95  ------ Resolution Options
% 3.19/0.95  
% 3.19/0.95  --resolution_flag                       true
% 3.19/0.95  --res_lit_sel                           adaptive
% 3.19/0.95  --res_lit_sel_side                      none
% 3.19/0.95  --res_ordering                          kbo
% 3.19/0.95  --res_to_prop_solver                    active
% 3.19/0.95  --res_prop_simpl_new                    false
% 3.19/0.95  --res_prop_simpl_given                  true
% 3.19/0.95  --res_passive_queue_type                priority_queues
% 3.19/0.95  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.19/0.95  --res_passive_queues_freq               [15;5]
% 3.19/0.95  --res_forward_subs                      full
% 3.19/0.95  --res_backward_subs                     full
% 3.19/0.95  --res_forward_subs_resolution           true
% 3.19/0.95  --res_backward_subs_resolution          true
% 3.19/0.95  --res_orphan_elimination                true
% 3.19/0.95  --res_time_limit                        2.
% 3.19/0.95  --res_out_proof                         true
% 3.19/0.95  
% 3.19/0.95  ------ Superposition Options
% 3.19/0.95  
% 3.19/0.95  --superposition_flag                    true
% 3.19/0.95  --sup_passive_queue_type                priority_queues
% 3.19/0.95  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.19/0.95  --sup_passive_queues_freq               [8;1;4]
% 3.19/0.95  --demod_completeness_check              fast
% 3.19/0.95  --demod_use_ground                      true
% 3.19/0.95  --sup_to_prop_solver                    passive
% 3.19/0.95  --sup_prop_simpl_new                    true
% 3.19/0.95  --sup_prop_simpl_given                  true
% 3.19/0.95  --sup_fun_splitting                     false
% 3.19/0.95  --sup_smt_interval                      50000
% 3.19/0.95  
% 3.19/0.95  ------ Superposition Simplification Setup
% 3.19/0.95  
% 3.19/0.95  --sup_indices_passive                   []
% 3.19/0.95  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.19/0.95  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.19/0.95  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.19/0.95  --sup_full_triv                         [TrivRules;PropSubs]
% 3.19/0.95  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.19/0.95  --sup_full_bw                           [BwDemod]
% 3.19/0.95  --sup_immed_triv                        [TrivRules]
% 3.19/0.95  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.19/0.95  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.19/0.95  --sup_immed_bw_main                     []
% 3.19/0.95  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.19/0.95  --sup_input_triv                        [Unflattening;TrivRules]
% 3.19/0.95  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.19/0.95  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.19/0.95  
% 3.19/0.95  ------ Combination Options
% 3.19/0.95  
% 3.19/0.95  --comb_res_mult                         3
% 3.19/0.95  --comb_sup_mult                         2
% 3.19/0.95  --comb_inst_mult                        10
% 3.19/0.95  
% 3.19/0.95  ------ Debug Options
% 3.19/0.95  
% 3.19/0.95  --dbg_backtrace                         false
% 3.19/0.95  --dbg_dump_prop_clauses                 false
% 3.19/0.95  --dbg_dump_prop_clauses_file            -
% 3.19/0.95  --dbg_out_stat                          false
% 3.19/0.95  ------ Parsing...
% 3.19/0.95  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.19/0.95  
% 3.19/0.95  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 3.19/0.95  
% 3.19/0.95  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.19/0.95  
% 3.19/0.95  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.19/0.95  ------ Proving...
% 3.19/0.95  ------ Problem Properties 
% 3.19/0.95  
% 3.19/0.95  
% 3.19/0.95  clauses                                 19
% 3.19/0.95  conjectures                             2
% 3.19/0.95  EPR                                     3
% 3.19/0.95  Horn                                    13
% 3.19/0.95  unary                                   4
% 3.19/0.95  binary                                  7
% 3.19/0.95  lits                                    44
% 3.19/0.95  lits eq                                 13
% 3.19/0.95  fd_pure                                 0
% 3.19/0.95  fd_pseudo                               0
% 3.19/0.95  fd_cond                                 1
% 3.19/0.95  fd_pseudo_cond                          4
% 3.19/0.95  AC symbols                              0
% 3.19/0.95  
% 3.19/0.95  ------ Schedule dynamic 5 is on 
% 3.19/0.95  
% 3.19/0.95  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.19/0.95  
% 3.19/0.95  
% 3.19/0.95  ------ 
% 3.19/0.95  Current options:
% 3.19/0.95  ------ 
% 3.19/0.95  
% 3.19/0.95  ------ Input Options
% 3.19/0.95  
% 3.19/0.95  --out_options                           all
% 3.19/0.95  --tptp_safe_out                         true
% 3.19/0.95  --problem_path                          ""
% 3.19/0.95  --include_path                          ""
% 3.19/0.95  --clausifier                            res/vclausify_rel
% 3.19/0.95  --clausifier_options                    --mode clausify
% 3.19/0.95  --stdin                                 false
% 3.19/0.95  --stats_out                             all
% 3.19/0.95  
% 3.19/0.95  ------ General Options
% 3.19/0.95  
% 3.19/0.95  --fof                                   false
% 3.19/0.95  --time_out_real                         305.
% 3.19/0.95  --time_out_virtual                      -1.
% 3.19/0.95  --symbol_type_check                     false
% 3.19/0.95  --clausify_out                          false
% 3.19/0.95  --sig_cnt_out                           false
% 3.19/0.95  --trig_cnt_out                          false
% 3.19/0.95  --trig_cnt_out_tolerance                1.
% 3.19/0.95  --trig_cnt_out_sk_spl                   false
% 3.19/0.95  --abstr_cl_out                          false
% 3.19/0.95  
% 3.19/0.95  ------ Global Options
% 3.19/0.95  
% 3.19/0.95  --schedule                              default
% 3.19/0.95  --add_important_lit                     false
% 3.19/0.95  --prop_solver_per_cl                    1000
% 3.19/0.95  --min_unsat_core                        false
% 3.19/0.95  --soft_assumptions                      false
% 3.19/0.95  --soft_lemma_size                       3
% 3.19/0.95  --prop_impl_unit_size                   0
% 3.19/0.95  --prop_impl_unit                        []
% 3.19/0.95  --share_sel_clauses                     true
% 3.19/0.95  --reset_solvers                         false
% 3.19/0.95  --bc_imp_inh                            [conj_cone]
% 3.19/0.95  --conj_cone_tolerance                   3.
% 3.19/0.95  --extra_neg_conj                        none
% 3.19/0.95  --large_theory_mode                     true
% 3.19/0.95  --prolific_symb_bound                   200
% 3.19/0.95  --lt_threshold                          2000
% 3.19/0.95  --clause_weak_htbl                      true
% 3.19/0.95  --gc_record_bc_elim                     false
% 3.19/0.95  
% 3.19/0.95  ------ Preprocessing Options
% 3.19/0.95  
% 3.19/0.95  --preprocessing_flag                    true
% 3.19/0.95  --time_out_prep_mult                    0.1
% 3.19/0.95  --splitting_mode                        input
% 3.19/0.95  --splitting_grd                         true
% 3.19/0.95  --splitting_cvd                         false
% 3.19/0.95  --splitting_cvd_svl                     false
% 3.19/0.95  --splitting_nvd                         32
% 3.19/0.95  --sub_typing                            true
% 3.19/0.95  --prep_gs_sim                           true
% 3.19/0.95  --prep_unflatten                        true
% 3.19/0.95  --prep_res_sim                          true
% 3.19/0.95  --prep_upred                            true
% 3.19/0.95  --prep_sem_filter                       exhaustive
% 3.19/0.95  --prep_sem_filter_out                   false
% 3.19/0.95  --pred_elim                             true
% 3.19/0.95  --res_sim_input                         true
% 3.19/0.95  --eq_ax_congr_red                       true
% 3.19/0.95  --pure_diseq_elim                       true
% 3.19/0.95  --brand_transform                       false
% 3.19/0.95  --non_eq_to_eq                          false
% 3.19/0.95  --prep_def_merge                        true
% 3.19/0.95  --prep_def_merge_prop_impl              false
% 3.19/0.95  --prep_def_merge_mbd                    true
% 3.19/0.95  --prep_def_merge_tr_red                 false
% 3.19/0.95  --prep_def_merge_tr_cl                  false
% 3.19/0.95  --smt_preprocessing                     true
% 3.19/0.95  --smt_ac_axioms                         fast
% 3.19/0.95  --preprocessed_out                      false
% 3.19/0.95  --preprocessed_stats                    false
% 3.19/0.95  
% 3.19/0.95  ------ Abstraction refinement Options
% 3.19/0.95  
% 3.19/0.95  --abstr_ref                             []
% 3.19/0.95  --abstr_ref_prep                        false
% 3.19/0.95  --abstr_ref_until_sat                   false
% 3.19/0.95  --abstr_ref_sig_restrict                funpre
% 3.19/0.95  --abstr_ref_af_restrict_to_split_sk     false
% 3.19/0.95  --abstr_ref_under                       []
% 3.19/0.95  
% 3.19/0.95  ------ SAT Options
% 3.19/0.95  
% 3.19/0.95  --sat_mode                              false
% 3.19/0.95  --sat_fm_restart_options                ""
% 3.19/0.95  --sat_gr_def                            false
% 3.19/0.95  --sat_epr_types                         true
% 3.19/0.95  --sat_non_cyclic_types                  false
% 3.19/0.95  --sat_finite_models                     false
% 3.19/0.95  --sat_fm_lemmas                         false
% 3.19/0.95  --sat_fm_prep                           false
% 3.19/0.95  --sat_fm_uc_incr                        true
% 3.19/0.95  --sat_out_model                         small
% 3.19/0.95  --sat_out_clauses                       false
% 3.19/0.95  
% 3.19/0.95  ------ QBF Options
% 3.19/0.95  
% 3.19/0.95  --qbf_mode                              false
% 3.19/0.95  --qbf_elim_univ                         false
% 3.19/0.95  --qbf_dom_inst                          none
% 3.19/0.95  --qbf_dom_pre_inst                      false
% 3.19/0.95  --qbf_sk_in                             false
% 3.19/0.95  --qbf_pred_elim                         true
% 3.19/0.95  --qbf_split                             512
% 3.19/0.95  
% 3.19/0.95  ------ BMC1 Options
% 3.19/0.95  
% 3.19/0.95  --bmc1_incremental                      false
% 3.19/0.95  --bmc1_axioms                           reachable_all
% 3.19/0.95  --bmc1_min_bound                        0
% 3.19/0.95  --bmc1_max_bound                        -1
% 3.19/0.95  --bmc1_max_bound_default                -1
% 3.19/0.95  --bmc1_symbol_reachability              true
% 3.19/0.95  --bmc1_property_lemmas                  false
% 3.19/0.95  --bmc1_k_induction                      false
% 3.19/0.95  --bmc1_non_equiv_states                 false
% 3.19/0.95  --bmc1_deadlock                         false
% 3.19/0.95  --bmc1_ucm                              false
% 3.19/0.95  --bmc1_add_unsat_core                   none
% 3.19/0.95  --bmc1_unsat_core_children              false
% 3.19/0.95  --bmc1_unsat_core_extrapolate_axioms    false
% 3.19/0.95  --bmc1_out_stat                         full
% 3.19/0.95  --bmc1_ground_init                      false
% 3.19/0.95  --bmc1_pre_inst_next_state              false
% 3.19/0.95  --bmc1_pre_inst_state                   false
% 3.19/0.95  --bmc1_pre_inst_reach_state             false
% 3.19/0.95  --bmc1_out_unsat_core                   false
% 3.19/0.95  --bmc1_aig_witness_out                  false
% 3.19/0.95  --bmc1_verbose                          false
% 3.19/0.95  --bmc1_dump_clauses_tptp                false
% 3.19/0.95  --bmc1_dump_unsat_core_tptp             false
% 3.19/0.95  --bmc1_dump_file                        -
% 3.19/0.95  --bmc1_ucm_expand_uc_limit              128
% 3.19/0.95  --bmc1_ucm_n_expand_iterations          6
% 3.19/0.95  --bmc1_ucm_extend_mode                  1
% 3.19/0.95  --bmc1_ucm_init_mode                    2
% 3.19/0.95  --bmc1_ucm_cone_mode                    none
% 3.19/0.95  --bmc1_ucm_reduced_relation_type        0
% 3.19/0.95  --bmc1_ucm_relax_model                  4
% 3.19/0.95  --bmc1_ucm_full_tr_after_sat            true
% 3.19/0.95  --bmc1_ucm_expand_neg_assumptions       false
% 3.19/0.95  --bmc1_ucm_layered_model                none
% 3.19/0.95  --bmc1_ucm_max_lemma_size               10
% 3.19/0.95  
% 3.19/0.95  ------ AIG Options
% 3.19/0.95  
% 3.19/0.95  --aig_mode                              false
% 3.19/0.95  
% 3.19/0.95  ------ Instantiation Options
% 3.19/0.95  
% 3.19/0.95  --instantiation_flag                    true
% 3.19/0.95  --inst_sos_flag                         false
% 3.19/0.95  --inst_sos_phase                        true
% 3.19/0.95  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.19/0.95  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.19/0.95  --inst_lit_sel_side                     none
% 3.19/0.95  --inst_solver_per_active                1400
% 3.19/0.95  --inst_solver_calls_frac                1.
% 3.19/0.95  --inst_passive_queue_type               priority_queues
% 3.19/0.95  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.19/0.95  --inst_passive_queues_freq              [25;2]
% 3.19/0.95  --inst_dismatching                      true
% 3.19/0.95  --inst_eager_unprocessed_to_passive     true
% 3.19/0.95  --inst_prop_sim_given                   true
% 3.19/0.95  --inst_prop_sim_new                     false
% 3.19/0.95  --inst_subs_new                         false
% 3.19/0.95  --inst_eq_res_simp                      false
% 3.19/0.95  --inst_subs_given                       false
% 3.19/0.95  --inst_orphan_elimination               true
% 3.19/0.95  --inst_learning_loop_flag               true
% 3.19/0.95  --inst_learning_start                   3000
% 3.19/0.95  --inst_learning_factor                  2
% 3.19/0.95  --inst_start_prop_sim_after_learn       3
% 3.19/0.95  --inst_sel_renew                        solver
% 3.19/0.95  --inst_lit_activity_flag                true
% 3.19/0.95  --inst_restr_to_given                   false
% 3.19/0.95  --inst_activity_threshold               500
% 3.19/0.95  --inst_out_proof                        true
% 3.19/0.95  
% 3.19/0.95  ------ Resolution Options
% 3.19/0.95  
% 3.19/0.95  --resolution_flag                       false
% 3.19/0.95  --res_lit_sel                           adaptive
% 3.19/0.95  --res_lit_sel_side                      none
% 3.19/0.95  --res_ordering                          kbo
% 3.19/0.95  --res_to_prop_solver                    active
% 3.19/0.95  --res_prop_simpl_new                    false
% 3.19/0.95  --res_prop_simpl_given                  true
% 3.19/0.95  --res_passive_queue_type                priority_queues
% 3.19/0.95  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.19/0.95  --res_passive_queues_freq               [15;5]
% 3.19/0.95  --res_forward_subs                      full
% 3.19/0.95  --res_backward_subs                     full
% 3.19/0.95  --res_forward_subs_resolution           true
% 3.19/0.95  --res_backward_subs_resolution          true
% 3.19/0.95  --res_orphan_elimination                true
% 3.19/0.95  --res_time_limit                        2.
% 3.19/0.95  --res_out_proof                         true
% 3.19/0.95  
% 3.19/0.95  ------ Superposition Options
% 3.19/0.95  
% 3.19/0.95  --superposition_flag                    true
% 3.19/0.95  --sup_passive_queue_type                priority_queues
% 3.19/0.95  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.19/0.95  --sup_passive_queues_freq               [8;1;4]
% 3.19/0.95  --demod_completeness_check              fast
% 3.19/0.95  --demod_use_ground                      true
% 3.19/0.95  --sup_to_prop_solver                    passive
% 3.19/0.95  --sup_prop_simpl_new                    true
% 3.19/0.95  --sup_prop_simpl_given                  true
% 3.19/0.95  --sup_fun_splitting                     false
% 3.19/0.95  --sup_smt_interval                      50000
% 3.19/0.95  
% 3.19/0.95  ------ Superposition Simplification Setup
% 3.19/0.95  
% 3.19/0.95  --sup_indices_passive                   []
% 3.19/0.95  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.19/0.95  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.19/0.95  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.19/0.95  --sup_full_triv                         [TrivRules;PropSubs]
% 3.19/0.95  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.19/0.95  --sup_full_bw                           [BwDemod]
% 3.19/0.95  --sup_immed_triv                        [TrivRules]
% 3.19/0.95  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.19/0.95  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.19/0.95  --sup_immed_bw_main                     []
% 3.19/0.95  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.19/0.95  --sup_input_triv                        [Unflattening;TrivRules]
% 3.19/0.95  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.19/0.95  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.19/0.95  
% 3.19/0.95  ------ Combination Options
% 3.19/0.95  
% 3.19/0.95  --comb_res_mult                         3
% 3.19/0.95  --comb_sup_mult                         2
% 3.19/0.95  --comb_inst_mult                        10
% 3.19/0.95  
% 3.19/0.95  ------ Debug Options
% 3.19/0.95  
% 3.19/0.95  --dbg_backtrace                         false
% 3.19/0.95  --dbg_dump_prop_clauses                 false
% 3.19/0.95  --dbg_dump_prop_clauses_file            -
% 3.19/0.95  --dbg_out_stat                          false
% 3.19/0.95  
% 3.19/0.95  
% 3.19/0.95  
% 3.19/0.95  
% 3.19/0.95  ------ Proving...
% 3.19/0.95  
% 3.19/0.95  
% 3.19/0.95  % SZS status Theorem for theBenchmark.p
% 3.19/0.95  
% 3.19/0.95  % SZS output start CNFRefutation for theBenchmark.p
% 3.19/0.95  
% 3.19/0.95  fof(f1,axiom,(
% 3.19/0.95    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 3.19/0.95    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.19/0.95  
% 3.19/0.95  fof(f8,plain,(
% 3.19/0.95    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 3.19/0.95    inference(rectify,[],[f1])).
% 3.19/0.95  
% 3.19/0.95  fof(f9,plain,(
% 3.19/0.95    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 3.19/0.95    inference(ennf_transformation,[],[f8])).
% 3.19/0.95  
% 3.19/0.95  fof(f12,plain,(
% 3.19/0.95    ! [X1,X0] : (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) => (r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 3.19/0.95    introduced(choice_axiom,[])).
% 3.19/0.95  
% 3.19/0.95  fof(f13,plain,(
% 3.19/0.95    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & ((r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)) | r1_xboole_0(X0,X1)))),
% 3.19/0.95    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f9,f12])).
% 3.19/0.95  
% 3.19/0.95  fof(f26,plain,(
% 3.19/0.95    ( ! [X0,X1] : (r2_hidden(sK0(X0,X1),X0) | r1_xboole_0(X0,X1)) )),
% 3.19/0.95    inference(cnf_transformation,[],[f13])).
% 3.19/0.95  
% 3.19/0.95  fof(f4,axiom,(
% 3.19/0.95    ! [X0,X1] : ~(! [X2] : ~(! [X3] : ~(r2_hidden(X3,X2) & r2_hidden(X3,X1)) & r2_hidden(X2,X1)) & r2_hidden(X0,X1))),
% 3.19/0.95    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.19/0.95  
% 3.19/0.95  fof(f10,plain,(
% 3.19/0.95    ! [X0,X1] : (? [X2] : (! [X3] : (~r2_hidden(X3,X2) | ~r2_hidden(X3,X1)) & r2_hidden(X2,X1)) | ~r2_hidden(X0,X1))),
% 3.19/0.95    inference(ennf_transformation,[],[f4])).
% 3.19/0.95  
% 3.19/0.95  fof(f16,plain,(
% 3.19/0.95    ! [X1] : (? [X2] : (! [X3] : (~r2_hidden(X3,X2) | ~r2_hidden(X3,X1)) & r2_hidden(X2,X1)) => (! [X3] : (~r2_hidden(X3,sK1(X1)) | ~r2_hidden(X3,X1)) & r2_hidden(sK1(X1),X1)))),
% 3.19/0.95    introduced(choice_axiom,[])).
% 3.19/0.95  
% 3.19/0.95  fof(f17,plain,(
% 3.19/0.95    ! [X0,X1] : ((! [X3] : (~r2_hidden(X3,sK1(X1)) | ~r2_hidden(X3,X1)) & r2_hidden(sK1(X1),X1)) | ~r2_hidden(X0,X1))),
% 3.19/0.95    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f10,f16])).
% 3.19/0.95  
% 3.19/0.95  fof(f33,plain,(
% 3.19/0.95    ( ! [X0,X1] : (r2_hidden(sK1(X1),X1) | ~r2_hidden(X0,X1)) )),
% 3.19/0.95    inference(cnf_transformation,[],[f17])).
% 3.19/0.95  
% 3.19/0.95  fof(f5,axiom,(
% 3.19/0.95    ! [X0,X1,X2] : (k3_setfam_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4,X5] : (k3_xboole_0(X4,X5) = X3 & r2_hidden(X5,X1) & r2_hidden(X4,X0))))),
% 3.19/0.95    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.19/0.95  
% 3.19/0.95  fof(f18,plain,(
% 3.19/0.95    ! [X0,X1,X2] : ((k3_setfam_1(X0,X1) = X2 | ? [X3] : ((! [X4,X5] : (k3_xboole_0(X4,X5) != X3 | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X0)) | ~r2_hidden(X3,X2)) & (? [X4,X5] : (k3_xboole_0(X4,X5) = X3 & r2_hidden(X5,X1) & r2_hidden(X4,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ! [X4,X5] : (k3_xboole_0(X4,X5) != X3 | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X0))) & (? [X4,X5] : (k3_xboole_0(X4,X5) = X3 & r2_hidden(X5,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X3,X2))) | k3_setfam_1(X0,X1) != X2))),
% 3.19/0.95    inference(nnf_transformation,[],[f5])).
% 3.19/0.95  
% 3.19/0.95  fof(f19,plain,(
% 3.19/0.95    ! [X0,X1,X2] : ((k3_setfam_1(X0,X1) = X2 | ? [X3] : ((! [X4,X5] : (k3_xboole_0(X4,X5) != X3 | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X0)) | ~r2_hidden(X3,X2)) & (? [X6,X7] : (k3_xboole_0(X6,X7) = X3 & r2_hidden(X7,X1) & r2_hidden(X6,X0)) | r2_hidden(X3,X2)))) & (! [X8] : ((r2_hidden(X8,X2) | ! [X9,X10] : (k3_xboole_0(X9,X10) != X8 | ~r2_hidden(X10,X1) | ~r2_hidden(X9,X0))) & (? [X11,X12] : (k3_xboole_0(X11,X12) = X8 & r2_hidden(X12,X1) & r2_hidden(X11,X0)) | ~r2_hidden(X8,X2))) | k3_setfam_1(X0,X1) != X2))),
% 3.19/0.95    inference(rectify,[],[f18])).
% 3.19/0.95  
% 3.19/0.95  fof(f22,plain,(
% 3.19/0.95    ! [X8,X1,X0] : (? [X11,X12] : (k3_xboole_0(X11,X12) = X8 & r2_hidden(X12,X1) & r2_hidden(X11,X0)) => (k3_xboole_0(sK5(X0,X1,X8),sK6(X0,X1,X8)) = X8 & r2_hidden(sK6(X0,X1,X8),X1) & r2_hidden(sK5(X0,X1,X8),X0)))),
% 3.19/0.95    introduced(choice_axiom,[])).
% 3.19/0.95  
% 3.19/0.95  fof(f21,plain,(
% 3.19/0.95    ( ! [X3] : (! [X2,X1,X0] : (? [X6,X7] : (k3_xboole_0(X6,X7) = X3 & r2_hidden(X7,X1) & r2_hidden(X6,X0)) => (k3_xboole_0(sK3(X0,X1,X2),sK4(X0,X1,X2)) = X3 & r2_hidden(sK4(X0,X1,X2),X1) & r2_hidden(sK3(X0,X1,X2),X0)))) )),
% 3.19/0.95    introduced(choice_axiom,[])).
% 3.19/0.95  
% 3.19/0.95  fof(f20,plain,(
% 3.19/0.95    ! [X2,X1,X0] : (? [X3] : ((! [X4,X5] : (k3_xboole_0(X4,X5) != X3 | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X0)) | ~r2_hidden(X3,X2)) & (? [X6,X7] : (k3_xboole_0(X6,X7) = X3 & r2_hidden(X7,X1) & r2_hidden(X6,X0)) | r2_hidden(X3,X2))) => ((! [X5,X4] : (k3_xboole_0(X4,X5) != sK2(X0,X1,X2) | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X0)) | ~r2_hidden(sK2(X0,X1,X2),X2)) & (? [X7,X6] : (k3_xboole_0(X6,X7) = sK2(X0,X1,X2) & r2_hidden(X7,X1) & r2_hidden(X6,X0)) | r2_hidden(sK2(X0,X1,X2),X2))))),
% 3.19/0.95    introduced(choice_axiom,[])).
% 3.19/0.95  
% 3.19/0.95  fof(f23,plain,(
% 3.19/0.95    ! [X0,X1,X2] : ((k3_setfam_1(X0,X1) = X2 | ((! [X4,X5] : (k3_xboole_0(X4,X5) != sK2(X0,X1,X2) | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X0)) | ~r2_hidden(sK2(X0,X1,X2),X2)) & ((k3_xboole_0(sK3(X0,X1,X2),sK4(X0,X1,X2)) = sK2(X0,X1,X2) & r2_hidden(sK4(X0,X1,X2),X1) & r2_hidden(sK3(X0,X1,X2),X0)) | r2_hidden(sK2(X0,X1,X2),X2)))) & (! [X8] : ((r2_hidden(X8,X2) | ! [X9,X10] : (k3_xboole_0(X9,X10) != X8 | ~r2_hidden(X10,X1) | ~r2_hidden(X9,X0))) & ((k3_xboole_0(sK5(X0,X1,X8),sK6(X0,X1,X8)) = X8 & r2_hidden(sK6(X0,X1,X8),X1) & r2_hidden(sK5(X0,X1,X8),X0)) | ~r2_hidden(X8,X2))) | k3_setfam_1(X0,X1) != X2))),
% 3.19/0.95    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5,sK6])],[f19,f22,f21,f20])).
% 3.19/0.95  
% 3.19/0.95  fof(f40,plain,(
% 3.19/0.95    ( ! [X2,X0,X1] : (k3_setfam_1(X0,X1) = X2 | r2_hidden(sK4(X0,X1,X2),X1) | r2_hidden(sK2(X0,X1,X2),X2)) )),
% 3.19/0.95    inference(cnf_transformation,[],[f23])).
% 3.19/0.95  
% 3.19/0.95  fof(f6,conjecture,(
% 3.19/0.95    ! [X0] : ~(! [X1] : ~(r1_xboole_0(X1,X0) & r2_hidden(X1,X0)) & k1_xboole_0 != X0)),
% 3.19/0.95    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.19/0.95  
% 3.19/0.95  fof(f7,negated_conjecture,(
% 3.19/0.95    ~! [X0] : ~(! [X1] : ~(r1_xboole_0(X1,X0) & r2_hidden(X1,X0)) & k1_xboole_0 != X0)),
% 3.19/0.95    inference(negated_conjecture,[],[f6])).
% 3.19/0.95  
% 3.19/0.95  fof(f11,plain,(
% 3.19/0.95    ? [X0] : (! [X1] : (~r1_xboole_0(X1,X0) | ~r2_hidden(X1,X0)) & k1_xboole_0 != X0)),
% 3.19/0.95    inference(ennf_transformation,[],[f7])).
% 3.19/0.95  
% 3.19/0.95  fof(f24,plain,(
% 3.19/0.95    ? [X0] : (! [X1] : (~r1_xboole_0(X1,X0) | ~r2_hidden(X1,X0)) & k1_xboole_0 != X0) => (! [X1] : (~r1_xboole_0(X1,sK7) | ~r2_hidden(X1,sK7)) & k1_xboole_0 != sK7)),
% 3.19/0.95    introduced(choice_axiom,[])).
% 3.19/0.95  
% 3.19/0.95  fof(f25,plain,(
% 3.19/0.95    ! [X1] : (~r1_xboole_0(X1,sK7) | ~r2_hidden(X1,sK7)) & k1_xboole_0 != sK7),
% 3.19/0.95    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f11,f24])).
% 3.19/0.95  
% 3.19/0.95  fof(f44,plain,(
% 3.19/0.95    ( ! [X1] : (~r1_xboole_0(X1,sK7) | ~r2_hidden(X1,sK7)) )),
% 3.19/0.95    inference(cnf_transformation,[],[f25])).
% 3.19/0.95  
% 3.19/0.95  fof(f27,plain,(
% 3.19/0.95    ( ! [X0,X1] : (r2_hidden(sK0(X0,X1),X1) | r1_xboole_0(X0,X1)) )),
% 3.19/0.95    inference(cnf_transformation,[],[f13])).
% 3.19/0.95  
% 3.19/0.95  fof(f34,plain,(
% 3.19/0.95    ( ! [X0,X3,X1] : (~r2_hidden(X3,sK1(X1)) | ~r2_hidden(X3,X1) | ~r2_hidden(X0,X1)) )),
% 3.19/0.95    inference(cnf_transformation,[],[f17])).
% 3.19/0.95  
% 3.19/0.95  fof(f2,axiom,(
% 3.19/0.95    ! [X0,X1] : (k2_zfmisc_1(X0,X1) = k1_xboole_0 <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 3.19/0.95    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.19/0.95  
% 3.19/0.95  fof(f14,plain,(
% 3.19/0.95    ! [X0,X1] : ((k2_zfmisc_1(X0,X1) = k1_xboole_0 | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k2_zfmisc_1(X0,X1) != k1_xboole_0))),
% 3.19/0.95    inference(nnf_transformation,[],[f2])).
% 3.19/0.95  
% 3.19/0.95  fof(f15,plain,(
% 3.19/0.95    ! [X0,X1] : ((k2_zfmisc_1(X0,X1) = k1_xboole_0 | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k2_zfmisc_1(X0,X1) != k1_xboole_0))),
% 3.19/0.95    inference(flattening,[],[f14])).
% 3.19/0.95  
% 3.19/0.95  fof(f31,plain,(
% 3.19/0.95    ( ! [X0,X1] : (k2_zfmisc_1(X0,X1) = k1_xboole_0 | k1_xboole_0 != X1) )),
% 3.19/0.95    inference(cnf_transformation,[],[f15])).
% 3.19/0.95  
% 3.19/0.95  fof(f45,plain,(
% 3.19/0.95    ( ! [X0] : (k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0) )),
% 3.19/0.95    inference(equality_resolution,[],[f31])).
% 3.19/0.95  
% 3.19/0.95  fof(f3,axiom,(
% 3.19/0.95    ! [X0,X1] : ~r2_hidden(X0,k2_zfmisc_1(X0,X1))),
% 3.19/0.95    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.19/0.95  
% 3.19/0.95  fof(f32,plain,(
% 3.19/0.95    ( ! [X0,X1] : (~r2_hidden(X0,k2_zfmisc_1(X0,X1))) )),
% 3.19/0.95    inference(cnf_transformation,[],[f3])).
% 3.19/0.95  
% 3.19/0.95  fof(f39,plain,(
% 3.19/0.95    ( ! [X2,X0,X1] : (k3_setfam_1(X0,X1) = X2 | r2_hidden(sK3(X0,X1,X2),X0) | r2_hidden(sK2(X0,X1,X2),X2)) )),
% 3.19/0.95    inference(cnf_transformation,[],[f23])).
% 3.19/0.95  
% 3.19/0.95  fof(f30,plain,(
% 3.19/0.95    ( ! [X0,X1] : (k2_zfmisc_1(X0,X1) = k1_xboole_0 | k1_xboole_0 != X0) )),
% 3.19/0.95    inference(cnf_transformation,[],[f15])).
% 3.19/0.95  
% 3.19/0.95  fof(f46,plain,(
% 3.19/0.95    ( ! [X1] : (k2_zfmisc_1(k1_xboole_0,X1) = k1_xboole_0) )),
% 3.19/0.95    inference(equality_resolution,[],[f30])).
% 3.19/0.95  
% 3.19/0.95  fof(f29,plain,(
% 3.19/0.95    ( ! [X0,X1] : (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k2_zfmisc_1(X0,X1) != k1_xboole_0) )),
% 3.19/0.95    inference(cnf_transformation,[],[f15])).
% 3.19/0.95  
% 3.19/0.95  fof(f43,plain,(
% 3.19/0.95    k1_xboole_0 != sK7),
% 3.19/0.95    inference(cnf_transformation,[],[f25])).
% 3.19/0.95  
% 3.19/0.95  cnf(c_2,plain,
% 3.19/0.95      ( r2_hidden(sK0(X0,X1),X0) | r1_xboole_0(X0,X1) ),
% 3.19/0.95      inference(cnf_transformation,[],[f26]) ).
% 3.19/0.95  
% 3.19/0.95  cnf(c_520,plain,
% 3.19/0.95      ( r2_hidden(sK0(X0,X1),X0) = iProver_top
% 3.19/0.95      | r1_xboole_0(X0,X1) = iProver_top ),
% 3.19/0.95      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 3.19/0.95  
% 3.19/0.95  cnf(c_8,plain,
% 3.19/0.95      ( ~ r2_hidden(X0,X1) | r2_hidden(sK1(X1),X1) ),
% 3.19/0.95      inference(cnf_transformation,[],[f33]) ).
% 3.19/0.95  
% 3.19/0.95  cnf(c_517,plain,
% 3.19/0.95      ( r2_hidden(X0,X1) != iProver_top
% 3.19/0.95      | r2_hidden(sK1(X1),X1) = iProver_top ),
% 3.19/0.95      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 3.19/0.95  
% 3.19/0.95  cnf(c_1203,plain,
% 3.19/0.95      ( r2_hidden(sK1(X0),X0) = iProver_top
% 3.19/0.95      | r1_xboole_0(X0,X1) = iProver_top ),
% 3.19/0.95      inference(superposition,[status(thm)],[c_520,c_517]) ).
% 3.19/0.95  
% 3.19/0.95  cnf(c_11,plain,
% 3.19/0.95      ( r2_hidden(sK4(X0,X1,X2),X1)
% 3.19/0.95      | r2_hidden(sK2(X0,X1,X2),X2)
% 3.19/0.95      | k3_setfam_1(X0,X1) = X2 ),
% 3.19/0.95      inference(cnf_transformation,[],[f40]) ).
% 3.19/0.95  
% 3.19/0.95  cnf(c_514,plain,
% 3.19/0.95      ( k3_setfam_1(X0,X1) = X2
% 3.19/0.95      | r2_hidden(sK4(X0,X1,X2),X1) = iProver_top
% 3.19/0.95      | r2_hidden(sK2(X0,X1,X2),X2) = iProver_top ),
% 3.19/0.95      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 3.19/0.95  
% 3.19/0.95  cnf(c_17,negated_conjecture,
% 3.19/0.95      ( ~ r2_hidden(X0,sK7) | ~ r1_xboole_0(X0,sK7) ),
% 3.19/0.95      inference(cnf_transformation,[],[f44]) ).
% 3.19/0.95  
% 3.19/0.95  cnf(c_508,plain,
% 3.19/0.95      ( r2_hidden(X0,sK7) != iProver_top
% 3.19/0.95      | r1_xboole_0(X0,sK7) != iProver_top ),
% 3.19/0.95      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 3.19/0.95  
% 3.19/0.95  cnf(c_2393,plain,
% 3.19/0.95      ( k3_setfam_1(X0,sK7) = X1
% 3.19/0.95      | r2_hidden(sK2(X0,sK7,X1),X1) = iProver_top
% 3.19/0.95      | r1_xboole_0(sK4(X0,sK7,X1),sK7) != iProver_top ),
% 3.19/0.95      inference(superposition,[status(thm)],[c_514,c_508]) ).
% 3.19/0.95  
% 3.19/0.95  cnf(c_3196,plain,
% 3.19/0.95      ( k3_setfam_1(X0,sK7) = X1
% 3.19/0.95      | r2_hidden(sK2(X0,sK7,X1),X1) = iProver_top
% 3.19/0.95      | r2_hidden(sK1(sK4(X0,sK7,X1)),sK4(X0,sK7,X1)) = iProver_top ),
% 3.19/0.95      inference(superposition,[status(thm)],[c_1203,c_2393]) ).
% 3.19/0.95  
% 3.19/0.95  cnf(c_815,plain,
% 3.19/0.95      ( ~ r2_hidden(sK1(sK7),sK7) | ~ r1_xboole_0(sK1(sK7),sK7) ),
% 3.19/0.95      inference(instantiation,[status(thm)],[c_17]) ).
% 3.19/0.95  
% 3.19/0.95  cnf(c_820,plain,
% 3.19/0.95      ( r2_hidden(sK1(sK7),sK7) != iProver_top
% 3.19/0.95      | r1_xboole_0(sK1(sK7),sK7) != iProver_top ),
% 3.19/0.95      inference(predicate_to_equality,[status(thm)],[c_815]) ).
% 3.19/0.95  
% 3.19/0.95  cnf(c_3692,plain,
% 3.19/0.95      ( r2_hidden(sK0(sK1(sK7),sK7),sK1(sK7))
% 3.19/0.95      | r1_xboole_0(sK1(sK7),sK7) ),
% 3.19/0.95      inference(instantiation,[status(thm)],[c_2]) ).
% 3.19/0.95  
% 3.19/0.95  cnf(c_3694,plain,
% 3.19/0.95      ( r2_hidden(sK0(sK1(sK7),sK7),sK1(sK7)) = iProver_top
% 3.19/0.95      | r1_xboole_0(sK1(sK7),sK7) = iProver_top ),
% 3.19/0.95      inference(predicate_to_equality,[status(thm)],[c_3692]) ).
% 3.19/0.95  
% 3.19/0.95  cnf(c_1,plain,
% 3.19/0.95      ( r2_hidden(sK0(X0,X1),X1) | r1_xboole_0(X0,X1) ),
% 3.19/0.95      inference(cnf_transformation,[],[f27]) ).
% 3.19/0.95  
% 3.19/0.95  cnf(c_649,plain,
% 3.19/0.95      ( r2_hidden(sK0(X0,sK7),sK7) | r1_xboole_0(X0,sK7) ),
% 3.19/0.95      inference(instantiation,[status(thm)],[c_1]) ).
% 3.19/0.95  
% 3.19/0.95  cnf(c_3700,plain,
% 3.19/0.95      ( r2_hidden(sK0(sK1(sK7),sK7),sK7) | r1_xboole_0(sK1(sK7),sK7) ),
% 3.19/0.95      inference(instantiation,[status(thm)],[c_649]) ).
% 3.19/0.95  
% 3.19/0.95  cnf(c_3701,plain,
% 3.19/0.95      ( r2_hidden(sK0(sK1(sK7),sK7),sK7) = iProver_top
% 3.19/0.95      | r1_xboole_0(sK1(sK7),sK7) = iProver_top ),
% 3.19/0.95      inference(predicate_to_equality,[status(thm)],[c_3700]) ).
% 3.19/0.95  
% 3.19/0.95  cnf(c_521,plain,
% 3.19/0.95      ( r2_hidden(sK0(X0,X1),X1) = iProver_top
% 3.19/0.95      | r1_xboole_0(X0,X1) = iProver_top ),
% 3.19/0.95      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 3.19/0.95  
% 3.19/0.95  cnf(c_1228,plain,
% 3.19/0.95      ( r2_hidden(sK1(X0),X0) = iProver_top
% 3.19/0.95      | r1_xboole_0(X1,X0) = iProver_top ),
% 3.19/0.95      inference(superposition,[status(thm)],[c_521,c_517]) ).
% 3.19/0.95  
% 3.19/0.95  cnf(c_3880,plain,
% 3.19/0.95      ( k3_setfam_1(X0,sK7) = X1
% 3.19/0.95      | r2_hidden(sK2(X0,sK7,X1),X1) = iProver_top
% 3.19/0.95      | r2_hidden(sK1(sK7),sK7) = iProver_top ),
% 3.19/0.95      inference(superposition,[status(thm)],[c_1228,c_2393]) ).
% 3.19/0.95  
% 3.19/0.95  cnf(c_7,plain,
% 3.19/0.95      ( ~ r2_hidden(X0,X1)
% 3.19/0.95      | ~ r2_hidden(X2,X1)
% 3.19/0.95      | ~ r2_hidden(X2,sK1(X1)) ),
% 3.19/0.95      inference(cnf_transformation,[],[f34]) ).
% 3.19/0.95  
% 3.19/0.95  cnf(c_779,plain,
% 3.19/0.95      ( ~ r2_hidden(X0,X1)
% 3.19/0.95      | ~ r2_hidden(X0,sK1(X1))
% 3.19/0.95      | ~ r2_hidden(sK1(X1),X1) ),
% 3.19/0.95      inference(instantiation,[status(thm)],[c_7]) ).
% 3.19/0.95  
% 3.19/0.95  cnf(c_934,plain,
% 3.19/0.95      ( ~ r2_hidden(sK0(X0,X1),X1)
% 3.19/0.95      | ~ r2_hidden(sK0(X0,X1),sK1(X1))
% 3.19/0.95      | ~ r2_hidden(sK1(X1),X1) ),
% 3.19/0.95      inference(instantiation,[status(thm)],[c_779]) ).
% 3.19/0.95  
% 3.19/0.95  cnf(c_3601,plain,
% 3.19/0.95      ( ~ r2_hidden(sK0(X0,sK7),sK1(sK7))
% 3.19/0.95      | ~ r2_hidden(sK0(X0,sK7),sK7)
% 3.19/0.95      | ~ r2_hidden(sK1(sK7),sK7) ),
% 3.19/0.95      inference(instantiation,[status(thm)],[c_934]) ).
% 3.19/0.95  
% 3.19/0.95  cnf(c_7804,plain,
% 3.19/0.95      ( ~ r2_hidden(sK0(sK1(sK7),sK7),sK1(sK7))
% 3.19/0.95      | ~ r2_hidden(sK0(sK1(sK7),sK7),sK7)
% 3.19/0.95      | ~ r2_hidden(sK1(sK7),sK7) ),
% 3.19/0.95      inference(instantiation,[status(thm)],[c_3601]) ).
% 3.19/0.95  
% 3.19/0.95  cnf(c_7805,plain,
% 3.19/0.95      ( r2_hidden(sK0(sK1(sK7),sK7),sK1(sK7)) != iProver_top
% 3.19/0.95      | r2_hidden(sK0(sK1(sK7),sK7),sK7) != iProver_top
% 3.19/0.95      | r2_hidden(sK1(sK7),sK7) != iProver_top ),
% 3.19/0.95      inference(predicate_to_equality,[status(thm)],[c_7804]) ).
% 3.19/0.95  
% 3.19/0.95  cnf(c_7860,plain,
% 3.19/0.95      ( r2_hidden(sK2(X0,sK7,X1),X1) = iProver_top
% 3.19/0.95      | k3_setfam_1(X0,sK7) = X1 ),
% 3.19/0.95      inference(global_propositional_subsumption,
% 3.19/0.95                [status(thm)],
% 3.19/0.95                [c_3196,c_820,c_3694,c_3701,c_3880,c_7805]) ).
% 3.19/0.95  
% 3.19/0.95  cnf(c_7861,plain,
% 3.19/0.95      ( k3_setfam_1(X0,sK7) = X1
% 3.19/0.95      | r2_hidden(sK2(X0,sK7,X1),X1) = iProver_top ),
% 3.19/0.95      inference(renaming,[status(thm)],[c_7860]) ).
% 3.19/0.95  
% 3.19/0.95  cnf(c_3,plain,
% 3.19/0.95      ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
% 3.19/0.95      inference(cnf_transformation,[],[f45]) ).
% 3.19/0.95  
% 3.19/0.95  cnf(c_6,plain,
% 3.19/0.95      ( ~ r2_hidden(X0,k2_zfmisc_1(X0,X1)) ),
% 3.19/0.95      inference(cnf_transformation,[],[f32]) ).
% 3.19/0.95  
% 3.19/0.95  cnf(c_519,plain,
% 3.19/0.95      ( r2_hidden(X0,k2_zfmisc_1(X0,X1)) != iProver_top ),
% 3.19/0.95      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 3.19/0.95  
% 3.19/0.95  cnf(c_759,plain,
% 3.19/0.95      ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
% 3.19/0.95      inference(superposition,[status(thm)],[c_3,c_519]) ).
% 3.19/0.95  
% 3.19/0.95  cnf(c_7874,plain,
% 3.19/0.95      ( k3_setfam_1(X0,sK7) = k1_xboole_0 ),
% 3.19/0.95      inference(superposition,[status(thm)],[c_7861,c_759]) ).
% 3.19/0.95  
% 3.19/0.95  cnf(c_12,plain,
% 3.19/0.95      ( r2_hidden(sK3(X0,X1,X2),X0)
% 3.19/0.95      | r2_hidden(sK2(X0,X1,X2),X2)
% 3.19/0.95      | k3_setfam_1(X0,X1) = X2 ),
% 3.19/0.95      inference(cnf_transformation,[],[f39]) ).
% 3.19/0.95  
% 3.19/0.95  cnf(c_513,plain,
% 3.19/0.95      ( k3_setfam_1(X0,X1) = X2
% 3.19/0.95      | r2_hidden(sK3(X0,X1,X2),X0) = iProver_top
% 3.19/0.95      | r2_hidden(sK2(X0,X1,X2),X2) = iProver_top ),
% 3.19/0.95      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 3.19/0.95  
% 3.19/0.95  cnf(c_2042,plain,
% 3.19/0.95      ( k3_setfam_1(X0,X1) = sK7
% 3.19/0.95      | r2_hidden(sK3(X0,X1,sK7),X0) = iProver_top
% 3.19/0.95      | r1_xboole_0(sK2(X0,X1,sK7),sK7) != iProver_top ),
% 3.19/0.95      inference(superposition,[status(thm)],[c_513,c_508]) ).
% 3.19/0.95  
% 3.19/0.95  cnf(c_3878,plain,
% 3.19/0.95      ( k3_setfam_1(X0,X1) = sK7
% 3.19/0.95      | r2_hidden(sK3(X0,X1,sK7),X0) = iProver_top
% 3.19/0.95      | r2_hidden(sK1(sK7),sK7) = iProver_top ),
% 3.19/0.95      inference(superposition,[status(thm)],[c_1228,c_2042]) ).
% 3.19/0.95  
% 3.19/0.95  cnf(c_894,plain,
% 3.19/0.95      ( r2_hidden(sK3(X0,X1,sK7),X0)
% 3.19/0.95      | r2_hidden(sK2(X0,X1,sK7),sK7)
% 3.19/0.95      | k3_setfam_1(X0,X1) = sK7 ),
% 3.19/0.95      inference(instantiation,[status(thm)],[c_12]) ).
% 3.19/0.95  
% 3.19/0.95  cnf(c_904,plain,
% 3.19/0.95      ( k3_setfam_1(X0,X1) = sK7
% 3.19/0.95      | r2_hidden(sK3(X0,X1,sK7),X0) = iProver_top
% 3.19/0.95      | r2_hidden(sK2(X0,X1,sK7),sK7) = iProver_top ),
% 3.19/0.95      inference(predicate_to_equality,[status(thm)],[c_894]) ).
% 3.19/0.95  
% 3.19/0.95  cnf(c_2602,plain,
% 3.19/0.95      ( ~ r2_hidden(X0,sK1(sK7))
% 3.19/0.95      | ~ r2_hidden(X0,sK7)
% 3.19/0.95      | ~ r2_hidden(sK2(X1,X2,sK7),sK7) ),
% 3.19/0.95      inference(instantiation,[status(thm)],[c_7]) ).
% 3.19/0.95  
% 3.19/0.95  cnf(c_5471,plain,
% 3.19/0.95      ( ~ r2_hidden(sK2(X0,X1,sK7),sK7)
% 3.19/0.95      | ~ r2_hidden(sK0(sK1(sK7),sK7),sK1(sK7))
% 3.19/0.95      | ~ r2_hidden(sK0(sK1(sK7),sK7),sK7) ),
% 3.19/0.95      inference(instantiation,[status(thm)],[c_2602]) ).
% 3.19/0.95  
% 3.19/0.95  cnf(c_5473,plain,
% 3.19/0.95      ( r2_hidden(sK2(X0,X1,sK7),sK7) != iProver_top
% 3.19/0.95      | r2_hidden(sK0(sK1(sK7),sK7),sK1(sK7)) != iProver_top
% 3.19/0.95      | r2_hidden(sK0(sK1(sK7),sK7),sK7) != iProver_top ),
% 3.19/0.95      inference(predicate_to_equality,[status(thm)],[c_5471]) ).
% 3.19/0.95  
% 3.19/0.95  cnf(c_6460,plain,
% 3.19/0.95      ( r2_hidden(sK3(X0,X1,sK7),X0) = iProver_top
% 3.19/0.95      | k3_setfam_1(X0,X1) = sK7 ),
% 3.19/0.95      inference(global_propositional_subsumption,
% 3.19/0.95                [status(thm)],
% 3.19/0.95                [c_3878,c_820,c_904,c_3694,c_3701,c_5473]) ).
% 3.19/0.95  
% 3.19/0.95  cnf(c_6461,plain,
% 3.19/0.95      ( k3_setfam_1(X0,X1) = sK7
% 3.19/0.95      | r2_hidden(sK3(X0,X1,sK7),X0) = iProver_top ),
% 3.19/0.95      inference(renaming,[status(thm)],[c_6460]) ).
% 3.19/0.95  
% 3.19/0.95  cnf(c_6475,plain,
% 3.19/0.95      ( k3_setfam_1(k1_xboole_0,X0) = sK7 ),
% 3.19/0.95      inference(superposition,[status(thm)],[c_6461,c_759]) ).
% 3.19/0.95  
% 3.19/0.95  cnf(c_7991,plain,
% 3.19/0.95      ( sK7 = k1_xboole_0 ),
% 3.19/0.95      inference(superposition,[status(thm)],[c_7874,c_6475]) ).
% 3.19/0.95  
% 3.19/0.95  cnf(c_247,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 3.19/0.95  
% 3.19/0.95  cnf(c_690,plain,
% 3.19/0.95      ( sK7 != X0 | k1_xboole_0 != X0 | k1_xboole_0 = sK7 ),
% 3.19/0.95      inference(instantiation,[status(thm)],[c_247]) ).
% 3.19/0.95  
% 3.19/0.95  cnf(c_691,plain,
% 3.19/0.95      ( sK7 != k1_xboole_0
% 3.19/0.95      | k1_xboole_0 = sK7
% 3.19/0.95      | k1_xboole_0 != k1_xboole_0 ),
% 3.19/0.95      inference(instantiation,[status(thm)],[c_690]) ).
% 3.19/0.95  
% 3.19/0.95  cnf(c_4,plain,
% 3.19/0.95      ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
% 3.19/0.95      inference(cnf_transformation,[],[f46]) ).
% 3.19/0.95  
% 3.19/0.95  cnf(c_56,plain,
% 3.19/0.95      ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
% 3.19/0.95      inference(instantiation,[status(thm)],[c_4]) ).
% 3.19/0.95  
% 3.19/0.95  cnf(c_5,plain,
% 3.19/0.95      ( k2_zfmisc_1(X0,X1) != k1_xboole_0
% 3.19/0.95      | k1_xboole_0 = X1
% 3.19/0.95      | k1_xboole_0 = X0 ),
% 3.19/0.95      inference(cnf_transformation,[],[f29]) ).
% 3.19/0.95  
% 3.19/0.95  cnf(c_55,plain,
% 3.19/0.95      ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) != k1_xboole_0
% 3.19/0.95      | k1_xboole_0 = k1_xboole_0 ),
% 3.19/0.95      inference(instantiation,[status(thm)],[c_5]) ).
% 3.19/0.95  
% 3.19/0.95  cnf(c_18,negated_conjecture,
% 3.19/0.95      ( k1_xboole_0 != sK7 ),
% 3.19/0.95      inference(cnf_transformation,[],[f43]) ).
% 3.19/0.95  
% 3.19/0.95  cnf(contradiction,plain,
% 3.19/0.95      ( $false ),
% 3.19/0.95      inference(minisat,[status(thm)],[c_7991,c_691,c_56,c_55,c_18]) ).
% 3.19/0.95  
% 3.19/0.95  
% 3.19/0.95  % SZS output end CNFRefutation for theBenchmark.p
% 3.19/0.95  
% 3.19/0.95  ------                               Statistics
% 3.19/0.95  
% 3.19/0.95  ------ General
% 3.19/0.95  
% 3.19/0.95  abstr_ref_over_cycles:                  0
% 3.19/0.95  abstr_ref_under_cycles:                 0
% 3.19/0.95  gc_basic_clause_elim:                   0
% 3.19/0.95  forced_gc_time:                         0
% 3.19/0.95  parsing_time:                           0.012
% 3.19/0.95  unif_index_cands_time:                  0.
% 3.19/0.95  unif_index_add_time:                    0.
% 3.19/0.95  orderings_time:                         0.
% 3.19/0.95  out_proof_time:                         0.008
% 3.19/0.95  total_time:                             0.259
% 3.19/0.95  num_of_symbols:                         45
% 3.19/0.95  num_of_terms:                           8731
% 3.19/0.95  
% 3.19/0.95  ------ Preprocessing
% 3.19/0.95  
% 3.19/0.95  num_of_splits:                          0
% 3.19/0.95  num_of_split_atoms:                     0
% 3.19/0.95  num_of_reused_defs:                     0
% 3.19/0.95  num_eq_ax_congr_red:                    42
% 3.19/0.95  num_of_sem_filtered_clauses:            1
% 3.19/0.95  num_of_subtypes:                        0
% 3.19/0.95  monotx_restored_types:                  0
% 3.19/0.95  sat_num_of_epr_types:                   0
% 3.19/0.95  sat_num_of_non_cyclic_types:            0
% 3.19/0.95  sat_guarded_non_collapsed_types:        0
% 3.19/0.95  num_pure_diseq_elim:                    0
% 3.19/0.95  simp_replaced_by:                       0
% 3.19/0.95  res_preprocessed:                       70
% 3.19/0.95  prep_upred:                             0
% 3.19/0.95  prep_unflattend:                        8
% 3.19/0.95  smt_new_axioms:                         0
% 3.19/0.95  pred_elim_cands:                        2
% 3.19/0.95  pred_elim:                              0
% 3.19/0.95  pred_elim_cl:                           0
% 3.19/0.95  pred_elim_cycles:                       1
% 3.19/0.95  merged_defs:                            0
% 3.19/0.95  merged_defs_ncl:                        0
% 3.19/0.95  bin_hyper_res:                          0
% 3.19/0.95  prep_cycles:                            3
% 3.19/0.95  pred_elim_time:                         0.001
% 3.19/0.95  splitting_time:                         0.
% 3.19/0.95  sem_filter_time:                        0.
% 3.19/0.95  monotx_time:                            0.001
% 3.19/0.95  subtype_inf_time:                       0.
% 3.19/0.95  
% 3.19/0.95  ------ Problem properties
% 3.19/0.95  
% 3.19/0.95  clauses:                                19
% 3.19/0.95  conjectures:                            2
% 3.19/0.95  epr:                                    3
% 3.19/0.95  horn:                                   13
% 3.19/0.95  ground:                                 1
% 3.19/0.95  unary:                                  4
% 3.19/0.95  binary:                                 7
% 3.19/0.95  lits:                                   44
% 3.19/0.95  lits_eq:                                13
% 3.19/0.95  fd_pure:                                0
% 3.19/0.95  fd_pseudo:                              0
% 3.19/0.95  fd_cond:                                1
% 3.19/0.95  fd_pseudo_cond:                         4
% 3.19/0.95  ac_symbols:                             0
% 3.19/0.95  
% 3.19/0.95  ------ Propositional Solver
% 3.19/0.95  
% 3.19/0.95  prop_solver_calls:                      25
% 3.19/0.95  prop_fast_solver_calls:                 528
% 3.19/0.95  smt_solver_calls:                       0
% 3.19/0.95  smt_fast_solver_calls:                  0
% 3.19/0.95  prop_num_of_clauses:                    3537
% 3.19/0.95  prop_preprocess_simplified:             6181
% 3.19/0.95  prop_fo_subsumed:                       4
% 3.19/0.95  prop_solver_time:                       0.
% 3.19/0.95  smt_solver_time:                        0.
% 3.19/0.95  smt_fast_solver_time:                   0.
% 3.19/0.95  prop_fast_solver_time:                  0.
% 3.19/0.95  prop_unsat_core_time:                   0.
% 3.19/0.95  
% 3.19/0.95  ------ QBF
% 3.19/0.95  
% 3.19/0.95  qbf_q_res:                              0
% 3.19/0.95  qbf_num_tautologies:                    0
% 3.19/0.95  qbf_prep_cycles:                        0
% 3.19/0.95  
% 3.19/0.95  ------ BMC1
% 3.19/0.95  
% 3.19/0.95  bmc1_current_bound:                     -1
% 3.19/0.95  bmc1_last_solved_bound:                 -1
% 3.19/0.95  bmc1_unsat_core_size:                   -1
% 3.19/0.95  bmc1_unsat_core_parents_size:           -1
% 3.19/0.95  bmc1_merge_next_fun:                    0
% 3.19/0.95  bmc1_unsat_core_clauses_time:           0.
% 3.19/0.95  
% 3.19/0.95  ------ Instantiation
% 3.19/0.95  
% 3.19/0.95  inst_num_of_clauses:                    781
% 3.19/0.95  inst_num_in_passive:                    135
% 3.19/0.95  inst_num_in_active:                     397
% 3.19/0.95  inst_num_in_unprocessed:                249
% 3.19/0.95  inst_num_of_loops:                      450
% 3.19/0.95  inst_num_of_learning_restarts:          0
% 3.19/0.95  inst_num_moves_active_passive:          50
% 3.19/0.95  inst_lit_activity:                      0
% 3.19/0.95  inst_lit_activity_moves:                0
% 3.19/0.95  inst_num_tautologies:                   0
% 3.19/0.95  inst_num_prop_implied:                  0
% 3.19/0.95  inst_num_existing_simplified:           0
% 3.19/0.95  inst_num_eq_res_simplified:             0
% 3.19/0.95  inst_num_child_elim:                    0
% 3.19/0.95  inst_num_of_dismatching_blockings:      242
% 3.19/0.95  inst_num_of_non_proper_insts:           490
% 3.19/0.95  inst_num_of_duplicates:                 0
% 3.19/0.95  inst_inst_num_from_inst_to_res:         0
% 3.19/0.95  inst_dismatching_checking_time:         0.
% 3.19/0.95  
% 3.19/0.95  ------ Resolution
% 3.19/0.95  
% 3.19/0.95  res_num_of_clauses:                     0
% 3.19/0.95  res_num_in_passive:                     0
% 3.19/0.95  res_num_in_active:                      0
% 3.19/0.95  res_num_of_loops:                       73
% 3.19/0.95  res_forward_subset_subsumed:            42
% 3.19/0.95  res_backward_subset_subsumed:           0
% 3.19/0.95  res_forward_subsumed:                   0
% 3.19/0.95  res_backward_subsumed:                  0
% 3.19/0.95  res_forward_subsumption_resolution:     0
% 3.19/0.95  res_backward_subsumption_resolution:    0
% 3.19/0.95  res_clause_to_clause_subsumption:       1339
% 3.19/0.95  res_orphan_elimination:                 0
% 3.19/0.95  res_tautology_del:                      29
% 3.19/0.95  res_num_eq_res_simplified:              0
% 3.19/0.95  res_num_sel_changes:                    0
% 3.19/0.95  res_moves_from_active_to_pass:          0
% 3.19/0.95  
% 3.19/0.95  ------ Superposition
% 3.19/0.95  
% 3.19/0.95  sup_time_total:                         0.
% 3.19/0.95  sup_time_generating:                    0.
% 3.19/0.95  sup_time_sim_full:                      0.
% 3.19/0.95  sup_time_sim_immed:                     0.
% 3.19/0.95  
% 3.19/0.95  sup_num_of_clauses:                     356
% 3.19/0.95  sup_num_in_active:                      43
% 3.19/0.95  sup_num_in_passive:                     313
% 3.19/0.95  sup_num_of_loops:                       89
% 3.19/0.95  sup_fw_superposition:                   204
% 3.19/0.95  sup_bw_superposition:                   344
% 3.19/0.95  sup_immediate_simplified:               52
% 3.19/0.95  sup_given_eliminated:                   2
% 3.19/0.95  comparisons_done:                       0
% 3.19/0.95  comparisons_avoided:                    8
% 3.19/0.95  
% 3.19/0.95  ------ Simplifications
% 3.19/0.95  
% 3.19/0.95  
% 3.19/0.95  sim_fw_subset_subsumed:                 10
% 3.19/0.95  sim_bw_subset_subsumed:                 63
% 3.19/0.95  sim_fw_subsumed:                        15
% 3.19/0.95  sim_bw_subsumed:                        1
% 3.19/0.95  sim_fw_subsumption_res:                 1
% 3.19/0.95  sim_bw_subsumption_res:                 0
% 3.19/0.95  sim_tautology_del:                      0
% 3.19/0.95  sim_eq_tautology_del:                   3
% 3.19/0.95  sim_eq_res_simp:                        0
% 3.19/0.95  sim_fw_demodulated:                     3
% 3.19/0.95  sim_bw_demodulated:                     47
% 3.19/0.95  sim_light_normalised:                   5
% 3.19/0.95  sim_joinable_taut:                      0
% 3.19/0.95  sim_joinable_simp:                      0
% 3.19/0.95  sim_ac_normalised:                      0
% 3.19/0.95  sim_smt_subsumption:                    0
% 3.19/0.95  
%------------------------------------------------------------------------------
