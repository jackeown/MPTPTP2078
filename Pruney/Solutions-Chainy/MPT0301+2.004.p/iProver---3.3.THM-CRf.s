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

% Result     : Theorem 3.76s
% Output     : CNFRefutation 3.76s
% Verified   : 
% Statistics : Number of formulae       :   91 (2505 expanded)
%              Number of clauses        :   52 ( 895 expanded)
%              Number of leaves         :   12 ( 714 expanded)
%              Depth                    :   27
%              Number of atoms          :  276 (11682 expanded)
%              Number of equality atoms :  161 (4235 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal clause size      :   18 (   2 average)
%              Maximal term depth       :    6 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( k2_zfmisc_1(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ? [X4,X5] :
              ( k4_tarski(X4,X5) = X3
              & r2_hidden(X5,X1)
              & r2_hidden(X4,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

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
    inference(nnf_transformation,[],[f6])).

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

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( k2_zfmisc_1(X0,X1) = X2
      | r2_hidden(sK2(X0,X1,X2),X0)
      | r2_hidden(sK1(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f5,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f9,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f2])).

fof(f10,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f12,plain,(
    ! [X1,X0] :
      ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
     => r2_hidden(sK0(X0,X1),k3_xboole_0(X0,X1)) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( r2_hidden(sK0(X0,X1),k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f10,f12])).

fof(f26,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,k3_xboole_0(X0,X1)) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f3,axiom,(
    ! [X0,X1] : r1_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1] : r1_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f4,axiom,(
    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f4])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f30,plain,(
    ! [X2,X0,X8,X1] :
      ( r2_hidden(sK4(X0,X1,X8),X0)
      | ~ r2_hidden(X8,X2)
      | k2_zfmisc_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f19])).

fof(f45,plain,(
    ! [X0,X8,X1] :
      ( r2_hidden(sK4(X0,X1,X8),X0)
      | ~ r2_hidden(X8,k2_zfmisc_1(X0,X1)) ) ),
    inference(equality_resolution,[],[f30])).

fof(f31,plain,(
    ! [X2,X0,X8,X1] :
      ( r2_hidden(sK5(X0,X1,X8),X1)
      | ~ r2_hidden(X8,X2)
      | k2_zfmisc_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f19])).

fof(f44,plain,(
    ! [X0,X8,X1] :
      ( r2_hidden(sK5(X0,X1,X8),X1)
      | ~ r2_hidden(X8,k2_zfmisc_1(X0,X1)) ) ),
    inference(equality_resolution,[],[f31])).

fof(f7,conjecture,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f8,negated_conjecture,(
    ~ ! [X0,X1] :
        ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      <=> ( k1_xboole_0 = X1
          | k1_xboole_0 = X0 ) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f11,plain,(
    ? [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <~> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f20,plain,(
    ? [X0,X1] :
      ( ( ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 )
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 = k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f11])).

fof(f21,plain,(
    ? [X0,X1] :
      ( ( ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 )
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 = k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f20])).

fof(f22,plain,
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

fof(f23,plain,
    ( ( ( k1_xboole_0 != sK7
        & k1_xboole_0 != sK6 )
      | k1_xboole_0 != k2_zfmisc_1(sK6,sK7) )
    & ( k1_xboole_0 = sK7
      | k1_xboole_0 = sK6
      | k1_xboole_0 = k2_zfmisc_1(sK6,sK7) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7])],[f21,f22])).

fof(f38,plain,
    ( k1_xboole_0 = sK7
    | k1_xboole_0 = sK6
    | k1_xboole_0 = k2_zfmisc_1(sK6,sK7) ),
    inference(cnf_transformation,[],[f23])).

fof(f33,plain,(
    ! [X2,X0,X10,X8,X1,X9] :
      ( r2_hidden(X8,X2)
      | k4_tarski(X9,X10) != X8
      | ~ r2_hidden(X10,X1)
      | ~ r2_hidden(X9,X0)
      | k2_zfmisc_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f19])).

fof(f41,plain,(
    ! [X2,X0,X10,X1,X9] :
      ( r2_hidden(k4_tarski(X9,X10),X2)
      | ~ r2_hidden(X10,X1)
      | ~ r2_hidden(X9,X0)
      | k2_zfmisc_1(X0,X1) != X2 ) ),
    inference(equality_resolution,[],[f33])).

fof(f42,plain,(
    ! [X0,X10,X1,X9] :
      ( r2_hidden(k4_tarski(X9,X10),k2_zfmisc_1(X0,X1))
      | ~ r2_hidden(X10,X1)
      | ~ r2_hidden(X9,X0) ) ),
    inference(equality_resolution,[],[f41])).

fof(f39,plain,
    ( k1_xboole_0 != sK6
    | k1_xboole_0 != k2_zfmisc_1(sK6,sK7) ),
    inference(cnf_transformation,[],[f23])).

fof(f40,plain,
    ( k1_xboole_0 != sK7
    | k1_xboole_0 != k2_zfmisc_1(sK6,sK7) ),
    inference(cnf_transformation,[],[f23])).

cnf(c_9,plain,
    ( r2_hidden(sK2(X0,X1,X2),X0)
    | r2_hidden(sK1(X0,X1,X2),X2)
    | k2_zfmisc_1(X0,X1) = X2 ),
    inference(cnf_transformation,[],[f34])).

cnf(c_412,plain,
    ( k2_zfmisc_1(X0,X1) = X2
    | r2_hidden(sK2(X0,X1,X2),X0) = iProver_top
    | r2_hidden(sK1(X0,X1,X2),X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_5,plain,
    ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f29])).

cnf(c_1,plain,
    ( ~ r2_hidden(X0,k3_xboole_0(X1,X2))
    | ~ r1_xboole_0(X1,X2) ),
    inference(cnf_transformation,[],[f26])).

cnf(c_3,plain,
    ( r1_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f27])).

cnf(c_156,plain,
    ( ~ r2_hidden(X0,k3_xboole_0(X1,X2))
    | k5_xboole_0(X3,X4) != X2
    | k3_xboole_0(X3,X4) != X1 ),
    inference(resolution_lifted,[status(thm)],[c_1,c_3])).

cnf(c_157,plain,
    ( ~ r2_hidden(X0,k3_xboole_0(k3_xboole_0(X1,X2),k5_xboole_0(X1,X2))) ),
    inference(unflattening,[status(thm)],[c_156])).

cnf(c_406,plain,
    ( r2_hidden(X0,k3_xboole_0(k3_xboole_0(X1,X2),k5_xboole_0(X1,X2))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_157])).

cnf(c_617,plain,
    ( r2_hidden(X0,k3_xboole_0(k3_xboole_0(X1,k1_xboole_0),X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_5,c_406])).

cnf(c_4,plain,
    ( k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f28])).

cnf(c_0,plain,
    ( k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f24])).

cnf(c_542,plain,
    ( k3_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_4,c_0])).

cnf(c_618,plain,
    ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_617,c_4,c_542])).

cnf(c_1144,plain,
    ( k2_zfmisc_1(k1_xboole_0,X0) = X1
    | r2_hidden(sK1(k1_xboole_0,X0,X1),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_412,c_618])).

cnf(c_1132,plain,
    ( k2_zfmisc_1(X0,X1) = k1_xboole_0
    | r2_hidden(sK2(X0,X1,k1_xboole_0),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_412,c_618])).

cnf(c_13,plain,
    ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
    | r2_hidden(sK4(X1,X2,X0),X1) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_408,plain,
    ( r2_hidden(X0,k2_zfmisc_1(X1,X2)) != iProver_top
    | r2_hidden(sK4(X1,X2,X0),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_12,plain,
    ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
    | r2_hidden(sK5(X1,X2,X0),X2) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_409,plain,
    ( r2_hidden(X0,k2_zfmisc_1(X1,X2)) != iProver_top
    | r2_hidden(sK5(X1,X2,X0),X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_676,plain,
    ( r2_hidden(X0,k2_zfmisc_1(k1_xboole_0,X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_408,c_618])).

cnf(c_806,plain,
    ( r2_hidden(X0,k2_zfmisc_1(X1,k2_zfmisc_1(k1_xboole_0,X2))) != iProver_top ),
    inference(superposition,[status(thm)],[c_409,c_676])).

cnf(c_861,plain,
    ( r2_hidden(X0,k2_zfmisc_1(k2_zfmisc_1(X1,k2_zfmisc_1(k1_xboole_0,X2)),X3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_408,c_806])).

cnf(c_5382,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,k2_zfmisc_1(k1_xboole_0,X1)),X2),X3) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1132,c_861])).

cnf(c_1008,plain,
    ( r2_hidden(X0,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,k2_zfmisc_1(k1_xboole_0,X2)),X3),X4)) != iProver_top ),
    inference(superposition,[status(thm)],[c_408,c_861])).

cnf(c_5392,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,k2_zfmisc_1(k1_xboole_0,X1)),X2),X3),X4) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1132,c_1008])).

cnf(c_5423,plain,
    ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_5382,c_5392])).

cnf(c_5649,plain,
    ( k1_xboole_0 = X0
    | r2_hidden(sK1(k1_xboole_0,X1,X0),X0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_1144,c_5423])).

cnf(c_16,negated_conjecture,
    ( k1_xboole_0 = k2_zfmisc_1(sK6,sK7)
    | k1_xboole_0 = sK6
    | k1_xboole_0 = sK7 ),
    inference(cnf_transformation,[],[f38])).

cnf(c_10,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X2,X3)
    | r2_hidden(k4_tarski(X2,X0),k2_zfmisc_1(X3,X1)) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_411,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X2,X3) != iProver_top
    | r2_hidden(k4_tarski(X2,X0),k2_zfmisc_1(X3,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_1016,plain,
    ( sK6 = k1_xboole_0
    | sK7 = k1_xboole_0
    | r2_hidden(X0,sK6) != iProver_top
    | r2_hidden(X1,sK7) != iProver_top
    | r2_hidden(k4_tarski(X0,X1),k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_16,c_411])).

cnf(c_1334,plain,
    ( sK6 = k1_xboole_0
    | sK7 = k1_xboole_0
    | r2_hidden(X0,sK6) != iProver_top
    | r2_hidden(X1,sK7) != iProver_top ),
    inference(superposition,[status(thm)],[c_1016,c_618])).

cnf(c_5677,plain,
    ( sK6 = k1_xboole_0
    | sK7 = k1_xboole_0
    | r2_hidden(X0,sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_5649,c_1334])).

cnf(c_5877,plain,
    ( sK6 = k1_xboole_0
    | sK7 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_5649,c_5677])).

cnf(c_15,negated_conjecture,
    ( k1_xboole_0 != k2_zfmisc_1(sK6,sK7)
    | k1_xboole_0 != sK6 ),
    inference(cnf_transformation,[],[f39])).

cnf(c_5882,plain,
    ( k2_zfmisc_1(k1_xboole_0,sK7) != k1_xboole_0
    | sK6 != k1_xboole_0
    | sK7 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_5877,c_15])).

cnf(c_5884,plain,
    ( sK6 != k1_xboole_0
    | sK7 = k1_xboole_0
    | k1_xboole_0 != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_5882,c_5423])).

cnf(c_5885,plain,
    ( sK6 != k1_xboole_0
    | sK7 = k1_xboole_0 ),
    inference(equality_resolution_simp,[status(thm)],[c_5884])).

cnf(c_5964,plain,
    ( sK7 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_5885,c_5877])).

cnf(c_14,negated_conjecture,
    ( k1_xboole_0 != k2_zfmisc_1(sK6,sK7)
    | k1_xboole_0 != sK7 ),
    inference(cnf_transformation,[],[f40])).

cnf(c_5968,plain,
    ( k2_zfmisc_1(sK6,k1_xboole_0) != k1_xboole_0
    | k1_xboole_0 != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_5964,c_14])).

cnf(c_5969,plain,
    ( k2_zfmisc_1(sK6,k1_xboole_0) != k1_xboole_0 ),
    inference(equality_resolution_simp,[status(thm)],[c_5968])).

cnf(c_1007,plain,
    ( r2_hidden(X0,k2_zfmisc_1(X1,k2_zfmisc_1(k2_zfmisc_1(X2,k2_zfmisc_1(k1_xboole_0,X3)),X4))) != iProver_top ),
    inference(superposition,[status(thm)],[c_409,c_861])).

cnf(c_5675,plain,
    ( k2_zfmisc_1(X0,k2_zfmisc_1(k2_zfmisc_1(X1,k2_zfmisc_1(k1_xboole_0,X2)),X3)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_5649,c_1007])).

cnf(c_807,plain,
    ( r2_hidden(X0,k2_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1),X2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_408,c_676])).

cnf(c_898,plain,
    ( r2_hidden(X0,k2_zfmisc_1(X1,k2_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X2),X3))) != iProver_top ),
    inference(superposition,[status(thm)],[c_409,c_807])).

cnf(c_5383,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(X0,k2_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1),X2)),X3) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1132,c_898])).

cnf(c_5425,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(X0,k2_zfmisc_1(k1_xboole_0,X1)),X2) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_5423,c_5383])).

cnf(c_5431,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0),X1) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_5425,c_5423])).

cnf(c_5707,plain,
    ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_5675,c_5423,c_5431])).

cnf(c_5970,plain,
    ( k1_xboole_0 != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_5969,c_5707])).

cnf(c_5971,plain,
    ( $false ),
    inference(equality_resolution_simp,[status(thm)],[c_5970])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.14/0.34  % Computer   : n008.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 13:22:30 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running in FOF mode
% 3.76/0.99  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.76/0.99  
% 3.76/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.76/0.99  
% 3.76/0.99  ------  iProver source info
% 3.76/0.99  
% 3.76/0.99  git: date: 2020-06-30 10:37:57 +0100
% 3.76/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.76/0.99  git: non_committed_changes: false
% 3.76/0.99  git: last_make_outside_of_git: false
% 3.76/0.99  
% 3.76/0.99  ------ 
% 3.76/0.99  
% 3.76/0.99  ------ Input Options
% 3.76/0.99  
% 3.76/0.99  --out_options                           all
% 3.76/0.99  --tptp_safe_out                         true
% 3.76/0.99  --problem_path                          ""
% 3.76/0.99  --include_path                          ""
% 3.76/0.99  --clausifier                            res/vclausify_rel
% 3.76/0.99  --clausifier_options                    ""
% 3.76/0.99  --stdin                                 false
% 3.76/0.99  --stats_out                             all
% 3.76/0.99  
% 3.76/0.99  ------ General Options
% 3.76/0.99  
% 3.76/0.99  --fof                                   false
% 3.76/0.99  --time_out_real                         305.
% 3.76/0.99  --time_out_virtual                      -1.
% 3.76/0.99  --symbol_type_check                     false
% 3.76/0.99  --clausify_out                          false
% 3.76/0.99  --sig_cnt_out                           false
% 3.76/0.99  --trig_cnt_out                          false
% 3.76/0.99  --trig_cnt_out_tolerance                1.
% 3.76/0.99  --trig_cnt_out_sk_spl                   false
% 3.76/0.99  --abstr_cl_out                          false
% 3.76/0.99  
% 3.76/0.99  ------ Global Options
% 3.76/0.99  
% 3.76/0.99  --schedule                              default
% 3.76/0.99  --add_important_lit                     false
% 3.76/0.99  --prop_solver_per_cl                    1000
% 3.76/0.99  --min_unsat_core                        false
% 3.76/0.99  --soft_assumptions                      false
% 3.76/0.99  --soft_lemma_size                       3
% 3.76/0.99  --prop_impl_unit_size                   0
% 3.76/0.99  --prop_impl_unit                        []
% 3.76/0.99  --share_sel_clauses                     true
% 3.76/0.99  --reset_solvers                         false
% 3.76/0.99  --bc_imp_inh                            [conj_cone]
% 3.76/0.99  --conj_cone_tolerance                   3.
% 3.76/0.99  --extra_neg_conj                        none
% 3.76/0.99  --large_theory_mode                     true
% 3.76/0.99  --prolific_symb_bound                   200
% 3.76/0.99  --lt_threshold                          2000
% 3.76/0.99  --clause_weak_htbl                      true
% 3.76/0.99  --gc_record_bc_elim                     false
% 3.76/0.99  
% 3.76/0.99  ------ Preprocessing Options
% 3.76/0.99  
% 3.76/0.99  --preprocessing_flag                    true
% 3.76/0.99  --time_out_prep_mult                    0.1
% 3.76/0.99  --splitting_mode                        input
% 3.76/0.99  --splitting_grd                         true
% 3.76/0.99  --splitting_cvd                         false
% 3.76/0.99  --splitting_cvd_svl                     false
% 3.76/0.99  --splitting_nvd                         32
% 3.76/0.99  --sub_typing                            true
% 3.76/0.99  --prep_gs_sim                           true
% 3.76/0.99  --prep_unflatten                        true
% 3.76/0.99  --prep_res_sim                          true
% 3.76/0.99  --prep_upred                            true
% 3.76/0.99  --prep_sem_filter                       exhaustive
% 3.76/0.99  --prep_sem_filter_out                   false
% 3.76/0.99  --pred_elim                             true
% 3.76/0.99  --res_sim_input                         true
% 3.76/0.99  --eq_ax_congr_red                       true
% 3.76/0.99  --pure_diseq_elim                       true
% 3.76/0.99  --brand_transform                       false
% 3.76/0.99  --non_eq_to_eq                          false
% 3.76/0.99  --prep_def_merge                        true
% 3.76/0.99  --prep_def_merge_prop_impl              false
% 3.76/0.99  --prep_def_merge_mbd                    true
% 3.76/0.99  --prep_def_merge_tr_red                 false
% 3.76/0.99  --prep_def_merge_tr_cl                  false
% 3.76/0.99  --smt_preprocessing                     true
% 3.76/0.99  --smt_ac_axioms                         fast
% 3.76/0.99  --preprocessed_out                      false
% 3.76/0.99  --preprocessed_stats                    false
% 3.76/0.99  
% 3.76/0.99  ------ Abstraction refinement Options
% 3.76/0.99  
% 3.76/0.99  --abstr_ref                             []
% 3.76/0.99  --abstr_ref_prep                        false
% 3.76/0.99  --abstr_ref_until_sat                   false
% 3.76/0.99  --abstr_ref_sig_restrict                funpre
% 3.76/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 3.76/0.99  --abstr_ref_under                       []
% 3.76/0.99  
% 3.76/0.99  ------ SAT Options
% 3.76/0.99  
% 3.76/0.99  --sat_mode                              false
% 3.76/0.99  --sat_fm_restart_options                ""
% 3.76/0.99  --sat_gr_def                            false
% 3.76/0.99  --sat_epr_types                         true
% 3.76/0.99  --sat_non_cyclic_types                  false
% 3.76/0.99  --sat_finite_models                     false
% 3.76/0.99  --sat_fm_lemmas                         false
% 3.76/0.99  --sat_fm_prep                           false
% 3.76/0.99  --sat_fm_uc_incr                        true
% 3.76/0.99  --sat_out_model                         small
% 3.76/0.99  --sat_out_clauses                       false
% 3.76/0.99  
% 3.76/0.99  ------ QBF Options
% 3.76/0.99  
% 3.76/0.99  --qbf_mode                              false
% 3.76/0.99  --qbf_elim_univ                         false
% 3.76/0.99  --qbf_dom_inst                          none
% 3.76/0.99  --qbf_dom_pre_inst                      false
% 3.76/0.99  --qbf_sk_in                             false
% 3.76/0.99  --qbf_pred_elim                         true
% 3.76/0.99  --qbf_split                             512
% 3.76/0.99  
% 3.76/0.99  ------ BMC1 Options
% 3.76/0.99  
% 3.76/0.99  --bmc1_incremental                      false
% 3.76/0.99  --bmc1_axioms                           reachable_all
% 3.76/0.99  --bmc1_min_bound                        0
% 3.76/0.99  --bmc1_max_bound                        -1
% 3.76/0.99  --bmc1_max_bound_default                -1
% 3.76/0.99  --bmc1_symbol_reachability              true
% 3.76/0.99  --bmc1_property_lemmas                  false
% 3.76/0.99  --bmc1_k_induction                      false
% 3.76/0.99  --bmc1_non_equiv_states                 false
% 3.76/0.99  --bmc1_deadlock                         false
% 3.76/0.99  --bmc1_ucm                              false
% 3.76/0.99  --bmc1_add_unsat_core                   none
% 3.76/0.99  --bmc1_unsat_core_children              false
% 3.76/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 3.76/0.99  --bmc1_out_stat                         full
% 3.76/0.99  --bmc1_ground_init                      false
% 3.76/0.99  --bmc1_pre_inst_next_state              false
% 3.76/0.99  --bmc1_pre_inst_state                   false
% 3.76/0.99  --bmc1_pre_inst_reach_state             false
% 3.76/0.99  --bmc1_out_unsat_core                   false
% 3.76/0.99  --bmc1_aig_witness_out                  false
% 3.76/0.99  --bmc1_verbose                          false
% 3.76/0.99  --bmc1_dump_clauses_tptp                false
% 3.76/0.99  --bmc1_dump_unsat_core_tptp             false
% 3.76/0.99  --bmc1_dump_file                        -
% 3.76/0.99  --bmc1_ucm_expand_uc_limit              128
% 3.76/0.99  --bmc1_ucm_n_expand_iterations          6
% 3.76/0.99  --bmc1_ucm_extend_mode                  1
% 3.76/0.99  --bmc1_ucm_init_mode                    2
% 3.76/0.99  --bmc1_ucm_cone_mode                    none
% 3.76/0.99  --bmc1_ucm_reduced_relation_type        0
% 3.76/0.99  --bmc1_ucm_relax_model                  4
% 3.76/0.99  --bmc1_ucm_full_tr_after_sat            true
% 3.76/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 3.76/0.99  --bmc1_ucm_layered_model                none
% 3.76/0.99  --bmc1_ucm_max_lemma_size               10
% 3.76/0.99  
% 3.76/0.99  ------ AIG Options
% 3.76/0.99  
% 3.76/0.99  --aig_mode                              false
% 3.76/0.99  
% 3.76/0.99  ------ Instantiation Options
% 3.76/0.99  
% 3.76/0.99  --instantiation_flag                    true
% 3.76/0.99  --inst_sos_flag                         true
% 3.76/0.99  --inst_sos_phase                        true
% 3.76/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.76/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.76/0.99  --inst_lit_sel_side                     num_symb
% 3.76/0.99  --inst_solver_per_active                1400
% 3.76/0.99  --inst_solver_calls_frac                1.
% 3.76/0.99  --inst_passive_queue_type               priority_queues
% 3.76/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.76/0.99  --inst_passive_queues_freq              [25;2]
% 3.76/0.99  --inst_dismatching                      true
% 3.76/0.99  --inst_eager_unprocessed_to_passive     true
% 3.76/0.99  --inst_prop_sim_given                   true
% 3.76/0.99  --inst_prop_sim_new                     false
% 3.76/0.99  --inst_subs_new                         false
% 3.76/0.99  --inst_eq_res_simp                      false
% 3.76/0.99  --inst_subs_given                       false
% 3.76/0.99  --inst_orphan_elimination               true
% 3.76/0.99  --inst_learning_loop_flag               true
% 3.76/0.99  --inst_learning_start                   3000
% 3.76/0.99  --inst_learning_factor                  2
% 3.76/0.99  --inst_start_prop_sim_after_learn       3
% 3.76/0.99  --inst_sel_renew                        solver
% 3.76/0.99  --inst_lit_activity_flag                true
% 3.76/0.99  --inst_restr_to_given                   false
% 3.76/0.99  --inst_activity_threshold               500
% 3.76/0.99  --inst_out_proof                        true
% 3.76/0.99  
% 3.76/0.99  ------ Resolution Options
% 3.76/0.99  
% 3.76/0.99  --resolution_flag                       true
% 3.76/0.99  --res_lit_sel                           adaptive
% 3.76/0.99  --res_lit_sel_side                      none
% 3.76/0.99  --res_ordering                          kbo
% 3.76/0.99  --res_to_prop_solver                    active
% 3.76/0.99  --res_prop_simpl_new                    false
% 3.76/0.99  --res_prop_simpl_given                  true
% 3.76/0.99  --res_passive_queue_type                priority_queues
% 3.76/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.76/0.99  --res_passive_queues_freq               [15;5]
% 3.76/0.99  --res_forward_subs                      full
% 3.76/0.99  --res_backward_subs                     full
% 3.76/0.99  --res_forward_subs_resolution           true
% 3.76/0.99  --res_backward_subs_resolution          true
% 3.76/0.99  --res_orphan_elimination                true
% 3.76/0.99  --res_time_limit                        2.
% 3.76/0.99  --res_out_proof                         true
% 3.76/0.99  
% 3.76/0.99  ------ Superposition Options
% 3.76/0.99  
% 3.76/0.99  --superposition_flag                    true
% 3.76/0.99  --sup_passive_queue_type                priority_queues
% 3.76/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.76/0.99  --sup_passive_queues_freq               [8;1;4]
% 3.76/0.99  --demod_completeness_check              fast
% 3.76/0.99  --demod_use_ground                      true
% 3.76/0.99  --sup_to_prop_solver                    passive
% 3.76/0.99  --sup_prop_simpl_new                    true
% 3.76/0.99  --sup_prop_simpl_given                  true
% 3.76/0.99  --sup_fun_splitting                     true
% 3.76/0.99  --sup_smt_interval                      50000
% 3.76/0.99  
% 3.76/0.99  ------ Superposition Simplification Setup
% 3.76/0.99  
% 3.76/0.99  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 3.76/0.99  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 3.76/0.99  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 3.76/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 3.76/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 3.76/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 3.76/0.99  --sup_full_bw                           [BwDemod;BwSubsumption]
% 3.76/0.99  --sup_immed_triv                        [TrivRules]
% 3.76/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.76/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.76/0.99  --sup_immed_bw_main                     []
% 3.76/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 3.76/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 3.76/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.76/0.99  --sup_input_bw                          []
% 3.76/0.99  
% 3.76/0.99  ------ Combination Options
% 3.76/0.99  
% 3.76/0.99  --comb_res_mult                         3
% 3.76/0.99  --comb_sup_mult                         2
% 3.76/0.99  --comb_inst_mult                        10
% 3.76/0.99  
% 3.76/0.99  ------ Debug Options
% 3.76/0.99  
% 3.76/0.99  --dbg_backtrace                         false
% 3.76/0.99  --dbg_dump_prop_clauses                 false
% 3.76/0.99  --dbg_dump_prop_clauses_file            -
% 3.76/0.99  --dbg_out_stat                          false
% 3.76/0.99  ------ Parsing...
% 3.76/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.76/0.99  
% 3.76/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 3.76/0.99  
% 3.76/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.76/0.99  
% 3.76/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.76/0.99  ------ Proving...
% 3.76/0.99  ------ Problem Properties 
% 3.76/0.99  
% 3.76/0.99  
% 3.76/0.99  clauses                                 16
% 3.76/0.99  conjectures                             3
% 3.76/0.99  EPR                                     0
% 3.76/0.99  Horn                                    12
% 3.76/0.99  unary                                   4
% 3.76/0.99  binary                                  6
% 3.76/0.99  lits                                    36
% 3.76/0.99  lits eq                                 17
% 3.76/0.99  fd_pure                                 0
% 3.76/0.99  fd_pseudo                               0
% 3.76/0.99  fd_cond                                 0
% 3.76/0.99  fd_pseudo_cond                          4
% 3.76/0.99  AC symbols                              0
% 3.76/0.99  
% 3.76/0.99  ------ Schedule dynamic 5 is on 
% 3.76/0.99  
% 3.76/0.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.76/0.99  
% 3.76/0.99  
% 3.76/0.99  ------ 
% 3.76/0.99  Current options:
% 3.76/0.99  ------ 
% 3.76/0.99  
% 3.76/0.99  ------ Input Options
% 3.76/0.99  
% 3.76/0.99  --out_options                           all
% 3.76/0.99  --tptp_safe_out                         true
% 3.76/0.99  --problem_path                          ""
% 3.76/0.99  --include_path                          ""
% 3.76/0.99  --clausifier                            res/vclausify_rel
% 3.76/0.99  --clausifier_options                    ""
% 3.76/0.99  --stdin                                 false
% 3.76/0.99  --stats_out                             all
% 3.76/0.99  
% 3.76/0.99  ------ General Options
% 3.76/0.99  
% 3.76/0.99  --fof                                   false
% 3.76/0.99  --time_out_real                         305.
% 3.76/0.99  --time_out_virtual                      -1.
% 3.76/0.99  --symbol_type_check                     false
% 3.76/0.99  --clausify_out                          false
% 3.76/0.99  --sig_cnt_out                           false
% 3.76/0.99  --trig_cnt_out                          false
% 3.76/0.99  --trig_cnt_out_tolerance                1.
% 3.76/0.99  --trig_cnt_out_sk_spl                   false
% 3.76/0.99  --abstr_cl_out                          false
% 3.76/0.99  
% 3.76/0.99  ------ Global Options
% 3.76/0.99  
% 3.76/0.99  --schedule                              default
% 3.76/0.99  --add_important_lit                     false
% 3.76/0.99  --prop_solver_per_cl                    1000
% 3.76/0.99  --min_unsat_core                        false
% 3.76/0.99  --soft_assumptions                      false
% 3.76/0.99  --soft_lemma_size                       3
% 3.76/0.99  --prop_impl_unit_size                   0
% 3.76/0.99  --prop_impl_unit                        []
% 3.76/0.99  --share_sel_clauses                     true
% 3.76/0.99  --reset_solvers                         false
% 3.76/0.99  --bc_imp_inh                            [conj_cone]
% 3.76/0.99  --conj_cone_tolerance                   3.
% 3.76/0.99  --extra_neg_conj                        none
% 3.76/0.99  --large_theory_mode                     true
% 3.76/0.99  --prolific_symb_bound                   200
% 3.76/0.99  --lt_threshold                          2000
% 3.76/0.99  --clause_weak_htbl                      true
% 3.76/0.99  --gc_record_bc_elim                     false
% 3.76/0.99  
% 3.76/0.99  ------ Preprocessing Options
% 3.76/0.99  
% 3.76/0.99  --preprocessing_flag                    true
% 3.76/0.99  --time_out_prep_mult                    0.1
% 3.76/0.99  --splitting_mode                        input
% 3.76/0.99  --splitting_grd                         true
% 3.76/0.99  --splitting_cvd                         false
% 3.76/0.99  --splitting_cvd_svl                     false
% 3.76/0.99  --splitting_nvd                         32
% 3.76/0.99  --sub_typing                            true
% 3.76/0.99  --prep_gs_sim                           true
% 3.76/0.99  --prep_unflatten                        true
% 3.76/0.99  --prep_res_sim                          true
% 3.76/0.99  --prep_upred                            true
% 3.76/0.99  --prep_sem_filter                       exhaustive
% 3.76/0.99  --prep_sem_filter_out                   false
% 3.76/0.99  --pred_elim                             true
% 3.76/0.99  --res_sim_input                         true
% 3.76/0.99  --eq_ax_congr_red                       true
% 3.76/0.99  --pure_diseq_elim                       true
% 3.76/0.99  --brand_transform                       false
% 3.76/0.99  --non_eq_to_eq                          false
% 3.76/0.99  --prep_def_merge                        true
% 3.76/0.99  --prep_def_merge_prop_impl              false
% 3.76/0.99  --prep_def_merge_mbd                    true
% 3.76/0.99  --prep_def_merge_tr_red                 false
% 3.76/0.99  --prep_def_merge_tr_cl                  false
% 3.76/0.99  --smt_preprocessing                     true
% 3.76/0.99  --smt_ac_axioms                         fast
% 3.76/0.99  --preprocessed_out                      false
% 3.76/0.99  --preprocessed_stats                    false
% 3.76/0.99  
% 3.76/0.99  ------ Abstraction refinement Options
% 3.76/0.99  
% 3.76/0.99  --abstr_ref                             []
% 3.76/0.99  --abstr_ref_prep                        false
% 3.76/0.99  --abstr_ref_until_sat                   false
% 3.76/0.99  --abstr_ref_sig_restrict                funpre
% 3.76/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 3.76/0.99  --abstr_ref_under                       []
% 3.76/0.99  
% 3.76/0.99  ------ SAT Options
% 3.76/0.99  
% 3.76/0.99  --sat_mode                              false
% 3.76/0.99  --sat_fm_restart_options                ""
% 3.76/0.99  --sat_gr_def                            false
% 3.76/0.99  --sat_epr_types                         true
% 3.76/0.99  --sat_non_cyclic_types                  false
% 3.76/0.99  --sat_finite_models                     false
% 3.76/0.99  --sat_fm_lemmas                         false
% 3.76/0.99  --sat_fm_prep                           false
% 3.76/0.99  --sat_fm_uc_incr                        true
% 3.76/0.99  --sat_out_model                         small
% 3.76/0.99  --sat_out_clauses                       false
% 3.76/0.99  
% 3.76/0.99  ------ QBF Options
% 3.76/0.99  
% 3.76/0.99  --qbf_mode                              false
% 3.76/0.99  --qbf_elim_univ                         false
% 3.76/0.99  --qbf_dom_inst                          none
% 3.76/0.99  --qbf_dom_pre_inst                      false
% 3.76/0.99  --qbf_sk_in                             false
% 3.76/0.99  --qbf_pred_elim                         true
% 3.76/0.99  --qbf_split                             512
% 3.76/0.99  
% 3.76/0.99  ------ BMC1 Options
% 3.76/0.99  
% 3.76/0.99  --bmc1_incremental                      false
% 3.76/0.99  --bmc1_axioms                           reachable_all
% 3.76/0.99  --bmc1_min_bound                        0
% 3.76/0.99  --bmc1_max_bound                        -1
% 3.76/0.99  --bmc1_max_bound_default                -1
% 3.76/0.99  --bmc1_symbol_reachability              true
% 3.76/0.99  --bmc1_property_lemmas                  false
% 3.76/0.99  --bmc1_k_induction                      false
% 3.76/0.99  --bmc1_non_equiv_states                 false
% 3.76/0.99  --bmc1_deadlock                         false
% 3.76/0.99  --bmc1_ucm                              false
% 3.76/0.99  --bmc1_add_unsat_core                   none
% 3.76/0.99  --bmc1_unsat_core_children              false
% 3.76/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 3.76/0.99  --bmc1_out_stat                         full
% 3.76/0.99  --bmc1_ground_init                      false
% 3.76/0.99  --bmc1_pre_inst_next_state              false
% 3.76/0.99  --bmc1_pre_inst_state                   false
% 3.76/0.99  --bmc1_pre_inst_reach_state             false
% 3.76/0.99  --bmc1_out_unsat_core                   false
% 3.76/0.99  --bmc1_aig_witness_out                  false
% 3.76/0.99  --bmc1_verbose                          false
% 3.76/0.99  --bmc1_dump_clauses_tptp                false
% 3.76/0.99  --bmc1_dump_unsat_core_tptp             false
% 3.76/0.99  --bmc1_dump_file                        -
% 3.76/0.99  --bmc1_ucm_expand_uc_limit              128
% 3.76/0.99  --bmc1_ucm_n_expand_iterations          6
% 3.76/0.99  --bmc1_ucm_extend_mode                  1
% 3.76/0.99  --bmc1_ucm_init_mode                    2
% 3.76/0.99  --bmc1_ucm_cone_mode                    none
% 3.76/0.99  --bmc1_ucm_reduced_relation_type        0
% 3.76/0.99  --bmc1_ucm_relax_model                  4
% 3.76/0.99  --bmc1_ucm_full_tr_after_sat            true
% 3.76/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 3.76/0.99  --bmc1_ucm_layered_model                none
% 3.76/0.99  --bmc1_ucm_max_lemma_size               10
% 3.76/0.99  
% 3.76/0.99  ------ AIG Options
% 3.76/0.99  
% 3.76/0.99  --aig_mode                              false
% 3.76/0.99  
% 3.76/0.99  ------ Instantiation Options
% 3.76/0.99  
% 3.76/0.99  --instantiation_flag                    true
% 3.76/0.99  --inst_sos_flag                         true
% 3.76/0.99  --inst_sos_phase                        true
% 3.76/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.76/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.76/0.99  --inst_lit_sel_side                     none
% 3.76/0.99  --inst_solver_per_active                1400
% 3.76/0.99  --inst_solver_calls_frac                1.
% 3.76/0.99  --inst_passive_queue_type               priority_queues
% 3.76/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.76/0.99  --inst_passive_queues_freq              [25;2]
% 3.76/0.99  --inst_dismatching                      true
% 3.76/0.99  --inst_eager_unprocessed_to_passive     true
% 3.76/0.99  --inst_prop_sim_given                   true
% 3.76/0.99  --inst_prop_sim_new                     false
% 3.76/0.99  --inst_subs_new                         false
% 3.76/0.99  --inst_eq_res_simp                      false
% 3.76/0.99  --inst_subs_given                       false
% 3.76/0.99  --inst_orphan_elimination               true
% 3.76/0.99  --inst_learning_loop_flag               true
% 3.76/0.99  --inst_learning_start                   3000
% 3.76/0.99  --inst_learning_factor                  2
% 3.76/0.99  --inst_start_prop_sim_after_learn       3
% 3.76/0.99  --inst_sel_renew                        solver
% 3.76/0.99  --inst_lit_activity_flag                true
% 3.76/0.99  --inst_restr_to_given                   false
% 3.76/0.99  --inst_activity_threshold               500
% 3.76/0.99  --inst_out_proof                        true
% 3.76/0.99  
% 3.76/0.99  ------ Resolution Options
% 3.76/0.99  
% 3.76/0.99  --resolution_flag                       false
% 3.76/0.99  --res_lit_sel                           adaptive
% 3.76/0.99  --res_lit_sel_side                      none
% 3.76/0.99  --res_ordering                          kbo
% 3.76/0.99  --res_to_prop_solver                    active
% 3.76/0.99  --res_prop_simpl_new                    false
% 3.76/0.99  --res_prop_simpl_given                  true
% 3.76/0.99  --res_passive_queue_type                priority_queues
% 3.76/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.76/0.99  --res_passive_queues_freq               [15;5]
% 3.76/0.99  --res_forward_subs                      full
% 3.76/0.99  --res_backward_subs                     full
% 3.76/0.99  --res_forward_subs_resolution           true
% 3.76/0.99  --res_backward_subs_resolution          true
% 3.76/0.99  --res_orphan_elimination                true
% 3.76/0.99  --res_time_limit                        2.
% 3.76/0.99  --res_out_proof                         true
% 3.76/0.99  
% 3.76/0.99  ------ Superposition Options
% 3.76/0.99  
% 3.76/0.99  --superposition_flag                    true
% 3.76/0.99  --sup_passive_queue_type                priority_queues
% 3.76/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.76/0.99  --sup_passive_queues_freq               [8;1;4]
% 3.76/0.99  --demod_completeness_check              fast
% 3.76/0.99  --demod_use_ground                      true
% 3.76/0.99  --sup_to_prop_solver                    passive
% 3.76/0.99  --sup_prop_simpl_new                    true
% 3.76/0.99  --sup_prop_simpl_given                  true
% 3.76/0.99  --sup_fun_splitting                     true
% 3.76/0.99  --sup_smt_interval                      50000
% 3.76/0.99  
% 3.76/0.99  ------ Superposition Simplification Setup
% 3.76/0.99  
% 3.76/0.99  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 3.76/0.99  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 3.76/0.99  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 3.76/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 3.76/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 3.76/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 3.76/0.99  --sup_full_bw                           [BwDemod;BwSubsumption]
% 3.76/0.99  --sup_immed_triv                        [TrivRules]
% 3.76/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.76/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.76/0.99  --sup_immed_bw_main                     []
% 3.76/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 3.76/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 3.76/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.76/0.99  --sup_input_bw                          []
% 3.76/0.99  
% 3.76/0.99  ------ Combination Options
% 3.76/0.99  
% 3.76/0.99  --comb_res_mult                         3
% 3.76/0.99  --comb_sup_mult                         2
% 3.76/0.99  --comb_inst_mult                        10
% 3.76/0.99  
% 3.76/0.99  ------ Debug Options
% 3.76/0.99  
% 3.76/0.99  --dbg_backtrace                         false
% 3.76/0.99  --dbg_dump_prop_clauses                 false
% 3.76/0.99  --dbg_dump_prop_clauses_file            -
% 3.76/0.99  --dbg_out_stat                          false
% 3.76/0.99  
% 3.76/0.99  
% 3.76/0.99  
% 3.76/0.99  
% 3.76/0.99  ------ Proving...
% 3.76/0.99  
% 3.76/0.99  
% 3.76/0.99  % SZS status Theorem for theBenchmark.p
% 3.76/0.99  
% 3.76/0.99   Resolution empty clause
% 3.76/0.99  
% 3.76/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 3.76/0.99  
% 3.76/0.99  fof(f6,axiom,(
% 3.76/0.99    ! [X0,X1,X2] : (k2_zfmisc_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4,X5] : (k4_tarski(X4,X5) = X3 & r2_hidden(X5,X1) & r2_hidden(X4,X0))))),
% 3.76/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.76/0.99  
% 3.76/0.99  fof(f14,plain,(
% 3.76/0.99    ! [X0,X1,X2] : ((k2_zfmisc_1(X0,X1) = X2 | ? [X3] : ((! [X4,X5] : (k4_tarski(X4,X5) != X3 | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X0)) | ~r2_hidden(X3,X2)) & (? [X4,X5] : (k4_tarski(X4,X5) = X3 & r2_hidden(X5,X1) & r2_hidden(X4,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ! [X4,X5] : (k4_tarski(X4,X5) != X3 | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X0))) & (? [X4,X5] : (k4_tarski(X4,X5) = X3 & r2_hidden(X5,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X3,X2))) | k2_zfmisc_1(X0,X1) != X2))),
% 3.76/0.99    inference(nnf_transformation,[],[f6])).
% 3.76/0.99  
% 3.76/0.99  fof(f15,plain,(
% 3.76/0.99    ! [X0,X1,X2] : ((k2_zfmisc_1(X0,X1) = X2 | ? [X3] : ((! [X4,X5] : (k4_tarski(X4,X5) != X3 | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X0)) | ~r2_hidden(X3,X2)) & (? [X6,X7] : (k4_tarski(X6,X7) = X3 & r2_hidden(X7,X1) & r2_hidden(X6,X0)) | r2_hidden(X3,X2)))) & (! [X8] : ((r2_hidden(X8,X2) | ! [X9,X10] : (k4_tarski(X9,X10) != X8 | ~r2_hidden(X10,X1) | ~r2_hidden(X9,X0))) & (? [X11,X12] : (k4_tarski(X11,X12) = X8 & r2_hidden(X12,X1) & r2_hidden(X11,X0)) | ~r2_hidden(X8,X2))) | k2_zfmisc_1(X0,X1) != X2))),
% 3.76/0.99    inference(rectify,[],[f14])).
% 3.76/0.99  
% 3.76/0.99  fof(f18,plain,(
% 3.76/0.99    ! [X8,X1,X0] : (? [X11,X12] : (k4_tarski(X11,X12) = X8 & r2_hidden(X12,X1) & r2_hidden(X11,X0)) => (k4_tarski(sK4(X0,X1,X8),sK5(X0,X1,X8)) = X8 & r2_hidden(sK5(X0,X1,X8),X1) & r2_hidden(sK4(X0,X1,X8),X0)))),
% 3.76/0.99    introduced(choice_axiom,[])).
% 3.76/0.99  
% 3.76/0.99  fof(f17,plain,(
% 3.76/0.99    ( ! [X3] : (! [X2,X1,X0] : (? [X6,X7] : (k4_tarski(X6,X7) = X3 & r2_hidden(X7,X1) & r2_hidden(X6,X0)) => (k4_tarski(sK2(X0,X1,X2),sK3(X0,X1,X2)) = X3 & r2_hidden(sK3(X0,X1,X2),X1) & r2_hidden(sK2(X0,X1,X2),X0)))) )),
% 3.76/0.99    introduced(choice_axiom,[])).
% 3.76/0.99  
% 3.76/0.99  fof(f16,plain,(
% 3.76/0.99    ! [X2,X1,X0] : (? [X3] : ((! [X4,X5] : (k4_tarski(X4,X5) != X3 | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X0)) | ~r2_hidden(X3,X2)) & (? [X6,X7] : (k4_tarski(X6,X7) = X3 & r2_hidden(X7,X1) & r2_hidden(X6,X0)) | r2_hidden(X3,X2))) => ((! [X5,X4] : (k4_tarski(X4,X5) != sK1(X0,X1,X2) | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X0)) | ~r2_hidden(sK1(X0,X1,X2),X2)) & (? [X7,X6] : (k4_tarski(X6,X7) = sK1(X0,X1,X2) & r2_hidden(X7,X1) & r2_hidden(X6,X0)) | r2_hidden(sK1(X0,X1,X2),X2))))),
% 3.76/0.99    introduced(choice_axiom,[])).
% 3.76/0.99  
% 3.76/0.99  fof(f19,plain,(
% 3.76/0.99    ! [X0,X1,X2] : ((k2_zfmisc_1(X0,X1) = X2 | ((! [X4,X5] : (k4_tarski(X4,X5) != sK1(X0,X1,X2) | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X0)) | ~r2_hidden(sK1(X0,X1,X2),X2)) & ((k4_tarski(sK2(X0,X1,X2),sK3(X0,X1,X2)) = sK1(X0,X1,X2) & r2_hidden(sK3(X0,X1,X2),X1) & r2_hidden(sK2(X0,X1,X2),X0)) | r2_hidden(sK1(X0,X1,X2),X2)))) & (! [X8] : ((r2_hidden(X8,X2) | ! [X9,X10] : (k4_tarski(X9,X10) != X8 | ~r2_hidden(X10,X1) | ~r2_hidden(X9,X0))) & ((k4_tarski(sK4(X0,X1,X8),sK5(X0,X1,X8)) = X8 & r2_hidden(sK5(X0,X1,X8),X1) & r2_hidden(sK4(X0,X1,X8),X0)) | ~r2_hidden(X8,X2))) | k2_zfmisc_1(X0,X1) != X2))),
% 3.76/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4,sK5])],[f15,f18,f17,f16])).
% 3.76/0.99  
% 3.76/0.99  fof(f34,plain,(
% 3.76/0.99    ( ! [X2,X0,X1] : (k2_zfmisc_1(X0,X1) = X2 | r2_hidden(sK2(X0,X1,X2),X0) | r2_hidden(sK1(X0,X1,X2),X2)) )),
% 3.76/0.99    inference(cnf_transformation,[],[f19])).
% 3.76/0.99  
% 3.76/0.99  fof(f5,axiom,(
% 3.76/0.99    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 3.76/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.76/0.99  
% 3.76/0.99  fof(f29,plain,(
% 3.76/0.99    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 3.76/0.99    inference(cnf_transformation,[],[f5])).
% 3.76/0.99  
% 3.76/0.99  fof(f2,axiom,(
% 3.76/0.99    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 3.76/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.76/0.99  
% 3.76/0.99  fof(f9,plain,(
% 3.76/0.99    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X3] : ~r2_hidden(X3,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 3.76/0.99    inference(rectify,[],[f2])).
% 3.76/0.99  
% 3.76/0.99  fof(f10,plain,(
% 3.76/0.99    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 3.76/0.99    inference(ennf_transformation,[],[f9])).
% 3.76/0.99  
% 3.76/0.99  fof(f12,plain,(
% 3.76/0.99    ! [X1,X0] : (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) => r2_hidden(sK0(X0,X1),k3_xboole_0(X0,X1)))),
% 3.76/0.99    introduced(choice_axiom,[])).
% 3.76/0.99  
% 3.76/0.99  fof(f13,plain,(
% 3.76/0.99    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (r2_hidden(sK0(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 3.76/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f10,f12])).
% 3.76/0.99  
% 3.76/0.99  fof(f26,plain,(
% 3.76/0.99    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,k3_xboole_0(X0,X1))) )),
% 3.76/0.99    inference(cnf_transformation,[],[f13])).
% 3.76/0.99  
% 3.76/0.99  fof(f3,axiom,(
% 3.76/0.99    ! [X0,X1] : r1_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X0,X1))),
% 3.76/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.76/0.99  
% 3.76/0.99  fof(f27,plain,(
% 3.76/0.99    ( ! [X0,X1] : (r1_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X0,X1))) )),
% 3.76/0.99    inference(cnf_transformation,[],[f3])).
% 3.76/0.99  
% 3.76/0.99  fof(f4,axiom,(
% 3.76/0.99    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0),
% 3.76/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.76/0.99  
% 3.76/0.99  fof(f28,plain,(
% 3.76/0.99    ( ! [X0] : (k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0) )),
% 3.76/0.99    inference(cnf_transformation,[],[f4])).
% 3.76/0.99  
% 3.76/0.99  fof(f1,axiom,(
% 3.76/0.99    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 3.76/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.76/0.99  
% 3.76/0.99  fof(f24,plain,(
% 3.76/0.99    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 3.76/0.99    inference(cnf_transformation,[],[f1])).
% 3.76/0.99  
% 3.76/0.99  fof(f30,plain,(
% 3.76/0.99    ( ! [X2,X0,X8,X1] : (r2_hidden(sK4(X0,X1,X8),X0) | ~r2_hidden(X8,X2) | k2_zfmisc_1(X0,X1) != X2) )),
% 3.76/0.99    inference(cnf_transformation,[],[f19])).
% 3.76/0.99  
% 3.76/0.99  fof(f45,plain,(
% 3.76/0.99    ( ! [X0,X8,X1] : (r2_hidden(sK4(X0,X1,X8),X0) | ~r2_hidden(X8,k2_zfmisc_1(X0,X1))) )),
% 3.76/0.99    inference(equality_resolution,[],[f30])).
% 3.76/0.99  
% 3.76/0.99  fof(f31,plain,(
% 3.76/0.99    ( ! [X2,X0,X8,X1] : (r2_hidden(sK5(X0,X1,X8),X1) | ~r2_hidden(X8,X2) | k2_zfmisc_1(X0,X1) != X2) )),
% 3.76/0.99    inference(cnf_transformation,[],[f19])).
% 3.76/0.99  
% 3.76/0.99  fof(f44,plain,(
% 3.76/0.99    ( ! [X0,X8,X1] : (r2_hidden(sK5(X0,X1,X8),X1) | ~r2_hidden(X8,k2_zfmisc_1(X0,X1))) )),
% 3.76/0.99    inference(equality_resolution,[],[f31])).
% 3.76/0.99  
% 3.76/0.99  fof(f7,conjecture,(
% 3.76/0.99    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 3.76/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.76/0.99  
% 3.76/0.99  fof(f8,negated_conjecture,(
% 3.76/0.99    ~! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 3.76/0.99    inference(negated_conjecture,[],[f7])).
% 3.76/0.99  
% 3.76/0.99  fof(f11,plain,(
% 3.76/0.99    ? [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <~> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 3.76/0.99    inference(ennf_transformation,[],[f8])).
% 3.76/0.99  
% 3.76/0.99  fof(f20,plain,(
% 3.76/0.99    ? [X0,X1] : (((k1_xboole_0 != X1 & k1_xboole_0 != X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 = k2_zfmisc_1(X0,X1)))),
% 3.76/0.99    inference(nnf_transformation,[],[f11])).
% 3.76/0.99  
% 3.76/0.99  fof(f21,plain,(
% 3.76/0.99    ? [X0,X1] : (((k1_xboole_0 != X1 & k1_xboole_0 != X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 = k2_zfmisc_1(X0,X1)))),
% 3.76/0.99    inference(flattening,[],[f20])).
% 3.76/0.99  
% 3.76/0.99  fof(f22,plain,(
% 3.76/0.99    ? [X0,X1] : (((k1_xboole_0 != X1 & k1_xboole_0 != X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 = k2_zfmisc_1(X0,X1))) => (((k1_xboole_0 != sK7 & k1_xboole_0 != sK6) | k1_xboole_0 != k2_zfmisc_1(sK6,sK7)) & (k1_xboole_0 = sK7 | k1_xboole_0 = sK6 | k1_xboole_0 = k2_zfmisc_1(sK6,sK7)))),
% 3.76/0.99    introduced(choice_axiom,[])).
% 3.76/0.99  
% 3.76/0.99  fof(f23,plain,(
% 3.76/0.99    ((k1_xboole_0 != sK7 & k1_xboole_0 != sK6) | k1_xboole_0 != k2_zfmisc_1(sK6,sK7)) & (k1_xboole_0 = sK7 | k1_xboole_0 = sK6 | k1_xboole_0 = k2_zfmisc_1(sK6,sK7))),
% 3.76/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7])],[f21,f22])).
% 3.76/0.99  
% 3.76/0.99  fof(f38,plain,(
% 3.76/0.99    k1_xboole_0 = sK7 | k1_xboole_0 = sK6 | k1_xboole_0 = k2_zfmisc_1(sK6,sK7)),
% 3.76/0.99    inference(cnf_transformation,[],[f23])).
% 3.76/0.99  
% 3.76/0.99  fof(f33,plain,(
% 3.76/0.99    ( ! [X2,X0,X10,X8,X1,X9] : (r2_hidden(X8,X2) | k4_tarski(X9,X10) != X8 | ~r2_hidden(X10,X1) | ~r2_hidden(X9,X0) | k2_zfmisc_1(X0,X1) != X2) )),
% 3.76/0.99    inference(cnf_transformation,[],[f19])).
% 3.76/0.99  
% 3.76/0.99  fof(f41,plain,(
% 3.76/0.99    ( ! [X2,X0,X10,X1,X9] : (r2_hidden(k4_tarski(X9,X10),X2) | ~r2_hidden(X10,X1) | ~r2_hidden(X9,X0) | k2_zfmisc_1(X0,X1) != X2) )),
% 3.76/0.99    inference(equality_resolution,[],[f33])).
% 3.76/0.99  
% 3.76/0.99  fof(f42,plain,(
% 3.76/0.99    ( ! [X0,X10,X1,X9] : (r2_hidden(k4_tarski(X9,X10),k2_zfmisc_1(X0,X1)) | ~r2_hidden(X10,X1) | ~r2_hidden(X9,X0)) )),
% 3.76/0.99    inference(equality_resolution,[],[f41])).
% 3.76/0.99  
% 3.76/0.99  fof(f39,plain,(
% 3.76/0.99    k1_xboole_0 != sK6 | k1_xboole_0 != k2_zfmisc_1(sK6,sK7)),
% 3.76/0.99    inference(cnf_transformation,[],[f23])).
% 3.76/0.99  
% 3.76/0.99  fof(f40,plain,(
% 3.76/0.99    k1_xboole_0 != sK7 | k1_xboole_0 != k2_zfmisc_1(sK6,sK7)),
% 3.76/0.99    inference(cnf_transformation,[],[f23])).
% 3.76/0.99  
% 3.76/0.99  cnf(c_9,plain,
% 3.76/0.99      ( r2_hidden(sK2(X0,X1,X2),X0)
% 3.76/0.99      | r2_hidden(sK1(X0,X1,X2),X2)
% 3.76/0.99      | k2_zfmisc_1(X0,X1) = X2 ),
% 3.76/0.99      inference(cnf_transformation,[],[f34]) ).
% 3.76/0.99  
% 3.76/0.99  cnf(c_412,plain,
% 3.76/0.99      ( k2_zfmisc_1(X0,X1) = X2
% 3.76/0.99      | r2_hidden(sK2(X0,X1,X2),X0) = iProver_top
% 3.76/0.99      | r2_hidden(sK1(X0,X1,X2),X2) = iProver_top ),
% 3.76/0.99      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 3.76/0.99  
% 3.76/0.99  cnf(c_5,plain,
% 3.76/0.99      ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
% 3.76/0.99      inference(cnf_transformation,[],[f29]) ).
% 3.76/0.99  
% 3.76/0.99  cnf(c_1,plain,
% 3.76/0.99      ( ~ r2_hidden(X0,k3_xboole_0(X1,X2)) | ~ r1_xboole_0(X1,X2) ),
% 3.76/0.99      inference(cnf_transformation,[],[f26]) ).
% 3.76/0.99  
% 3.76/0.99  cnf(c_3,plain,
% 3.76/0.99      ( r1_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X0,X1)) ),
% 3.76/0.99      inference(cnf_transformation,[],[f27]) ).
% 3.76/0.99  
% 3.76/0.99  cnf(c_156,plain,
% 3.76/0.99      ( ~ r2_hidden(X0,k3_xboole_0(X1,X2))
% 3.76/0.99      | k5_xboole_0(X3,X4) != X2
% 3.76/0.99      | k3_xboole_0(X3,X4) != X1 ),
% 3.76/0.99      inference(resolution_lifted,[status(thm)],[c_1,c_3]) ).
% 3.76/0.99  
% 3.76/0.99  cnf(c_157,plain,
% 3.76/0.99      ( ~ r2_hidden(X0,k3_xboole_0(k3_xboole_0(X1,X2),k5_xboole_0(X1,X2))) ),
% 3.76/0.99      inference(unflattening,[status(thm)],[c_156]) ).
% 3.76/0.99  
% 3.76/0.99  cnf(c_406,plain,
% 3.76/0.99      ( r2_hidden(X0,k3_xboole_0(k3_xboole_0(X1,X2),k5_xboole_0(X1,X2))) != iProver_top ),
% 3.76/0.99      inference(predicate_to_equality,[status(thm)],[c_157]) ).
% 3.76/0.99  
% 3.76/0.99  cnf(c_617,plain,
% 3.76/0.99      ( r2_hidden(X0,k3_xboole_0(k3_xboole_0(X1,k1_xboole_0),X1)) != iProver_top ),
% 3.76/0.99      inference(superposition,[status(thm)],[c_5,c_406]) ).
% 3.76/0.99  
% 3.76/0.99  cnf(c_4,plain,
% 3.76/0.99      ( k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
% 3.76/0.99      inference(cnf_transformation,[],[f28]) ).
% 3.76/0.99  
% 3.76/0.99  cnf(c_0,plain,
% 3.76/0.99      ( k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
% 3.76/0.99      inference(cnf_transformation,[],[f24]) ).
% 3.76/0.99  
% 3.76/0.99  cnf(c_542,plain,
% 3.76/0.99      ( k3_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
% 3.76/0.99      inference(superposition,[status(thm)],[c_4,c_0]) ).
% 3.76/0.99  
% 3.76/0.99  cnf(c_618,plain,
% 3.76/0.99      ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
% 3.76/0.99      inference(demodulation,[status(thm)],[c_617,c_4,c_542]) ).
% 3.76/0.99  
% 3.76/0.99  cnf(c_1144,plain,
% 3.76/0.99      ( k2_zfmisc_1(k1_xboole_0,X0) = X1
% 3.76/0.99      | r2_hidden(sK1(k1_xboole_0,X0,X1),X1) = iProver_top ),
% 3.76/0.99      inference(superposition,[status(thm)],[c_412,c_618]) ).
% 3.76/0.99  
% 3.76/0.99  cnf(c_1132,plain,
% 3.76/0.99      ( k2_zfmisc_1(X0,X1) = k1_xboole_0
% 3.76/0.99      | r2_hidden(sK2(X0,X1,k1_xboole_0),X0) = iProver_top ),
% 3.76/0.99      inference(superposition,[status(thm)],[c_412,c_618]) ).
% 3.76/0.99  
% 3.76/0.99  cnf(c_13,plain,
% 3.76/0.99      ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) | r2_hidden(sK4(X1,X2,X0),X1) ),
% 3.76/0.99      inference(cnf_transformation,[],[f45]) ).
% 3.76/0.99  
% 3.76/0.99  cnf(c_408,plain,
% 3.76/0.99      ( r2_hidden(X0,k2_zfmisc_1(X1,X2)) != iProver_top
% 3.76/0.99      | r2_hidden(sK4(X1,X2,X0),X1) = iProver_top ),
% 3.76/0.99      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 3.76/0.99  
% 3.76/0.99  cnf(c_12,plain,
% 3.76/0.99      ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) | r2_hidden(sK5(X1,X2,X0),X2) ),
% 3.76/0.99      inference(cnf_transformation,[],[f44]) ).
% 3.76/0.99  
% 3.76/0.99  cnf(c_409,plain,
% 3.76/0.99      ( r2_hidden(X0,k2_zfmisc_1(X1,X2)) != iProver_top
% 3.76/0.99      | r2_hidden(sK5(X1,X2,X0),X2) = iProver_top ),
% 3.76/0.99      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 3.76/0.99  
% 3.76/0.99  cnf(c_676,plain,
% 3.76/0.99      ( r2_hidden(X0,k2_zfmisc_1(k1_xboole_0,X1)) != iProver_top ),
% 3.76/0.99      inference(superposition,[status(thm)],[c_408,c_618]) ).
% 3.76/0.99  
% 3.76/0.99  cnf(c_806,plain,
% 3.76/0.99      ( r2_hidden(X0,k2_zfmisc_1(X1,k2_zfmisc_1(k1_xboole_0,X2))) != iProver_top ),
% 3.76/0.99      inference(superposition,[status(thm)],[c_409,c_676]) ).
% 3.76/0.99  
% 3.76/0.99  cnf(c_861,plain,
% 3.76/0.99      ( r2_hidden(X0,k2_zfmisc_1(k2_zfmisc_1(X1,k2_zfmisc_1(k1_xboole_0,X2)),X3)) != iProver_top ),
% 3.76/0.99      inference(superposition,[status(thm)],[c_408,c_806]) ).
% 3.76/0.99  
% 3.76/0.99  cnf(c_5382,plain,
% 3.76/0.99      ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,k2_zfmisc_1(k1_xboole_0,X1)),X2),X3) = k1_xboole_0 ),
% 3.76/0.99      inference(superposition,[status(thm)],[c_1132,c_861]) ).
% 3.76/0.99  
% 3.76/0.99  cnf(c_1008,plain,
% 3.76/0.99      ( r2_hidden(X0,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,k2_zfmisc_1(k1_xboole_0,X2)),X3),X4)) != iProver_top ),
% 3.76/0.99      inference(superposition,[status(thm)],[c_408,c_861]) ).
% 3.76/0.99  
% 3.76/0.99  cnf(c_5392,plain,
% 3.76/0.99      ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,k2_zfmisc_1(k1_xboole_0,X1)),X2),X3),X4) = k1_xboole_0 ),
% 3.76/0.99      inference(superposition,[status(thm)],[c_1132,c_1008]) ).
% 3.76/0.99  
% 3.76/0.99  cnf(c_5423,plain,
% 3.76/0.99      ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
% 3.76/0.99      inference(demodulation,[status(thm)],[c_5382,c_5392]) ).
% 3.76/0.99  
% 3.76/0.99  cnf(c_5649,plain,
% 3.76/0.99      ( k1_xboole_0 = X0 | r2_hidden(sK1(k1_xboole_0,X1,X0),X0) = iProver_top ),
% 3.76/0.99      inference(demodulation,[status(thm)],[c_1144,c_5423]) ).
% 3.76/0.99  
% 3.76/0.99  cnf(c_16,negated_conjecture,
% 3.76/0.99      ( k1_xboole_0 = k2_zfmisc_1(sK6,sK7)
% 3.76/0.99      | k1_xboole_0 = sK6
% 3.76/0.99      | k1_xboole_0 = sK7 ),
% 3.76/0.99      inference(cnf_transformation,[],[f38]) ).
% 3.76/0.99  
% 3.76/0.99  cnf(c_10,plain,
% 3.76/0.99      ( ~ r2_hidden(X0,X1)
% 3.76/0.99      | ~ r2_hidden(X2,X3)
% 3.76/0.99      | r2_hidden(k4_tarski(X2,X0),k2_zfmisc_1(X3,X1)) ),
% 3.76/0.99      inference(cnf_transformation,[],[f42]) ).
% 3.76/0.99  
% 3.76/0.99  cnf(c_411,plain,
% 3.76/0.99      ( r2_hidden(X0,X1) != iProver_top
% 3.76/0.99      | r2_hidden(X2,X3) != iProver_top
% 3.76/0.99      | r2_hidden(k4_tarski(X2,X0),k2_zfmisc_1(X3,X1)) = iProver_top ),
% 3.76/0.99      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 3.76/0.99  
% 3.76/0.99  cnf(c_1016,plain,
% 3.76/0.99      ( sK6 = k1_xboole_0
% 3.76/0.99      | sK7 = k1_xboole_0
% 3.76/0.99      | r2_hidden(X0,sK6) != iProver_top
% 3.76/0.99      | r2_hidden(X1,sK7) != iProver_top
% 3.76/0.99      | r2_hidden(k4_tarski(X0,X1),k1_xboole_0) = iProver_top ),
% 3.76/0.99      inference(superposition,[status(thm)],[c_16,c_411]) ).
% 3.76/0.99  
% 3.76/0.99  cnf(c_1334,plain,
% 3.76/0.99      ( sK6 = k1_xboole_0
% 3.76/0.99      | sK7 = k1_xboole_0
% 3.76/0.99      | r2_hidden(X0,sK6) != iProver_top
% 3.76/0.99      | r2_hidden(X1,sK7) != iProver_top ),
% 3.76/0.99      inference(superposition,[status(thm)],[c_1016,c_618]) ).
% 3.76/0.99  
% 3.76/0.99  cnf(c_5677,plain,
% 3.76/0.99      ( sK6 = k1_xboole_0
% 3.76/0.99      | sK7 = k1_xboole_0
% 3.76/0.99      | r2_hidden(X0,sK6) != iProver_top ),
% 3.76/0.99      inference(superposition,[status(thm)],[c_5649,c_1334]) ).
% 3.76/0.99  
% 3.76/0.99  cnf(c_5877,plain,
% 3.76/0.99      ( sK6 = k1_xboole_0 | sK7 = k1_xboole_0 ),
% 3.76/0.99      inference(superposition,[status(thm)],[c_5649,c_5677]) ).
% 3.76/0.99  
% 3.76/0.99  cnf(c_15,negated_conjecture,
% 3.76/0.99      ( k1_xboole_0 != k2_zfmisc_1(sK6,sK7) | k1_xboole_0 != sK6 ),
% 3.76/0.99      inference(cnf_transformation,[],[f39]) ).
% 3.76/0.99  
% 3.76/0.99  cnf(c_5882,plain,
% 3.76/0.99      ( k2_zfmisc_1(k1_xboole_0,sK7) != k1_xboole_0
% 3.76/0.99      | sK6 != k1_xboole_0
% 3.76/0.99      | sK7 = k1_xboole_0 ),
% 3.76/0.99      inference(superposition,[status(thm)],[c_5877,c_15]) ).
% 3.76/0.99  
% 3.76/0.99  cnf(c_5884,plain,
% 3.76/0.99      ( sK6 != k1_xboole_0 | sK7 = k1_xboole_0 | k1_xboole_0 != k1_xboole_0 ),
% 3.76/0.99      inference(demodulation,[status(thm)],[c_5882,c_5423]) ).
% 3.76/0.99  
% 3.76/0.99  cnf(c_5885,plain,
% 3.76/0.99      ( sK6 != k1_xboole_0 | sK7 = k1_xboole_0 ),
% 3.76/0.99      inference(equality_resolution_simp,[status(thm)],[c_5884]) ).
% 3.76/0.99  
% 3.76/0.99  cnf(c_5964,plain,
% 3.76/0.99      ( sK7 = k1_xboole_0 ),
% 3.76/0.99      inference(global_propositional_subsumption,[status(thm)],[c_5885,c_5877]) ).
% 3.76/0.99  
% 3.76/0.99  cnf(c_14,negated_conjecture,
% 3.76/0.99      ( k1_xboole_0 != k2_zfmisc_1(sK6,sK7) | k1_xboole_0 != sK7 ),
% 3.76/0.99      inference(cnf_transformation,[],[f40]) ).
% 3.76/0.99  
% 3.76/0.99  cnf(c_5968,plain,
% 3.76/0.99      ( k2_zfmisc_1(sK6,k1_xboole_0) != k1_xboole_0
% 3.76/0.99      | k1_xboole_0 != k1_xboole_0 ),
% 3.76/0.99      inference(demodulation,[status(thm)],[c_5964,c_14]) ).
% 3.76/0.99  
% 3.76/0.99  cnf(c_5969,plain,
% 3.76/0.99      ( k2_zfmisc_1(sK6,k1_xboole_0) != k1_xboole_0 ),
% 3.76/0.99      inference(equality_resolution_simp,[status(thm)],[c_5968]) ).
% 3.76/0.99  
% 3.76/0.99  cnf(c_1007,plain,
% 3.76/0.99      ( r2_hidden(X0,k2_zfmisc_1(X1,k2_zfmisc_1(k2_zfmisc_1(X2,k2_zfmisc_1(k1_xboole_0,X3)),X4))) != iProver_top ),
% 3.76/0.99      inference(superposition,[status(thm)],[c_409,c_861]) ).
% 3.76/0.99  
% 3.76/0.99  cnf(c_5675,plain,
% 3.76/0.99      ( k2_zfmisc_1(X0,k2_zfmisc_1(k2_zfmisc_1(X1,k2_zfmisc_1(k1_xboole_0,X2)),X3)) = k1_xboole_0 ),
% 3.76/0.99      inference(superposition,[status(thm)],[c_5649,c_1007]) ).
% 3.76/0.99  
% 3.76/0.99  cnf(c_807,plain,
% 3.76/0.99      ( r2_hidden(X0,k2_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1),X2)) != iProver_top ),
% 3.76/0.99      inference(superposition,[status(thm)],[c_408,c_676]) ).
% 3.76/0.99  
% 3.76/0.99  cnf(c_898,plain,
% 3.76/0.99      ( r2_hidden(X0,k2_zfmisc_1(X1,k2_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X2),X3))) != iProver_top ),
% 3.76/0.99      inference(superposition,[status(thm)],[c_409,c_807]) ).
% 3.76/0.99  
% 3.76/0.99  cnf(c_5383,plain,
% 3.76/0.99      ( k2_zfmisc_1(k2_zfmisc_1(X0,k2_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1),X2)),X3) = k1_xboole_0 ),
% 3.76/0.99      inference(superposition,[status(thm)],[c_1132,c_898]) ).
% 3.76/0.99  
% 3.76/0.99  cnf(c_5425,plain,
% 3.76/0.99      ( k2_zfmisc_1(k2_zfmisc_1(X0,k2_zfmisc_1(k1_xboole_0,X1)),X2) = k1_xboole_0 ),
% 3.76/0.99      inference(demodulation,[status(thm)],[c_5423,c_5383]) ).
% 3.76/0.99  
% 3.76/0.99  cnf(c_5431,plain,
% 3.76/0.99      ( k2_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0),X1) = k1_xboole_0 ),
% 3.76/0.99      inference(demodulation,[status(thm)],[c_5425,c_5423]) ).
% 3.76/0.99  
% 3.76/0.99  cnf(c_5707,plain,
% 3.76/0.99      ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
% 3.76/0.99      inference(demodulation,[status(thm)],[c_5675,c_5423,c_5431]) ).
% 3.76/0.99  
% 3.76/0.99  cnf(c_5970,plain,
% 3.76/0.99      ( k1_xboole_0 != k1_xboole_0 ),
% 3.76/0.99      inference(demodulation,[status(thm)],[c_5969,c_5707]) ).
% 3.76/0.99  
% 3.76/0.99  cnf(c_5971,plain,
% 3.76/0.99      ( $false ),
% 3.76/0.99      inference(equality_resolution_simp,[status(thm)],[c_5970]) ).
% 3.76/0.99  
% 3.76/0.99  
% 3.76/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 3.76/0.99  
% 3.76/0.99  ------                               Statistics
% 3.76/0.99  
% 3.76/0.99  ------ General
% 3.76/0.99  
% 3.76/0.99  abstr_ref_over_cycles:                  0
% 3.76/0.99  abstr_ref_under_cycles:                 0
% 3.76/0.99  gc_basic_clause_elim:                   0
% 3.76/0.99  forced_gc_time:                         0
% 3.76/0.99  parsing_time:                           0.008
% 3.76/0.99  unif_index_cands_time:                  0.
% 3.76/0.99  unif_index_add_time:                    0.
% 3.76/0.99  orderings_time:                         0.
% 3.76/0.99  out_proof_time:                         0.007
% 3.76/0.99  total_time:                             0.266
% 3.76/0.99  num_of_symbols:                         46
% 3.76/0.99  num_of_terms:                           8853
% 3.76/0.99  
% 3.76/0.99  ------ Preprocessing
% 3.76/0.99  
% 3.76/0.99  num_of_splits:                          0
% 3.76/0.99  num_of_split_atoms:                     0
% 3.76/0.99  num_of_reused_defs:                     0
% 3.76/0.99  num_eq_ax_congr_red:                    55
% 3.76/0.99  num_of_sem_filtered_clauses:            1
% 3.76/0.99  num_of_subtypes:                        0
% 3.76/0.99  monotx_restored_types:                  0
% 3.76/0.99  sat_num_of_epr_types:                   0
% 3.76/0.99  sat_num_of_non_cyclic_types:            0
% 3.76/0.99  sat_guarded_non_collapsed_types:        0
% 3.76/0.99  num_pure_diseq_elim:                    0
% 3.76/0.99  simp_replaced_by:                       0
% 3.76/0.99  res_preprocessed:                       80
% 3.76/0.99  prep_upred:                             0
% 3.76/0.99  prep_unflattend:                        4
% 3.76/0.99  smt_new_axioms:                         0
% 3.76/0.99  pred_elim_cands:                        1
% 3.76/0.99  pred_elim:                              1
% 3.76/0.99  pred_elim_cl:                           1
% 3.76/0.99  pred_elim_cycles:                       3
% 3.76/0.99  merged_defs:                            0
% 3.76/0.99  merged_defs_ncl:                        0
% 3.76/0.99  bin_hyper_res:                          0
% 3.76/0.99  prep_cycles:                            4
% 3.76/0.99  pred_elim_time:                         0.
% 3.76/0.99  splitting_time:                         0.
% 3.76/0.99  sem_filter_time:                        0.
% 3.76/0.99  monotx_time:                            0.
% 3.76/0.99  subtype_inf_time:                       0.
% 3.76/0.99  
% 3.76/0.99  ------ Problem properties
% 3.76/0.99  
% 3.76/0.99  clauses:                                16
% 3.76/0.99  conjectures:                            3
% 3.76/0.99  epr:                                    0
% 3.76/0.99  horn:                                   12
% 3.76/0.99  ground:                                 3
% 3.76/0.99  unary:                                  4
% 3.76/0.99  binary:                                 6
% 3.76/0.99  lits:                                   36
% 3.76/0.99  lits_eq:                                17
% 3.76/0.99  fd_pure:                                0
% 3.76/0.99  fd_pseudo:                              0
% 3.76/0.99  fd_cond:                                0
% 3.76/0.99  fd_pseudo_cond:                         4
% 3.76/0.99  ac_symbols:                             0
% 3.76/0.99  
% 3.76/0.99  ------ Propositional Solver
% 3.76/0.99  
% 3.76/0.99  prop_solver_calls:                      35
% 3.76/0.99  prop_fast_solver_calls:                 618
% 3.76/0.99  smt_solver_calls:                       0
% 3.76/0.99  smt_fast_solver_calls:                  0
% 3.76/0.99  prop_num_of_clauses:                    3463
% 3.76/0.99  prop_preprocess_simplified:             5299
% 3.76/0.99  prop_fo_subsumed:                       3
% 3.76/0.99  prop_solver_time:                       0.
% 3.76/0.99  smt_solver_time:                        0.
% 3.76/0.99  smt_fast_solver_time:                   0.
% 3.76/0.99  prop_fast_solver_time:                  0.
% 3.76/0.99  prop_unsat_core_time:                   0.
% 3.76/0.99  
% 3.76/0.99  ------ QBF
% 3.76/0.99  
% 3.76/0.99  qbf_q_res:                              0
% 3.76/0.99  qbf_num_tautologies:                    0
% 3.76/0.99  qbf_prep_cycles:                        0
% 3.76/0.99  
% 3.76/0.99  ------ BMC1
% 3.76/0.99  
% 3.76/0.99  bmc1_current_bound:                     -1
% 3.76/0.99  bmc1_last_solved_bound:                 -1
% 3.76/0.99  bmc1_unsat_core_size:                   -1
% 3.76/0.99  bmc1_unsat_core_parents_size:           -1
% 3.76/0.99  bmc1_merge_next_fun:                    0
% 3.76/0.99  bmc1_unsat_core_clauses_time:           0.
% 3.76/0.99  
% 3.76/0.99  ------ Instantiation
% 3.76/0.99  
% 3.76/0.99  inst_num_of_clauses:                    697
% 3.76/0.99  inst_num_in_passive:                    338
% 3.76/0.99  inst_num_in_active:                     320
% 3.76/0.99  inst_num_in_unprocessed:                39
% 3.76/0.99  inst_num_of_loops:                      410
% 3.76/0.99  inst_num_of_learning_restarts:          0
% 3.76/0.99  inst_num_moves_active_passive:          83
% 3.76/0.99  inst_lit_activity:                      0
% 3.76/0.99  inst_lit_activity_moves:                0
% 3.76/0.99  inst_num_tautologies:                   0
% 3.76/0.99  inst_num_prop_implied:                  0
% 3.76/0.99  inst_num_existing_simplified:           0
% 3.76/0.99  inst_num_eq_res_simplified:             0
% 3.76/0.99  inst_num_child_elim:                    0
% 3.76/0.99  inst_num_of_dismatching_blockings:      221
% 3.76/0.99  inst_num_of_non_proper_insts:           673
% 3.76/0.99  inst_num_of_duplicates:                 0
% 3.76/0.99  inst_inst_num_from_inst_to_res:         0
% 3.76/0.99  inst_dismatching_checking_time:         0.
% 3.76/0.99  
% 3.76/0.99  ------ Resolution
% 3.76/0.99  
% 3.76/0.99  res_num_of_clauses:                     0
% 3.76/0.99  res_num_in_passive:                     0
% 3.76/0.99  res_num_in_active:                      0
% 3.76/0.99  res_num_of_loops:                       84
% 3.76/0.99  res_forward_subset_subsumed:            103
% 3.76/0.99  res_backward_subset_subsumed:           4
% 3.76/0.99  res_forward_subsumed:                   0
% 3.76/0.99  res_backward_subsumed:                  0
% 3.76/0.99  res_forward_subsumption_resolution:     0
% 3.76/0.99  res_backward_subsumption_resolution:    0
% 3.76/0.99  res_clause_to_clause_subsumption:       2148
% 3.76/0.99  res_orphan_elimination:                 0
% 3.76/0.99  res_tautology_del:                      64
% 3.76/0.99  res_num_eq_res_simplified:              0
% 3.76/0.99  res_num_sel_changes:                    0
% 3.76/0.99  res_moves_from_active_to_pass:          0
% 3.76/0.99  
% 3.76/0.99  ------ Superposition
% 3.76/0.99  
% 3.76/0.99  sup_time_total:                         0.
% 3.76/0.99  sup_time_generating:                    0.
% 3.76/0.99  sup_time_sim_full:                      0.
% 3.76/0.99  sup_time_sim_immed:                     0.
% 3.76/0.99  
% 3.76/0.99  sup_num_of_clauses:                     634
% 3.76/0.99  sup_num_in_active:                      38
% 3.76/0.99  sup_num_in_passive:                     596
% 3.76/0.99  sup_num_of_loops:                       80
% 3.76/0.99  sup_fw_superposition:                   442
% 3.76/0.99  sup_bw_superposition:                   462
% 3.76/0.99  sup_immediate_simplified:               130
% 3.76/0.99  sup_given_eliminated:                   0
% 3.76/0.99  comparisons_done:                       0
% 3.76/0.99  comparisons_avoided:                    149
% 3.76/0.99  
% 3.76/0.99  ------ Simplifications
% 3.76/0.99  
% 3.76/0.99  
% 3.76/0.99  sim_fw_subset_subsumed:                 16
% 3.76/0.99  sim_bw_subset_subsumed:                 16
% 3.76/0.99  sim_fw_subsumed:                        54
% 3.76/0.99  sim_bw_subsumed:                        41
% 3.76/0.99  sim_fw_subsumption_res:                 0
% 3.76/0.99  sim_bw_subsumption_res:                 0
% 3.76/0.99  sim_tautology_del:                      3
% 3.76/0.99  sim_eq_tautology_del:                   7
% 3.76/0.99  sim_eq_res_simp:                        2
% 3.76/0.99  sim_fw_demodulated:                     31
% 3.76/0.99  sim_bw_demodulated:                     22
% 3.76/0.99  sim_light_normalised:                   4
% 3.76/0.99  sim_joinable_taut:                      0
% 3.76/0.99  sim_joinable_simp:                      0
% 3.76/0.99  sim_ac_normalised:                      0
% 3.76/0.99  sim_smt_subsumption:                    0
% 3.76/0.99  
%------------------------------------------------------------------------------
