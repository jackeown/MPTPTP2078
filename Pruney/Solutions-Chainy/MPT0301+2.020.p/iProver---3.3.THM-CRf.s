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
% DateTime   : Thu Dec  3 11:36:58 EST 2020

% Result     : Theorem 3.35s
% Output     : CNFRefutation 3.35s
% Verified   : 
% Statistics : Number of formulae       :   75 ( 510 expanded)
%              Number of clauses        :   35 ( 168 expanded)
%              Number of leaves         :   13 ( 138 expanded)
%              Depth                    :   20
%              Number of atoms          :  309 (2005 expanded)
%              Number of equality atoms :  156 ( 844 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal clause size      :   18 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f4,axiom,(
    ! [X0,X1] :
      ( k3_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] :
              ( r2_hidden(X3,X0)
              & r2_hidden(X2,X3) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
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
    inference(nnf_transformation,[],[f4])).

fof(f16,plain,(
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
    inference(rectify,[],[f15])).

fof(f19,plain,(
    ! [X5,X0] :
      ( ? [X7] :
          ( r2_hidden(X7,X0)
          & r2_hidden(X5,X7) )
     => ( r2_hidden(sK7(X0,X5),X0)
        & r2_hidden(X5,sK7(X0,X5)) ) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( r2_hidden(X4,X0)
          & r2_hidden(X2,X4) )
     => ( r2_hidden(sK6(X0,X1),X0)
        & r2_hidden(X2,sK6(X0,X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
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
              | ~ r2_hidden(sK5(X0,X1),X3) )
          | ~ r2_hidden(sK5(X0,X1),X1) )
        & ( ? [X4] :
              ( r2_hidden(X4,X0)
              & r2_hidden(sK5(X0,X1),X4) )
          | r2_hidden(sK5(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( k3_tarski(X0) = X1
        | ( ( ! [X3] :
                ( ~ r2_hidden(X3,X0)
                | ~ r2_hidden(sK5(X0,X1),X3) )
            | ~ r2_hidden(sK5(X0,X1),X1) )
          & ( ( r2_hidden(sK6(X0,X1),X0)
              & r2_hidden(sK5(X0,X1),sK6(X0,X1)) )
            | r2_hidden(sK5(X0,X1),X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] :
                  ( ~ r2_hidden(X6,X0)
                  | ~ r2_hidden(X5,X6) ) )
            & ( ( r2_hidden(sK7(X0,X5),X0)
                & r2_hidden(X5,sK7(X0,X5)) )
              | ~ r2_hidden(X5,X1) ) )
        | k3_tarski(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6,sK7])],[f16,f19,f18,f17])).

fof(f40,plain,(
    ! [X0,X1] :
      ( k3_tarski(X0) = X1
      | r2_hidden(sK6(X0,X1),X0)
      | r2_hidden(sK5(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f1,axiom,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k1_tarski(X1)) = X0
    <=> ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(X0,k1_tarski(X1)) = X0
        | r2_hidden(X1,X0) )
      & ( ~ r2_hidden(X1,X0)
        | k4_xboole_0(X0,k1_tarski(X1)) != X0 ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | k4_xboole_0(X0,k1_tarski(X1)) != X0 ) ),
    inference(cnf_transformation,[],[f21])).

fof(f2,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | k4_xboole_0(X0,k2_tarski(X1,X1)) != X0 ) ),
    inference(definition_unfolding,[],[f42,f27])).

fof(f6,conjecture,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f7,negated_conjecture,(
    ~ ! [X0,X1] :
        ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      <=> ( k1_xboole_0 = X1
          | k1_xboole_0 = X0 ) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f8,plain,(
    ? [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <~> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f22,plain,(
    ? [X0,X1] :
      ( ( ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 )
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 = k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f8])).

fof(f23,plain,(
    ? [X0,X1] :
      ( ( ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 )
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 = k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f22])).

fof(f24,plain,
    ( ? [X0,X1] :
        ( ( ( k1_xboole_0 != X1
            & k1_xboole_0 != X0 )
          | k1_xboole_0 != k2_zfmisc_1(X0,X1) )
        & ( k1_xboole_0 = X1
          | k1_xboole_0 = X0
          | k1_xboole_0 = k2_zfmisc_1(X0,X1) ) )
   => ( ( ( k1_xboole_0 != sK9
          & k1_xboole_0 != sK8 )
        | k1_xboole_0 != k2_zfmisc_1(sK8,sK9) )
      & ( k1_xboole_0 = sK9
        | k1_xboole_0 = sK8
        | k1_xboole_0 = k2_zfmisc_1(sK8,sK9) ) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,
    ( ( ( k1_xboole_0 != sK9
        & k1_xboole_0 != sK8 )
      | k1_xboole_0 != k2_zfmisc_1(sK8,sK9) )
    & ( k1_xboole_0 = sK9
      | k1_xboole_0 = sK8
      | k1_xboole_0 = k2_zfmisc_1(sK8,sK9) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8,sK9])],[f23,f24])).

fof(f44,plain,
    ( k1_xboole_0 = sK9
    | k1_xboole_0 = sK8
    | k1_xboole_0 = k2_zfmisc_1(sK8,sK9) ),
    inference(cnf_transformation,[],[f25])).

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

fof(f9,plain,(
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

fof(f10,plain,(
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
    inference(rectify,[],[f9])).

fof(f13,plain,(
    ! [X8,X1,X0] :
      ( ? [X11,X12] :
          ( k4_tarski(X11,X12) = X8
          & r2_hidden(X12,X1)
          & r2_hidden(X11,X0) )
     => ( k4_tarski(sK3(X0,X1,X8),sK4(X0,X1,X8)) = X8
        & r2_hidden(sK4(X0,X1,X8),X1)
        & r2_hidden(sK3(X0,X1,X8),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f12,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X6,X7] :
          ( k4_tarski(X6,X7) = X3
          & r2_hidden(X7,X1)
          & r2_hidden(X6,X0) )
     => ( k4_tarski(sK1(X0,X1,X2),sK2(X0,X1,X2)) = X3
        & r2_hidden(sK2(X0,X1,X2),X1)
        & r2_hidden(sK1(X0,X1,X2),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f11,plain,(
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

fof(f14,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f10,f13,f12,f11])).

fof(f31,plain,(
    ! [X2,X0,X10,X8,X1,X9] :
      ( r2_hidden(X8,X2)
      | k4_tarski(X9,X10) != X8
      | ~ r2_hidden(X10,X1)
      | ~ r2_hidden(X9,X0)
      | k2_zfmisc_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f14])).

fof(f49,plain,(
    ! [X2,X0,X10,X1,X9] :
      ( r2_hidden(k4_tarski(X9,X10),X2)
      | ~ r2_hidden(X10,X1)
      | ~ r2_hidden(X9,X0)
      | k2_zfmisc_1(X0,X1) != X2 ) ),
    inference(equality_resolution,[],[f31])).

fof(f50,plain,(
    ! [X0,X10,X1,X9] :
      ( r2_hidden(k4_tarski(X9,X10),k2_zfmisc_1(X0,X1))
      | ~ r2_hidden(X10,X1)
      | ~ r2_hidden(X9,X0) ) ),
    inference(equality_resolution,[],[f49])).

fof(f45,plain,
    ( k1_xboole_0 != sK8
    | k1_xboole_0 != k2_zfmisc_1(sK8,sK9) ),
    inference(cnf_transformation,[],[f25])).

fof(f28,plain,(
    ! [X2,X0,X8,X1] :
      ( r2_hidden(sK3(X0,X1,X8),X0)
      | ~ r2_hidden(X8,X2)
      | k2_zfmisc_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f14])).

fof(f53,plain,(
    ! [X0,X8,X1] :
      ( r2_hidden(sK3(X0,X1,X8),X0)
      | ~ r2_hidden(X8,k2_zfmisc_1(X0,X1)) ) ),
    inference(equality_resolution,[],[f28])).

fof(f46,plain,
    ( k1_xboole_0 != sK9
    | k1_xboole_0 != k2_zfmisc_1(sK8,sK9) ),
    inference(cnf_transformation,[],[f25])).

fof(f29,plain,(
    ! [X2,X0,X8,X1] :
      ( r2_hidden(sK4(X0,X1,X8),X1)
      | ~ r2_hidden(X8,X2)
      | k2_zfmisc_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f14])).

fof(f52,plain,(
    ! [X0,X8,X1] :
      ( r2_hidden(sK4(X0,X1,X8),X1)
      | ~ r2_hidden(X8,k2_zfmisc_1(X0,X1)) ) ),
    inference(equality_resolution,[],[f29])).

cnf(c_10,plain,
    ( r2_hidden(sK6(X0,X1),X0)
    | r2_hidden(sK5(X0,X1),X1)
    | k3_tarski(X0) = X1 ),
    inference(cnf_transformation,[],[f40])).

cnf(c_1839,plain,
    ( k3_tarski(X0) = X1
    | r2_hidden(sK6(X0,X1),X0) = iProver_top
    | r2_hidden(sK5(X0,X1),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_0,plain,
    ( k4_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f26])).

cnf(c_16,negated_conjecture,
    ( ~ r2_hidden(X0,X1)
    | k4_xboole_0(X1,k2_tarski(X0,X0)) != X1 ),
    inference(cnf_transformation,[],[f48])).

cnf(c_1833,plain,
    ( k4_xboole_0(X0,k2_tarski(X1,X1)) != X0
    | r2_hidden(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_2026,plain,
    ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_0,c_1833])).

cnf(c_2134,plain,
    ( k3_tarski(k1_xboole_0) = X0
    | r2_hidden(sK5(k1_xboole_0,X0),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1839,c_2026])).

cnf(c_2132,plain,
    ( k3_tarski(X0) = k1_xboole_0
    | r2_hidden(sK6(X0,k1_xboole_0),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1839,c_2026])).

cnf(c_2312,plain,
    ( k3_tarski(k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2132,c_2026])).

cnf(c_2346,plain,
    ( k1_xboole_0 = X0
    | r2_hidden(sK5(k1_xboole_0,X0),X0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_2134,c_2312])).

cnf(c_19,negated_conjecture,
    ( k1_xboole_0 = k2_zfmisc_1(sK8,sK9)
    | k1_xboole_0 = sK8
    | k1_xboole_0 = sK9 ),
    inference(cnf_transformation,[],[f44])).

cnf(c_5,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X2,X3)
    | r2_hidden(k4_tarski(X2,X0),k2_zfmisc_1(X3,X1)) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_1844,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X2,X3) != iProver_top
    | r2_hidden(k4_tarski(X2,X0),k2_zfmisc_1(X3,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_2468,plain,
    ( sK8 = k1_xboole_0
    | sK9 = k1_xboole_0
    | r2_hidden(X0,sK8) != iProver_top
    | r2_hidden(X1,sK9) != iProver_top
    | r2_hidden(k4_tarski(X0,X1),k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_19,c_1844])).

cnf(c_2647,plain,
    ( sK8 = k1_xboole_0
    | sK9 = k1_xboole_0
    | r2_hidden(X0,sK8) != iProver_top
    | r2_hidden(X1,sK9) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_2468,c_2026])).

cnf(c_2662,plain,
    ( sK8 = k1_xboole_0
    | sK9 = k1_xboole_0
    | r2_hidden(X0,sK8) != iProver_top ),
    inference(superposition,[status(thm)],[c_2346,c_2647])).

cnf(c_2743,plain,
    ( sK8 = k1_xboole_0
    | sK9 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2346,c_2662])).

cnf(c_18,negated_conjecture,
    ( k1_xboole_0 != k2_zfmisc_1(sK8,sK9)
    | k1_xboole_0 != sK8 ),
    inference(cnf_transformation,[],[f45])).

cnf(c_3138,plain,
    ( k2_zfmisc_1(k1_xboole_0,sK9) != k1_xboole_0
    | sK8 != k1_xboole_0
    | sK9 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2743,c_18])).

cnf(c_3143,plain,
    ( k2_zfmisc_1(k1_xboole_0,sK9) != k1_xboole_0
    | sK9 = k1_xboole_0 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_3138,c_2743])).

cnf(c_8,plain,
    ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
    | r2_hidden(sK3(X1,X2,X0),X1) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_1841,plain,
    ( r2_hidden(X0,k2_zfmisc_1(X1,X2)) != iProver_top
    | r2_hidden(sK3(X1,X2,X0),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_2097,plain,
    ( r2_hidden(X0,k2_zfmisc_1(k1_xboole_0,X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1841,c_2026])).

cnf(c_2352,plain,
    ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2346,c_2097])).

cnf(c_3144,plain,
    ( sK9 = k1_xboole_0
    | k1_xboole_0 != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_3143,c_2352])).

cnf(c_3145,plain,
    ( sK9 = k1_xboole_0 ),
    inference(equality_resolution_simp,[status(thm)],[c_3144])).

cnf(c_17,negated_conjecture,
    ( k1_xboole_0 != k2_zfmisc_1(sK8,sK9)
    | k1_xboole_0 != sK9 ),
    inference(cnf_transformation,[],[f46])).

cnf(c_3156,plain,
    ( k2_zfmisc_1(sK8,k1_xboole_0) != k1_xboole_0
    | k1_xboole_0 != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_3145,c_17])).

cnf(c_3157,plain,
    ( k2_zfmisc_1(sK8,k1_xboole_0) != k1_xboole_0 ),
    inference(equality_resolution_simp,[status(thm)],[c_3156])).

cnf(c_7,plain,
    ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
    | r2_hidden(sK4(X1,X2,X0),X2) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_1842,plain,
    ( r2_hidden(X0,k2_zfmisc_1(X1,X2)) != iProver_top
    | r2_hidden(sK4(X1,X2,X0),X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_2116,plain,
    ( r2_hidden(X0,k2_zfmisc_1(X1,k1_xboole_0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1842,c_2026])).

cnf(c_2353,plain,
    ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2346,c_2116])).

cnf(c_3159,plain,
    ( k1_xboole_0 != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_3157,c_2353])).

cnf(c_3160,plain,
    ( $false ),
    inference(equality_resolution_simp,[status(thm)],[c_3159])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.12  % Command    : iproveropt_run.sh %d %s
% 0.13/0.33  % Computer   : n008.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 16:10:00 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 3.35/1.00  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.35/1.00  
% 3.35/1.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.35/1.00  
% 3.35/1.00  ------  iProver source info
% 3.35/1.00  
% 3.35/1.00  git: date: 2020-06-30 10:37:57 +0100
% 3.35/1.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.35/1.00  git: non_committed_changes: false
% 3.35/1.00  git: last_make_outside_of_git: false
% 3.35/1.00  
% 3.35/1.00  ------ 
% 3.35/1.00  ------ Parsing...
% 3.35/1.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.35/1.00  
% 3.35/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 3.35/1.00  
% 3.35/1.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.35/1.00  
% 3.35/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.35/1.00  ------ Proving...
% 3.35/1.00  ------ Problem Properties 
% 3.35/1.00  
% 3.35/1.00  
% 3.35/1.00  clauses                                 20
% 3.35/1.00  conjectures                             4
% 3.35/1.00  EPR                                     0
% 3.35/1.00  Horn                                    13
% 3.35/1.00  unary                                   1
% 3.35/1.00  binary                                  9
% 3.35/1.00  lits                                    52
% 3.35/1.00  lits eq                                 20
% 3.35/1.00  fd_pure                                 0
% 3.35/1.00  fd_pseudo                               0
% 3.35/1.00  fd_cond                                 0
% 3.35/1.00  fd_pseudo_cond                          7
% 3.35/1.00  AC symbols                              0
% 3.35/1.00  
% 3.35/1.00  ------ Input Options Time Limit: Unbounded
% 3.35/1.00  
% 3.35/1.00  
% 3.35/1.00  
% 3.35/1.00  
% 3.35/1.00  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  sf_s  rm: 0 0s  sf_e ------ 
% 3.35/1.00  Current options:
% 3.35/1.00  ------ 
% 3.35/1.00  
% 3.35/1.00  
% 3.35/1.00  
% 3.35/1.00  
% 3.35/1.00  ------ Proving...
% 3.35/1.00  
% 3.35/1.00  
% 3.35/1.00  ------ Preprocessing... sf_s  rm: 3 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.35/1.00  
% 3.35/1.00  ------ Proving...
% 3.35/1.00  
% 3.35/1.00  
% 3.35/1.00  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 3.35/1.00  
% 3.35/1.00  ------ Proving...
% 3.35/1.00  
% 3.35/1.00  
% 3.35/1.00  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.35/1.00  
% 3.35/1.00  ------ Proving...
% 3.35/1.00  
% 3.35/1.00  
% 3.35/1.00  ------ Preprocessing... sf_s  rm: 3 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.35/1.00  
% 3.35/1.00  ------ Proving...
% 3.35/1.00  
% 3.35/1.00  
% 3.35/1.00  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 3.35/1.00  
% 3.35/1.00  ------ Proving...
% 3.35/1.00  
% 3.35/1.00  
% 3.35/1.00  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 3.35/1.00  
% 3.35/1.00  ------ Proving...
% 3.35/1.00  
% 3.35/1.00  
% 3.35/1.00  % SZS status Theorem for theBenchmark.p
% 3.35/1.00  
% 3.35/1.00   Resolution empty clause
% 3.35/1.00  
% 3.35/1.00  % SZS output start CNFRefutation for theBenchmark.p
% 3.35/1.00  
% 3.35/1.00  fof(f4,axiom,(
% 3.35/1.00    ! [X0,X1] : (k3_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (r2_hidden(X3,X0) & r2_hidden(X2,X3))))),
% 3.35/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.35/1.00  
% 3.35/1.00  fof(f15,plain,(
% 3.35/1.00    ! [X0,X1] : ((k3_tarski(X0) = X1 | ? [X2] : ((! [X3] : (~r2_hidden(X3,X0) | ~r2_hidden(X2,X3)) | ~r2_hidden(X2,X1)) & (? [X3] : (r2_hidden(X3,X0) & r2_hidden(X2,X3)) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ! [X3] : (~r2_hidden(X3,X0) | ~r2_hidden(X2,X3))) & (? [X3] : (r2_hidden(X3,X0) & r2_hidden(X2,X3)) | ~r2_hidden(X2,X1))) | k3_tarski(X0) != X1))),
% 3.35/1.00    inference(nnf_transformation,[],[f4])).
% 3.35/1.00  
% 3.35/1.00  fof(f16,plain,(
% 3.35/1.00    ! [X0,X1] : ((k3_tarski(X0) = X1 | ? [X2] : ((! [X3] : (~r2_hidden(X3,X0) | ~r2_hidden(X2,X3)) | ~r2_hidden(X2,X1)) & (? [X4] : (r2_hidden(X4,X0) & r2_hidden(X2,X4)) | r2_hidden(X2,X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : (~r2_hidden(X6,X0) | ~r2_hidden(X5,X6))) & (? [X7] : (r2_hidden(X7,X0) & r2_hidden(X5,X7)) | ~r2_hidden(X5,X1))) | k3_tarski(X0) != X1))),
% 3.35/1.00    inference(rectify,[],[f15])).
% 3.35/1.00  
% 3.35/1.00  fof(f19,plain,(
% 3.35/1.00    ! [X5,X0] : (? [X7] : (r2_hidden(X7,X0) & r2_hidden(X5,X7)) => (r2_hidden(sK7(X0,X5),X0) & r2_hidden(X5,sK7(X0,X5))))),
% 3.35/1.00    introduced(choice_axiom,[])).
% 3.35/1.00  
% 3.35/1.00  fof(f18,plain,(
% 3.35/1.00    ( ! [X2] : (! [X1,X0] : (? [X4] : (r2_hidden(X4,X0) & r2_hidden(X2,X4)) => (r2_hidden(sK6(X0,X1),X0) & r2_hidden(X2,sK6(X0,X1))))) )),
% 3.35/1.00    introduced(choice_axiom,[])).
% 3.35/1.00  
% 3.35/1.00  fof(f17,plain,(
% 3.35/1.00    ! [X1,X0] : (? [X2] : ((! [X3] : (~r2_hidden(X3,X0) | ~r2_hidden(X2,X3)) | ~r2_hidden(X2,X1)) & (? [X4] : (r2_hidden(X4,X0) & r2_hidden(X2,X4)) | r2_hidden(X2,X1))) => ((! [X3] : (~r2_hidden(X3,X0) | ~r2_hidden(sK5(X0,X1),X3)) | ~r2_hidden(sK5(X0,X1),X1)) & (? [X4] : (r2_hidden(X4,X0) & r2_hidden(sK5(X0,X1),X4)) | r2_hidden(sK5(X0,X1),X1))))),
% 3.35/1.00    introduced(choice_axiom,[])).
% 3.35/1.00  
% 3.35/1.00  fof(f20,plain,(
% 3.35/1.00    ! [X0,X1] : ((k3_tarski(X0) = X1 | ((! [X3] : (~r2_hidden(X3,X0) | ~r2_hidden(sK5(X0,X1),X3)) | ~r2_hidden(sK5(X0,X1),X1)) & ((r2_hidden(sK6(X0,X1),X0) & r2_hidden(sK5(X0,X1),sK6(X0,X1))) | r2_hidden(sK5(X0,X1),X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : (~r2_hidden(X6,X0) | ~r2_hidden(X5,X6))) & ((r2_hidden(sK7(X0,X5),X0) & r2_hidden(X5,sK7(X0,X5))) | ~r2_hidden(X5,X1))) | k3_tarski(X0) != X1))),
% 3.35/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6,sK7])],[f16,f19,f18,f17])).
% 3.35/1.00  
% 3.35/1.00  fof(f40,plain,(
% 3.35/1.00    ( ! [X0,X1] : (k3_tarski(X0) = X1 | r2_hidden(sK6(X0,X1),X0) | r2_hidden(sK5(X0,X1),X1)) )),
% 3.35/1.00    inference(cnf_transformation,[],[f20])).
% 3.35/1.00  
% 3.35/1.00  fof(f1,axiom,(
% 3.35/1.00    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)),
% 3.35/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.35/1.00  
% 3.35/1.00  fof(f26,plain,(
% 3.35/1.00    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)) )),
% 3.35/1.00    inference(cnf_transformation,[],[f1])).
% 3.35/1.00  
% 3.35/1.00  fof(f5,axiom,(
% 3.35/1.00    ! [X0,X1] : (k4_xboole_0(X0,k1_tarski(X1)) = X0 <=> ~r2_hidden(X1,X0))),
% 3.35/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.35/1.00  
% 3.35/1.00  fof(f21,plain,(
% 3.35/1.00    ! [X0,X1] : ((k4_xboole_0(X0,k1_tarski(X1)) = X0 | r2_hidden(X1,X0)) & (~r2_hidden(X1,X0) | k4_xboole_0(X0,k1_tarski(X1)) != X0))),
% 3.35/1.00    inference(nnf_transformation,[],[f5])).
% 3.35/1.00  
% 3.35/1.00  fof(f42,plain,(
% 3.35/1.00    ( ! [X0,X1] : (~r2_hidden(X1,X0) | k4_xboole_0(X0,k1_tarski(X1)) != X0) )),
% 3.35/1.00    inference(cnf_transformation,[],[f21])).
% 3.35/1.00  
% 3.35/1.00  fof(f2,axiom,(
% 3.35/1.00    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 3.35/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.35/1.00  
% 3.35/1.00  fof(f27,plain,(
% 3.35/1.00    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 3.35/1.00    inference(cnf_transformation,[],[f2])).
% 3.35/1.00  
% 3.35/1.00  fof(f48,plain,(
% 3.35/1.00    ( ! [X0,X1] : (~r2_hidden(X1,X0) | k4_xboole_0(X0,k2_tarski(X1,X1)) != X0) )),
% 3.35/1.00    inference(definition_unfolding,[],[f42,f27])).
% 3.35/1.00  
% 3.35/1.00  fof(f6,conjecture,(
% 3.35/1.00    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 3.35/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.35/1.00  
% 3.35/1.00  fof(f7,negated_conjecture,(
% 3.35/1.00    ~! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 3.35/1.00    inference(negated_conjecture,[],[f6])).
% 3.35/1.00  
% 3.35/1.00  fof(f8,plain,(
% 3.35/1.00    ? [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <~> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 3.35/1.00    inference(ennf_transformation,[],[f7])).
% 3.35/1.00  
% 3.35/1.00  fof(f22,plain,(
% 3.35/1.00    ? [X0,X1] : (((k1_xboole_0 != X1 & k1_xboole_0 != X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 = k2_zfmisc_1(X0,X1)))),
% 3.35/1.00    inference(nnf_transformation,[],[f8])).
% 3.35/1.00  
% 3.35/1.00  fof(f23,plain,(
% 3.35/1.00    ? [X0,X1] : (((k1_xboole_0 != X1 & k1_xboole_0 != X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 = k2_zfmisc_1(X0,X1)))),
% 3.35/1.00    inference(flattening,[],[f22])).
% 3.35/1.00  
% 3.35/1.00  fof(f24,plain,(
% 3.35/1.00    ? [X0,X1] : (((k1_xboole_0 != X1 & k1_xboole_0 != X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 = k2_zfmisc_1(X0,X1))) => (((k1_xboole_0 != sK9 & k1_xboole_0 != sK8) | k1_xboole_0 != k2_zfmisc_1(sK8,sK9)) & (k1_xboole_0 = sK9 | k1_xboole_0 = sK8 | k1_xboole_0 = k2_zfmisc_1(sK8,sK9)))),
% 3.35/1.00    introduced(choice_axiom,[])).
% 3.35/1.00  
% 3.35/1.00  fof(f25,plain,(
% 3.35/1.00    ((k1_xboole_0 != sK9 & k1_xboole_0 != sK8) | k1_xboole_0 != k2_zfmisc_1(sK8,sK9)) & (k1_xboole_0 = sK9 | k1_xboole_0 = sK8 | k1_xboole_0 = k2_zfmisc_1(sK8,sK9))),
% 3.35/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8,sK9])],[f23,f24])).
% 3.35/1.00  
% 3.35/1.00  fof(f44,plain,(
% 3.35/1.00    k1_xboole_0 = sK9 | k1_xboole_0 = sK8 | k1_xboole_0 = k2_zfmisc_1(sK8,sK9)),
% 3.35/1.00    inference(cnf_transformation,[],[f25])).
% 3.35/1.00  
% 3.35/1.00  fof(f3,axiom,(
% 3.35/1.00    ! [X0,X1,X2] : (k2_zfmisc_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4,X5] : (k4_tarski(X4,X5) = X3 & r2_hidden(X5,X1) & r2_hidden(X4,X0))))),
% 3.35/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.35/1.00  
% 3.35/1.00  fof(f9,plain,(
% 3.35/1.00    ! [X0,X1,X2] : ((k2_zfmisc_1(X0,X1) = X2 | ? [X3] : ((! [X4,X5] : (k4_tarski(X4,X5) != X3 | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X0)) | ~r2_hidden(X3,X2)) & (? [X4,X5] : (k4_tarski(X4,X5) = X3 & r2_hidden(X5,X1) & r2_hidden(X4,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ! [X4,X5] : (k4_tarski(X4,X5) != X3 | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X0))) & (? [X4,X5] : (k4_tarski(X4,X5) = X3 & r2_hidden(X5,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X3,X2))) | k2_zfmisc_1(X0,X1) != X2))),
% 3.35/1.00    inference(nnf_transformation,[],[f3])).
% 3.35/1.00  
% 3.35/1.00  fof(f10,plain,(
% 3.35/1.00    ! [X0,X1,X2] : ((k2_zfmisc_1(X0,X1) = X2 | ? [X3] : ((! [X4,X5] : (k4_tarski(X4,X5) != X3 | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X0)) | ~r2_hidden(X3,X2)) & (? [X6,X7] : (k4_tarski(X6,X7) = X3 & r2_hidden(X7,X1) & r2_hidden(X6,X0)) | r2_hidden(X3,X2)))) & (! [X8] : ((r2_hidden(X8,X2) | ! [X9,X10] : (k4_tarski(X9,X10) != X8 | ~r2_hidden(X10,X1) | ~r2_hidden(X9,X0))) & (? [X11,X12] : (k4_tarski(X11,X12) = X8 & r2_hidden(X12,X1) & r2_hidden(X11,X0)) | ~r2_hidden(X8,X2))) | k2_zfmisc_1(X0,X1) != X2))),
% 3.35/1.00    inference(rectify,[],[f9])).
% 3.35/1.00  
% 3.35/1.00  fof(f13,plain,(
% 3.35/1.00    ! [X8,X1,X0] : (? [X11,X12] : (k4_tarski(X11,X12) = X8 & r2_hidden(X12,X1) & r2_hidden(X11,X0)) => (k4_tarski(sK3(X0,X1,X8),sK4(X0,X1,X8)) = X8 & r2_hidden(sK4(X0,X1,X8),X1) & r2_hidden(sK3(X0,X1,X8),X0)))),
% 3.35/1.00    introduced(choice_axiom,[])).
% 3.35/1.00  
% 3.35/1.00  fof(f12,plain,(
% 3.35/1.00    ( ! [X3] : (! [X2,X1,X0] : (? [X6,X7] : (k4_tarski(X6,X7) = X3 & r2_hidden(X7,X1) & r2_hidden(X6,X0)) => (k4_tarski(sK1(X0,X1,X2),sK2(X0,X1,X2)) = X3 & r2_hidden(sK2(X0,X1,X2),X1) & r2_hidden(sK1(X0,X1,X2),X0)))) )),
% 3.35/1.00    introduced(choice_axiom,[])).
% 3.35/1.00  
% 3.35/1.00  fof(f11,plain,(
% 3.35/1.00    ! [X2,X1,X0] : (? [X3] : ((! [X4,X5] : (k4_tarski(X4,X5) != X3 | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X0)) | ~r2_hidden(X3,X2)) & (? [X6,X7] : (k4_tarski(X6,X7) = X3 & r2_hidden(X7,X1) & r2_hidden(X6,X0)) | r2_hidden(X3,X2))) => ((! [X5,X4] : (k4_tarski(X4,X5) != sK0(X0,X1,X2) | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X0)) | ~r2_hidden(sK0(X0,X1,X2),X2)) & (? [X7,X6] : (k4_tarski(X6,X7) = sK0(X0,X1,X2) & r2_hidden(X7,X1) & r2_hidden(X6,X0)) | r2_hidden(sK0(X0,X1,X2),X2))))),
% 3.35/1.00    introduced(choice_axiom,[])).
% 3.35/1.00  
% 3.35/1.00  fof(f14,plain,(
% 3.35/1.00    ! [X0,X1,X2] : ((k2_zfmisc_1(X0,X1) = X2 | ((! [X4,X5] : (k4_tarski(X4,X5) != sK0(X0,X1,X2) | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X0)) | ~r2_hidden(sK0(X0,X1,X2),X2)) & ((k4_tarski(sK1(X0,X1,X2),sK2(X0,X1,X2)) = sK0(X0,X1,X2) & r2_hidden(sK2(X0,X1,X2),X1) & r2_hidden(sK1(X0,X1,X2),X0)) | r2_hidden(sK0(X0,X1,X2),X2)))) & (! [X8] : ((r2_hidden(X8,X2) | ! [X9,X10] : (k4_tarski(X9,X10) != X8 | ~r2_hidden(X10,X1) | ~r2_hidden(X9,X0))) & ((k4_tarski(sK3(X0,X1,X8),sK4(X0,X1,X8)) = X8 & r2_hidden(sK4(X0,X1,X8),X1) & r2_hidden(sK3(X0,X1,X8),X0)) | ~r2_hidden(X8,X2))) | k2_zfmisc_1(X0,X1) != X2))),
% 3.35/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f10,f13,f12,f11])).
% 3.35/1.00  
% 3.35/1.00  fof(f31,plain,(
% 3.35/1.00    ( ! [X2,X0,X10,X8,X1,X9] : (r2_hidden(X8,X2) | k4_tarski(X9,X10) != X8 | ~r2_hidden(X10,X1) | ~r2_hidden(X9,X0) | k2_zfmisc_1(X0,X1) != X2) )),
% 3.35/1.00    inference(cnf_transformation,[],[f14])).
% 3.35/1.00  
% 3.35/1.00  fof(f49,plain,(
% 3.35/1.00    ( ! [X2,X0,X10,X1,X9] : (r2_hidden(k4_tarski(X9,X10),X2) | ~r2_hidden(X10,X1) | ~r2_hidden(X9,X0) | k2_zfmisc_1(X0,X1) != X2) )),
% 3.35/1.00    inference(equality_resolution,[],[f31])).
% 3.35/1.00  
% 3.35/1.00  fof(f50,plain,(
% 3.35/1.00    ( ! [X0,X10,X1,X9] : (r2_hidden(k4_tarski(X9,X10),k2_zfmisc_1(X0,X1)) | ~r2_hidden(X10,X1) | ~r2_hidden(X9,X0)) )),
% 3.35/1.00    inference(equality_resolution,[],[f49])).
% 3.35/1.00  
% 3.35/1.00  fof(f45,plain,(
% 3.35/1.00    k1_xboole_0 != sK8 | k1_xboole_0 != k2_zfmisc_1(sK8,sK9)),
% 3.35/1.00    inference(cnf_transformation,[],[f25])).
% 3.35/1.00  
% 3.35/1.00  fof(f28,plain,(
% 3.35/1.00    ( ! [X2,X0,X8,X1] : (r2_hidden(sK3(X0,X1,X8),X0) | ~r2_hidden(X8,X2) | k2_zfmisc_1(X0,X1) != X2) )),
% 3.35/1.00    inference(cnf_transformation,[],[f14])).
% 3.35/1.00  
% 3.35/1.00  fof(f53,plain,(
% 3.35/1.00    ( ! [X0,X8,X1] : (r2_hidden(sK3(X0,X1,X8),X0) | ~r2_hidden(X8,k2_zfmisc_1(X0,X1))) )),
% 3.35/1.00    inference(equality_resolution,[],[f28])).
% 3.35/1.00  
% 3.35/1.00  fof(f46,plain,(
% 3.35/1.00    k1_xboole_0 != sK9 | k1_xboole_0 != k2_zfmisc_1(sK8,sK9)),
% 3.35/1.00    inference(cnf_transformation,[],[f25])).
% 3.35/1.00  
% 3.35/1.00  fof(f29,plain,(
% 3.35/1.00    ( ! [X2,X0,X8,X1] : (r2_hidden(sK4(X0,X1,X8),X1) | ~r2_hidden(X8,X2) | k2_zfmisc_1(X0,X1) != X2) )),
% 3.35/1.00    inference(cnf_transformation,[],[f14])).
% 3.35/1.00  
% 3.35/1.00  fof(f52,plain,(
% 3.35/1.00    ( ! [X0,X8,X1] : (r2_hidden(sK4(X0,X1,X8),X1) | ~r2_hidden(X8,k2_zfmisc_1(X0,X1))) )),
% 3.35/1.00    inference(equality_resolution,[],[f29])).
% 3.35/1.00  
% 3.35/1.00  cnf(c_10,plain,
% 3.35/1.00      ( r2_hidden(sK6(X0,X1),X0)
% 3.35/1.00      | r2_hidden(sK5(X0,X1),X1)
% 3.35/1.00      | k3_tarski(X0) = X1 ),
% 3.35/1.00      inference(cnf_transformation,[],[f40]) ).
% 3.35/1.00  
% 3.35/1.00  cnf(c_1839,plain,
% 3.35/1.00      ( k3_tarski(X0) = X1
% 3.35/1.00      | r2_hidden(sK6(X0,X1),X0) = iProver_top
% 3.35/1.00      | r2_hidden(sK5(X0,X1),X1) = iProver_top ),
% 3.35/1.00      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 3.35/1.00  
% 3.35/1.00  cnf(c_0,plain,
% 3.35/1.00      ( k4_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
% 3.35/1.00      inference(cnf_transformation,[],[f26]) ).
% 3.35/1.00  
% 3.35/1.00  cnf(c_16,negated_conjecture,
% 3.35/1.00      ( ~ r2_hidden(X0,X1) | k4_xboole_0(X1,k2_tarski(X0,X0)) != X1 ),
% 3.35/1.00      inference(cnf_transformation,[],[f48]) ).
% 3.35/1.00  
% 3.35/1.00  cnf(c_1833,plain,
% 3.35/1.00      ( k4_xboole_0(X0,k2_tarski(X1,X1)) != X0
% 3.35/1.00      | r2_hidden(X1,X0) != iProver_top ),
% 3.35/1.00      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 3.35/1.00  
% 3.35/1.00  cnf(c_2026,plain,
% 3.35/1.00      ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
% 3.35/1.00      inference(superposition,[status(thm)],[c_0,c_1833]) ).
% 3.35/1.00  
% 3.35/1.00  cnf(c_2134,plain,
% 3.35/1.00      ( k3_tarski(k1_xboole_0) = X0
% 3.35/1.00      | r2_hidden(sK5(k1_xboole_0,X0),X0) = iProver_top ),
% 3.35/1.00      inference(superposition,[status(thm)],[c_1839,c_2026]) ).
% 3.35/1.00  
% 3.35/1.00  cnf(c_2132,plain,
% 3.35/1.00      ( k3_tarski(X0) = k1_xboole_0
% 3.35/1.00      | r2_hidden(sK6(X0,k1_xboole_0),X0) = iProver_top ),
% 3.35/1.00      inference(superposition,[status(thm)],[c_1839,c_2026]) ).
% 3.35/1.00  
% 3.35/1.00  cnf(c_2312,plain,
% 3.35/1.00      ( k3_tarski(k1_xboole_0) = k1_xboole_0 ),
% 3.35/1.00      inference(superposition,[status(thm)],[c_2132,c_2026]) ).
% 3.35/1.00  
% 3.35/1.00  cnf(c_2346,plain,
% 3.35/1.00      ( k1_xboole_0 = X0 | r2_hidden(sK5(k1_xboole_0,X0),X0) = iProver_top ),
% 3.35/1.00      inference(demodulation,[status(thm)],[c_2134,c_2312]) ).
% 3.35/1.00  
% 3.35/1.00  cnf(c_19,negated_conjecture,
% 3.35/1.00      ( k1_xboole_0 = k2_zfmisc_1(sK8,sK9)
% 3.35/1.00      | k1_xboole_0 = sK8
% 3.35/1.00      | k1_xboole_0 = sK9 ),
% 3.35/1.00      inference(cnf_transformation,[],[f44]) ).
% 3.35/1.00  
% 3.35/1.00  cnf(c_5,plain,
% 3.35/1.00      ( ~ r2_hidden(X0,X1)
% 3.35/1.00      | ~ r2_hidden(X2,X3)
% 3.35/1.00      | r2_hidden(k4_tarski(X2,X0),k2_zfmisc_1(X3,X1)) ),
% 3.35/1.00      inference(cnf_transformation,[],[f50]) ).
% 3.35/1.00  
% 3.35/1.00  cnf(c_1844,plain,
% 3.35/1.00      ( r2_hidden(X0,X1) != iProver_top
% 3.35/1.00      | r2_hidden(X2,X3) != iProver_top
% 3.35/1.00      | r2_hidden(k4_tarski(X2,X0),k2_zfmisc_1(X3,X1)) = iProver_top ),
% 3.35/1.00      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 3.35/1.00  
% 3.35/1.00  cnf(c_2468,plain,
% 3.35/1.00      ( sK8 = k1_xboole_0
% 3.35/1.00      | sK9 = k1_xboole_0
% 3.35/1.00      | r2_hidden(X0,sK8) != iProver_top
% 3.35/1.00      | r2_hidden(X1,sK9) != iProver_top
% 3.35/1.00      | r2_hidden(k4_tarski(X0,X1),k1_xboole_0) = iProver_top ),
% 3.35/1.00      inference(superposition,[status(thm)],[c_19,c_1844]) ).
% 3.35/1.00  
% 3.35/1.00  cnf(c_2647,plain,
% 3.35/1.00      ( sK8 = k1_xboole_0
% 3.35/1.00      | sK9 = k1_xboole_0
% 3.35/1.00      | r2_hidden(X0,sK8) != iProver_top
% 3.35/1.00      | r2_hidden(X1,sK9) != iProver_top ),
% 3.35/1.00      inference(forward_subsumption_resolution,[status(thm)],[c_2468,c_2026]) ).
% 3.35/1.00  
% 3.35/1.00  cnf(c_2662,plain,
% 3.35/1.00      ( sK8 = k1_xboole_0
% 3.35/1.00      | sK9 = k1_xboole_0
% 3.35/1.00      | r2_hidden(X0,sK8) != iProver_top ),
% 3.35/1.00      inference(superposition,[status(thm)],[c_2346,c_2647]) ).
% 3.35/1.00  
% 3.35/1.00  cnf(c_2743,plain,
% 3.35/1.00      ( sK8 = k1_xboole_0 | sK9 = k1_xboole_0 ),
% 3.35/1.00      inference(superposition,[status(thm)],[c_2346,c_2662]) ).
% 3.35/1.00  
% 3.35/1.00  cnf(c_18,negated_conjecture,
% 3.35/1.00      ( k1_xboole_0 != k2_zfmisc_1(sK8,sK9) | k1_xboole_0 != sK8 ),
% 3.35/1.00      inference(cnf_transformation,[],[f45]) ).
% 3.35/1.00  
% 3.35/1.00  cnf(c_3138,plain,
% 3.35/1.00      ( k2_zfmisc_1(k1_xboole_0,sK9) != k1_xboole_0
% 3.35/1.00      | sK8 != k1_xboole_0
% 3.35/1.00      | sK9 = k1_xboole_0 ),
% 3.35/1.00      inference(superposition,[status(thm)],[c_2743,c_18]) ).
% 3.35/1.00  
% 3.35/1.00  cnf(c_3143,plain,
% 3.35/1.00      ( k2_zfmisc_1(k1_xboole_0,sK9) != k1_xboole_0 | sK9 = k1_xboole_0 ),
% 3.35/1.00      inference(forward_subsumption_resolution,[status(thm)],[c_3138,c_2743]) ).
% 3.35/1.00  
% 3.35/1.00  cnf(c_8,plain,
% 3.35/1.00      ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) | r2_hidden(sK3(X1,X2,X0),X1) ),
% 3.35/1.00      inference(cnf_transformation,[],[f53]) ).
% 3.35/1.00  
% 3.35/1.00  cnf(c_1841,plain,
% 3.35/1.00      ( r2_hidden(X0,k2_zfmisc_1(X1,X2)) != iProver_top
% 3.35/1.00      | r2_hidden(sK3(X1,X2,X0),X1) = iProver_top ),
% 3.35/1.00      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 3.35/1.00  
% 3.35/1.00  cnf(c_2097,plain,
% 3.35/1.00      ( r2_hidden(X0,k2_zfmisc_1(k1_xboole_0,X1)) != iProver_top ),
% 3.35/1.00      inference(superposition,[status(thm)],[c_1841,c_2026]) ).
% 3.35/1.00  
% 3.35/1.00  cnf(c_2352,plain,
% 3.35/1.00      ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
% 3.35/1.00      inference(superposition,[status(thm)],[c_2346,c_2097]) ).
% 3.35/1.00  
% 3.35/1.00  cnf(c_3144,plain,
% 3.35/1.00      ( sK9 = k1_xboole_0 | k1_xboole_0 != k1_xboole_0 ),
% 3.35/1.00      inference(demodulation,[status(thm)],[c_3143,c_2352]) ).
% 3.35/1.00  
% 3.35/1.00  cnf(c_3145,plain,
% 3.35/1.00      ( sK9 = k1_xboole_0 ),
% 3.35/1.00      inference(equality_resolution_simp,[status(thm)],[c_3144]) ).
% 3.35/1.00  
% 3.35/1.00  cnf(c_17,negated_conjecture,
% 3.35/1.00      ( k1_xboole_0 != k2_zfmisc_1(sK8,sK9) | k1_xboole_0 != sK9 ),
% 3.35/1.00      inference(cnf_transformation,[],[f46]) ).
% 3.35/1.00  
% 3.35/1.00  cnf(c_3156,plain,
% 3.35/1.00      ( k2_zfmisc_1(sK8,k1_xboole_0) != k1_xboole_0
% 3.35/1.00      | k1_xboole_0 != k1_xboole_0 ),
% 3.35/1.00      inference(demodulation,[status(thm)],[c_3145,c_17]) ).
% 3.35/1.00  
% 3.35/1.00  cnf(c_3157,plain,
% 3.35/1.00      ( k2_zfmisc_1(sK8,k1_xboole_0) != k1_xboole_0 ),
% 3.35/1.00      inference(equality_resolution_simp,[status(thm)],[c_3156]) ).
% 3.35/1.00  
% 3.35/1.00  cnf(c_7,plain,
% 3.35/1.00      ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) | r2_hidden(sK4(X1,X2,X0),X2) ),
% 3.35/1.00      inference(cnf_transformation,[],[f52]) ).
% 3.35/1.00  
% 3.35/1.00  cnf(c_1842,plain,
% 3.35/1.00      ( r2_hidden(X0,k2_zfmisc_1(X1,X2)) != iProver_top
% 3.35/1.00      | r2_hidden(sK4(X1,X2,X0),X2) = iProver_top ),
% 3.35/1.00      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 3.35/1.00  
% 3.35/1.00  cnf(c_2116,plain,
% 3.35/1.00      ( r2_hidden(X0,k2_zfmisc_1(X1,k1_xboole_0)) != iProver_top ),
% 3.35/1.00      inference(superposition,[status(thm)],[c_1842,c_2026]) ).
% 3.35/1.00  
% 3.35/1.00  cnf(c_2353,plain,
% 3.35/1.00      ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
% 3.35/1.00      inference(superposition,[status(thm)],[c_2346,c_2116]) ).
% 3.35/1.00  
% 3.35/1.00  cnf(c_3159,plain,
% 3.35/1.00      ( k1_xboole_0 != k1_xboole_0 ),
% 3.35/1.00      inference(demodulation,[status(thm)],[c_3157,c_2353]) ).
% 3.35/1.00  
% 3.35/1.00  cnf(c_3160,plain,
% 3.35/1.00      ( $false ),
% 3.35/1.00      inference(equality_resolution_simp,[status(thm)],[c_3159]) ).
% 3.35/1.00  
% 3.35/1.00  
% 3.35/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 3.35/1.00  
% 3.35/1.00  ------                               Statistics
% 3.35/1.00  
% 3.35/1.00  ------ Selected
% 3.35/1.00  
% 3.35/1.00  total_time:                             0.148
% 3.35/1.00  
%------------------------------------------------------------------------------
