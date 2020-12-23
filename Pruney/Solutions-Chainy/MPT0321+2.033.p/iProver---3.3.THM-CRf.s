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
% DateTime   : Thu Dec  3 11:37:43 EST 2020

% Result     : Theorem 36.00s
% Output     : CNFRefutation 36.00s
% Verified   : 
% Statistics : Number of formulae       :  176 (2362 expanded)
%              Number of clauses        :  120 ( 832 expanded)
%              Number of leaves         :   17 ( 474 expanded)
%              Depth                    :   29
%              Number of atoms          :  515 (8708 expanded)
%              Number of equality atoms :  281 (4445 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal clause size      :   14 (   2 average)
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

fof(f24,plain,(
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

fof(f25,plain,(
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
    inference(rectify,[],[f24])).

fof(f28,plain,(
    ! [X5,X0] :
      ( ? [X7] :
          ( r2_hidden(X7,X0)
          & r2_hidden(X5,X7) )
     => ( r2_hidden(sK3(X0,X5),X0)
        & r2_hidden(X5,sK3(X0,X5)) ) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( r2_hidden(X4,X0)
          & r2_hidden(X2,X4) )
     => ( r2_hidden(sK2(X0,X1),X0)
        & r2_hidden(X2,sK2(X0,X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,(
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
              | ~ r2_hidden(sK1(X0,X1),X3) )
          | ~ r2_hidden(sK1(X0,X1),X1) )
        & ( ? [X4] :
              ( r2_hidden(X4,X0)
              & r2_hidden(sK1(X0,X1),X4) )
          | r2_hidden(sK1(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( k3_tarski(X0) = X1
        | ( ( ! [X3] :
                ( ~ r2_hidden(X3,X0)
                | ~ r2_hidden(sK1(X0,X1),X3) )
            | ~ r2_hidden(sK1(X0,X1),X1) )
          & ( ( r2_hidden(sK2(X0,X1),X0)
              & r2_hidden(sK1(X0,X1),sK2(X0,X1)) )
            | r2_hidden(sK1(X0,X1),X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] :
                  ( ~ r2_hidden(X6,X0)
                  | ~ r2_hidden(X5,X6) ) )
            & ( ( r2_hidden(sK3(X0,X5),X0)
                & r2_hidden(X5,sK3(X0,X5)) )
              | ~ r2_hidden(X5,X1) ) )
        | k3_tarski(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f25,f28,f27,f26])).

fof(f44,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(sK3(X0,X5),X0)
      | ~ r2_hidden(X5,X1)
      | k3_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f29])).

fof(f66,plain,(
    ! [X0,X5] :
      ( r2_hidden(sK3(X0,X5),X0)
      | ~ r2_hidden(X5,k3_tarski(X0)) ) ),
    inference(equality_resolution,[],[f44])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f12])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f18])).

fof(f20,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK0(X0,X1),X1)
          & r2_hidden(sK0(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f19,f20])).

fof(f37,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK0(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f10,conjecture,(
    ! [X0,X1,X2,X3] :
      ( k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X2,X3)
     => ( ( X1 = X3
          & X0 = X2 )
        | k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f11,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X2,X3)
       => ( ( X1 = X3
            & X0 = X2 )
          | k1_xboole_0 = X1
          | k1_xboole_0 = X0 ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f16,plain,(
    ? [X0,X1,X2,X3] :
      ( ( X1 != X3
        | X0 != X2 )
      & k1_xboole_0 != X1
      & k1_xboole_0 != X0
      & k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X2,X3) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f17,plain,(
    ? [X0,X1,X2,X3] :
      ( ( X1 != X3
        | X0 != X2 )
      & k1_xboole_0 != X1
      & k1_xboole_0 != X0
      & k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X2,X3) ) ),
    inference(flattening,[],[f16])).

fof(f34,plain,
    ( ? [X0,X1,X2,X3] :
        ( ( X1 != X3
          | X0 != X2 )
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0
        & k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X2,X3) )
   => ( ( sK6 != sK8
        | sK5 != sK7 )
      & k1_xboole_0 != sK6
      & k1_xboole_0 != sK5
      & k2_zfmisc_1(sK5,sK6) = k2_zfmisc_1(sK7,sK8) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,
    ( ( sK6 != sK8
      | sK5 != sK7 )
    & k1_xboole_0 != sK6
    & k1_xboole_0 != sK5
    & k2_zfmisc_1(sK5,sK6) = k2_zfmisc_1(sK7,sK8) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6,sK7,sK8])],[f17,f34])).

fof(f59,plain,(
    k2_zfmisc_1(sK5,sK6) = k2_zfmisc_1(sK7,sK8) ),
    inference(cnf_transformation,[],[f35])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
    <=> ( r2_hidden(X1,X3)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
        | ~ r2_hidden(X1,X3)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X3)
          & r2_hidden(X0,X2) )
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f31,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
        | ~ r2_hidden(X1,X3)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X3)
          & r2_hidden(X0,X2) )
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ) ),
    inference(flattening,[],[f30])).

fof(f51,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
      | ~ r2_hidden(X1,X3)
      | ~ r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f50,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X1,X3)
      | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f9,axiom,(
    ! [X0,X1] :
      ~ ( ! [X2] :
            ~ ( ! [X3] :
                  ~ ( r2_hidden(X3,X2)
                    & r2_hidden(X3,X1) )
              & r2_hidden(X2,X1) )
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ! [X3] :
              ( ~ r2_hidden(X3,X2)
              | ~ r2_hidden(X3,X1) )
          & r2_hidden(X2,X1) )
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f32,plain,(
    ! [X1] :
      ( ? [X2] :
          ( ! [X3] :
              ( ~ r2_hidden(X3,X2)
              | ~ r2_hidden(X3,X1) )
          & r2_hidden(X2,X1) )
     => ( ! [X3] :
            ( ~ r2_hidden(X3,sK4(X1))
            | ~ r2_hidden(X3,X1) )
        & r2_hidden(sK4(X1),X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( ! [X3] :
            ( ~ r2_hidden(X3,sK4(X1))
            | ~ r2_hidden(X3,X1) )
        & r2_hidden(sK4(X1),X1) )
      | ~ r2_hidden(X0,X1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f15,f32])).

fof(f57,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK4(X1),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f61,plain,(
    k1_xboole_0 != sK6 ),
    inference(cnf_transformation,[],[f35])).

fof(f3,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f22])).

fof(f41,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => ( r1_tarski(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1))
        & r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1))
        & r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)) )
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ~ ( ~ r1_tarski(X1,X2)
        & ( r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X2))
          | r1_tarski(k2_zfmisc_1(X1,X0),k2_zfmisc_1(X2,X0)) )
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X1,X2)
      | ( ~ r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X2))
        & ~ r1_tarski(k2_zfmisc_1(X1,X0),k2_zfmisc_1(X2,X0)) )
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f6])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X1,X2)
      | ~ r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X2))
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f13])).

fof(f60,plain,(
    k1_xboole_0 != sK5 ),
    inference(cnf_transformation,[],[f35])).

fof(f36,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f49,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X0,X2)
      | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f38,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK0(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X1,X2)
      | ~ r1_tarski(k2_zfmisc_1(X1,X0),k2_zfmisc_1(X2,X0))
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f13])).

fof(f62,plain,
    ( sK6 != sK8
    | sK5 != sK7 ),
    inference(cnf_transformation,[],[f35])).

fof(f8,axiom,(
    k1_xboole_0 = k3_tarski(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f56,plain,(
    k1_xboole_0 = k3_tarski(k1_xboole_0) ),
    inference(cnf_transformation,[],[f8])).

fof(f58,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,sK4(X1))
      | ~ r2_hidden(X3,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_11,plain,
    ( ~ r2_hidden(X0,k3_tarski(X1))
    | r2_hidden(sK3(X1,X0),X1) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_763,plain,
    ( r2_hidden(X0,k3_tarski(X1)) != iProver_top
    | r2_hidden(sK3(X1,X0),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_1,plain,
    ( r2_hidden(sK0(X0,X1),X0)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_772,plain,
    ( r2_hidden(sK0(X0,X1),X0) = iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_26,negated_conjecture,
    ( k2_zfmisc_1(sK5,sK6) = k2_zfmisc_1(sK7,sK8) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_13,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X2,X3)
    | r2_hidden(k4_tarski(X2,X0),k2_zfmisc_1(X3,X1)) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_761,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X2,X3) != iProver_top
    | r2_hidden(k4_tarski(X2,X0),k2_zfmisc_1(X3,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_5591,plain,
    ( r2_hidden(X0,sK7) != iProver_top
    | r2_hidden(X1,sK8) != iProver_top
    | r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(sK5,sK6)) = iProver_top ),
    inference(superposition,[status(thm)],[c_26,c_761])).

cnf(c_14,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(k4_tarski(X2,X0),k2_zfmisc_1(X3,X1)) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_760,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r2_hidden(k4_tarski(X2,X0),k2_zfmisc_1(X3,X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_5972,plain,
    ( r2_hidden(X0,sK7) != iProver_top
    | r2_hidden(X1,sK8) != iProver_top
    | r2_hidden(X1,sK6) = iProver_top ),
    inference(superposition,[status(thm)],[c_5591,c_760])).

cnf(c_6670,plain,
    ( r2_hidden(X0,sK8) != iProver_top
    | r2_hidden(X0,sK6) = iProver_top
    | r1_tarski(sK7,X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_772,c_5972])).

cnf(c_15231,plain,
    ( r2_hidden(X0,k3_tarski(sK8)) != iProver_top
    | r2_hidden(sK3(sK8,X0),sK6) = iProver_top
    | r1_tarski(sK7,X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_763,c_6670])).

cnf(c_22,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(sK4(X1),X1) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_753,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(sK4(X1),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_94202,plain,
    ( r2_hidden(X0,k3_tarski(sK8)) != iProver_top
    | r2_hidden(sK4(sK6),sK6) = iProver_top
    | r1_tarski(sK7,X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_15231,c_753])).

cnf(c_24,negated_conjecture,
    ( k1_xboole_0 != sK6 ),
    inference(cnf_transformation,[],[f61])).

cnf(c_6,plain,
    ( r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_61,plain,
    ( r1_tarski(k1_xboole_0,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_3,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f41])).

cnf(c_66,plain,
    ( ~ r1_tarski(k1_xboole_0,k1_xboole_0)
    | k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_381,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_961,plain,
    ( sK6 != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = sK6 ),
    inference(instantiation,[status(thm)],[c_381])).

cnf(c_962,plain,
    ( sK6 != k1_xboole_0
    | k1_xboole_0 = sK6
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_961])).

cnf(c_1007,plain,
    ( r2_hidden(sK0(sK6,k1_xboole_0),sK6)
    | r1_tarski(sK6,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_1014,plain,
    ( r2_hidden(sK0(sK6,k1_xboole_0),sK6) = iProver_top
    | r1_tarski(sK6,k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1007])).

cnf(c_1035,plain,
    ( ~ r1_tarski(X0,sK6)
    | ~ r1_tarski(sK6,X0)
    | sK6 = X0 ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_1036,plain,
    ( sK6 = X0
    | r1_tarski(X0,sK6) != iProver_top
    | r1_tarski(sK6,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1035])).

cnf(c_1038,plain,
    ( sK6 = k1_xboole_0
    | r1_tarski(sK6,k1_xboole_0) != iProver_top
    | r1_tarski(k1_xboole_0,sK6) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1036])).

cnf(c_1111,plain,
    ( ~ r2_hidden(sK0(sK6,k1_xboole_0),sK6)
    | r2_hidden(sK4(sK6),sK6) ),
    inference(instantiation,[status(thm)],[c_22])).

cnf(c_1120,plain,
    ( r2_hidden(sK0(sK6,k1_xboole_0),sK6) != iProver_top
    | r2_hidden(sK4(sK6),sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1111])).

cnf(c_1249,plain,
    ( r1_tarski(k1_xboole_0,sK6) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_1252,plain,
    ( r1_tarski(k1_xboole_0,sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1249])).

cnf(c_96411,plain,
    ( r2_hidden(sK4(sK6),sK6) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_94202,c_24,c_61,c_66,c_962,c_1014,c_1038,c_1120,c_1252])).

cnf(c_1216,plain,
    ( r2_hidden(sK4(X0),X0) = iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_772,c_753])).

cnf(c_19,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_755,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_1198,plain,
    ( r1_tarski(X0,sK7) != iProver_top
    | r1_tarski(k2_zfmisc_1(X0,sK8),k2_zfmisc_1(sK5,sK6)) = iProver_top ),
    inference(superposition,[status(thm)],[c_26,c_755])).

cnf(c_16,plain,
    ( r1_tarski(X0,X1)
    | ~ r1_tarski(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1))
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f53])).

cnf(c_758,plain,
    ( k1_xboole_0 = X0
    | r1_tarski(X1,X2) = iProver_top
    | r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_3931,plain,
    ( sK5 = k1_xboole_0
    | r1_tarski(sK5,sK7) != iProver_top
    | r1_tarski(sK8,sK6) = iProver_top ),
    inference(superposition,[status(thm)],[c_1198,c_758])).

cnf(c_25,negated_conjecture,
    ( k1_xboole_0 != sK5 ),
    inference(cnf_transformation,[],[f60])).

cnf(c_963,plain,
    ( sK5 != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = sK5 ),
    inference(instantiation,[status(thm)],[c_381])).

cnf(c_964,plain,
    ( sK5 != k1_xboole_0
    | k1_xboole_0 = sK5
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_963])).

cnf(c_5097,plain,
    ( r1_tarski(sK5,sK7) != iProver_top
    | r1_tarski(sK8,sK6) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3931,c_25,c_61,c_66,c_964])).

cnf(c_7850,plain,
    ( r2_hidden(sK4(sK5),sK5) = iProver_top
    | r1_tarski(sK8,sK6) = iProver_top ),
    inference(superposition,[status(thm)],[c_1216,c_5097])).

cnf(c_1021,plain,
    ( r2_hidden(sK0(sK5,k1_xboole_0),sK5)
    | r1_tarski(sK5,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_1028,plain,
    ( r2_hidden(sK0(sK5,k1_xboole_0),sK5) = iProver_top
    | r1_tarski(sK5,k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1021])).

cnf(c_1046,plain,
    ( ~ r1_tarski(X0,sK5)
    | ~ r1_tarski(sK5,X0)
    | sK5 = X0 ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_1047,plain,
    ( sK5 = X0
    | r1_tarski(X0,sK5) != iProver_top
    | r1_tarski(sK5,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1046])).

cnf(c_1049,plain,
    ( sK5 = k1_xboole_0
    | r1_tarski(sK5,k1_xboole_0) != iProver_top
    | r1_tarski(k1_xboole_0,sK5) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1047])).

cnf(c_1159,plain,
    ( r1_tarski(k1_xboole_0,sK5) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_1160,plain,
    ( r1_tarski(k1_xboole_0,sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1159])).

cnf(c_1498,plain,
    ( ~ r2_hidden(sK0(sK5,k1_xboole_0),sK5)
    | r2_hidden(sK4(sK5),sK5) ),
    inference(instantiation,[status(thm)],[c_22])).

cnf(c_1507,plain,
    ( r2_hidden(sK0(sK5,k1_xboole_0),sK5) != iProver_top
    | r2_hidden(sK4(sK5),sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1498])).

cnf(c_59078,plain,
    ( r2_hidden(sK4(sK5),sK5) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_7850,c_25,c_61,c_66,c_964,c_1028,c_1049,c_1160,c_1507])).

cnf(c_1197,plain,
    ( r1_tarski(k2_zfmisc_1(sK5,sK6),k2_zfmisc_1(X0,sK8)) = iProver_top
    | r1_tarski(sK7,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_26,c_755])).

cnf(c_2,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | ~ r1_tarski(X1,X2) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_771,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,X2) = iProver_top
    | r1_tarski(X1,X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_5593,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X2,X3) != iProver_top
    | r2_hidden(k4_tarski(X2,X0),X4) = iProver_top
    | r1_tarski(k2_zfmisc_1(X3,X1),X4) != iProver_top ),
    inference(superposition,[status(thm)],[c_761,c_771])).

cnf(c_17231,plain,
    ( r2_hidden(X0,sK5) != iProver_top
    | r2_hidden(X1,sK6) != iProver_top
    | r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,sK8)) = iProver_top
    | r1_tarski(sK7,X2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1197,c_5593])).

cnf(c_18469,plain,
    ( r2_hidden(X0,sK5) != iProver_top
    | r2_hidden(X1,sK6) != iProver_top
    | r2_hidden(k4_tarski(X0,X1),X2) = iProver_top
    | r1_tarski(k2_zfmisc_1(X3,sK8),X2) != iProver_top
    | r1_tarski(sK7,X3) != iProver_top ),
    inference(superposition,[status(thm)],[c_17231,c_771])).

cnf(c_15,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(k4_tarski(X0,X2),k2_zfmisc_1(X1,X3)) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_759,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r2_hidden(k4_tarski(X0,X2),k2_zfmisc_1(X1,X3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_1940,plain,
    ( r2_hidden(X0,sK7) = iProver_top
    | r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(sK5,sK6)) != iProver_top ),
    inference(superposition,[status(thm)],[c_26,c_759])).

cnf(c_5597,plain,
    ( r2_hidden(X0,sK7) = iProver_top
    | r2_hidden(X0,sK5) != iProver_top
    | r2_hidden(X1,sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_761,c_1940])).

cnf(c_2163,plain,
    ( r2_hidden(X0,sK8) = iProver_top
    | r2_hidden(k4_tarski(X1,X0),k2_zfmisc_1(sK5,sK6)) != iProver_top ),
    inference(superposition,[status(thm)],[c_26,c_760])).

cnf(c_5598,plain,
    ( r2_hidden(X0,sK5) != iProver_top
    | r2_hidden(X1,sK8) = iProver_top
    | r2_hidden(X1,sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_761,c_2163])).

cnf(c_768,plain,
    ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_15228,plain,
    ( r2_hidden(sK0(sK8,X0),sK6) = iProver_top
    | r1_tarski(sK7,X1) = iProver_top
    | r1_tarski(sK8,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_772,c_6670])).

cnf(c_0,plain,
    ( ~ r2_hidden(sK0(X0,X1),X1)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_773,plain,
    ( r2_hidden(sK0(X0,X1),X1) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_21827,plain,
    ( r1_tarski(sK7,X0) = iProver_top
    | r1_tarski(sK8,sK6) = iProver_top ),
    inference(superposition,[status(thm)],[c_15228,c_773])).

cnf(c_18,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_756,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_1552,plain,
    ( r1_tarski(X0,sK8) != iProver_top
    | r1_tarski(k2_zfmisc_1(sK7,X0),k2_zfmisc_1(sK5,sK6)) = iProver_top ),
    inference(superposition,[status(thm)],[c_26,c_756])).

cnf(c_17,plain,
    ( r1_tarski(X0,X1)
    | ~ r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2))
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f52])).

cnf(c_757,plain,
    ( k1_xboole_0 = X0
    | r1_tarski(X1,X2) = iProver_top
    | r1_tarski(k2_zfmisc_1(X1,X0),k2_zfmisc_1(X2,X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_1952,plain,
    ( sK6 = k1_xboole_0
    | r1_tarski(sK7,sK5) = iProver_top
    | r1_tarski(sK6,sK8) != iProver_top ),
    inference(superposition,[status(thm)],[c_1552,c_757])).

cnf(c_770,plain,
    ( X0 = X1
    | r1_tarski(X1,X0) != iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_2334,plain,
    ( k2_zfmisc_1(X0,sK8) = k2_zfmisc_1(sK5,sK6)
    | r1_tarski(k2_zfmisc_1(X0,sK8),k2_zfmisc_1(sK5,sK6)) != iProver_top
    | r1_tarski(sK7,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1197,c_770])).

cnf(c_2997,plain,
    ( k2_zfmisc_1(sK5,sK8) = k2_zfmisc_1(sK5,sK6)
    | r1_tarski(sK7,sK5) != iProver_top
    | r1_tarski(sK8,sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_756,c_2334])).

cnf(c_23,negated_conjecture,
    ( sK5 != sK7
    | sK6 != sK8 ),
    inference(cnf_transformation,[],[f62])).

cnf(c_1331,plain,
    ( ~ r1_tarski(sK7,sK5)
    | ~ r1_tarski(sK5,sK7)
    | sK6 != sK8 ),
    inference(resolution,[status(thm)],[c_3,c_23])).

cnf(c_1406,plain,
    ( ~ r1_tarski(sK7,sK5)
    | ~ r1_tarski(sK5,sK7)
    | ~ r1_tarski(sK8,sK6)
    | ~ r1_tarski(sK6,sK8) ),
    inference(resolution,[status(thm)],[c_1331,c_3])).

cnf(c_1407,plain,
    ( r1_tarski(sK7,sK5) != iProver_top
    | r1_tarski(sK5,sK7) != iProver_top
    | r1_tarski(sK8,sK6) != iProver_top
    | r1_tarski(sK6,sK8) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1406])).

cnf(c_1551,plain,
    ( r1_tarski(k2_zfmisc_1(sK5,sK6),k2_zfmisc_1(sK7,X0)) = iProver_top
    | r1_tarski(sK8,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_26,c_756])).

cnf(c_1951,plain,
    ( sK6 = k1_xboole_0
    | r1_tarski(sK5,sK7) = iProver_top
    | r1_tarski(sK8,sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_1551,c_757])).

cnf(c_3930,plain,
    ( sK5 = k1_xboole_0
    | r1_tarski(sK7,sK5) != iProver_top
    | r1_tarski(sK6,sK8) = iProver_top ),
    inference(superposition,[status(thm)],[c_1197,c_758])).

cnf(c_5090,plain,
    ( r1_tarski(sK7,sK5) != iProver_top
    | r1_tarski(sK6,sK8) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3930,c_25,c_61,c_66,c_964])).

cnf(c_10451,plain,
    ( r1_tarski(sK7,sK5) != iProver_top
    | r1_tarski(sK8,sK6) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2997,c_25,c_24,c_61,c_66,c_962,c_964,c_1407,c_1951,c_3930])).

cnf(c_6622,plain,
    ( r2_hidden(X0,sK8) = iProver_top
    | r2_hidden(X0,sK6) != iProver_top
    | r1_tarski(sK5,X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_772,c_5598])).

cnf(c_12199,plain,
    ( r2_hidden(sK0(sK6,X0),sK8) = iProver_top
    | r1_tarski(sK5,X1) = iProver_top
    | r1_tarski(sK6,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_772,c_6622])).

cnf(c_18050,plain,
    ( r1_tarski(sK5,X0) = iProver_top
    | r1_tarski(sK6,sK8) = iProver_top ),
    inference(superposition,[status(thm)],[c_12199,c_773])).

cnf(c_18155,plain,
    ( r1_tarski(sK5,k1_xboole_0) = iProver_top
    | r1_tarski(sK6,sK8) = iProver_top ),
    inference(instantiation,[status(thm)],[c_18050])).

cnf(c_21988,plain,
    ( r1_tarski(sK7,X0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_21827,c_25,c_24,c_61,c_66,c_962,c_964,c_1049,c_1160,c_1407,c_1951,c_1952,c_18155])).

cnf(c_2998,plain,
    ( k2_zfmisc_1(X0,sK8) = k2_zfmisc_1(sK5,sK6)
    | r1_tarski(X0,sK7) != iProver_top
    | r1_tarski(sK7,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1198,c_2334])).

cnf(c_21997,plain,
    ( k2_zfmisc_1(X0,sK8) = k2_zfmisc_1(sK5,sK6)
    | r1_tarski(X0,sK7) != iProver_top ),
    inference(superposition,[status(thm)],[c_21988,c_2998])).

cnf(c_22520,plain,
    ( k2_zfmisc_1(k1_xboole_0,sK8) = k2_zfmisc_1(sK5,sK6) ),
    inference(superposition,[status(thm)],[c_768,c_21997])).

cnf(c_24448,plain,
    ( r2_hidden(X0,sK7) != iProver_top
    | r2_hidden(X1,sK8) != iProver_top
    | r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_xboole_0,sK8)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_22520,c_5591])).

cnf(c_25656,plain,
    ( r2_hidden(X0,sK7) != iProver_top
    | r2_hidden(X1,sK8) != iProver_top
    | r2_hidden(X0,k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_24448,c_759])).

cnf(c_24460,plain,
    ( r1_tarski(k2_zfmisc_1(k1_xboole_0,sK8),k2_zfmisc_1(X0,sK8)) = iProver_top
    | r1_tarski(sK7,X0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_22520,c_1197])).

cnf(c_25434,plain,
    ( r1_tarski(k2_zfmisc_1(k1_xboole_0,sK8),k2_zfmisc_1(X0,sK8)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_24460,c_25,c_24,c_61,c_66,c_962,c_964,c_1049,c_1160,c_1407,c_1951,c_1952,c_18155,c_21827])).

cnf(c_25448,plain,
    ( r2_hidden(X0,sK8) != iProver_top
    | r2_hidden(X1,k1_xboole_0) != iProver_top
    | r2_hidden(k4_tarski(X1,X0),k2_zfmisc_1(X2,sK8)) = iProver_top ),
    inference(superposition,[status(thm)],[c_25434,c_5593])).

cnf(c_27009,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r2_hidden(X2,sK8) != iProver_top
    | r2_hidden(X0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_25448,c_759])).

cnf(c_2179,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_2,c_6])).

cnf(c_2180,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r2_hidden(X0,k1_xboole_0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2179])).

cnf(c_44624,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r2_hidden(X0,k1_xboole_0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_27009,c_2180])).

cnf(c_44635,plain,
    ( r2_hidden(X0,k3_tarski(k1_xboole_0)) != iProver_top
    | r2_hidden(sK3(k1_xboole_0,X0),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_763,c_44624])).

cnf(c_20,plain,
    ( k3_tarski(k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f56])).

cnf(c_44704,plain,
    ( r2_hidden(X0,k1_xboole_0) != iProver_top
    | r2_hidden(sK3(k1_xboole_0,X0),X1) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_44635,c_20])).

cnf(c_21,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X2,X1)
    | ~ r2_hidden(X2,sK4(X1)) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_754,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X2,X1) != iProver_top
    | r2_hidden(X2,sK4(X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_44906,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X2,k1_xboole_0) != iProver_top
    | r2_hidden(sK3(k1_xboole_0,X2),X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_44704,c_754])).

cnf(c_45067,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X2,k1_xboole_0) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_44906,c_44704])).

cnf(c_45069,plain,
    ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
    inference(backward_subsumption_resolution,[status(thm)],[c_45067,c_44704])).

cnf(c_51422,plain,
    ( r2_hidden(X1,sK6) != iProver_top
    | r2_hidden(X0,sK5) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_18469,c_5597,c_5598,c_25656,c_45069])).

cnf(c_51423,plain,
    ( r2_hidden(X0,sK5) != iProver_top
    | r2_hidden(X1,sK6) != iProver_top ),
    inference(renaming,[status(thm)],[c_51422])).

cnf(c_59090,plain,
    ( r2_hidden(X0,sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_59078,c_51423])).

cnf(c_97872,plain,
    ( $false ),
    inference(superposition,[status(thm)],[c_96411,c_59090])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n012.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 11:57:37 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 36.00/5.02  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 36.00/5.02  
% 36.00/5.02  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 36.00/5.02  
% 36.00/5.02  ------  iProver source info
% 36.00/5.02  
% 36.00/5.02  git: date: 2020-06-30 10:37:57 +0100
% 36.00/5.02  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 36.00/5.02  git: non_committed_changes: false
% 36.00/5.02  git: last_make_outside_of_git: false
% 36.00/5.02  
% 36.00/5.02  ------ 
% 36.00/5.02  ------ Parsing...
% 36.00/5.02  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 36.00/5.02  
% 36.00/5.02  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e  sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 36.00/5.02  
% 36.00/5.02  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 36.00/5.02  
% 36.00/5.02  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 36.00/5.02  ------ Proving...
% 36.00/5.02  ------ Problem Properties 
% 36.00/5.02  
% 36.00/5.02  
% 36.00/5.02  clauses                                 26
% 36.00/5.02  conjectures                             4
% 36.00/5.02  EPR                                     7
% 36.00/5.02  Horn                                    21
% 36.00/5.02  unary                                   6
% 36.00/5.02  binary                                  10
% 36.00/5.02  lits                                    57
% 36.00/5.02  lits eq                                 12
% 36.00/5.02  fd_pure                                 0
% 36.00/5.02  fd_pseudo                               0
% 36.00/5.02  fd_cond                                 2
% 36.00/5.02  fd_pseudo_cond                          4
% 36.00/5.02  AC symbols                              0
% 36.00/5.02  
% 36.00/5.02  ------ Input Options Time Limit: Unbounded
% 36.00/5.02  
% 36.00/5.02  
% 36.00/5.02  ------ 
% 36.00/5.02  Current options:
% 36.00/5.02  ------ 
% 36.00/5.02  
% 36.00/5.02  
% 36.00/5.02  
% 36.00/5.02  
% 36.00/5.02  ------ Proving...
% 36.00/5.02  
% 36.00/5.02  
% 36.00/5.02  % SZS status Theorem for theBenchmark.p
% 36.00/5.02  
% 36.00/5.02   Resolution empty clause
% 36.00/5.02  
% 36.00/5.02  % SZS output start CNFRefutation for theBenchmark.p
% 36.00/5.02  
% 36.00/5.02  fof(f4,axiom,(
% 36.00/5.02    ! [X0,X1] : (k3_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (r2_hidden(X3,X0) & r2_hidden(X2,X3))))),
% 36.00/5.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 36.00/5.02  
% 36.00/5.02  fof(f24,plain,(
% 36.00/5.02    ! [X0,X1] : ((k3_tarski(X0) = X1 | ? [X2] : ((! [X3] : (~r2_hidden(X3,X0) | ~r2_hidden(X2,X3)) | ~r2_hidden(X2,X1)) & (? [X3] : (r2_hidden(X3,X0) & r2_hidden(X2,X3)) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ! [X3] : (~r2_hidden(X3,X0) | ~r2_hidden(X2,X3))) & (? [X3] : (r2_hidden(X3,X0) & r2_hidden(X2,X3)) | ~r2_hidden(X2,X1))) | k3_tarski(X0) != X1))),
% 36.00/5.02    inference(nnf_transformation,[],[f4])).
% 36.00/5.02  
% 36.00/5.02  fof(f25,plain,(
% 36.00/5.02    ! [X0,X1] : ((k3_tarski(X0) = X1 | ? [X2] : ((! [X3] : (~r2_hidden(X3,X0) | ~r2_hidden(X2,X3)) | ~r2_hidden(X2,X1)) & (? [X4] : (r2_hidden(X4,X0) & r2_hidden(X2,X4)) | r2_hidden(X2,X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : (~r2_hidden(X6,X0) | ~r2_hidden(X5,X6))) & (? [X7] : (r2_hidden(X7,X0) & r2_hidden(X5,X7)) | ~r2_hidden(X5,X1))) | k3_tarski(X0) != X1))),
% 36.00/5.02    inference(rectify,[],[f24])).
% 36.00/5.02  
% 36.00/5.02  fof(f28,plain,(
% 36.00/5.02    ! [X5,X0] : (? [X7] : (r2_hidden(X7,X0) & r2_hidden(X5,X7)) => (r2_hidden(sK3(X0,X5),X0) & r2_hidden(X5,sK3(X0,X5))))),
% 36.00/5.02    introduced(choice_axiom,[])).
% 36.00/5.02  
% 36.00/5.02  fof(f27,plain,(
% 36.00/5.02    ( ! [X2] : (! [X1,X0] : (? [X4] : (r2_hidden(X4,X0) & r2_hidden(X2,X4)) => (r2_hidden(sK2(X0,X1),X0) & r2_hidden(X2,sK2(X0,X1))))) )),
% 36.00/5.02    introduced(choice_axiom,[])).
% 36.00/5.02  
% 36.00/5.02  fof(f26,plain,(
% 36.00/5.02    ! [X1,X0] : (? [X2] : ((! [X3] : (~r2_hidden(X3,X0) | ~r2_hidden(X2,X3)) | ~r2_hidden(X2,X1)) & (? [X4] : (r2_hidden(X4,X0) & r2_hidden(X2,X4)) | r2_hidden(X2,X1))) => ((! [X3] : (~r2_hidden(X3,X0) | ~r2_hidden(sK1(X0,X1),X3)) | ~r2_hidden(sK1(X0,X1),X1)) & (? [X4] : (r2_hidden(X4,X0) & r2_hidden(sK1(X0,X1),X4)) | r2_hidden(sK1(X0,X1),X1))))),
% 36.00/5.02    introduced(choice_axiom,[])).
% 36.00/5.02  
% 36.00/5.02  fof(f29,plain,(
% 36.00/5.02    ! [X0,X1] : ((k3_tarski(X0) = X1 | ((! [X3] : (~r2_hidden(X3,X0) | ~r2_hidden(sK1(X0,X1),X3)) | ~r2_hidden(sK1(X0,X1),X1)) & ((r2_hidden(sK2(X0,X1),X0) & r2_hidden(sK1(X0,X1),sK2(X0,X1))) | r2_hidden(sK1(X0,X1),X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : (~r2_hidden(X6,X0) | ~r2_hidden(X5,X6))) & ((r2_hidden(sK3(X0,X5),X0) & r2_hidden(X5,sK3(X0,X5))) | ~r2_hidden(X5,X1))) | k3_tarski(X0) != X1))),
% 36.00/5.02    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f25,f28,f27,f26])).
% 36.00/5.02  
% 36.00/5.02  fof(f44,plain,(
% 36.00/5.02    ( ! [X0,X5,X1] : (r2_hidden(sK3(X0,X5),X0) | ~r2_hidden(X5,X1) | k3_tarski(X0) != X1) )),
% 36.00/5.02    inference(cnf_transformation,[],[f29])).
% 36.00/5.02  
% 36.00/5.02  fof(f66,plain,(
% 36.00/5.02    ( ! [X0,X5] : (r2_hidden(sK3(X0,X5),X0) | ~r2_hidden(X5,k3_tarski(X0))) )),
% 36.00/5.02    inference(equality_resolution,[],[f44])).
% 36.00/5.02  
% 36.00/5.02  fof(f1,axiom,(
% 36.00/5.02    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 36.00/5.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 36.00/5.02  
% 36.00/5.02  fof(f12,plain,(
% 36.00/5.02    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 36.00/5.02    inference(ennf_transformation,[],[f1])).
% 36.00/5.02  
% 36.00/5.02  fof(f18,plain,(
% 36.00/5.02    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 36.00/5.02    inference(nnf_transformation,[],[f12])).
% 36.00/5.02  
% 36.00/5.02  fof(f19,plain,(
% 36.00/5.02    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 36.00/5.02    inference(rectify,[],[f18])).
% 36.00/5.02  
% 36.00/5.02  fof(f20,plain,(
% 36.00/5.02    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 36.00/5.02    introduced(choice_axiom,[])).
% 36.00/5.02  
% 36.00/5.02  fof(f21,plain,(
% 36.00/5.02    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 36.00/5.02    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f19,f20])).
% 36.00/5.02  
% 36.00/5.02  fof(f37,plain,(
% 36.00/5.02    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK0(X0,X1),X0)) )),
% 36.00/5.02    inference(cnf_transformation,[],[f21])).
% 36.00/5.02  
% 36.00/5.02  fof(f10,conjecture,(
% 36.00/5.02    ! [X0,X1,X2,X3] : (k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X2,X3) => ((X1 = X3 & X0 = X2) | k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 36.00/5.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 36.00/5.02  
% 36.00/5.02  fof(f11,negated_conjecture,(
% 36.00/5.02    ~! [X0,X1,X2,X3] : (k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X2,X3) => ((X1 = X3 & X0 = X2) | k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 36.00/5.02    inference(negated_conjecture,[],[f10])).
% 36.00/5.02  
% 36.00/5.02  fof(f16,plain,(
% 36.00/5.02    ? [X0,X1,X2,X3] : (((X1 != X3 | X0 != X2) & k1_xboole_0 != X1 & k1_xboole_0 != X0) & k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X2,X3))),
% 36.00/5.02    inference(ennf_transformation,[],[f11])).
% 36.00/5.02  
% 36.00/5.02  fof(f17,plain,(
% 36.00/5.02    ? [X0,X1,X2,X3] : ((X1 != X3 | X0 != X2) & k1_xboole_0 != X1 & k1_xboole_0 != X0 & k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X2,X3))),
% 36.00/5.02    inference(flattening,[],[f16])).
% 36.00/5.02  
% 36.00/5.02  fof(f34,plain,(
% 36.00/5.02    ? [X0,X1,X2,X3] : ((X1 != X3 | X0 != X2) & k1_xboole_0 != X1 & k1_xboole_0 != X0 & k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X2,X3)) => ((sK6 != sK8 | sK5 != sK7) & k1_xboole_0 != sK6 & k1_xboole_0 != sK5 & k2_zfmisc_1(sK5,sK6) = k2_zfmisc_1(sK7,sK8))),
% 36.00/5.02    introduced(choice_axiom,[])).
% 36.00/5.02  
% 36.00/5.02  fof(f35,plain,(
% 36.00/5.02    (sK6 != sK8 | sK5 != sK7) & k1_xboole_0 != sK6 & k1_xboole_0 != sK5 & k2_zfmisc_1(sK5,sK6) = k2_zfmisc_1(sK7,sK8)),
% 36.00/5.02    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6,sK7,sK8])],[f17,f34])).
% 36.00/5.02  
% 36.00/5.02  fof(f59,plain,(
% 36.00/5.02    k2_zfmisc_1(sK5,sK6) = k2_zfmisc_1(sK7,sK8)),
% 36.00/5.02    inference(cnf_transformation,[],[f35])).
% 36.00/5.02  
% 36.00/5.02  fof(f5,axiom,(
% 36.00/5.02    ! [X0,X1,X2,X3] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) <=> (r2_hidden(X1,X3) & r2_hidden(X0,X2)))),
% 36.00/5.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 36.00/5.02  
% 36.00/5.02  fof(f30,plain,(
% 36.00/5.02    ! [X0,X1,X2,X3] : ((r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | (~r2_hidden(X1,X3) | ~r2_hidden(X0,X2))) & ((r2_hidden(X1,X3) & r2_hidden(X0,X2)) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))))),
% 36.00/5.02    inference(nnf_transformation,[],[f5])).
% 36.00/5.02  
% 36.00/5.02  fof(f31,plain,(
% 36.00/5.02    ! [X0,X1,X2,X3] : ((r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | ~r2_hidden(X1,X3) | ~r2_hidden(X0,X2)) & ((r2_hidden(X1,X3) & r2_hidden(X0,X2)) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))))),
% 36.00/5.02    inference(flattening,[],[f30])).
% 36.00/5.02  
% 36.00/5.02  fof(f51,plain,(
% 36.00/5.02    ( ! [X2,X0,X3,X1] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | ~r2_hidden(X1,X3) | ~r2_hidden(X0,X2)) )),
% 36.00/5.02    inference(cnf_transformation,[],[f31])).
% 36.00/5.02  
% 36.00/5.02  fof(f50,plain,(
% 36.00/5.02    ( ! [X2,X0,X3,X1] : (r2_hidden(X1,X3) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))) )),
% 36.00/5.02    inference(cnf_transformation,[],[f31])).
% 36.00/5.02  
% 36.00/5.02  fof(f9,axiom,(
% 36.00/5.02    ! [X0,X1] : ~(! [X2] : ~(! [X3] : ~(r2_hidden(X3,X2) & r2_hidden(X3,X1)) & r2_hidden(X2,X1)) & r2_hidden(X0,X1))),
% 36.00/5.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 36.00/5.02  
% 36.00/5.02  fof(f15,plain,(
% 36.00/5.02    ! [X0,X1] : (? [X2] : (! [X3] : (~r2_hidden(X3,X2) | ~r2_hidden(X3,X1)) & r2_hidden(X2,X1)) | ~r2_hidden(X0,X1))),
% 36.00/5.02    inference(ennf_transformation,[],[f9])).
% 36.00/5.02  
% 36.00/5.02  fof(f32,plain,(
% 36.00/5.02    ! [X1] : (? [X2] : (! [X3] : (~r2_hidden(X3,X2) | ~r2_hidden(X3,X1)) & r2_hidden(X2,X1)) => (! [X3] : (~r2_hidden(X3,sK4(X1)) | ~r2_hidden(X3,X1)) & r2_hidden(sK4(X1),X1)))),
% 36.00/5.02    introduced(choice_axiom,[])).
% 36.00/5.02  
% 36.00/5.02  fof(f33,plain,(
% 36.00/5.02    ! [X0,X1] : ((! [X3] : (~r2_hidden(X3,sK4(X1)) | ~r2_hidden(X3,X1)) & r2_hidden(sK4(X1),X1)) | ~r2_hidden(X0,X1))),
% 36.00/5.02    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f15,f32])).
% 36.00/5.02  
% 36.00/5.02  fof(f57,plain,(
% 36.00/5.02    ( ! [X0,X1] : (r2_hidden(sK4(X1),X1) | ~r2_hidden(X0,X1)) )),
% 36.00/5.02    inference(cnf_transformation,[],[f33])).
% 36.00/5.02  
% 36.00/5.02  fof(f61,plain,(
% 36.00/5.02    k1_xboole_0 != sK6),
% 36.00/5.02    inference(cnf_transformation,[],[f35])).
% 36.00/5.02  
% 36.00/5.02  fof(f3,axiom,(
% 36.00/5.02    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 36.00/5.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 36.00/5.02  
% 36.00/5.02  fof(f42,plain,(
% 36.00/5.02    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 36.00/5.02    inference(cnf_transformation,[],[f3])).
% 36.00/5.02  
% 36.00/5.02  fof(f2,axiom,(
% 36.00/5.02    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 36.00/5.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 36.00/5.02  
% 36.00/5.02  fof(f22,plain,(
% 36.00/5.02    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 36.00/5.02    inference(nnf_transformation,[],[f2])).
% 36.00/5.02  
% 36.00/5.02  fof(f23,plain,(
% 36.00/5.02    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 36.00/5.02    inference(flattening,[],[f22])).
% 36.00/5.02  
% 36.00/5.02  fof(f41,plain,(
% 36.00/5.02    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 36.00/5.02    inference(cnf_transformation,[],[f23])).
% 36.00/5.02  
% 36.00/5.02  fof(f7,axiom,(
% 36.00/5.02    ! [X0,X1,X2] : (r1_tarski(X0,X1) => (r1_tarski(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)) & r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2))))),
% 36.00/5.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 36.00/5.02  
% 36.00/5.02  fof(f14,plain,(
% 36.00/5.02    ! [X0,X1,X2] : ((r1_tarski(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)) & r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2))) | ~r1_tarski(X0,X1))),
% 36.00/5.02    inference(ennf_transformation,[],[f7])).
% 36.00/5.02  
% 36.00/5.02  fof(f54,plain,(
% 36.00/5.02    ( ! [X2,X0,X1] : (r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)) | ~r1_tarski(X0,X1)) )),
% 36.00/5.02    inference(cnf_transformation,[],[f14])).
% 36.00/5.02  
% 36.00/5.02  fof(f6,axiom,(
% 36.00/5.02    ! [X0,X1,X2] : ~(~r1_tarski(X1,X2) & (r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X2)) | r1_tarski(k2_zfmisc_1(X1,X0),k2_zfmisc_1(X2,X0))) & k1_xboole_0 != X0)),
% 36.00/5.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 36.00/5.02  
% 36.00/5.02  fof(f13,plain,(
% 36.00/5.02    ! [X0,X1,X2] : (r1_tarski(X1,X2) | (~r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X2)) & ~r1_tarski(k2_zfmisc_1(X1,X0),k2_zfmisc_1(X2,X0))) | k1_xboole_0 = X0)),
% 36.00/5.02    inference(ennf_transformation,[],[f6])).
% 36.00/5.02  
% 36.00/5.02  fof(f53,plain,(
% 36.00/5.02    ( ! [X2,X0,X1] : (r1_tarski(X1,X2) | ~r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X2)) | k1_xboole_0 = X0) )),
% 36.00/5.02    inference(cnf_transformation,[],[f13])).
% 36.00/5.02  
% 36.00/5.02  fof(f60,plain,(
% 36.00/5.02    k1_xboole_0 != sK5),
% 36.00/5.02    inference(cnf_transformation,[],[f35])).
% 36.00/5.02  
% 36.00/5.02  fof(f36,plain,(
% 36.00/5.02    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,X1)) )),
% 36.00/5.02    inference(cnf_transformation,[],[f21])).
% 36.00/5.02  
% 36.00/5.02  fof(f49,plain,(
% 36.00/5.02    ( ! [X2,X0,X3,X1] : (r2_hidden(X0,X2) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))) )),
% 36.00/5.02    inference(cnf_transformation,[],[f31])).
% 36.00/5.02  
% 36.00/5.02  fof(f38,plain,(
% 36.00/5.02    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r2_hidden(sK0(X0,X1),X1)) )),
% 36.00/5.02    inference(cnf_transformation,[],[f21])).
% 36.00/5.02  
% 36.00/5.02  fof(f55,plain,(
% 36.00/5.02    ( ! [X2,X0,X1] : (r1_tarski(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)) | ~r1_tarski(X0,X1)) )),
% 36.00/5.02    inference(cnf_transformation,[],[f14])).
% 36.00/5.02  
% 36.00/5.02  fof(f52,plain,(
% 36.00/5.02    ( ! [X2,X0,X1] : (r1_tarski(X1,X2) | ~r1_tarski(k2_zfmisc_1(X1,X0),k2_zfmisc_1(X2,X0)) | k1_xboole_0 = X0) )),
% 36.00/5.02    inference(cnf_transformation,[],[f13])).
% 36.00/5.02  
% 36.00/5.02  fof(f62,plain,(
% 36.00/5.02    sK6 != sK8 | sK5 != sK7),
% 36.00/5.02    inference(cnf_transformation,[],[f35])).
% 36.00/5.02  
% 36.00/5.02  fof(f8,axiom,(
% 36.00/5.02    k1_xboole_0 = k3_tarski(k1_xboole_0)),
% 36.00/5.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 36.00/5.02  
% 36.00/5.02  fof(f56,plain,(
% 36.00/5.02    k1_xboole_0 = k3_tarski(k1_xboole_0)),
% 36.00/5.02    inference(cnf_transformation,[],[f8])).
% 36.00/5.02  
% 36.00/5.02  fof(f58,plain,(
% 36.00/5.02    ( ! [X0,X3,X1] : (~r2_hidden(X3,sK4(X1)) | ~r2_hidden(X3,X1) | ~r2_hidden(X0,X1)) )),
% 36.00/5.02    inference(cnf_transformation,[],[f33])).
% 36.00/5.02  
% 36.00/5.02  cnf(c_11,plain,
% 36.00/5.02      ( ~ r2_hidden(X0,k3_tarski(X1)) | r2_hidden(sK3(X1,X0),X1) ),
% 36.00/5.02      inference(cnf_transformation,[],[f66]) ).
% 36.00/5.02  
% 36.00/5.02  cnf(c_763,plain,
% 36.00/5.02      ( r2_hidden(X0,k3_tarski(X1)) != iProver_top
% 36.00/5.02      | r2_hidden(sK3(X1,X0),X1) = iProver_top ),
% 36.00/5.02      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 36.00/5.02  
% 36.00/5.02  cnf(c_1,plain,
% 36.00/5.02      ( r2_hidden(sK0(X0,X1),X0) | r1_tarski(X0,X1) ),
% 36.00/5.02      inference(cnf_transformation,[],[f37]) ).
% 36.00/5.02  
% 36.00/5.02  cnf(c_772,plain,
% 36.00/5.02      ( r2_hidden(sK0(X0,X1),X0) = iProver_top
% 36.00/5.02      | r1_tarski(X0,X1) = iProver_top ),
% 36.00/5.02      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 36.00/5.02  
% 36.00/5.02  cnf(c_26,negated_conjecture,
% 36.00/5.02      ( k2_zfmisc_1(sK5,sK6) = k2_zfmisc_1(sK7,sK8) ),
% 36.00/5.02      inference(cnf_transformation,[],[f59]) ).
% 36.00/5.02  
% 36.00/5.02  cnf(c_13,plain,
% 36.00/5.02      ( ~ r2_hidden(X0,X1)
% 36.00/5.02      | ~ r2_hidden(X2,X3)
% 36.00/5.02      | r2_hidden(k4_tarski(X2,X0),k2_zfmisc_1(X3,X1)) ),
% 36.00/5.02      inference(cnf_transformation,[],[f51]) ).
% 36.00/5.02  
% 36.00/5.02  cnf(c_761,plain,
% 36.00/5.02      ( r2_hidden(X0,X1) != iProver_top
% 36.00/5.02      | r2_hidden(X2,X3) != iProver_top
% 36.00/5.02      | r2_hidden(k4_tarski(X2,X0),k2_zfmisc_1(X3,X1)) = iProver_top ),
% 36.00/5.02      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 36.00/5.02  
% 36.00/5.02  cnf(c_5591,plain,
% 36.00/5.02      ( r2_hidden(X0,sK7) != iProver_top
% 36.00/5.02      | r2_hidden(X1,sK8) != iProver_top
% 36.00/5.02      | r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(sK5,sK6)) = iProver_top ),
% 36.00/5.02      inference(superposition,[status(thm)],[c_26,c_761]) ).
% 36.00/5.02  
% 36.00/5.02  cnf(c_14,plain,
% 36.00/5.02      ( r2_hidden(X0,X1) | ~ r2_hidden(k4_tarski(X2,X0),k2_zfmisc_1(X3,X1)) ),
% 36.00/5.02      inference(cnf_transformation,[],[f50]) ).
% 36.00/5.02  
% 36.00/5.02  cnf(c_760,plain,
% 36.00/5.02      ( r2_hidden(X0,X1) = iProver_top
% 36.00/5.02      | r2_hidden(k4_tarski(X2,X0),k2_zfmisc_1(X3,X1)) != iProver_top ),
% 36.00/5.02      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 36.00/5.02  
% 36.00/5.02  cnf(c_5972,plain,
% 36.00/5.02      ( r2_hidden(X0,sK7) != iProver_top
% 36.00/5.02      | r2_hidden(X1,sK8) != iProver_top
% 36.00/5.02      | r2_hidden(X1,sK6) = iProver_top ),
% 36.00/5.02      inference(superposition,[status(thm)],[c_5591,c_760]) ).
% 36.00/5.02  
% 36.00/5.02  cnf(c_6670,plain,
% 36.00/5.02      ( r2_hidden(X0,sK8) != iProver_top
% 36.00/5.02      | r2_hidden(X0,sK6) = iProver_top
% 36.00/5.02      | r1_tarski(sK7,X1) = iProver_top ),
% 36.00/5.02      inference(superposition,[status(thm)],[c_772,c_5972]) ).
% 36.00/5.02  
% 36.00/5.02  cnf(c_15231,plain,
% 36.00/5.02      ( r2_hidden(X0,k3_tarski(sK8)) != iProver_top
% 36.00/5.02      | r2_hidden(sK3(sK8,X0),sK6) = iProver_top
% 36.00/5.02      | r1_tarski(sK7,X1) = iProver_top ),
% 36.00/5.02      inference(superposition,[status(thm)],[c_763,c_6670]) ).
% 36.00/5.02  
% 36.00/5.02  cnf(c_22,plain,
% 36.00/5.02      ( ~ r2_hidden(X0,X1) | r2_hidden(sK4(X1),X1) ),
% 36.00/5.02      inference(cnf_transformation,[],[f57]) ).
% 36.00/5.02  
% 36.00/5.02  cnf(c_753,plain,
% 36.00/5.02      ( r2_hidden(X0,X1) != iProver_top | r2_hidden(sK4(X1),X1) = iProver_top ),
% 36.00/5.02      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 36.00/5.02  
% 36.00/5.02  cnf(c_94202,plain,
% 36.00/5.02      ( r2_hidden(X0,k3_tarski(sK8)) != iProver_top
% 36.00/5.02      | r2_hidden(sK4(sK6),sK6) = iProver_top
% 36.00/5.02      | r1_tarski(sK7,X1) = iProver_top ),
% 36.00/5.02      inference(superposition,[status(thm)],[c_15231,c_753]) ).
% 36.00/5.02  
% 36.00/5.02  cnf(c_24,negated_conjecture,
% 36.00/5.02      ( k1_xboole_0 != sK6 ),
% 36.00/5.02      inference(cnf_transformation,[],[f61]) ).
% 36.00/5.02  
% 36.00/5.02  cnf(c_6,plain,
% 36.00/5.02      ( r1_tarski(k1_xboole_0,X0) ),
% 36.00/5.02      inference(cnf_transformation,[],[f42]) ).
% 36.00/5.02  
% 36.00/5.02  cnf(c_61,plain,
% 36.00/5.02      ( r1_tarski(k1_xboole_0,k1_xboole_0) ),
% 36.00/5.02      inference(instantiation,[status(thm)],[c_6]) ).
% 36.00/5.02  
% 36.00/5.02  cnf(c_3,plain,
% 36.00/5.02      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X1 = X0 ),
% 36.00/5.02      inference(cnf_transformation,[],[f41]) ).
% 36.00/5.02  
% 36.00/5.02  cnf(c_66,plain,
% 36.00/5.02      ( ~ r1_tarski(k1_xboole_0,k1_xboole_0) | k1_xboole_0 = k1_xboole_0 ),
% 36.00/5.02      inference(instantiation,[status(thm)],[c_3]) ).
% 36.00/5.02  
% 36.00/5.02  cnf(c_381,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 36.00/5.02  
% 36.00/5.02  cnf(c_961,plain,
% 36.00/5.02      ( sK6 != X0 | k1_xboole_0 != X0 | k1_xboole_0 = sK6 ),
% 36.00/5.02      inference(instantiation,[status(thm)],[c_381]) ).
% 36.00/5.02  
% 36.00/5.02  cnf(c_962,plain,
% 36.00/5.02      ( sK6 != k1_xboole_0 | k1_xboole_0 = sK6 | k1_xboole_0 != k1_xboole_0 ),
% 36.00/5.02      inference(instantiation,[status(thm)],[c_961]) ).
% 36.00/5.02  
% 36.00/5.02  cnf(c_1007,plain,
% 36.00/5.02      ( r2_hidden(sK0(sK6,k1_xboole_0),sK6) | r1_tarski(sK6,k1_xboole_0) ),
% 36.00/5.02      inference(instantiation,[status(thm)],[c_1]) ).
% 36.00/5.02  
% 36.00/5.02  cnf(c_1014,plain,
% 36.00/5.02      ( r2_hidden(sK0(sK6,k1_xboole_0),sK6) = iProver_top
% 36.00/5.02      | r1_tarski(sK6,k1_xboole_0) = iProver_top ),
% 36.00/5.02      inference(predicate_to_equality,[status(thm)],[c_1007]) ).
% 36.00/5.02  
% 36.00/5.02  cnf(c_1035,plain,
% 36.00/5.02      ( ~ r1_tarski(X0,sK6) | ~ r1_tarski(sK6,X0) | sK6 = X0 ),
% 36.00/5.02      inference(instantiation,[status(thm)],[c_3]) ).
% 36.00/5.02  
% 36.00/5.02  cnf(c_1036,plain,
% 36.00/5.02      ( sK6 = X0
% 36.00/5.02      | r1_tarski(X0,sK6) != iProver_top
% 36.00/5.02      | r1_tarski(sK6,X0) != iProver_top ),
% 36.00/5.02      inference(predicate_to_equality,[status(thm)],[c_1035]) ).
% 36.00/5.02  
% 36.00/5.02  cnf(c_1038,plain,
% 36.00/5.02      ( sK6 = k1_xboole_0
% 36.00/5.02      | r1_tarski(sK6,k1_xboole_0) != iProver_top
% 36.00/5.02      | r1_tarski(k1_xboole_0,sK6) != iProver_top ),
% 36.00/5.02      inference(instantiation,[status(thm)],[c_1036]) ).
% 36.00/5.02  
% 36.00/5.02  cnf(c_1111,plain,
% 36.00/5.02      ( ~ r2_hidden(sK0(sK6,k1_xboole_0),sK6) | r2_hidden(sK4(sK6),sK6) ),
% 36.00/5.02      inference(instantiation,[status(thm)],[c_22]) ).
% 36.00/5.02  
% 36.00/5.02  cnf(c_1120,plain,
% 36.00/5.02      ( r2_hidden(sK0(sK6,k1_xboole_0),sK6) != iProver_top
% 36.00/5.02      | r2_hidden(sK4(sK6),sK6) = iProver_top ),
% 36.00/5.02      inference(predicate_to_equality,[status(thm)],[c_1111]) ).
% 36.00/5.02  
% 36.00/5.02  cnf(c_1249,plain,
% 36.00/5.02      ( r1_tarski(k1_xboole_0,sK6) ),
% 36.00/5.02      inference(instantiation,[status(thm)],[c_6]) ).
% 36.00/5.02  
% 36.00/5.02  cnf(c_1252,plain,
% 36.00/5.02      ( r1_tarski(k1_xboole_0,sK6) = iProver_top ),
% 36.00/5.02      inference(predicate_to_equality,[status(thm)],[c_1249]) ).
% 36.00/5.02  
% 36.00/5.02  cnf(c_96411,plain,
% 36.00/5.02      ( r2_hidden(sK4(sK6),sK6) = iProver_top ),
% 36.00/5.02      inference(global_propositional_subsumption,
% 36.00/5.02                [status(thm)],
% 36.00/5.02                [c_94202,c_24,c_61,c_66,c_962,c_1014,c_1038,c_1120,c_1252]) ).
% 36.00/5.02  
% 36.00/5.02  cnf(c_1216,plain,
% 36.00/5.02      ( r2_hidden(sK4(X0),X0) = iProver_top | r1_tarski(X0,X1) = iProver_top ),
% 36.00/5.02      inference(superposition,[status(thm)],[c_772,c_753]) ).
% 36.00/5.02  
% 36.00/5.02  cnf(c_19,plain,
% 36.00/5.02      ( ~ r1_tarski(X0,X1) | r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)) ),
% 36.00/5.02      inference(cnf_transformation,[],[f54]) ).
% 36.00/5.02  
% 36.00/5.02  cnf(c_755,plain,
% 36.00/5.02      ( r1_tarski(X0,X1) != iProver_top
% 36.00/5.02      | r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)) = iProver_top ),
% 36.00/5.02      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 36.00/5.02  
% 36.00/5.02  cnf(c_1198,plain,
% 36.00/5.02      ( r1_tarski(X0,sK7) != iProver_top
% 36.00/5.02      | r1_tarski(k2_zfmisc_1(X0,sK8),k2_zfmisc_1(sK5,sK6)) = iProver_top ),
% 36.00/5.02      inference(superposition,[status(thm)],[c_26,c_755]) ).
% 36.00/5.02  
% 36.00/5.02  cnf(c_16,plain,
% 36.00/5.02      ( r1_tarski(X0,X1)
% 36.00/5.02      | ~ r1_tarski(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1))
% 36.00/5.02      | k1_xboole_0 = X2 ),
% 36.00/5.02      inference(cnf_transformation,[],[f53]) ).
% 36.00/5.02  
% 36.00/5.02  cnf(c_758,plain,
% 36.00/5.02      ( k1_xboole_0 = X0
% 36.00/5.02      | r1_tarski(X1,X2) = iProver_top
% 36.00/5.02      | r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X2)) != iProver_top ),
% 36.00/5.02      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 36.00/5.02  
% 36.00/5.02  cnf(c_3931,plain,
% 36.00/5.02      ( sK5 = k1_xboole_0
% 36.00/5.02      | r1_tarski(sK5,sK7) != iProver_top
% 36.00/5.02      | r1_tarski(sK8,sK6) = iProver_top ),
% 36.00/5.02      inference(superposition,[status(thm)],[c_1198,c_758]) ).
% 36.00/5.02  
% 36.00/5.02  cnf(c_25,negated_conjecture,
% 36.00/5.02      ( k1_xboole_0 != sK5 ),
% 36.00/5.02      inference(cnf_transformation,[],[f60]) ).
% 36.00/5.02  
% 36.00/5.02  cnf(c_963,plain,
% 36.00/5.02      ( sK5 != X0 | k1_xboole_0 != X0 | k1_xboole_0 = sK5 ),
% 36.00/5.02      inference(instantiation,[status(thm)],[c_381]) ).
% 36.00/5.02  
% 36.00/5.02  cnf(c_964,plain,
% 36.00/5.02      ( sK5 != k1_xboole_0 | k1_xboole_0 = sK5 | k1_xboole_0 != k1_xboole_0 ),
% 36.00/5.02      inference(instantiation,[status(thm)],[c_963]) ).
% 36.00/5.02  
% 36.00/5.02  cnf(c_5097,plain,
% 36.00/5.02      ( r1_tarski(sK5,sK7) != iProver_top | r1_tarski(sK8,sK6) = iProver_top ),
% 36.00/5.02      inference(global_propositional_subsumption,
% 36.00/5.02                [status(thm)],
% 36.00/5.02                [c_3931,c_25,c_61,c_66,c_964]) ).
% 36.00/5.02  
% 36.00/5.02  cnf(c_7850,plain,
% 36.00/5.02      ( r2_hidden(sK4(sK5),sK5) = iProver_top
% 36.00/5.02      | r1_tarski(sK8,sK6) = iProver_top ),
% 36.00/5.02      inference(superposition,[status(thm)],[c_1216,c_5097]) ).
% 36.00/5.02  
% 36.00/5.02  cnf(c_1021,plain,
% 36.00/5.02      ( r2_hidden(sK0(sK5,k1_xboole_0),sK5) | r1_tarski(sK5,k1_xboole_0) ),
% 36.00/5.02      inference(instantiation,[status(thm)],[c_1]) ).
% 36.00/5.02  
% 36.00/5.02  cnf(c_1028,plain,
% 36.00/5.02      ( r2_hidden(sK0(sK5,k1_xboole_0),sK5) = iProver_top
% 36.00/5.02      | r1_tarski(sK5,k1_xboole_0) = iProver_top ),
% 36.00/5.02      inference(predicate_to_equality,[status(thm)],[c_1021]) ).
% 36.00/5.02  
% 36.00/5.02  cnf(c_1046,plain,
% 36.00/5.02      ( ~ r1_tarski(X0,sK5) | ~ r1_tarski(sK5,X0) | sK5 = X0 ),
% 36.00/5.02      inference(instantiation,[status(thm)],[c_3]) ).
% 36.00/5.02  
% 36.00/5.02  cnf(c_1047,plain,
% 36.00/5.02      ( sK5 = X0
% 36.00/5.02      | r1_tarski(X0,sK5) != iProver_top
% 36.00/5.02      | r1_tarski(sK5,X0) != iProver_top ),
% 36.00/5.02      inference(predicate_to_equality,[status(thm)],[c_1046]) ).
% 36.00/5.02  
% 36.00/5.02  cnf(c_1049,plain,
% 36.00/5.02      ( sK5 = k1_xboole_0
% 36.00/5.02      | r1_tarski(sK5,k1_xboole_0) != iProver_top
% 36.00/5.02      | r1_tarski(k1_xboole_0,sK5) != iProver_top ),
% 36.00/5.02      inference(instantiation,[status(thm)],[c_1047]) ).
% 36.00/5.02  
% 36.00/5.02  cnf(c_1159,plain,
% 36.00/5.02      ( r1_tarski(k1_xboole_0,sK5) ),
% 36.00/5.02      inference(instantiation,[status(thm)],[c_6]) ).
% 36.00/5.02  
% 36.00/5.02  cnf(c_1160,plain,
% 36.00/5.02      ( r1_tarski(k1_xboole_0,sK5) = iProver_top ),
% 36.00/5.02      inference(predicate_to_equality,[status(thm)],[c_1159]) ).
% 36.00/5.02  
% 36.00/5.02  cnf(c_1498,plain,
% 36.00/5.02      ( ~ r2_hidden(sK0(sK5,k1_xboole_0),sK5) | r2_hidden(sK4(sK5),sK5) ),
% 36.00/5.02      inference(instantiation,[status(thm)],[c_22]) ).
% 36.00/5.02  
% 36.00/5.02  cnf(c_1507,plain,
% 36.00/5.02      ( r2_hidden(sK0(sK5,k1_xboole_0),sK5) != iProver_top
% 36.00/5.02      | r2_hidden(sK4(sK5),sK5) = iProver_top ),
% 36.00/5.02      inference(predicate_to_equality,[status(thm)],[c_1498]) ).
% 36.00/5.02  
% 36.00/5.02  cnf(c_59078,plain,
% 36.00/5.02      ( r2_hidden(sK4(sK5),sK5) = iProver_top ),
% 36.00/5.02      inference(global_propositional_subsumption,
% 36.00/5.02                [status(thm)],
% 36.00/5.02                [c_7850,c_25,c_61,c_66,c_964,c_1028,c_1049,c_1160,c_1507]) ).
% 36.00/5.02  
% 36.00/5.02  cnf(c_1197,plain,
% 36.00/5.02      ( r1_tarski(k2_zfmisc_1(sK5,sK6),k2_zfmisc_1(X0,sK8)) = iProver_top
% 36.00/5.02      | r1_tarski(sK7,X0) != iProver_top ),
% 36.00/5.02      inference(superposition,[status(thm)],[c_26,c_755]) ).
% 36.00/5.02  
% 36.00/5.02  cnf(c_2,plain,
% 36.00/5.02      ( ~ r2_hidden(X0,X1) | r2_hidden(X0,X2) | ~ r1_tarski(X1,X2) ),
% 36.00/5.02      inference(cnf_transformation,[],[f36]) ).
% 36.00/5.02  
% 36.00/5.02  cnf(c_771,plain,
% 36.00/5.02      ( r2_hidden(X0,X1) != iProver_top
% 36.00/5.02      | r2_hidden(X0,X2) = iProver_top
% 36.00/5.02      | r1_tarski(X1,X2) != iProver_top ),
% 36.00/5.02      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 36.00/5.02  
% 36.00/5.02  cnf(c_5593,plain,
% 36.00/5.02      ( r2_hidden(X0,X1) != iProver_top
% 36.00/5.02      | r2_hidden(X2,X3) != iProver_top
% 36.00/5.02      | r2_hidden(k4_tarski(X2,X0),X4) = iProver_top
% 36.00/5.02      | r1_tarski(k2_zfmisc_1(X3,X1),X4) != iProver_top ),
% 36.00/5.02      inference(superposition,[status(thm)],[c_761,c_771]) ).
% 36.00/5.02  
% 36.00/5.02  cnf(c_17231,plain,
% 36.00/5.02      ( r2_hidden(X0,sK5) != iProver_top
% 36.00/5.02      | r2_hidden(X1,sK6) != iProver_top
% 36.00/5.02      | r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,sK8)) = iProver_top
% 36.00/5.02      | r1_tarski(sK7,X2) != iProver_top ),
% 36.00/5.02      inference(superposition,[status(thm)],[c_1197,c_5593]) ).
% 36.00/5.02  
% 36.00/5.02  cnf(c_18469,plain,
% 36.00/5.02      ( r2_hidden(X0,sK5) != iProver_top
% 36.00/5.02      | r2_hidden(X1,sK6) != iProver_top
% 36.00/5.02      | r2_hidden(k4_tarski(X0,X1),X2) = iProver_top
% 36.00/5.02      | r1_tarski(k2_zfmisc_1(X3,sK8),X2) != iProver_top
% 36.00/5.02      | r1_tarski(sK7,X3) != iProver_top ),
% 36.00/5.02      inference(superposition,[status(thm)],[c_17231,c_771]) ).
% 36.00/5.02  
% 36.00/5.02  cnf(c_15,plain,
% 36.00/5.02      ( r2_hidden(X0,X1) | ~ r2_hidden(k4_tarski(X0,X2),k2_zfmisc_1(X1,X3)) ),
% 36.00/5.02      inference(cnf_transformation,[],[f49]) ).
% 36.00/5.02  
% 36.00/5.02  cnf(c_759,plain,
% 36.00/5.02      ( r2_hidden(X0,X1) = iProver_top
% 36.00/5.02      | r2_hidden(k4_tarski(X0,X2),k2_zfmisc_1(X1,X3)) != iProver_top ),
% 36.00/5.02      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 36.00/5.02  
% 36.00/5.02  cnf(c_1940,plain,
% 36.00/5.02      ( r2_hidden(X0,sK7) = iProver_top
% 36.00/5.02      | r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(sK5,sK6)) != iProver_top ),
% 36.00/5.02      inference(superposition,[status(thm)],[c_26,c_759]) ).
% 36.00/5.02  
% 36.00/5.02  cnf(c_5597,plain,
% 36.00/5.02      ( r2_hidden(X0,sK7) = iProver_top
% 36.00/5.02      | r2_hidden(X0,sK5) != iProver_top
% 36.00/5.02      | r2_hidden(X1,sK6) != iProver_top ),
% 36.00/5.02      inference(superposition,[status(thm)],[c_761,c_1940]) ).
% 36.00/5.02  
% 36.00/5.02  cnf(c_2163,plain,
% 36.00/5.02      ( r2_hidden(X0,sK8) = iProver_top
% 36.00/5.02      | r2_hidden(k4_tarski(X1,X0),k2_zfmisc_1(sK5,sK6)) != iProver_top ),
% 36.00/5.02      inference(superposition,[status(thm)],[c_26,c_760]) ).
% 36.00/5.02  
% 36.00/5.02  cnf(c_5598,plain,
% 36.00/5.02      ( r2_hidden(X0,sK5) != iProver_top
% 36.00/5.02      | r2_hidden(X1,sK8) = iProver_top
% 36.00/5.02      | r2_hidden(X1,sK6) != iProver_top ),
% 36.00/5.02      inference(superposition,[status(thm)],[c_761,c_2163]) ).
% 36.00/5.02  
% 36.00/5.02  cnf(c_768,plain,
% 36.00/5.02      ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
% 36.00/5.02      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 36.00/5.02  
% 36.00/5.02  cnf(c_15228,plain,
% 36.00/5.02      ( r2_hidden(sK0(sK8,X0),sK6) = iProver_top
% 36.00/5.02      | r1_tarski(sK7,X1) = iProver_top
% 36.00/5.02      | r1_tarski(sK8,X0) = iProver_top ),
% 36.00/5.02      inference(superposition,[status(thm)],[c_772,c_6670]) ).
% 36.00/5.02  
% 36.00/5.02  cnf(c_0,plain,
% 36.00/5.02      ( ~ r2_hidden(sK0(X0,X1),X1) | r1_tarski(X0,X1) ),
% 36.00/5.02      inference(cnf_transformation,[],[f38]) ).
% 36.00/5.02  
% 36.00/5.02  cnf(c_773,plain,
% 36.00/5.02      ( r2_hidden(sK0(X0,X1),X1) != iProver_top
% 36.00/5.02      | r1_tarski(X0,X1) = iProver_top ),
% 36.00/5.02      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 36.00/5.02  
% 36.00/5.02  cnf(c_21827,plain,
% 36.00/5.02      ( r1_tarski(sK7,X0) = iProver_top | r1_tarski(sK8,sK6) = iProver_top ),
% 36.00/5.02      inference(superposition,[status(thm)],[c_15228,c_773]) ).
% 36.00/5.02  
% 36.00/5.02  cnf(c_18,plain,
% 36.00/5.02      ( ~ r1_tarski(X0,X1) | r1_tarski(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)) ),
% 36.00/5.02      inference(cnf_transformation,[],[f55]) ).
% 36.00/5.02  
% 36.00/5.02  cnf(c_756,plain,
% 36.00/5.02      ( r1_tarski(X0,X1) != iProver_top
% 36.00/5.02      | r1_tarski(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)) = iProver_top ),
% 36.00/5.02      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 36.00/5.02  
% 36.00/5.02  cnf(c_1552,plain,
% 36.00/5.02      ( r1_tarski(X0,sK8) != iProver_top
% 36.00/5.02      | r1_tarski(k2_zfmisc_1(sK7,X0),k2_zfmisc_1(sK5,sK6)) = iProver_top ),
% 36.00/5.02      inference(superposition,[status(thm)],[c_26,c_756]) ).
% 36.00/5.02  
% 36.00/5.02  cnf(c_17,plain,
% 36.00/5.02      ( r1_tarski(X0,X1)
% 36.00/5.02      | ~ r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2))
% 36.00/5.02      | k1_xboole_0 = X2 ),
% 36.00/5.02      inference(cnf_transformation,[],[f52]) ).
% 36.00/5.02  
% 36.00/5.02  cnf(c_757,plain,
% 36.00/5.02      ( k1_xboole_0 = X0
% 36.00/5.02      | r1_tarski(X1,X2) = iProver_top
% 36.00/5.02      | r1_tarski(k2_zfmisc_1(X1,X0),k2_zfmisc_1(X2,X0)) != iProver_top ),
% 36.00/5.02      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 36.00/5.02  
% 36.00/5.02  cnf(c_1952,plain,
% 36.00/5.02      ( sK6 = k1_xboole_0
% 36.00/5.02      | r1_tarski(sK7,sK5) = iProver_top
% 36.00/5.02      | r1_tarski(sK6,sK8) != iProver_top ),
% 36.00/5.02      inference(superposition,[status(thm)],[c_1552,c_757]) ).
% 36.00/5.02  
% 36.00/5.02  cnf(c_770,plain,
% 36.00/5.02      ( X0 = X1
% 36.00/5.02      | r1_tarski(X1,X0) != iProver_top
% 36.00/5.02      | r1_tarski(X0,X1) != iProver_top ),
% 36.00/5.02      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 36.00/5.02  
% 36.00/5.02  cnf(c_2334,plain,
% 36.00/5.02      ( k2_zfmisc_1(X0,sK8) = k2_zfmisc_1(sK5,sK6)
% 36.00/5.02      | r1_tarski(k2_zfmisc_1(X0,sK8),k2_zfmisc_1(sK5,sK6)) != iProver_top
% 36.00/5.02      | r1_tarski(sK7,X0) != iProver_top ),
% 36.00/5.02      inference(superposition,[status(thm)],[c_1197,c_770]) ).
% 36.00/5.02  
% 36.00/5.02  cnf(c_2997,plain,
% 36.00/5.02      ( k2_zfmisc_1(sK5,sK8) = k2_zfmisc_1(sK5,sK6)
% 36.00/5.02      | r1_tarski(sK7,sK5) != iProver_top
% 36.00/5.02      | r1_tarski(sK8,sK6) != iProver_top ),
% 36.00/5.02      inference(superposition,[status(thm)],[c_756,c_2334]) ).
% 36.00/5.02  
% 36.00/5.02  cnf(c_23,negated_conjecture,
% 36.00/5.02      ( sK5 != sK7 | sK6 != sK8 ),
% 36.00/5.02      inference(cnf_transformation,[],[f62]) ).
% 36.00/5.02  
% 36.00/5.02  cnf(c_1331,plain,
% 36.00/5.02      ( ~ r1_tarski(sK7,sK5) | ~ r1_tarski(sK5,sK7) | sK6 != sK8 ),
% 36.00/5.02      inference(resolution,[status(thm)],[c_3,c_23]) ).
% 36.00/5.02  
% 36.00/5.02  cnf(c_1406,plain,
% 36.00/5.02      ( ~ r1_tarski(sK7,sK5)
% 36.00/5.02      | ~ r1_tarski(sK5,sK7)
% 36.00/5.02      | ~ r1_tarski(sK8,sK6)
% 36.00/5.02      | ~ r1_tarski(sK6,sK8) ),
% 36.00/5.02      inference(resolution,[status(thm)],[c_1331,c_3]) ).
% 36.00/5.02  
% 36.00/5.02  cnf(c_1407,plain,
% 36.00/5.02      ( r1_tarski(sK7,sK5) != iProver_top
% 36.00/5.02      | r1_tarski(sK5,sK7) != iProver_top
% 36.00/5.02      | r1_tarski(sK8,sK6) != iProver_top
% 36.00/5.02      | r1_tarski(sK6,sK8) != iProver_top ),
% 36.00/5.02      inference(predicate_to_equality,[status(thm)],[c_1406]) ).
% 36.00/5.02  
% 36.00/5.02  cnf(c_1551,plain,
% 36.00/5.02      ( r1_tarski(k2_zfmisc_1(sK5,sK6),k2_zfmisc_1(sK7,X0)) = iProver_top
% 36.00/5.02      | r1_tarski(sK8,X0) != iProver_top ),
% 36.00/5.02      inference(superposition,[status(thm)],[c_26,c_756]) ).
% 36.00/5.02  
% 36.00/5.02  cnf(c_1951,plain,
% 36.00/5.02      ( sK6 = k1_xboole_0
% 36.00/5.02      | r1_tarski(sK5,sK7) = iProver_top
% 36.00/5.02      | r1_tarski(sK8,sK6) != iProver_top ),
% 36.00/5.02      inference(superposition,[status(thm)],[c_1551,c_757]) ).
% 36.00/5.02  
% 36.00/5.02  cnf(c_3930,plain,
% 36.00/5.02      ( sK5 = k1_xboole_0
% 36.00/5.02      | r1_tarski(sK7,sK5) != iProver_top
% 36.00/5.02      | r1_tarski(sK6,sK8) = iProver_top ),
% 36.00/5.02      inference(superposition,[status(thm)],[c_1197,c_758]) ).
% 36.00/5.02  
% 36.00/5.02  cnf(c_5090,plain,
% 36.00/5.02      ( r1_tarski(sK7,sK5) != iProver_top | r1_tarski(sK6,sK8) = iProver_top ),
% 36.00/5.02      inference(global_propositional_subsumption,
% 36.00/5.02                [status(thm)],
% 36.00/5.02                [c_3930,c_25,c_61,c_66,c_964]) ).
% 36.00/5.02  
% 36.00/5.02  cnf(c_10451,plain,
% 36.00/5.02      ( r1_tarski(sK7,sK5) != iProver_top | r1_tarski(sK8,sK6) != iProver_top ),
% 36.00/5.02      inference(global_propositional_subsumption,
% 36.00/5.02                [status(thm)],
% 36.00/5.02                [c_2997,c_25,c_24,c_61,c_66,c_962,c_964,c_1407,c_1951,c_3930]) ).
% 36.00/5.02  
% 36.00/5.02  cnf(c_6622,plain,
% 36.00/5.02      ( r2_hidden(X0,sK8) = iProver_top
% 36.00/5.02      | r2_hidden(X0,sK6) != iProver_top
% 36.00/5.02      | r1_tarski(sK5,X1) = iProver_top ),
% 36.00/5.02      inference(superposition,[status(thm)],[c_772,c_5598]) ).
% 36.00/5.02  
% 36.00/5.02  cnf(c_12199,plain,
% 36.00/5.02      ( r2_hidden(sK0(sK6,X0),sK8) = iProver_top
% 36.00/5.02      | r1_tarski(sK5,X1) = iProver_top
% 36.00/5.02      | r1_tarski(sK6,X0) = iProver_top ),
% 36.00/5.02      inference(superposition,[status(thm)],[c_772,c_6622]) ).
% 36.00/5.02  
% 36.00/5.02  cnf(c_18050,plain,
% 36.00/5.02      ( r1_tarski(sK5,X0) = iProver_top | r1_tarski(sK6,sK8) = iProver_top ),
% 36.00/5.02      inference(superposition,[status(thm)],[c_12199,c_773]) ).
% 36.00/5.02  
% 36.00/5.02  cnf(c_18155,plain,
% 36.00/5.02      ( r1_tarski(sK5,k1_xboole_0) = iProver_top
% 36.00/5.02      | r1_tarski(sK6,sK8) = iProver_top ),
% 36.00/5.02      inference(instantiation,[status(thm)],[c_18050]) ).
% 36.00/5.02  
% 36.00/5.02  cnf(c_21988,plain,
% 36.00/5.02      ( r1_tarski(sK7,X0) = iProver_top ),
% 36.00/5.02      inference(global_propositional_subsumption,
% 36.00/5.02                [status(thm)],
% 36.00/5.02                [c_21827,c_25,c_24,c_61,c_66,c_962,c_964,c_1049,c_1160,
% 36.00/5.02                 c_1407,c_1951,c_1952,c_18155]) ).
% 36.00/5.02  
% 36.00/5.02  cnf(c_2998,plain,
% 36.00/5.02      ( k2_zfmisc_1(X0,sK8) = k2_zfmisc_1(sK5,sK6)
% 36.00/5.02      | r1_tarski(X0,sK7) != iProver_top
% 36.00/5.02      | r1_tarski(sK7,X0) != iProver_top ),
% 36.00/5.02      inference(superposition,[status(thm)],[c_1198,c_2334]) ).
% 36.00/5.02  
% 36.00/5.02  cnf(c_21997,plain,
% 36.00/5.02      ( k2_zfmisc_1(X0,sK8) = k2_zfmisc_1(sK5,sK6)
% 36.00/5.02      | r1_tarski(X0,sK7) != iProver_top ),
% 36.00/5.02      inference(superposition,[status(thm)],[c_21988,c_2998]) ).
% 36.00/5.02  
% 36.00/5.02  cnf(c_22520,plain,
% 36.00/5.02      ( k2_zfmisc_1(k1_xboole_0,sK8) = k2_zfmisc_1(sK5,sK6) ),
% 36.00/5.02      inference(superposition,[status(thm)],[c_768,c_21997]) ).
% 36.00/5.02  
% 36.00/5.02  cnf(c_24448,plain,
% 36.00/5.02      ( r2_hidden(X0,sK7) != iProver_top
% 36.00/5.02      | r2_hidden(X1,sK8) != iProver_top
% 36.00/5.02      | r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_xboole_0,sK8)) = iProver_top ),
% 36.00/5.02      inference(demodulation,[status(thm)],[c_22520,c_5591]) ).
% 36.00/5.02  
% 36.00/5.02  cnf(c_25656,plain,
% 36.00/5.02      ( r2_hidden(X0,sK7) != iProver_top
% 36.00/5.02      | r2_hidden(X1,sK8) != iProver_top
% 36.00/5.02      | r2_hidden(X0,k1_xboole_0) = iProver_top ),
% 36.00/5.02      inference(superposition,[status(thm)],[c_24448,c_759]) ).
% 36.00/5.02  
% 36.00/5.02  cnf(c_24460,plain,
% 36.00/5.02      ( r1_tarski(k2_zfmisc_1(k1_xboole_0,sK8),k2_zfmisc_1(X0,sK8)) = iProver_top
% 36.00/5.02      | r1_tarski(sK7,X0) != iProver_top ),
% 36.00/5.02      inference(demodulation,[status(thm)],[c_22520,c_1197]) ).
% 36.00/5.02  
% 36.00/5.02  cnf(c_25434,plain,
% 36.00/5.02      ( r1_tarski(k2_zfmisc_1(k1_xboole_0,sK8),k2_zfmisc_1(X0,sK8)) = iProver_top ),
% 36.00/5.02      inference(global_propositional_subsumption,
% 36.00/5.02                [status(thm)],
% 36.00/5.02                [c_24460,c_25,c_24,c_61,c_66,c_962,c_964,c_1049,c_1160,
% 36.00/5.02                 c_1407,c_1951,c_1952,c_18155,c_21827]) ).
% 36.00/5.02  
% 36.00/5.02  cnf(c_25448,plain,
% 36.00/5.02      ( r2_hidden(X0,sK8) != iProver_top
% 36.00/5.02      | r2_hidden(X1,k1_xboole_0) != iProver_top
% 36.00/5.02      | r2_hidden(k4_tarski(X1,X0),k2_zfmisc_1(X2,sK8)) = iProver_top ),
% 36.00/5.02      inference(superposition,[status(thm)],[c_25434,c_5593]) ).
% 36.00/5.02  
% 36.00/5.02  cnf(c_27009,plain,
% 36.00/5.02      ( r2_hidden(X0,X1) = iProver_top
% 36.00/5.02      | r2_hidden(X2,sK8) != iProver_top
% 36.00/5.02      | r2_hidden(X0,k1_xboole_0) != iProver_top ),
% 36.00/5.02      inference(superposition,[status(thm)],[c_25448,c_759]) ).
% 36.00/5.02  
% 36.00/5.02  cnf(c_2179,plain,
% 36.00/5.02      ( r2_hidden(X0,X1) | ~ r2_hidden(X0,k1_xboole_0) ),
% 36.00/5.02      inference(resolution,[status(thm)],[c_2,c_6]) ).
% 36.00/5.02  
% 36.00/5.02  cnf(c_2180,plain,
% 36.00/5.02      ( r2_hidden(X0,X1) = iProver_top
% 36.00/5.02      | r2_hidden(X0,k1_xboole_0) != iProver_top ),
% 36.00/5.02      inference(predicate_to_equality,[status(thm)],[c_2179]) ).
% 36.00/5.02  
% 36.00/5.02  cnf(c_44624,plain,
% 36.00/5.02      ( r2_hidden(X0,X1) = iProver_top
% 36.00/5.02      | r2_hidden(X0,k1_xboole_0) != iProver_top ),
% 36.00/5.02      inference(global_propositional_subsumption,
% 36.00/5.02                [status(thm)],
% 36.00/5.02                [c_27009,c_2180]) ).
% 36.00/5.02  
% 36.00/5.02  cnf(c_44635,plain,
% 36.00/5.02      ( r2_hidden(X0,k3_tarski(k1_xboole_0)) != iProver_top
% 36.00/5.02      | r2_hidden(sK3(k1_xboole_0,X0),X1) = iProver_top ),
% 36.00/5.02      inference(superposition,[status(thm)],[c_763,c_44624]) ).
% 36.00/5.02  
% 36.00/5.02  cnf(c_20,plain,
% 36.00/5.02      ( k3_tarski(k1_xboole_0) = k1_xboole_0 ),
% 36.00/5.02      inference(cnf_transformation,[],[f56]) ).
% 36.00/5.02  
% 36.00/5.02  cnf(c_44704,plain,
% 36.00/5.02      ( r2_hidden(X0,k1_xboole_0) != iProver_top
% 36.00/5.02      | r2_hidden(sK3(k1_xboole_0,X0),X1) = iProver_top ),
% 36.00/5.02      inference(light_normalisation,[status(thm)],[c_44635,c_20]) ).
% 36.00/5.02  
% 36.00/5.02  cnf(c_21,plain,
% 36.00/5.02      ( ~ r2_hidden(X0,X1) | ~ r2_hidden(X2,X1) | ~ r2_hidden(X2,sK4(X1)) ),
% 36.00/5.02      inference(cnf_transformation,[],[f58]) ).
% 36.00/5.02  
% 36.00/5.02  cnf(c_754,plain,
% 36.00/5.02      ( r2_hidden(X0,X1) != iProver_top
% 36.00/5.02      | r2_hidden(X2,X1) != iProver_top
% 36.00/5.02      | r2_hidden(X2,sK4(X1)) != iProver_top ),
% 36.00/5.02      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 36.00/5.02  
% 36.00/5.02  cnf(c_44906,plain,
% 36.00/5.02      ( r2_hidden(X0,X1) != iProver_top
% 36.00/5.02      | r2_hidden(X2,k1_xboole_0) != iProver_top
% 36.00/5.02      | r2_hidden(sK3(k1_xboole_0,X2),X1) != iProver_top ),
% 36.00/5.02      inference(superposition,[status(thm)],[c_44704,c_754]) ).
% 36.00/5.02  
% 36.00/5.02  cnf(c_45067,plain,
% 36.00/5.02      ( r2_hidden(X0,X1) != iProver_top
% 36.00/5.02      | r2_hidden(X2,k1_xboole_0) != iProver_top ),
% 36.00/5.02      inference(forward_subsumption_resolution,[status(thm)],[c_44906,c_44704]) ).
% 36.00/5.02  
% 36.00/5.02  cnf(c_45069,plain,
% 36.00/5.02      ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
% 36.00/5.02      inference(backward_subsumption_resolution,
% 36.00/5.02                [status(thm)],
% 36.00/5.02                [c_45067,c_44704]) ).
% 36.00/5.02  
% 36.00/5.02  cnf(c_51422,plain,
% 36.00/5.02      ( r2_hidden(X1,sK6) != iProver_top | r2_hidden(X0,sK5) != iProver_top ),
% 36.00/5.02      inference(global_propositional_subsumption,
% 36.00/5.02                [status(thm)],
% 36.00/5.02                [c_18469,c_5597,c_5598,c_25656,c_45069]) ).
% 36.00/5.02  
% 36.00/5.02  cnf(c_51423,plain,
% 36.00/5.02      ( r2_hidden(X0,sK5) != iProver_top | r2_hidden(X1,sK6) != iProver_top ),
% 36.00/5.02      inference(renaming,[status(thm)],[c_51422]) ).
% 36.00/5.02  
% 36.00/5.02  cnf(c_59090,plain,
% 36.00/5.02      ( r2_hidden(X0,sK6) != iProver_top ),
% 36.00/5.02      inference(superposition,[status(thm)],[c_59078,c_51423]) ).
% 36.00/5.02  
% 36.00/5.02  cnf(c_97872,plain,
% 36.00/5.02      ( $false ),
% 36.00/5.02      inference(superposition,[status(thm)],[c_96411,c_59090]) ).
% 36.00/5.02  
% 36.00/5.02  
% 36.00/5.02  % SZS output end CNFRefutation for theBenchmark.p
% 36.00/5.02  
% 36.00/5.02  ------                               Statistics
% 36.00/5.02  
% 36.00/5.02  ------ Selected
% 36.00/5.02  
% 36.00/5.02  total_time:                             4.386
% 36.00/5.02  
%------------------------------------------------------------------------------
