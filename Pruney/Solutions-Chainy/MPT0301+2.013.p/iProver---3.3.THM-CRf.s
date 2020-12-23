%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:36:57 EST 2020

% Result     : Theorem 3.68s
% Output     : CNFRefutation 3.68s
% Verified   : 
% Statistics : Number of formulae       :  130 (2279 expanded)
%              Number of clauses        :   66 ( 394 expanded)
%              Number of leaves         :   21 ( 709 expanded)
%              Depth                    :   28
%              Number of atoms          :  378 (6305 expanded)
%              Number of equality atoms :  251 (4157 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal clause size      :   18 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( k2_zfmisc_1(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ? [X4,X5] :
              ( k4_tarski(X4,X5) = X3
              & r2_hidden(X5,X1)
              & r2_hidden(X4,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
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
    inference(nnf_transformation,[],[f10])).

fof(f21,plain,(
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
    inference(rectify,[],[f20])).

fof(f24,plain,(
    ! [X8,X1,X0] :
      ( ? [X11,X12] :
          ( k4_tarski(X11,X12) = X8
          & r2_hidden(X12,X1)
          & r2_hidden(X11,X0) )
     => ( k4_tarski(sK4(X0,X1,X8),sK5(X0,X1,X8)) = X8
        & r2_hidden(sK5(X0,X1,X8),X1)
        & r2_hidden(sK4(X0,X1,X8),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X6,X7] :
          ( k4_tarski(X6,X7) = X3
          & r2_hidden(X7,X1)
          & r2_hidden(X6,X0) )
     => ( k4_tarski(sK2(X0,X1,X2),sK3(X0,X1,X2)) = X3
        & r2_hidden(sK3(X0,X1,X2),X1)
        & r2_hidden(sK2(X0,X1,X2),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
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

fof(f25,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4,sK5])],[f21,f24,f23,f22])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( k2_zfmisc_1(X0,X1) = X2
      | r2_hidden(sK3(X0,X1,X2),X1)
      | r2_hidden(sK1(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => k2_xboole_0(k1_tarski(X0),X1) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(k1_tarski(X0),X1) = X1
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f47,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(k1_tarski(X0),X1) = X1
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f3,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f4,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f5,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f5])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f6])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f7])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f8])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f9])).

fof(f52,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f37,f38])).

fof(f53,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f36,f52])).

fof(f54,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f35,f53])).

fof(f55,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f34,f54])).

fof(f56,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f33,f55])).

fof(f57,plain,(
    ! [X0] : k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f32,f56])).

fof(f59,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1) = X1
      | ~ r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f47,f57])).

fof(f12,axiom,(
    ! [X0,X1] : k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
    ! [X0,X1] : k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1) ),
    inference(cnf_transformation,[],[f12])).

fof(f1,axiom,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf_transformation,[],[f1])).

fof(f60,plain,(
    ! [X0,X1] : o_0_0_xboole_0 != k2_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1) ),
    inference(definition_unfolding,[],[f48,f30,f57])).

fof(f13,conjecture,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,negated_conjecture,(
    ~ ! [X0,X1] :
        ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      <=> ( k1_xboole_0 = X1
          | k1_xboole_0 = X0 ) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f17,plain,(
    ? [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <~> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f26,plain,(
    ? [X0,X1] :
      ( ( ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 )
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 = k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f17])).

fof(f27,plain,(
    ? [X0,X1] :
      ( ( ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 )
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 = k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f26])).

fof(f28,plain,
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

fof(f29,plain,
    ( ( ( k1_xboole_0 != sK7
        & k1_xboole_0 != sK6 )
      | k1_xboole_0 != k2_zfmisc_1(sK6,sK7) )
    & ( k1_xboole_0 = sK7
      | k1_xboole_0 = sK6
      | k1_xboole_0 = k2_zfmisc_1(sK6,sK7) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7])],[f27,f28])).

fof(f49,plain,
    ( k1_xboole_0 = sK7
    | k1_xboole_0 = sK6
    | k1_xboole_0 = k2_zfmisc_1(sK6,sK7) ),
    inference(cnf_transformation,[],[f29])).

fof(f63,plain,
    ( o_0_0_xboole_0 = sK7
    | o_0_0_xboole_0 = sK6
    | o_0_0_xboole_0 = k2_zfmisc_1(sK6,sK7) ),
    inference(definition_unfolding,[],[f49,f30,f30,f30])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( k2_zfmisc_1(X0,X1) = X2
      | r2_hidden(sK2(X0,X1,X2),X0)
      | r2_hidden(sK1(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f2,axiom,(
    ! [X0] :
      ~ ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f2])).

fof(f18,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK0(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
    ! [X0] :
      ( r2_hidden(sK0(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f15,f18])).

fof(f31,plain,(
    ! [X0] :
      ( r2_hidden(sK0(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f19])).

fof(f58,plain,(
    ! [X0] :
      ( r2_hidden(sK0(X0),X0)
      | o_0_0_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f31,f30])).

fof(f42,plain,(
    ! [X2,X0,X10,X8,X1,X9] :
      ( r2_hidden(X8,X2)
      | k4_tarski(X9,X10) != X8
      | ~ r2_hidden(X10,X1)
      | ~ r2_hidden(X9,X0)
      | k2_zfmisc_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f64,plain,(
    ! [X2,X0,X10,X1,X9] :
      ( r2_hidden(k4_tarski(X9,X10),X2)
      | ~ r2_hidden(X10,X1)
      | ~ r2_hidden(X9,X0)
      | k2_zfmisc_1(X0,X1) != X2 ) ),
    inference(equality_resolution,[],[f42])).

fof(f65,plain,(
    ! [X0,X10,X1,X9] :
      ( r2_hidden(k4_tarski(X9,X10),k2_zfmisc_1(X0,X1))
      | ~ r2_hidden(X10,X1)
      | ~ r2_hidden(X9,X0) ) ),
    inference(equality_resolution,[],[f64])).

fof(f40,plain,(
    ! [X2,X0,X8,X1] :
      ( r2_hidden(sK5(X0,X1,X8),X1)
      | ~ r2_hidden(X8,X2)
      | k2_zfmisc_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f67,plain,(
    ! [X0,X8,X1] :
      ( r2_hidden(sK5(X0,X1,X8),X1)
      | ~ r2_hidden(X8,k2_zfmisc_1(X0,X1)) ) ),
    inference(equality_resolution,[],[f40])).

fof(f50,plain,
    ( k1_xboole_0 != sK6
    | k1_xboole_0 != k2_zfmisc_1(sK6,sK7) ),
    inference(cnf_transformation,[],[f29])).

fof(f62,plain,
    ( o_0_0_xboole_0 != sK6
    | o_0_0_xboole_0 != k2_zfmisc_1(sK6,sK7) ),
    inference(definition_unfolding,[],[f50,f30,f30])).

fof(f39,plain,(
    ! [X2,X0,X8,X1] :
      ( r2_hidden(sK4(X0,X1,X8),X0)
      | ~ r2_hidden(X8,X2)
      | k2_zfmisc_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f68,plain,(
    ! [X0,X8,X1] :
      ( r2_hidden(sK4(X0,X1,X8),X0)
      | ~ r2_hidden(X8,k2_zfmisc_1(X0,X1)) ) ),
    inference(equality_resolution,[],[f39])).

fof(f51,plain,
    ( k1_xboole_0 != sK7
    | k1_xboole_0 != k2_zfmisc_1(sK6,sK7) ),
    inference(cnf_transformation,[],[f29])).

fof(f61,plain,
    ( o_0_0_xboole_0 != sK7
    | o_0_0_xboole_0 != k2_zfmisc_1(sK6,sK7) ),
    inference(definition_unfolding,[],[f51,f30,f30])).

cnf(c_129,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_128,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_669,plain,
    ( X0 != X1
    | X1 = X0 ),
    inference(resolution,[status(thm)],[c_129,c_128])).

cnf(c_3,plain,
    ( r2_hidden(sK3(X0,X1,X2),X1)
    | r2_hidden(sK1(X0,X1,X2),X2)
    | k2_zfmisc_1(X0,X1) = X2 ),
    inference(cnf_transformation,[],[f44])).

cnf(c_4347,plain,
    ( r2_hidden(sK3(X0,X1,X2),X1)
    | r2_hidden(sK1(X0,X1,X2),X2)
    | X2 = k2_zfmisc_1(X0,X1) ),
    inference(resolution,[status(thm)],[c_669,c_3])).

cnf(c_9,plain,
    ( ~ r2_hidden(X0,X1)
    | k2_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1) = X1 ),
    inference(cnf_transformation,[],[f59])).

cnf(c_10,plain,
    ( k2_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1) != o_0_0_xboole_0 ),
    inference(cnf_transformation,[],[f60])).

cnf(c_2488,plain,
    ( ~ r2_hidden(X0,o_0_0_xboole_0) ),
    inference(resolution,[status(thm)],[c_9,c_10])).

cnf(c_13,negated_conjecture,
    ( o_0_0_xboole_0 = k2_zfmisc_1(sK6,sK7)
    | o_0_0_xboole_0 = sK6
    | o_0_0_xboole_0 = sK7 ),
    inference(cnf_transformation,[],[f63])).

cnf(c_668,plain,
    ( X0 != k2_zfmisc_1(sK6,sK7)
    | o_0_0_xboole_0 = X0
    | o_0_0_xboole_0 = sK6
    | o_0_0_xboole_0 = sK7 ),
    inference(resolution,[status(thm)],[c_129,c_13])).

cnf(c_4,plain,
    ( r2_hidden(sK2(X0,X1,X2),X0)
    | r2_hidden(sK1(X0,X1,X2),X2)
    | k2_zfmisc_1(X0,X1) = X2 ),
    inference(cnf_transformation,[],[f43])).

cnf(c_1014,plain,
    ( r2_hidden(sK2(X0,X1,k2_zfmisc_1(sK6,sK7)),X0)
    | r2_hidden(sK1(X0,X1,k2_zfmisc_1(sK6,sK7)),k2_zfmisc_1(sK6,sK7))
    | o_0_0_xboole_0 = k2_zfmisc_1(X0,X1)
    | o_0_0_xboole_0 = sK6
    | o_0_0_xboole_0 = sK7 ),
    inference(resolution,[status(thm)],[c_668,c_4])).

cnf(c_4155,plain,
    ( r2_hidden(sK1(o_0_0_xboole_0,X0,k2_zfmisc_1(sK6,sK7)),k2_zfmisc_1(sK6,sK7))
    | o_0_0_xboole_0 = k2_zfmisc_1(o_0_0_xboole_0,X0)
    | o_0_0_xboole_0 = sK6
    | o_0_0_xboole_0 = sK7 ),
    inference(resolution,[status(thm)],[c_2488,c_1014])).

cnf(c_139,plain,
    ( o_0_0_xboole_0 = o_0_0_xboole_0 ),
    inference(instantiation,[status(thm)],[c_128])).

cnf(c_435,plain,
    ( sK7 != X0
    | o_0_0_xboole_0 != X0
    | o_0_0_xboole_0 = sK7 ),
    inference(instantiation,[status(thm)],[c_129])).

cnf(c_436,plain,
    ( sK7 != o_0_0_xboole_0
    | o_0_0_xboole_0 = sK7
    | o_0_0_xboole_0 != o_0_0_xboole_0 ),
    inference(instantiation,[status(thm)],[c_435])).

cnf(c_0,plain,
    ( r2_hidden(sK0(X0),X0)
    | o_0_0_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f58])).

cnf(c_323,plain,
    ( o_0_0_xboole_0 = X0
    | r2_hidden(sK0(X0),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_5,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X2,X3)
    | r2_hidden(k4_tarski(X2,X0),k2_zfmisc_1(X3,X1)) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_318,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X2,X3) != iProver_top
    | r2_hidden(k4_tarski(X2,X0),k2_zfmisc_1(X3,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_756,plain,
    ( sK6 = o_0_0_xboole_0
    | sK7 = o_0_0_xboole_0
    | r2_hidden(X0,sK6) != iProver_top
    | r2_hidden(X1,sK7) != iProver_top
    | r2_hidden(k4_tarski(X0,X1),o_0_0_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_13,c_318])).

cnf(c_7,plain,
    ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
    | r2_hidden(sK5(X1,X2,X0),X2) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_316,plain,
    ( r2_hidden(X0,k2_zfmisc_1(X1,X2)) != iProver_top
    | r2_hidden(sK5(X1,X2,X0),X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_314,plain,
    ( k2_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1) = X1
    | r2_hidden(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_603,plain,
    ( k2_xboole_0(k6_enumset1(sK5(X0,X1,X2),sK5(X0,X1,X2),sK5(X0,X1,X2),sK5(X0,X1,X2),sK5(X0,X1,X2),sK5(X0,X1,X2),sK5(X0,X1,X2),sK5(X0,X1,X2)),X1) = X1
    | r2_hidden(X2,k2_zfmisc_1(X0,X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_316,c_314])).

cnf(c_3511,plain,
    ( k2_xboole_0(k6_enumset1(sK5(sK6,sK7,X0),sK5(sK6,sK7,X0),sK5(sK6,sK7,X0),sK5(sK6,sK7,X0),sK5(sK6,sK7,X0),sK5(sK6,sK7,X0),sK5(sK6,sK7,X0),sK5(sK6,sK7,X0)),sK7) = sK7
    | sK6 = o_0_0_xboole_0
    | sK7 = o_0_0_xboole_0
    | r2_hidden(X0,o_0_0_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_13,c_603])).

cnf(c_2489,plain,
    ( r2_hidden(X0,o_0_0_xboole_0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2488])).

cnf(c_3837,plain,
    ( r2_hidden(X0,o_0_0_xboole_0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3511,c_2489])).

cnf(c_3850,plain,
    ( sK6 = o_0_0_xboole_0
    | sK7 = o_0_0_xboole_0
    | r2_hidden(X0,sK6) != iProver_top
    | r2_hidden(X1,sK7) != iProver_top ),
    inference(superposition,[status(thm)],[c_756,c_3837])).

cnf(c_5060,plain,
    ( sK6 = o_0_0_xboole_0
    | sK7 = o_0_0_xboole_0
    | r2_hidden(X0,sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_323,c_3850])).

cnf(c_595,plain,
    ( X0 != X1
    | sK7 != X1
    | sK7 = X0 ),
    inference(instantiation,[status(thm)],[c_129])).

cnf(c_1378,plain,
    ( X0 != sK7
    | sK7 = X0
    | sK7 != sK7 ),
    inference(instantiation,[status(thm)],[c_595])).

cnf(c_1380,plain,
    ( sK7 != sK7
    | sK7 = o_0_0_xboole_0
    | o_0_0_xboole_0 != sK7 ),
    inference(instantiation,[status(thm)],[c_1378])).

cnf(c_1379,plain,
    ( sK7 = sK7 ),
    inference(instantiation,[status(thm)],[c_128])).

cnf(c_597,plain,
    ( X0 != X1
    | sK6 != X1
    | sK6 = X0 ),
    inference(instantiation,[status(thm)],[c_129])).

cnf(c_1382,plain,
    ( X0 != sK6
    | sK6 = X0
    | sK6 != sK6 ),
    inference(instantiation,[status(thm)],[c_597])).

cnf(c_1384,plain,
    ( sK6 != sK6
    | sK6 = o_0_0_xboole_0
    | o_0_0_xboole_0 != sK6 ),
    inference(instantiation,[status(thm)],[c_1382])).

cnf(c_1383,plain,
    ( sK6 = sK6 ),
    inference(instantiation,[status(thm)],[c_128])).

cnf(c_130,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_826,plain,
    ( ~ r2_hidden(X0,k2_zfmisc_1(sK6,sK7))
    | r2_hidden(X1,o_0_0_xboole_0)
    | X1 != X0
    | o_0_0_xboole_0 = sK6
    | o_0_0_xboole_0 = sK7 ),
    inference(resolution,[status(thm)],[c_130,c_13])).

cnf(c_1287,plain,
    ( ~ r2_hidden(X0,sK6)
    | ~ r2_hidden(X1,sK7)
    | r2_hidden(X2,o_0_0_xboole_0)
    | X2 != k4_tarski(X0,X1)
    | o_0_0_xboole_0 = sK6
    | o_0_0_xboole_0 = sK7 ),
    inference(resolution,[status(thm)],[c_826,c_5])).

cnf(c_4034,plain,
    ( ~ r2_hidden(X0,sK6)
    | ~ r2_hidden(X1,sK7)
    | X2 != k4_tarski(X0,X1)
    | o_0_0_xboole_0 = sK6
    | o_0_0_xboole_0 = sK7 ),
    inference(backward_subsumption_resolution,[status(thm)],[c_2488,c_1287])).

cnf(c_437,plain,
    ( sK6 != X0
    | o_0_0_xboole_0 != X0
    | o_0_0_xboole_0 = sK6 ),
    inference(instantiation,[status(thm)],[c_129])).

cnf(c_438,plain,
    ( sK6 != o_0_0_xboole_0
    | o_0_0_xboole_0 = sK6
    | o_0_0_xboole_0 != o_0_0_xboole_0 ),
    inference(instantiation,[status(thm)],[c_437])).

cnf(c_5200,plain,
    ( ~ r2_hidden(X0,sK6)
    | sK6 = o_0_0_xboole_0
    | sK7 = o_0_0_xboole_0 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_5060])).

cnf(c_5470,plain,
    ( ~ r2_hidden(X0,sK6)
    | o_0_0_xboole_0 = sK6
    | o_0_0_xboole_0 = sK7 ),
    inference(global_propositional_subsumption,[status(thm)],[c_4034,c_139,c_436,c_438,c_5200])).

cnf(c_5492,plain,
    ( o_0_0_xboole_0 = sK6
    | o_0_0_xboole_0 = sK7 ),
    inference(resolution,[status(thm)],[c_5470,c_0])).

cnf(c_5501,plain,
    ( sK7 = o_0_0_xboole_0
    | sK6 = o_0_0_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_5060,c_1380,c_1379,c_1384,c_1383,c_5492])).

cnf(c_5502,plain,
    ( sK6 = o_0_0_xboole_0
    | sK7 = o_0_0_xboole_0 ),
    inference(renaming,[status(thm)],[c_5501])).

cnf(c_12,negated_conjecture,
    ( o_0_0_xboole_0 != k2_zfmisc_1(sK6,sK7)
    | o_0_0_xboole_0 != sK6 ),
    inference(cnf_transformation,[],[f62])).

cnf(c_5516,plain,
    ( k2_zfmisc_1(o_0_0_xboole_0,sK7) != o_0_0_xboole_0
    | sK6 != o_0_0_xboole_0
    | sK7 = o_0_0_xboole_0 ),
    inference(superposition,[status(thm)],[c_5502,c_12])).

cnf(c_5521,plain,
    ( k2_zfmisc_1(o_0_0_xboole_0,sK7) != o_0_0_xboole_0
    | sK7 = o_0_0_xboole_0 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_5516,c_5502])).

cnf(c_8,plain,
    ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
    | r2_hidden(sK4(X1,X2,X0),X1) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_315,plain,
    ( r2_hidden(X0,k2_zfmisc_1(X1,X2)) != iProver_top
    | r2_hidden(sK4(X1,X2,X0),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_3849,plain,
    ( r2_hidden(X0,k2_zfmisc_1(o_0_0_xboole_0,X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_315,c_3837])).

cnf(c_4495,plain,
    ( k2_zfmisc_1(o_0_0_xboole_0,X0) = o_0_0_xboole_0 ),
    inference(superposition,[status(thm)],[c_323,c_3849])).

cnf(c_5522,plain,
    ( sK7 = o_0_0_xboole_0
    | o_0_0_xboole_0 != o_0_0_xboole_0 ),
    inference(demodulation,[status(thm)],[c_5521,c_4495])).

cnf(c_5523,plain,
    ( sK7 = o_0_0_xboole_0 ),
    inference(equality_resolution_simp,[status(thm)],[c_5522])).

cnf(c_5657,plain,
    ( o_0_0_xboole_0 = sK7 ),
    inference(global_propositional_subsumption,[status(thm)],[c_4155,c_139,c_436,c_5523])).

cnf(c_11,negated_conjecture,
    ( o_0_0_xboole_0 != k2_zfmisc_1(sK6,sK7)
    | o_0_0_xboole_0 != sK7 ),
    inference(cnf_transformation,[],[f61])).

cnf(c_5663,plain,
    ( o_0_0_xboole_0 != k2_zfmisc_1(sK6,sK7) ),
    inference(backward_subsumption_resolution,[status(thm)],[c_5657,c_11])).

cnf(c_9668,plain,
    ( r2_hidden(sK3(sK6,sK7,o_0_0_xboole_0),sK7)
    | r2_hidden(sK1(sK6,sK7,o_0_0_xboole_0),o_0_0_xboole_0) ),
    inference(resolution,[status(thm)],[c_4347,c_5663])).

cnf(c_2492,plain,
    ( ~ r2_hidden(X0,X1)
    | X2 != X1
    | k2_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1) = X2 ),
    inference(resolution,[status(thm)],[c_9,c_129])).

cnf(c_6963,plain,
    ( ~ r2_hidden(X0,X1)
    | o_0_0_xboole_0 != X1 ),
    inference(resolution,[status(thm)],[c_2492,c_10])).

cnf(c_8850,plain,
    ( ~ r2_hidden(X0,sK7) ),
    inference(resolution,[status(thm)],[c_6963,c_5657])).

cnf(c_10001,plain,
    ( $false ),
    inference(forward_subsumption_resolution,[status(thm)],[c_9668,c_2488,c_8850])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 14:36:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 3.68/0.99  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.68/0.99  
% 3.68/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.68/0.99  
% 3.68/0.99  ------  iProver source info
% 3.68/0.99  
% 3.68/0.99  git: date: 2020-06-30 10:37:57 +0100
% 3.68/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.68/0.99  git: non_committed_changes: false
% 3.68/0.99  git: last_make_outside_of_git: false
% 3.68/0.99  
% 3.68/0.99  ------ 
% 3.68/0.99  ------ Parsing...
% 3.68/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.68/0.99  
% 3.68/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 3.68/0.99  
% 3.68/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.68/0.99  
% 3.68/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.68/0.99  ------ Proving...
% 3.68/0.99  ------ Problem Properties 
% 3.68/0.99  
% 3.68/0.99  
% 3.68/0.99  clauses                                 14
% 3.68/0.99  conjectures                             3
% 3.68/0.99  EPR                                     0
% 3.68/0.99  Horn                                    9
% 3.68/0.99  unary                                   1
% 3.68/0.99  binary                                  7
% 3.68/0.99  lits                                    35
% 3.68/0.99  lits eq                                 17
% 3.68/0.99  fd_pure                                 0
% 3.68/0.99  fd_pseudo                               0
% 3.68/0.99  fd_cond                                 1
% 3.68/0.99  fd_pseudo_cond                          4
% 3.68/0.99  AC symbols                              0
% 3.68/0.99  
% 3.68/0.99  ------ Input Options Time Limit: Unbounded
% 3.68/0.99  
% 3.68/0.99  
% 3.68/0.99  ------ 
% 3.68/0.99  Current options:
% 3.68/0.99  ------ 
% 3.68/0.99  
% 3.68/0.99  
% 3.68/0.99  
% 3.68/0.99  
% 3.68/0.99  ------ Proving...
% 3.68/0.99  
% 3.68/0.99  
% 3.68/0.99  % SZS status Theorem for theBenchmark.p
% 3.68/0.99  
% 3.68/0.99   Resolution empty clause
% 3.68/0.99  
% 3.68/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 3.68/0.99  
% 3.68/0.99  fof(f10,axiom,(
% 3.68/0.99    ! [X0,X1,X2] : (k2_zfmisc_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4,X5] : (k4_tarski(X4,X5) = X3 & r2_hidden(X5,X1) & r2_hidden(X4,X0))))),
% 3.68/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.68/0.99  
% 3.68/0.99  fof(f20,plain,(
% 3.68/0.99    ! [X0,X1,X2] : ((k2_zfmisc_1(X0,X1) = X2 | ? [X3] : ((! [X4,X5] : (k4_tarski(X4,X5) != X3 | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X0)) | ~r2_hidden(X3,X2)) & (? [X4,X5] : (k4_tarski(X4,X5) = X3 & r2_hidden(X5,X1) & r2_hidden(X4,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ! [X4,X5] : (k4_tarski(X4,X5) != X3 | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X0))) & (? [X4,X5] : (k4_tarski(X4,X5) = X3 & r2_hidden(X5,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X3,X2))) | k2_zfmisc_1(X0,X1) != X2))),
% 3.68/0.99    inference(nnf_transformation,[],[f10])).
% 3.68/0.99  
% 3.68/0.99  fof(f21,plain,(
% 3.68/0.99    ! [X0,X1,X2] : ((k2_zfmisc_1(X0,X1) = X2 | ? [X3] : ((! [X4,X5] : (k4_tarski(X4,X5) != X3 | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X0)) | ~r2_hidden(X3,X2)) & (? [X6,X7] : (k4_tarski(X6,X7) = X3 & r2_hidden(X7,X1) & r2_hidden(X6,X0)) | r2_hidden(X3,X2)))) & (! [X8] : ((r2_hidden(X8,X2) | ! [X9,X10] : (k4_tarski(X9,X10) != X8 | ~r2_hidden(X10,X1) | ~r2_hidden(X9,X0))) & (? [X11,X12] : (k4_tarski(X11,X12) = X8 & r2_hidden(X12,X1) & r2_hidden(X11,X0)) | ~r2_hidden(X8,X2))) | k2_zfmisc_1(X0,X1) != X2))),
% 3.68/0.99    inference(rectify,[],[f20])).
% 3.68/0.99  
% 3.68/0.99  fof(f24,plain,(
% 3.68/0.99    ! [X8,X1,X0] : (? [X11,X12] : (k4_tarski(X11,X12) = X8 & r2_hidden(X12,X1) & r2_hidden(X11,X0)) => (k4_tarski(sK4(X0,X1,X8),sK5(X0,X1,X8)) = X8 & r2_hidden(sK5(X0,X1,X8),X1) & r2_hidden(sK4(X0,X1,X8),X0)))),
% 3.68/0.99    introduced(choice_axiom,[])).
% 3.68/0.99  
% 3.68/0.99  fof(f23,plain,(
% 3.68/0.99    ( ! [X3] : (! [X2,X1,X0] : (? [X6,X7] : (k4_tarski(X6,X7) = X3 & r2_hidden(X7,X1) & r2_hidden(X6,X0)) => (k4_tarski(sK2(X0,X1,X2),sK3(X0,X1,X2)) = X3 & r2_hidden(sK3(X0,X1,X2),X1) & r2_hidden(sK2(X0,X1,X2),X0)))) )),
% 3.68/0.99    introduced(choice_axiom,[])).
% 3.68/0.99  
% 3.68/0.99  fof(f22,plain,(
% 3.68/0.99    ! [X2,X1,X0] : (? [X3] : ((! [X4,X5] : (k4_tarski(X4,X5) != X3 | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X0)) | ~r2_hidden(X3,X2)) & (? [X6,X7] : (k4_tarski(X6,X7) = X3 & r2_hidden(X7,X1) & r2_hidden(X6,X0)) | r2_hidden(X3,X2))) => ((! [X5,X4] : (k4_tarski(X4,X5) != sK1(X0,X1,X2) | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X0)) | ~r2_hidden(sK1(X0,X1,X2),X2)) & (? [X7,X6] : (k4_tarski(X6,X7) = sK1(X0,X1,X2) & r2_hidden(X7,X1) & r2_hidden(X6,X0)) | r2_hidden(sK1(X0,X1,X2),X2))))),
% 3.68/0.99    introduced(choice_axiom,[])).
% 3.68/0.99  
% 3.68/0.99  fof(f25,plain,(
% 3.68/0.99    ! [X0,X1,X2] : ((k2_zfmisc_1(X0,X1) = X2 | ((! [X4,X5] : (k4_tarski(X4,X5) != sK1(X0,X1,X2) | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X0)) | ~r2_hidden(sK1(X0,X1,X2),X2)) & ((k4_tarski(sK2(X0,X1,X2),sK3(X0,X1,X2)) = sK1(X0,X1,X2) & r2_hidden(sK3(X0,X1,X2),X1) & r2_hidden(sK2(X0,X1,X2),X0)) | r2_hidden(sK1(X0,X1,X2),X2)))) & (! [X8] : ((r2_hidden(X8,X2) | ! [X9,X10] : (k4_tarski(X9,X10) != X8 | ~r2_hidden(X10,X1) | ~r2_hidden(X9,X0))) & ((k4_tarski(sK4(X0,X1,X8),sK5(X0,X1,X8)) = X8 & r2_hidden(sK5(X0,X1,X8),X1) & r2_hidden(sK4(X0,X1,X8),X0)) | ~r2_hidden(X8,X2))) | k2_zfmisc_1(X0,X1) != X2))),
% 3.68/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4,sK5])],[f21,f24,f23,f22])).
% 3.68/0.99  
% 3.68/0.99  fof(f44,plain,(
% 3.68/0.99    ( ! [X2,X0,X1] : (k2_zfmisc_1(X0,X1) = X2 | r2_hidden(sK3(X0,X1,X2),X1) | r2_hidden(sK1(X0,X1,X2),X2)) )),
% 3.68/0.99    inference(cnf_transformation,[],[f25])).
% 3.68/0.99  
% 3.68/0.99  fof(f11,axiom,(
% 3.68/0.99    ! [X0,X1] : (r2_hidden(X0,X1) => k2_xboole_0(k1_tarski(X0),X1) = X1)),
% 3.68/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.68/0.99  
% 3.68/0.99  fof(f16,plain,(
% 3.68/0.99    ! [X0,X1] : (k2_xboole_0(k1_tarski(X0),X1) = X1 | ~r2_hidden(X0,X1))),
% 3.68/0.99    inference(ennf_transformation,[],[f11])).
% 3.68/0.99  
% 3.68/0.99  fof(f47,plain,(
% 3.68/0.99    ( ! [X0,X1] : (k2_xboole_0(k1_tarski(X0),X1) = X1 | ~r2_hidden(X0,X1)) )),
% 3.68/0.99    inference(cnf_transformation,[],[f16])).
% 3.68/0.99  
% 3.68/0.99  fof(f3,axiom,(
% 3.68/0.99    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 3.68/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.68/0.99  
% 3.68/0.99  fof(f32,plain,(
% 3.68/0.99    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 3.68/0.99    inference(cnf_transformation,[],[f3])).
% 3.68/0.99  
% 3.68/0.99  fof(f4,axiom,(
% 3.68/0.99    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 3.68/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.68/0.99  
% 3.68/0.99  fof(f33,plain,(
% 3.68/0.99    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 3.68/0.99    inference(cnf_transformation,[],[f4])).
% 3.68/0.99  
% 3.68/0.99  fof(f5,axiom,(
% 3.68/0.99    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 3.68/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.68/0.99  
% 3.68/0.99  fof(f34,plain,(
% 3.68/0.99    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 3.68/0.99    inference(cnf_transformation,[],[f5])).
% 3.68/0.99  
% 3.68/0.99  fof(f6,axiom,(
% 3.68/0.99    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 3.68/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.68/0.99  
% 3.68/0.99  fof(f35,plain,(
% 3.68/0.99    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 3.68/0.99    inference(cnf_transformation,[],[f6])).
% 3.68/0.99  
% 3.68/0.99  fof(f7,axiom,(
% 3.68/0.99    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)),
% 3.68/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.68/0.99  
% 3.68/0.99  fof(f36,plain,(
% 3.68/0.99    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)) )),
% 3.68/0.99    inference(cnf_transformation,[],[f7])).
% 3.68/0.99  
% 3.68/0.99  fof(f8,axiom,(
% 3.68/0.99    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)),
% 3.68/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.68/0.99  
% 3.68/0.99  fof(f37,plain,(
% 3.68/0.99    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)) )),
% 3.68/0.99    inference(cnf_transformation,[],[f8])).
% 3.68/0.99  
% 3.68/0.99  fof(f9,axiom,(
% 3.68/0.99    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)),
% 3.68/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.68/0.99  
% 3.68/0.99  fof(f38,plain,(
% 3.68/0.99    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)) )),
% 3.68/0.99    inference(cnf_transformation,[],[f9])).
% 3.68/0.99  
% 3.68/0.99  fof(f52,plain,(
% 3.68/0.99    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 3.68/0.99    inference(definition_unfolding,[],[f37,f38])).
% 3.68/0.99  
% 3.68/0.99  fof(f53,plain,(
% 3.68/0.99    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 3.68/0.99    inference(definition_unfolding,[],[f36,f52])).
% 3.68/0.99  
% 3.68/0.99  fof(f54,plain,(
% 3.68/0.99    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 3.68/0.99    inference(definition_unfolding,[],[f35,f53])).
% 3.68/0.99  
% 3.68/0.99  fof(f55,plain,(
% 3.68/0.99    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 3.68/0.99    inference(definition_unfolding,[],[f34,f54])).
% 3.68/0.99  
% 3.68/0.99  fof(f56,plain,(
% 3.68/0.99    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 3.68/0.99    inference(definition_unfolding,[],[f33,f55])).
% 3.68/0.99  
% 3.68/0.99  fof(f57,plain,(
% 3.68/0.99    ( ! [X0] : (k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) )),
% 3.68/0.99    inference(definition_unfolding,[],[f32,f56])).
% 3.68/0.99  
% 3.68/0.99  fof(f59,plain,(
% 3.68/0.99    ( ! [X0,X1] : (k2_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1) = X1 | ~r2_hidden(X0,X1)) )),
% 3.68/0.99    inference(definition_unfolding,[],[f47,f57])).
% 3.68/0.99  
% 3.68/0.99  fof(f12,axiom,(
% 3.68/0.99    ! [X0,X1] : k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1)),
% 3.68/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.68/0.99  
% 3.68/0.99  fof(f48,plain,(
% 3.68/0.99    ( ! [X0,X1] : (k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1)) )),
% 3.68/0.99    inference(cnf_transformation,[],[f12])).
% 3.68/0.99  
% 3.68/0.99  fof(f1,axiom,(
% 3.68/0.99    k1_xboole_0 = o_0_0_xboole_0),
% 3.68/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.68/0.99  
% 3.68/0.99  fof(f30,plain,(
% 3.68/0.99    k1_xboole_0 = o_0_0_xboole_0),
% 3.68/0.99    inference(cnf_transformation,[],[f1])).
% 3.68/0.99  
% 3.68/0.99  fof(f60,plain,(
% 3.68/0.99    ( ! [X0,X1] : (o_0_0_xboole_0 != k2_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1)) )),
% 3.68/0.99    inference(definition_unfolding,[],[f48,f30,f57])).
% 3.68/0.99  
% 3.68/0.99  fof(f13,conjecture,(
% 3.68/0.99    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 3.68/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.68/0.99  
% 3.68/0.99  fof(f14,negated_conjecture,(
% 3.68/0.99    ~! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 3.68/0.99    inference(negated_conjecture,[],[f13])).
% 3.68/0.99  
% 3.68/0.99  fof(f17,plain,(
% 3.68/0.99    ? [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <~> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 3.68/0.99    inference(ennf_transformation,[],[f14])).
% 3.68/0.99  
% 3.68/0.99  fof(f26,plain,(
% 3.68/0.99    ? [X0,X1] : (((k1_xboole_0 != X1 & k1_xboole_0 != X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 = k2_zfmisc_1(X0,X1)))),
% 3.68/0.99    inference(nnf_transformation,[],[f17])).
% 3.68/0.99  
% 3.68/0.99  fof(f27,plain,(
% 3.68/0.99    ? [X0,X1] : (((k1_xboole_0 != X1 & k1_xboole_0 != X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 = k2_zfmisc_1(X0,X1)))),
% 3.68/0.99    inference(flattening,[],[f26])).
% 3.68/0.99  
% 3.68/0.99  fof(f28,plain,(
% 3.68/0.99    ? [X0,X1] : (((k1_xboole_0 != X1 & k1_xboole_0 != X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 = k2_zfmisc_1(X0,X1))) => (((k1_xboole_0 != sK7 & k1_xboole_0 != sK6) | k1_xboole_0 != k2_zfmisc_1(sK6,sK7)) & (k1_xboole_0 = sK7 | k1_xboole_0 = sK6 | k1_xboole_0 = k2_zfmisc_1(sK6,sK7)))),
% 3.68/0.99    introduced(choice_axiom,[])).
% 3.68/0.99  
% 3.68/0.99  fof(f29,plain,(
% 3.68/0.99    ((k1_xboole_0 != sK7 & k1_xboole_0 != sK6) | k1_xboole_0 != k2_zfmisc_1(sK6,sK7)) & (k1_xboole_0 = sK7 | k1_xboole_0 = sK6 | k1_xboole_0 = k2_zfmisc_1(sK6,sK7))),
% 3.68/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7])],[f27,f28])).
% 3.68/0.99  
% 3.68/0.99  fof(f49,plain,(
% 3.68/0.99    k1_xboole_0 = sK7 | k1_xboole_0 = sK6 | k1_xboole_0 = k2_zfmisc_1(sK6,sK7)),
% 3.68/0.99    inference(cnf_transformation,[],[f29])).
% 3.68/0.99  
% 3.68/0.99  fof(f63,plain,(
% 3.68/0.99    o_0_0_xboole_0 = sK7 | o_0_0_xboole_0 = sK6 | o_0_0_xboole_0 = k2_zfmisc_1(sK6,sK7)),
% 3.68/0.99    inference(definition_unfolding,[],[f49,f30,f30,f30])).
% 3.68/0.99  
% 3.68/0.99  fof(f43,plain,(
% 3.68/0.99    ( ! [X2,X0,X1] : (k2_zfmisc_1(X0,X1) = X2 | r2_hidden(sK2(X0,X1,X2),X0) | r2_hidden(sK1(X0,X1,X2),X2)) )),
% 3.68/0.99    inference(cnf_transformation,[],[f25])).
% 3.68/0.99  
% 3.68/0.99  fof(f2,axiom,(
% 3.68/0.99    ! [X0] : ~(! [X1] : ~r2_hidden(X1,X0) & k1_xboole_0 != X0)),
% 3.68/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.68/0.99  
% 3.68/0.99  fof(f15,plain,(
% 3.68/0.99    ! [X0] : (? [X1] : r2_hidden(X1,X0) | k1_xboole_0 = X0)),
% 3.68/0.99    inference(ennf_transformation,[],[f2])).
% 3.68/0.99  
% 3.68/0.99  fof(f18,plain,(
% 3.68/0.99    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK0(X0),X0))),
% 3.68/0.99    introduced(choice_axiom,[])).
% 3.68/0.99  
% 3.68/0.99  fof(f19,plain,(
% 3.68/0.99    ! [X0] : (r2_hidden(sK0(X0),X0) | k1_xboole_0 = X0)),
% 3.68/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f15,f18])).
% 3.68/0.99  
% 3.68/0.99  fof(f31,plain,(
% 3.68/0.99    ( ! [X0] : (r2_hidden(sK0(X0),X0) | k1_xboole_0 = X0) )),
% 3.68/0.99    inference(cnf_transformation,[],[f19])).
% 3.68/0.99  
% 3.68/0.99  fof(f58,plain,(
% 3.68/0.99    ( ! [X0] : (r2_hidden(sK0(X0),X0) | o_0_0_xboole_0 = X0) )),
% 3.68/0.99    inference(definition_unfolding,[],[f31,f30])).
% 3.68/0.99  
% 3.68/0.99  fof(f42,plain,(
% 3.68/0.99    ( ! [X2,X0,X10,X8,X1,X9] : (r2_hidden(X8,X2) | k4_tarski(X9,X10) != X8 | ~r2_hidden(X10,X1) | ~r2_hidden(X9,X0) | k2_zfmisc_1(X0,X1) != X2) )),
% 3.68/0.99    inference(cnf_transformation,[],[f25])).
% 3.68/0.99  
% 3.68/0.99  fof(f64,plain,(
% 3.68/0.99    ( ! [X2,X0,X10,X1,X9] : (r2_hidden(k4_tarski(X9,X10),X2) | ~r2_hidden(X10,X1) | ~r2_hidden(X9,X0) | k2_zfmisc_1(X0,X1) != X2) )),
% 3.68/0.99    inference(equality_resolution,[],[f42])).
% 3.68/0.99  
% 3.68/0.99  fof(f65,plain,(
% 3.68/0.99    ( ! [X0,X10,X1,X9] : (r2_hidden(k4_tarski(X9,X10),k2_zfmisc_1(X0,X1)) | ~r2_hidden(X10,X1) | ~r2_hidden(X9,X0)) )),
% 3.68/0.99    inference(equality_resolution,[],[f64])).
% 3.68/0.99  
% 3.68/0.99  fof(f40,plain,(
% 3.68/0.99    ( ! [X2,X0,X8,X1] : (r2_hidden(sK5(X0,X1,X8),X1) | ~r2_hidden(X8,X2) | k2_zfmisc_1(X0,X1) != X2) )),
% 3.68/0.99    inference(cnf_transformation,[],[f25])).
% 3.68/0.99  
% 3.68/0.99  fof(f67,plain,(
% 3.68/0.99    ( ! [X0,X8,X1] : (r2_hidden(sK5(X0,X1,X8),X1) | ~r2_hidden(X8,k2_zfmisc_1(X0,X1))) )),
% 3.68/0.99    inference(equality_resolution,[],[f40])).
% 3.68/0.99  
% 3.68/0.99  fof(f50,plain,(
% 3.68/0.99    k1_xboole_0 != sK6 | k1_xboole_0 != k2_zfmisc_1(sK6,sK7)),
% 3.68/0.99    inference(cnf_transformation,[],[f29])).
% 3.68/0.99  
% 3.68/0.99  fof(f62,plain,(
% 3.68/0.99    o_0_0_xboole_0 != sK6 | o_0_0_xboole_0 != k2_zfmisc_1(sK6,sK7)),
% 3.68/0.99    inference(definition_unfolding,[],[f50,f30,f30])).
% 3.68/0.99  
% 3.68/0.99  fof(f39,plain,(
% 3.68/0.99    ( ! [X2,X0,X8,X1] : (r2_hidden(sK4(X0,X1,X8),X0) | ~r2_hidden(X8,X2) | k2_zfmisc_1(X0,X1) != X2) )),
% 3.68/0.99    inference(cnf_transformation,[],[f25])).
% 3.68/0.99  
% 3.68/0.99  fof(f68,plain,(
% 3.68/0.99    ( ! [X0,X8,X1] : (r2_hidden(sK4(X0,X1,X8),X0) | ~r2_hidden(X8,k2_zfmisc_1(X0,X1))) )),
% 3.68/0.99    inference(equality_resolution,[],[f39])).
% 3.68/0.99  
% 3.68/0.99  fof(f51,plain,(
% 3.68/0.99    k1_xboole_0 != sK7 | k1_xboole_0 != k2_zfmisc_1(sK6,sK7)),
% 3.68/0.99    inference(cnf_transformation,[],[f29])).
% 3.68/0.99  
% 3.68/0.99  fof(f61,plain,(
% 3.68/0.99    o_0_0_xboole_0 != sK7 | o_0_0_xboole_0 != k2_zfmisc_1(sK6,sK7)),
% 3.68/0.99    inference(definition_unfolding,[],[f51,f30,f30])).
% 3.68/0.99  
% 3.68/0.99  cnf(c_129,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 3.68/0.99  
% 3.68/0.99  cnf(c_128,plain,( X0 = X0 ),theory(equality) ).
% 3.68/0.99  
% 3.68/0.99  cnf(c_669,plain,
% 3.68/0.99      ( X0 != X1 | X1 = X0 ),
% 3.68/0.99      inference(resolution,[status(thm)],[c_129,c_128]) ).
% 3.68/0.99  
% 3.68/0.99  cnf(c_3,plain,
% 3.68/0.99      ( r2_hidden(sK3(X0,X1,X2),X1)
% 3.68/0.99      | r2_hidden(sK1(X0,X1,X2),X2)
% 3.68/0.99      | k2_zfmisc_1(X0,X1) = X2 ),
% 3.68/0.99      inference(cnf_transformation,[],[f44]) ).
% 3.68/0.99  
% 3.68/0.99  cnf(c_4347,plain,
% 3.68/0.99      ( r2_hidden(sK3(X0,X1,X2),X1)
% 3.68/0.99      | r2_hidden(sK1(X0,X1,X2),X2)
% 3.68/0.99      | X2 = k2_zfmisc_1(X0,X1) ),
% 3.68/0.99      inference(resolution,[status(thm)],[c_669,c_3]) ).
% 3.68/0.99  
% 3.68/0.99  cnf(c_9,plain,
% 3.68/0.99      ( ~ r2_hidden(X0,X1)
% 3.68/0.99      | k2_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1) = X1 ),
% 3.68/0.99      inference(cnf_transformation,[],[f59]) ).
% 3.68/0.99  
% 3.68/0.99  cnf(c_10,plain,
% 3.68/0.99      ( k2_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1) != o_0_0_xboole_0 ),
% 3.68/0.99      inference(cnf_transformation,[],[f60]) ).
% 3.68/0.99  
% 3.68/0.99  cnf(c_2488,plain,
% 3.68/0.99      ( ~ r2_hidden(X0,o_0_0_xboole_0) ),
% 3.68/0.99      inference(resolution,[status(thm)],[c_9,c_10]) ).
% 3.68/0.99  
% 3.68/0.99  cnf(c_13,negated_conjecture,
% 3.68/0.99      ( o_0_0_xboole_0 = k2_zfmisc_1(sK6,sK7)
% 3.68/0.99      | o_0_0_xboole_0 = sK6
% 3.68/0.99      | o_0_0_xboole_0 = sK7 ),
% 3.68/0.99      inference(cnf_transformation,[],[f63]) ).
% 3.68/0.99  
% 3.68/0.99  cnf(c_668,plain,
% 3.68/0.99      ( X0 != k2_zfmisc_1(sK6,sK7)
% 3.68/0.99      | o_0_0_xboole_0 = X0
% 3.68/0.99      | o_0_0_xboole_0 = sK6
% 3.68/0.99      | o_0_0_xboole_0 = sK7 ),
% 3.68/0.99      inference(resolution,[status(thm)],[c_129,c_13]) ).
% 3.68/0.99  
% 3.68/0.99  cnf(c_4,plain,
% 3.68/0.99      ( r2_hidden(sK2(X0,X1,X2),X0)
% 3.68/0.99      | r2_hidden(sK1(X0,X1,X2),X2)
% 3.68/0.99      | k2_zfmisc_1(X0,X1) = X2 ),
% 3.68/0.99      inference(cnf_transformation,[],[f43]) ).
% 3.68/0.99  
% 3.68/0.99  cnf(c_1014,plain,
% 3.68/0.99      ( r2_hidden(sK2(X0,X1,k2_zfmisc_1(sK6,sK7)),X0)
% 3.68/0.99      | r2_hidden(sK1(X0,X1,k2_zfmisc_1(sK6,sK7)),k2_zfmisc_1(sK6,sK7))
% 3.68/0.99      | o_0_0_xboole_0 = k2_zfmisc_1(X0,X1)
% 3.68/0.99      | o_0_0_xboole_0 = sK6
% 3.68/0.99      | o_0_0_xboole_0 = sK7 ),
% 3.68/0.99      inference(resolution,[status(thm)],[c_668,c_4]) ).
% 3.68/0.99  
% 3.68/0.99  cnf(c_4155,plain,
% 3.68/0.99      ( r2_hidden(sK1(o_0_0_xboole_0,X0,k2_zfmisc_1(sK6,sK7)),k2_zfmisc_1(sK6,sK7))
% 3.68/0.99      | o_0_0_xboole_0 = k2_zfmisc_1(o_0_0_xboole_0,X0)
% 3.68/0.99      | o_0_0_xboole_0 = sK6
% 3.68/0.99      | o_0_0_xboole_0 = sK7 ),
% 3.68/0.99      inference(resolution,[status(thm)],[c_2488,c_1014]) ).
% 3.68/0.99  
% 3.68/0.99  cnf(c_139,plain,
% 3.68/0.99      ( o_0_0_xboole_0 = o_0_0_xboole_0 ),
% 3.68/0.99      inference(instantiation,[status(thm)],[c_128]) ).
% 3.68/0.99  
% 3.68/0.99  cnf(c_435,plain,
% 3.68/0.99      ( sK7 != X0 | o_0_0_xboole_0 != X0 | o_0_0_xboole_0 = sK7 ),
% 3.68/0.99      inference(instantiation,[status(thm)],[c_129]) ).
% 3.68/0.99  
% 3.68/0.99  cnf(c_436,plain,
% 3.68/0.99      ( sK7 != o_0_0_xboole_0
% 3.68/0.99      | o_0_0_xboole_0 = sK7
% 3.68/0.99      | o_0_0_xboole_0 != o_0_0_xboole_0 ),
% 3.68/0.99      inference(instantiation,[status(thm)],[c_435]) ).
% 3.68/0.99  
% 3.68/0.99  cnf(c_0,plain,
% 3.68/0.99      ( r2_hidden(sK0(X0),X0) | o_0_0_xboole_0 = X0 ),
% 3.68/0.99      inference(cnf_transformation,[],[f58]) ).
% 3.68/0.99  
% 3.68/0.99  cnf(c_323,plain,
% 3.68/0.99      ( o_0_0_xboole_0 = X0 | r2_hidden(sK0(X0),X0) = iProver_top ),
% 3.68/0.99      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 3.68/0.99  
% 3.68/0.99  cnf(c_5,plain,
% 3.68/0.99      ( ~ r2_hidden(X0,X1)
% 3.68/0.99      | ~ r2_hidden(X2,X3)
% 3.68/0.99      | r2_hidden(k4_tarski(X2,X0),k2_zfmisc_1(X3,X1)) ),
% 3.68/0.99      inference(cnf_transformation,[],[f65]) ).
% 3.68/0.99  
% 3.68/0.99  cnf(c_318,plain,
% 3.68/0.99      ( r2_hidden(X0,X1) != iProver_top
% 3.68/0.99      | r2_hidden(X2,X3) != iProver_top
% 3.68/0.99      | r2_hidden(k4_tarski(X2,X0),k2_zfmisc_1(X3,X1)) = iProver_top ),
% 3.68/0.99      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 3.68/0.99  
% 3.68/0.99  cnf(c_756,plain,
% 3.68/0.99      ( sK6 = o_0_0_xboole_0
% 3.68/0.99      | sK7 = o_0_0_xboole_0
% 3.68/0.99      | r2_hidden(X0,sK6) != iProver_top
% 3.68/0.99      | r2_hidden(X1,sK7) != iProver_top
% 3.68/0.99      | r2_hidden(k4_tarski(X0,X1),o_0_0_xboole_0) = iProver_top ),
% 3.68/0.99      inference(superposition,[status(thm)],[c_13,c_318]) ).
% 3.68/0.99  
% 3.68/0.99  cnf(c_7,plain,
% 3.68/0.99      ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) | r2_hidden(sK5(X1,X2,X0),X2) ),
% 3.68/0.99      inference(cnf_transformation,[],[f67]) ).
% 3.68/0.99  
% 3.68/0.99  cnf(c_316,plain,
% 3.68/0.99      ( r2_hidden(X0,k2_zfmisc_1(X1,X2)) != iProver_top
% 3.68/0.99      | r2_hidden(sK5(X1,X2,X0),X2) = iProver_top ),
% 3.68/0.99      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 3.68/0.99  
% 3.68/0.99  cnf(c_314,plain,
% 3.68/0.99      ( k2_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1) = X1
% 3.68/0.99      | r2_hidden(X0,X1) != iProver_top ),
% 3.68/0.99      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 3.68/0.99  
% 3.68/0.99  cnf(c_603,plain,
% 3.68/0.99      ( k2_xboole_0(k6_enumset1(sK5(X0,X1,X2),sK5(X0,X1,X2),sK5(X0,X1,X2),sK5(X0,X1,X2),sK5(X0,X1,X2),sK5(X0,X1,X2),sK5(X0,X1,X2),sK5(X0,X1,X2)),X1) = X1
% 3.68/0.99      | r2_hidden(X2,k2_zfmisc_1(X0,X1)) != iProver_top ),
% 3.68/0.99      inference(superposition,[status(thm)],[c_316,c_314]) ).
% 3.68/0.99  
% 3.68/0.99  cnf(c_3511,plain,
% 3.68/0.99      ( k2_xboole_0(k6_enumset1(sK5(sK6,sK7,X0),sK5(sK6,sK7,X0),sK5(sK6,sK7,X0),sK5(sK6,sK7,X0),sK5(sK6,sK7,X0),sK5(sK6,sK7,X0),sK5(sK6,sK7,X0),sK5(sK6,sK7,X0)),sK7) = sK7
% 3.68/0.99      | sK6 = o_0_0_xboole_0
% 3.68/0.99      | sK7 = o_0_0_xboole_0
% 3.68/0.99      | r2_hidden(X0,o_0_0_xboole_0) != iProver_top ),
% 3.68/0.99      inference(superposition,[status(thm)],[c_13,c_603]) ).
% 3.68/0.99  
% 3.68/0.99  cnf(c_2489,plain,
% 3.68/0.99      ( r2_hidden(X0,o_0_0_xboole_0) != iProver_top ),
% 3.68/0.99      inference(predicate_to_equality,[status(thm)],[c_2488]) ).
% 3.68/0.99  
% 3.68/0.99  cnf(c_3837,plain,
% 3.68/0.99      ( r2_hidden(X0,o_0_0_xboole_0) != iProver_top ),
% 3.68/0.99      inference(global_propositional_subsumption,[status(thm)],[c_3511,c_2489]) ).
% 3.68/0.99  
% 3.68/0.99  cnf(c_3850,plain,
% 3.68/0.99      ( sK6 = o_0_0_xboole_0
% 3.68/0.99      | sK7 = o_0_0_xboole_0
% 3.68/0.99      | r2_hidden(X0,sK6) != iProver_top
% 3.68/0.99      | r2_hidden(X1,sK7) != iProver_top ),
% 3.68/0.99      inference(superposition,[status(thm)],[c_756,c_3837]) ).
% 3.68/0.99  
% 3.68/0.99  cnf(c_5060,plain,
% 3.68/0.99      ( sK6 = o_0_0_xboole_0
% 3.68/0.99      | sK7 = o_0_0_xboole_0
% 3.68/0.99      | r2_hidden(X0,sK6) != iProver_top ),
% 3.68/0.99      inference(superposition,[status(thm)],[c_323,c_3850]) ).
% 3.68/0.99  
% 3.68/0.99  cnf(c_595,plain,
% 3.68/0.99      ( X0 != X1 | sK7 != X1 | sK7 = X0 ),
% 3.68/0.99      inference(instantiation,[status(thm)],[c_129]) ).
% 3.68/0.99  
% 3.68/0.99  cnf(c_1378,plain,
% 3.68/0.99      ( X0 != sK7 | sK7 = X0 | sK7 != sK7 ),
% 3.68/0.99      inference(instantiation,[status(thm)],[c_595]) ).
% 3.68/0.99  
% 3.68/0.99  cnf(c_1380,plain,
% 3.68/0.99      ( sK7 != sK7 | sK7 = o_0_0_xboole_0 | o_0_0_xboole_0 != sK7 ),
% 3.68/0.99      inference(instantiation,[status(thm)],[c_1378]) ).
% 3.68/0.99  
% 3.68/0.99  cnf(c_1379,plain,
% 3.68/0.99      ( sK7 = sK7 ),
% 3.68/0.99      inference(instantiation,[status(thm)],[c_128]) ).
% 3.68/0.99  
% 3.68/0.99  cnf(c_597,plain,
% 3.68/0.99      ( X0 != X1 | sK6 != X1 | sK6 = X0 ),
% 3.68/0.99      inference(instantiation,[status(thm)],[c_129]) ).
% 3.68/0.99  
% 3.68/0.99  cnf(c_1382,plain,
% 3.68/0.99      ( X0 != sK6 | sK6 = X0 | sK6 != sK6 ),
% 3.68/0.99      inference(instantiation,[status(thm)],[c_597]) ).
% 3.68/0.99  
% 3.68/0.99  cnf(c_1384,plain,
% 3.68/0.99      ( sK6 != sK6 | sK6 = o_0_0_xboole_0 | o_0_0_xboole_0 != sK6 ),
% 3.68/0.99      inference(instantiation,[status(thm)],[c_1382]) ).
% 3.68/0.99  
% 3.68/0.99  cnf(c_1383,plain,
% 3.68/0.99      ( sK6 = sK6 ),
% 3.68/0.99      inference(instantiation,[status(thm)],[c_128]) ).
% 3.68/0.99  
% 3.68/0.99  cnf(c_130,plain,
% 3.68/0.99      ( ~ r2_hidden(X0,X1) | r2_hidden(X2,X3) | X2 != X0 | X3 != X1 ),
% 3.68/0.99      theory(equality) ).
% 3.68/0.99  
% 3.68/0.99  cnf(c_826,plain,
% 3.68/0.99      ( ~ r2_hidden(X0,k2_zfmisc_1(sK6,sK7))
% 3.68/0.99      | r2_hidden(X1,o_0_0_xboole_0)
% 3.68/0.99      | X1 != X0
% 3.68/0.99      | o_0_0_xboole_0 = sK6
% 3.68/0.99      | o_0_0_xboole_0 = sK7 ),
% 3.68/0.99      inference(resolution,[status(thm)],[c_130,c_13]) ).
% 3.68/0.99  
% 3.68/0.99  cnf(c_1287,plain,
% 3.68/0.99      ( ~ r2_hidden(X0,sK6)
% 3.68/0.99      | ~ r2_hidden(X1,sK7)
% 3.68/0.99      | r2_hidden(X2,o_0_0_xboole_0)
% 3.68/0.99      | X2 != k4_tarski(X0,X1)
% 3.68/0.99      | o_0_0_xboole_0 = sK6
% 3.68/0.99      | o_0_0_xboole_0 = sK7 ),
% 3.68/0.99      inference(resolution,[status(thm)],[c_826,c_5]) ).
% 3.68/0.99  
% 3.68/0.99  cnf(c_4034,plain,
% 3.68/0.99      ( ~ r2_hidden(X0,sK6)
% 3.68/0.99      | ~ r2_hidden(X1,sK7)
% 3.68/0.99      | X2 != k4_tarski(X0,X1)
% 3.68/0.99      | o_0_0_xboole_0 = sK6
% 3.68/0.99      | o_0_0_xboole_0 = sK7 ),
% 3.68/0.99      inference(backward_subsumption_resolution,[status(thm)],[c_2488,c_1287]) ).
% 3.68/0.99  
% 3.68/0.99  cnf(c_437,plain,
% 3.68/0.99      ( sK6 != X0 | o_0_0_xboole_0 != X0 | o_0_0_xboole_0 = sK6 ),
% 3.68/0.99      inference(instantiation,[status(thm)],[c_129]) ).
% 3.68/0.99  
% 3.68/0.99  cnf(c_438,plain,
% 3.68/0.99      ( sK6 != o_0_0_xboole_0
% 3.68/0.99      | o_0_0_xboole_0 = sK6
% 3.68/0.99      | o_0_0_xboole_0 != o_0_0_xboole_0 ),
% 3.68/0.99      inference(instantiation,[status(thm)],[c_437]) ).
% 3.68/0.99  
% 3.68/0.99  cnf(c_5200,plain,
% 3.68/0.99      ( ~ r2_hidden(X0,sK6) | sK6 = o_0_0_xboole_0 | sK7 = o_0_0_xboole_0 ),
% 3.68/0.99      inference(predicate_to_equality_rev,[status(thm)],[c_5060]) ).
% 3.68/0.99  
% 3.68/0.99  cnf(c_5470,plain,
% 3.68/0.99      ( ~ r2_hidden(X0,sK6) | o_0_0_xboole_0 = sK6 | o_0_0_xboole_0 = sK7 ),
% 3.68/0.99      inference(global_propositional_subsumption,
% 3.68/0.99                [status(thm)],
% 3.68/0.99                [c_4034,c_139,c_436,c_438,c_5200]) ).
% 3.68/0.99  
% 3.68/0.99  cnf(c_5492,plain,
% 3.68/0.99      ( o_0_0_xboole_0 = sK6 | o_0_0_xboole_0 = sK7 ),
% 3.68/0.99      inference(resolution,[status(thm)],[c_5470,c_0]) ).
% 3.68/0.99  
% 3.68/0.99  cnf(c_5501,plain,
% 3.68/0.99      ( sK7 = o_0_0_xboole_0 | sK6 = o_0_0_xboole_0 ),
% 3.68/0.99      inference(global_propositional_subsumption,
% 3.68/0.99                [status(thm)],
% 3.68/0.99                [c_5060,c_1380,c_1379,c_1384,c_1383,c_5492]) ).
% 3.68/0.99  
% 3.68/0.99  cnf(c_5502,plain,
% 3.68/0.99      ( sK6 = o_0_0_xboole_0 | sK7 = o_0_0_xboole_0 ),
% 3.68/0.99      inference(renaming,[status(thm)],[c_5501]) ).
% 3.68/0.99  
% 3.68/0.99  cnf(c_12,negated_conjecture,
% 3.68/0.99      ( o_0_0_xboole_0 != k2_zfmisc_1(sK6,sK7) | o_0_0_xboole_0 != sK6 ),
% 3.68/0.99      inference(cnf_transformation,[],[f62]) ).
% 3.68/0.99  
% 3.68/0.99  cnf(c_5516,plain,
% 3.68/0.99      ( k2_zfmisc_1(o_0_0_xboole_0,sK7) != o_0_0_xboole_0
% 3.68/0.99      | sK6 != o_0_0_xboole_0
% 3.68/0.99      | sK7 = o_0_0_xboole_0 ),
% 3.68/0.99      inference(superposition,[status(thm)],[c_5502,c_12]) ).
% 3.68/0.99  
% 3.68/0.99  cnf(c_5521,plain,
% 3.68/0.99      ( k2_zfmisc_1(o_0_0_xboole_0,sK7) != o_0_0_xboole_0
% 3.68/0.99      | sK7 = o_0_0_xboole_0 ),
% 3.68/0.99      inference(forward_subsumption_resolution,[status(thm)],[c_5516,c_5502]) ).
% 3.68/0.99  
% 3.68/0.99  cnf(c_8,plain,
% 3.68/0.99      ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) | r2_hidden(sK4(X1,X2,X0),X1) ),
% 3.68/0.99      inference(cnf_transformation,[],[f68]) ).
% 3.68/0.99  
% 3.68/0.99  cnf(c_315,plain,
% 3.68/0.99      ( r2_hidden(X0,k2_zfmisc_1(X1,X2)) != iProver_top
% 3.68/0.99      | r2_hidden(sK4(X1,X2,X0),X1) = iProver_top ),
% 3.68/0.99      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 3.68/0.99  
% 3.68/0.99  cnf(c_3849,plain,
% 3.68/0.99      ( r2_hidden(X0,k2_zfmisc_1(o_0_0_xboole_0,X1)) != iProver_top ),
% 3.68/0.99      inference(superposition,[status(thm)],[c_315,c_3837]) ).
% 3.68/0.99  
% 3.68/0.99  cnf(c_4495,plain,
% 3.68/0.99      ( k2_zfmisc_1(o_0_0_xboole_0,X0) = o_0_0_xboole_0 ),
% 3.68/0.99      inference(superposition,[status(thm)],[c_323,c_3849]) ).
% 3.68/0.99  
% 3.68/0.99  cnf(c_5522,plain,
% 3.68/0.99      ( sK7 = o_0_0_xboole_0 | o_0_0_xboole_0 != o_0_0_xboole_0 ),
% 3.68/0.99      inference(demodulation,[status(thm)],[c_5521,c_4495]) ).
% 3.68/0.99  
% 3.68/0.99  cnf(c_5523,plain,
% 3.68/0.99      ( sK7 = o_0_0_xboole_0 ),
% 3.68/0.99      inference(equality_resolution_simp,[status(thm)],[c_5522]) ).
% 3.68/0.99  
% 3.68/0.99  cnf(c_5657,plain,
% 3.68/0.99      ( o_0_0_xboole_0 = sK7 ),
% 3.68/0.99      inference(global_propositional_subsumption,
% 3.68/0.99                [status(thm)],
% 3.68/0.99                [c_4155,c_139,c_436,c_5523]) ).
% 3.68/0.99  
% 3.68/0.99  cnf(c_11,negated_conjecture,
% 3.68/0.99      ( o_0_0_xboole_0 != k2_zfmisc_1(sK6,sK7) | o_0_0_xboole_0 != sK7 ),
% 3.68/0.99      inference(cnf_transformation,[],[f61]) ).
% 3.68/0.99  
% 3.68/0.99  cnf(c_5663,plain,
% 3.68/0.99      ( o_0_0_xboole_0 != k2_zfmisc_1(sK6,sK7) ),
% 3.68/0.99      inference(backward_subsumption_resolution,[status(thm)],[c_5657,c_11]) ).
% 3.68/0.99  
% 3.68/0.99  cnf(c_9668,plain,
% 3.68/0.99      ( r2_hidden(sK3(sK6,sK7,o_0_0_xboole_0),sK7)
% 3.68/0.99      | r2_hidden(sK1(sK6,sK7,o_0_0_xboole_0),o_0_0_xboole_0) ),
% 3.68/0.99      inference(resolution,[status(thm)],[c_4347,c_5663]) ).
% 3.68/0.99  
% 3.68/0.99  cnf(c_2492,plain,
% 3.68/0.99      ( ~ r2_hidden(X0,X1)
% 3.68/0.99      | X2 != X1
% 3.68/0.99      | k2_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1) = X2 ),
% 3.68/0.99      inference(resolution,[status(thm)],[c_9,c_129]) ).
% 3.68/0.99  
% 3.68/0.99  cnf(c_6963,plain,
% 3.68/0.99      ( ~ r2_hidden(X0,X1) | o_0_0_xboole_0 != X1 ),
% 3.68/0.99      inference(resolution,[status(thm)],[c_2492,c_10]) ).
% 3.68/0.99  
% 3.68/0.99  cnf(c_8850,plain,
% 3.68/0.99      ( ~ r2_hidden(X0,sK7) ),
% 3.68/0.99      inference(resolution,[status(thm)],[c_6963,c_5657]) ).
% 3.68/0.99  
% 3.68/0.99  cnf(c_10001,plain,
% 3.68/0.99      ( $false ),
% 3.68/0.99      inference(forward_subsumption_resolution,
% 3.68/0.99                [status(thm)],
% 3.68/0.99                [c_9668,c_2488,c_8850]) ).
% 3.68/0.99  
% 3.68/0.99  
% 3.68/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 3.68/0.99  
% 3.68/0.99  ------                               Statistics
% 3.68/0.99  
% 3.68/0.99  ------ Selected
% 3.68/0.99  
% 3.68/0.99  total_time:                             0.297
% 3.68/0.99  
%------------------------------------------------------------------------------
