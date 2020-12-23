%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:37:51 EST 2020

% Result     : Theorem 10.77s
% Output     : CNFRefutation 10.77s
% Verified   : 
% Statistics : Number of formulae       :  140 ( 427 expanded)
%              Number of clauses        :   89 ( 140 expanded)
%              Number of leaves         :   16 (  99 expanded)
%              Depth                    :   18
%              Number of atoms          :  455 (1871 expanded)
%              Number of equality atoms :  178 ( 533 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal clause size      :   18 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f7,conjecture,(
    ! [X0,X1,X2,X3] :
      ( r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3))
     => ( ( r1_tarski(X1,X3)
          & r1_tarski(X0,X2) )
        | k1_xboole_0 = k2_zfmisc_1(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f8,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3))
       => ( ( r1_tarski(X1,X3)
            & r1_tarski(X0,X2) )
          | k1_xboole_0 = k2_zfmisc_1(X0,X1) ) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f12,plain,(
    ? [X0,X1,X2,X3] :
      ( ( ~ r1_tarski(X1,X3)
        | ~ r1_tarski(X0,X2) )
      & k1_xboole_0 != k2_zfmisc_1(X0,X1)
      & r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f13,plain,(
    ? [X0,X1,X2,X3] :
      ( ( ~ r1_tarski(X1,X3)
        | ~ r1_tarski(X0,X2) )
      & k1_xboole_0 != k2_zfmisc_1(X0,X1)
      & r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)) ) ),
    inference(flattening,[],[f12])).

fof(f30,plain,
    ( ? [X0,X1,X2,X3] :
        ( ( ~ r1_tarski(X1,X3)
          | ~ r1_tarski(X0,X2) )
        & k1_xboole_0 != k2_zfmisc_1(X0,X1)
        & r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)) )
   => ( ( ~ r1_tarski(sK8,sK10)
        | ~ r1_tarski(sK7,sK9) )
      & k1_xboole_0 != k2_zfmisc_1(sK7,sK8)
      & r1_tarski(k2_zfmisc_1(sK7,sK8),k2_zfmisc_1(sK9,sK10)) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,
    ( ( ~ r1_tarski(sK8,sK10)
      | ~ r1_tarski(sK7,sK9) )
    & k1_xboole_0 != k2_zfmisc_1(sK7,sK8)
    & r1_tarski(k2_zfmisc_1(sK7,sK8),k2_zfmisc_1(sK9,sK10)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7,sK8,sK9,sK10])],[f13,f30])).

fof(f53,plain,(
    r1_tarski(k2_zfmisc_1(sK7,sK8),k2_zfmisc_1(sK9,sK10)) ),
    inference(cnf_transformation,[],[f31])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( k2_zfmisc_1(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ? [X4,X5] :
              ( k4_tarski(X4,X5) = X3
              & r2_hidden(X5,X1)
              & r2_hidden(X4,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

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
    inference(nnf_transformation,[],[f4])).

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
     => ( k4_tarski(sK5(X0,X1,X8),sK6(X0,X1,X8)) = X8
        & r2_hidden(sK6(X0,X1,X8),X1)
        & r2_hidden(sK5(X0,X1,X8),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X6,X7] :
          ( k4_tarski(X6,X7) = X3
          & r2_hidden(X7,X1)
          & r2_hidden(X6,X0) )
     => ( k4_tarski(sK3(X0,X1,X2),sK4(X0,X1,X2)) = X3
        & r2_hidden(sK4(X0,X1,X2),X1)
        & r2_hidden(sK3(X0,X1,X2),X0) ) ) ),
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

fof(f25,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5,sK6])],[f21,f24,f23,f22])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( k2_zfmisc_1(X0,X1) = X2
      | r2_hidden(sK3(X0,X1,X2),X0)
      | r2_hidden(sK2(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
    <=> ( r2_hidden(X1,X3)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
        | ~ r2_hidden(X1,X3)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X3)
          & r2_hidden(X0,X2) )
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f27,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
        | ~ r2_hidden(X1,X3)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X3)
          & r2_hidden(X0,X2) )
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ) ),
    inference(flattening,[],[f26])).

fof(f48,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X1,X3)
      | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f10,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f14,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f10])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f14])).

fof(f16,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK0(X0,X1),X1)
          & r2_hidden(sK0(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f15,f16])).

fof(f32,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f49,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
      | ~ r2_hidden(X1,X3)
      | ~ r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f54,plain,(
    k1_xboole_0 != k2_zfmisc_1(sK7,sK8) ),
    inference(cnf_transformation,[],[f31])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f28])).

fof(f50,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f51,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f29])).

fof(f62,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f51])).

fof(f3,axiom,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f3])).

fof(f34,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK0(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f33,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK0(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f17])).

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

fof(f9,plain,(
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

fof(f11,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f18,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
     => ( r2_hidden(sK1(X0,X1),X1)
        & r2_hidden(sK1(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ( r2_hidden(sK1(X0,X1),X1)
          & r2_hidden(sK1(X0,X1),X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f11,f18])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( k2_zfmisc_1(X0,X1) = X2
      | r2_hidden(sK4(X0,X1,X2),X1)
      | r2_hidden(sK2(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f40,plain,(
    ! [X2,X0,X8,X1] :
      ( r2_hidden(sK6(X0,X1,X8),X1)
      | ~ r2_hidden(X8,X2)
      | k2_zfmisc_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f59,plain,(
    ! [X0,X8,X1] :
      ( r2_hidden(sK6(X0,X1,X8),X1)
      | ~ r2_hidden(X8,k2_zfmisc_1(X0,X1)) ) ),
    inference(equality_resolution,[],[f40])).

fof(f52,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f29])).

fof(f61,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f52])).

fof(f47,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X0,X2)
      | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f55,plain,
    ( ~ r1_tarski(sK8,sK10)
    | ~ r1_tarski(sK7,sK9) ),
    inference(cnf_transformation,[],[f31])).

cnf(c_444,plain,
    ( X0 != X1
    | X2 != X3
    | k2_zfmisc_1(X0,X2) = k2_zfmisc_1(X1,X3) ),
    theory(equality)).

cnf(c_441,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_5051,plain,
    ( ~ r1_tarski(X0,k2_zfmisc_1(X1,X2))
    | r1_tarski(X3,k2_zfmisc_1(X4,X5))
    | X3 != X0
    | X4 != X1
    | X5 != X2 ),
    inference(resolution,[status(thm)],[c_444,c_441])).

cnf(c_23,negated_conjecture,
    ( r1_tarski(k2_zfmisc_1(sK7,sK8),k2_zfmisc_1(sK9,sK10)) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_31643,plain,
    ( r1_tarski(X0,k2_zfmisc_1(X1,X2))
    | X0 != k2_zfmisc_1(sK7,sK8)
    | X1 != sK9
    | X2 != sK10 ),
    inference(resolution,[status(thm)],[c_5051,c_23])).

cnf(c_10,plain,
    ( r2_hidden(sK3(X0,X1,X2),X0)
    | r2_hidden(sK2(X0,X1,X2),X2)
    | k2_zfmisc_1(X0,X1) = X2 ),
    inference(cnf_transformation,[],[f43])).

cnf(c_16,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(k4_tarski(X2,X0),k2_zfmisc_1(X3,X1)) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_2,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | ~ r1_tarski(X1,X2) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_1141,plain,
    ( r2_hidden(X0,k2_zfmisc_1(sK9,sK10))
    | ~ r2_hidden(X0,k2_zfmisc_1(sK7,sK8)) ),
    inference(resolution,[status(thm)],[c_2,c_23])).

cnf(c_1285,plain,
    ( r2_hidden(X0,sK10)
    | ~ r2_hidden(k4_tarski(X1,X0),k2_zfmisc_1(sK7,sK8)) ),
    inference(resolution,[status(thm)],[c_16,c_1141])).

cnf(c_15,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X2,X3)
    | r2_hidden(k4_tarski(X2,X0),k2_zfmisc_1(X3,X1)) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_2445,plain,
    ( ~ r2_hidden(X0,sK7)
    | r2_hidden(X1,sK10)
    | ~ r2_hidden(X1,sK8) ),
    inference(resolution,[status(thm)],[c_1285,c_15])).

cnf(c_3544,plain,
    ( r2_hidden(X0,sK10)
    | ~ r2_hidden(X0,sK8)
    | r2_hidden(sK2(sK7,X1,X2),X2)
    | k2_zfmisc_1(sK7,X1) = X2 ),
    inference(resolution,[status(thm)],[c_10,c_2445])).

cnf(c_32828,plain,
    ( r2_hidden(X0,sK10)
    | ~ r2_hidden(X0,sK8)
    | r2_hidden(sK2(sK7,X1,k2_zfmisc_1(sK7,sK8)),k2_zfmisc_1(sK7,sK8))
    | r1_tarski(k2_zfmisc_1(sK7,X1),k2_zfmisc_1(X2,X3))
    | X2 != sK9
    | X3 != sK10 ),
    inference(resolution,[status(thm)],[c_31643,c_3544])).

cnf(c_22,negated_conjecture,
    ( k1_xboole_0 != k2_zfmisc_1(sK7,sK8) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_20,plain,
    ( k2_zfmisc_1(X0,X1) != k1_xboole_0
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f50])).

cnf(c_26,plain,
    ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) != k1_xboole_0
    | k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_20])).

cnf(c_19,plain,
    ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f62])).

cnf(c_27,plain,
    ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_19])).

cnf(c_6,plain,
    ( r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_50,plain,
    ( r1_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_440,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_989,plain,
    ( k2_zfmisc_1(sK7,sK8) != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = k2_zfmisc_1(sK7,sK8) ),
    inference(instantiation,[status(thm)],[c_440])).

cnf(c_990,plain,
    ( k2_zfmisc_1(sK7,sK8) != k1_xboole_0
    | k1_xboole_0 = k2_zfmisc_1(sK7,sK8)
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_989])).

cnf(c_0,plain,
    ( ~ r2_hidden(sK0(X0,X1),X1)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_1,plain,
    ( r2_hidden(sK0(X0,X1),X0)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_1019,plain,
    ( r1_tarski(X0,X0) ),
    inference(resolution,[status(thm)],[c_0,c_1])).

cnf(c_1021,plain,
    ( r1_tarski(k1_xboole_0,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_1019])).

cnf(c_1055,plain,
    ( r2_hidden(sK3(sK7,sK8,X0),sK7)
    | r2_hidden(sK2(sK7,sK8,X0),X0)
    | k2_zfmisc_1(sK7,sK8) = X0 ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_1062,plain,
    ( r2_hidden(sK3(sK7,sK8,k1_xboole_0),sK7)
    | r2_hidden(sK2(sK7,sK8,k1_xboole_0),k1_xboole_0)
    | k2_zfmisc_1(sK7,sK8) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1055])).

cnf(c_3,plain,
    ( ~ r1_xboole_0(X0,X1)
    | ~ r2_hidden(X2,X1)
    | ~ r2_hidden(X2,X0) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_1296,plain,
    ( ~ r1_xboole_0(X0,X1)
    | ~ r2_hidden(sK2(sK7,sK8,X0),X0)
    | ~ r2_hidden(sK2(sK7,sK8,X0),X1) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_1298,plain,
    ( ~ r1_xboole_0(k1_xboole_0,k1_xboole_0)
    | ~ r2_hidden(sK2(sK7,sK8,k1_xboole_0),k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_1296])).

cnf(c_1650,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(sK7,X2)
    | X2 != X1
    | sK7 != X0 ),
    inference(instantiation,[status(thm)],[c_441])).

cnf(c_1652,plain,
    ( r1_tarski(sK7,k1_xboole_0)
    | ~ r1_tarski(k1_xboole_0,k1_xboole_0)
    | sK7 != k1_xboole_0
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1650])).

cnf(c_1658,plain,
    ( ~ r1_xboole_0(sK7,X0)
    | ~ r2_hidden(sK3(sK7,sK8,X1),X0)
    | ~ r2_hidden(sK3(sK7,sK8,X1),sK7) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_1660,plain,
    ( ~ r1_xboole_0(sK7,k1_xboole_0)
    | ~ r2_hidden(sK3(sK7,sK8,k1_xboole_0),sK7)
    | ~ r2_hidden(sK3(sK7,sK8,k1_xboole_0),k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_1658])).

cnf(c_1666,plain,
    ( r2_hidden(sK3(sK7,sK8,X0),X1)
    | ~ r2_hidden(sK3(sK7,sK8,X0),sK7)
    | ~ r1_tarski(sK7,X1) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_1668,plain,
    ( ~ r2_hidden(sK3(sK7,sK8,k1_xboole_0),sK7)
    | r2_hidden(sK3(sK7,sK8,k1_xboole_0),k1_xboole_0)
    | ~ r1_tarski(sK7,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_1666])).

cnf(c_3566,plain,
    ( r1_xboole_0(sK7,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_9,plain,
    ( r2_hidden(sK4(X0,X1,X2),X1)
    | r2_hidden(sK2(X0,X1,X2),X2)
    | k2_zfmisc_1(X0,X1) = X2 ),
    inference(cnf_transformation,[],[f44])).

cnf(c_809,plain,
    ( k2_zfmisc_1(X0,X1) = X2
    | r2_hidden(sK4(X0,X1,X2),X1) = iProver_top
    | r2_hidden(sK2(X0,X1,X2),X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_13,plain,
    ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
    | r2_hidden(sK6(X1,X2,X0),X2) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_805,plain,
    ( r2_hidden(X0,k2_zfmisc_1(X1,X2)) != iProver_top
    | r2_hidden(sK6(X1,X2,X0),X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_812,plain,
    ( r1_xboole_0(X0,k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_815,plain,
    ( r1_xboole_0(X0,X1) != iProver_top
    | r2_hidden(X2,X1) != iProver_top
    | r2_hidden(X2,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_2199,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_812,c_815])).

cnf(c_2477,plain,
    ( r2_hidden(X0,k2_zfmisc_1(X1,X2)) != iProver_top
    | r2_hidden(sK6(X1,X2,X0),k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_805,c_2199])).

cnf(c_2672,plain,
    ( r2_hidden(X0,k2_zfmisc_1(X1,k1_xboole_0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_805,c_2477])).

cnf(c_18,plain,
    ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f61])).

cnf(c_2673,plain,
    ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2672,c_18])).

cnf(c_3085,plain,
    ( k2_zfmisc_1(X0,k1_xboole_0) = X1
    | r2_hidden(sK2(X0,k1_xboole_0,X1),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_809,c_2673])).

cnf(c_3104,plain,
    ( k1_xboole_0 = X0
    | r2_hidden(sK2(X1,k1_xboole_0,X0),X0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_3085,c_18])).

cnf(c_800,plain,
    ( r1_tarski(k2_zfmisc_1(sK7,sK8),k2_zfmisc_1(sK9,sK10)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_807,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X2,X3) != iProver_top
    | r2_hidden(k4_tarski(X2,X0),k2_zfmisc_1(X3,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_816,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,X2) = iProver_top
    | r1_tarski(X1,X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_2048,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X2,X3) != iProver_top
    | r2_hidden(k4_tarski(X2,X0),X4) = iProver_top
    | r1_tarski(k2_zfmisc_1(X3,X1),X4) != iProver_top ),
    inference(superposition,[status(thm)],[c_807,c_816])).

cnf(c_30547,plain,
    ( r2_hidden(X0,sK7) != iProver_top
    | r2_hidden(X1,sK8) != iProver_top
    | r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(sK9,sK10)) = iProver_top ),
    inference(superposition,[status(thm)],[c_800,c_2048])).

cnf(c_803,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r2_hidden(k4_tarski(X2,X0),k2_zfmisc_1(X3,X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_33531,plain,
    ( r2_hidden(X0,sK7) != iProver_top
    | r2_hidden(X1,sK10) = iProver_top
    | r2_hidden(X1,sK8) != iProver_top ),
    inference(superposition,[status(thm)],[c_30547,c_803])).

cnf(c_33626,plain,
    ( sK7 = k1_xboole_0
    | r2_hidden(X0,sK10) = iProver_top
    | r2_hidden(X0,sK8) != iProver_top ),
    inference(superposition,[status(thm)],[c_3104,c_33531])).

cnf(c_33802,plain,
    ( r2_hidden(X0,sK10)
    | ~ r2_hidden(X0,sK8)
    | sK7 = k1_xboole_0 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_33626])).

cnf(c_35295,plain,
    ( r2_hidden(X0,sK10)
    | ~ r2_hidden(X0,sK8) ),
    inference(global_propositional_subsumption,[status(thm)],[c_32828,c_22,c_26,c_27,c_50,c_990,c_1021,c_1062,c_1298,c_1652,c_1660,c_1668,c_3566,c_33802])).

cnf(c_35313,plain,
    ( ~ r2_hidden(sK0(X0,sK10),sK8)
    | r1_tarski(X0,sK10) ),
    inference(resolution,[status(thm)],[c_35295,c_0])).

cnf(c_37363,plain,
    ( r1_tarski(sK8,sK10) ),
    inference(resolution,[status(thm)],[c_35313,c_1])).

cnf(c_817,plain,
    ( r2_hidden(sK0(X0,X1),X0) = iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_17,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(k4_tarski(X0,X2),k2_zfmisc_1(X1,X3)) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_802,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r2_hidden(k4_tarski(X0,X2),k2_zfmisc_1(X1,X3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_33534,plain,
    ( r2_hidden(X0,sK9) = iProver_top
    | r2_hidden(X0,sK7) != iProver_top
    | r2_hidden(X1,sK8) != iProver_top ),
    inference(superposition,[status(thm)],[c_30547,c_802])).

cnf(c_49,plain,
    ( r1_xboole_0(X0,k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_51,plain,
    ( r1_xboole_0(k1_xboole_0,k1_xboole_0) = iProver_top ),
    inference(instantiation,[status(thm)],[c_49])).

cnf(c_1297,plain,
    ( r1_xboole_0(X0,X1) != iProver_top
    | r2_hidden(sK2(sK7,sK8,X0),X0) != iProver_top
    | r2_hidden(sK2(sK7,sK8,X0),X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1296])).

cnf(c_1299,plain,
    ( r1_xboole_0(k1_xboole_0,k1_xboole_0) != iProver_top
    | r2_hidden(sK2(sK7,sK8,k1_xboole_0),k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1297])).

cnf(c_2283,plain,
    ( X0 != k1_xboole_0
    | k2_zfmisc_1(X1,k1_xboole_0) = X0 ),
    inference(resolution,[status(thm)],[c_440,c_18])).

cnf(c_32832,plain,
    ( r1_tarski(k2_zfmisc_1(X0,k1_xboole_0),k2_zfmisc_1(X1,X2))
    | X1 != sK9
    | X2 != sK10
    | k2_zfmisc_1(sK7,sK8) != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_31643,c_2283])).

cnf(c_33826,plain,
    ( k2_zfmisc_1(sK7,sK8) != k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_32832,c_22,c_26,c_27,c_990])).

cnf(c_1409,plain,
    ( r2_hidden(X0,sK9)
    | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(sK7,sK8)) ),
    inference(resolution,[status(thm)],[c_17,c_1141])).

cnf(c_2454,plain,
    ( r2_hidden(X0,sK9)
    | ~ r2_hidden(X0,sK7)
    | ~ r2_hidden(X1,sK8) ),
    inference(resolution,[status(thm)],[c_1409,c_15])).

cnf(c_3500,plain,
    ( r2_hidden(X0,sK9)
    | ~ r2_hidden(X0,sK7)
    | r2_hidden(sK2(X1,sK8,X2),X2)
    | k2_zfmisc_1(X1,sK8) = X2 ),
    inference(resolution,[status(thm)],[c_9,c_2454])).

cnf(c_33840,plain,
    ( r2_hidden(X0,sK9)
    | ~ r2_hidden(X0,sK7)
    | r2_hidden(sK2(sK7,sK8,k1_xboole_0),k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_33826,c_3500])).

cnf(c_33841,plain,
    ( r2_hidden(X0,sK9) = iProver_top
    | r2_hidden(X0,sK7) != iProver_top
    | r2_hidden(sK2(sK7,sK8,k1_xboole_0),k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33840])).

cnf(c_34383,plain,
    ( r2_hidden(X0,sK7) != iProver_top
    | r2_hidden(X0,sK9) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_33534,c_51,c_1299,c_33841])).

cnf(c_34384,plain,
    ( r2_hidden(X0,sK9) = iProver_top
    | r2_hidden(X0,sK7) != iProver_top ),
    inference(renaming,[status(thm)],[c_34383])).

cnf(c_34391,plain,
    ( r2_hidden(sK0(sK7,X0),sK9) = iProver_top
    | r1_tarski(sK7,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_817,c_34384])).

cnf(c_818,plain,
    ( r2_hidden(sK0(X0,X1),X1) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_37258,plain,
    ( r1_tarski(sK7,sK9) = iProver_top ),
    inference(superposition,[status(thm)],[c_34391,c_818])).

cnf(c_37275,plain,
    ( r1_tarski(sK7,sK9) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_37258])).

cnf(c_21,negated_conjecture,
    ( ~ r1_tarski(sK7,sK9)
    | ~ r1_tarski(sK8,sK10) ),
    inference(cnf_transformation,[],[f55])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_37363,c_37275,c_21])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 15:01:54 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 10.77/1.99  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 10.77/1.99  
% 10.77/1.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 10.77/1.99  
% 10.77/1.99  ------  iProver source info
% 10.77/1.99  
% 10.77/1.99  git: date: 2020-06-30 10:37:57 +0100
% 10.77/1.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 10.77/1.99  git: non_committed_changes: false
% 10.77/1.99  git: last_make_outside_of_git: false
% 10.77/1.99  
% 10.77/1.99  ------ 
% 10.77/1.99  ------ Parsing...
% 10.77/1.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 10.77/1.99  
% 10.77/1.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e  sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 10.77/1.99  
% 10.77/1.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 10.77/1.99  
% 10.77/1.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 10.77/1.99  ------ Proving...
% 10.77/1.99  ------ Problem Properties 
% 10.77/1.99  
% 10.77/1.99  
% 10.77/1.99  clauses                                 23
% 10.77/1.99  conjectures                             3
% 10.77/1.99  EPR                                     4
% 10.77/1.99  Horn                                    16
% 10.77/1.99  unary                                   5
% 10.77/1.99  binary                                  10
% 10.77/1.99  lits                                    51
% 10.77/1.99  lits eq                                 13
% 10.77/1.99  fd_pure                                 0
% 10.77/1.99  fd_pseudo                               0
% 10.77/1.99  fd_cond                                 1
% 10.77/1.99  fd_pseudo_cond                          4
% 10.77/1.99  AC symbols                              0
% 10.77/1.99  
% 10.77/1.99  ------ Input Options Time Limit: Unbounded
% 10.77/1.99  
% 10.77/1.99  
% 10.77/1.99  ------ 
% 10.77/1.99  Current options:
% 10.77/1.99  ------ 
% 10.77/1.99  
% 10.77/1.99  
% 10.77/1.99  
% 10.77/1.99  
% 10.77/1.99  ------ Proving...
% 10.77/1.99  
% 10.77/1.99  
% 10.77/1.99  % SZS status Theorem for theBenchmark.p
% 10.77/1.99  
% 10.77/1.99  % SZS output start CNFRefutation for theBenchmark.p
% 10.77/1.99  
% 10.77/1.99  fof(f7,conjecture,(
% 10.77/1.99    ! [X0,X1,X2,X3] : (r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)) => ((r1_tarski(X1,X3) & r1_tarski(X0,X2)) | k1_xboole_0 = k2_zfmisc_1(X0,X1)))),
% 10.77/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 10.77/1.99  
% 10.77/1.99  fof(f8,negated_conjecture,(
% 10.77/1.99    ~! [X0,X1,X2,X3] : (r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)) => ((r1_tarski(X1,X3) & r1_tarski(X0,X2)) | k1_xboole_0 = k2_zfmisc_1(X0,X1)))),
% 10.77/1.99    inference(negated_conjecture,[],[f7])).
% 10.77/1.99  
% 10.77/1.99  fof(f12,plain,(
% 10.77/1.99    ? [X0,X1,X2,X3] : (((~r1_tarski(X1,X3) | ~r1_tarski(X0,X2)) & k1_xboole_0 != k2_zfmisc_1(X0,X1)) & r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)))),
% 10.77/1.99    inference(ennf_transformation,[],[f8])).
% 10.77/1.99  
% 10.77/1.99  fof(f13,plain,(
% 10.77/1.99    ? [X0,X1,X2,X3] : ((~r1_tarski(X1,X3) | ~r1_tarski(X0,X2)) & k1_xboole_0 != k2_zfmisc_1(X0,X1) & r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)))),
% 10.77/1.99    inference(flattening,[],[f12])).
% 10.77/1.99  
% 10.77/1.99  fof(f30,plain,(
% 10.77/1.99    ? [X0,X1,X2,X3] : ((~r1_tarski(X1,X3) | ~r1_tarski(X0,X2)) & k1_xboole_0 != k2_zfmisc_1(X0,X1) & r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3))) => ((~r1_tarski(sK8,sK10) | ~r1_tarski(sK7,sK9)) & k1_xboole_0 != k2_zfmisc_1(sK7,sK8) & r1_tarski(k2_zfmisc_1(sK7,sK8),k2_zfmisc_1(sK9,sK10)))),
% 10.77/1.99    introduced(choice_axiom,[])).
% 10.77/1.99  
% 10.77/1.99  fof(f31,plain,(
% 10.77/1.99    (~r1_tarski(sK8,sK10) | ~r1_tarski(sK7,sK9)) & k1_xboole_0 != k2_zfmisc_1(sK7,sK8) & r1_tarski(k2_zfmisc_1(sK7,sK8),k2_zfmisc_1(sK9,sK10))),
% 10.77/1.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7,sK8,sK9,sK10])],[f13,f30])).
% 10.77/1.99  
% 10.77/1.99  fof(f53,plain,(
% 10.77/1.99    r1_tarski(k2_zfmisc_1(sK7,sK8),k2_zfmisc_1(sK9,sK10))),
% 10.77/1.99    inference(cnf_transformation,[],[f31])).
% 10.77/1.99  
% 10.77/1.99  fof(f4,axiom,(
% 10.77/1.99    ! [X0,X1,X2] : (k2_zfmisc_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4,X5] : (k4_tarski(X4,X5) = X3 & r2_hidden(X5,X1) & r2_hidden(X4,X0))))),
% 10.77/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 10.77/1.99  
% 10.77/1.99  fof(f20,plain,(
% 10.77/1.99    ! [X0,X1,X2] : ((k2_zfmisc_1(X0,X1) = X2 | ? [X3] : ((! [X4,X5] : (k4_tarski(X4,X5) != X3 | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X0)) | ~r2_hidden(X3,X2)) & (? [X4,X5] : (k4_tarski(X4,X5) = X3 & r2_hidden(X5,X1) & r2_hidden(X4,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ! [X4,X5] : (k4_tarski(X4,X5) != X3 | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X0))) & (? [X4,X5] : (k4_tarski(X4,X5) = X3 & r2_hidden(X5,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X3,X2))) | k2_zfmisc_1(X0,X1) != X2))),
% 10.77/1.99    inference(nnf_transformation,[],[f4])).
% 10.77/1.99  
% 10.77/1.99  fof(f21,plain,(
% 10.77/1.99    ! [X0,X1,X2] : ((k2_zfmisc_1(X0,X1) = X2 | ? [X3] : ((! [X4,X5] : (k4_tarski(X4,X5) != X3 | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X0)) | ~r2_hidden(X3,X2)) & (? [X6,X7] : (k4_tarski(X6,X7) = X3 & r2_hidden(X7,X1) & r2_hidden(X6,X0)) | r2_hidden(X3,X2)))) & (! [X8] : ((r2_hidden(X8,X2) | ! [X9,X10] : (k4_tarski(X9,X10) != X8 | ~r2_hidden(X10,X1) | ~r2_hidden(X9,X0))) & (? [X11,X12] : (k4_tarski(X11,X12) = X8 & r2_hidden(X12,X1) & r2_hidden(X11,X0)) | ~r2_hidden(X8,X2))) | k2_zfmisc_1(X0,X1) != X2))),
% 10.77/1.99    inference(rectify,[],[f20])).
% 10.77/1.99  
% 10.77/1.99  fof(f24,plain,(
% 10.77/1.99    ! [X8,X1,X0] : (? [X11,X12] : (k4_tarski(X11,X12) = X8 & r2_hidden(X12,X1) & r2_hidden(X11,X0)) => (k4_tarski(sK5(X0,X1,X8),sK6(X0,X1,X8)) = X8 & r2_hidden(sK6(X0,X1,X8),X1) & r2_hidden(sK5(X0,X1,X8),X0)))),
% 10.77/1.99    introduced(choice_axiom,[])).
% 10.77/1.99  
% 10.77/1.99  fof(f23,plain,(
% 10.77/1.99    ( ! [X3] : (! [X2,X1,X0] : (? [X6,X7] : (k4_tarski(X6,X7) = X3 & r2_hidden(X7,X1) & r2_hidden(X6,X0)) => (k4_tarski(sK3(X0,X1,X2),sK4(X0,X1,X2)) = X3 & r2_hidden(sK4(X0,X1,X2),X1) & r2_hidden(sK3(X0,X1,X2),X0)))) )),
% 10.77/1.99    introduced(choice_axiom,[])).
% 10.77/1.99  
% 10.77/1.99  fof(f22,plain,(
% 10.77/1.99    ! [X2,X1,X0] : (? [X3] : ((! [X4,X5] : (k4_tarski(X4,X5) != X3 | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X0)) | ~r2_hidden(X3,X2)) & (? [X6,X7] : (k4_tarski(X6,X7) = X3 & r2_hidden(X7,X1) & r2_hidden(X6,X0)) | r2_hidden(X3,X2))) => ((! [X5,X4] : (k4_tarski(X4,X5) != sK2(X0,X1,X2) | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X0)) | ~r2_hidden(sK2(X0,X1,X2),X2)) & (? [X7,X6] : (k4_tarski(X6,X7) = sK2(X0,X1,X2) & r2_hidden(X7,X1) & r2_hidden(X6,X0)) | r2_hidden(sK2(X0,X1,X2),X2))))),
% 10.77/1.99    introduced(choice_axiom,[])).
% 10.77/1.99  
% 10.77/1.99  fof(f25,plain,(
% 10.77/1.99    ! [X0,X1,X2] : ((k2_zfmisc_1(X0,X1) = X2 | ((! [X4,X5] : (k4_tarski(X4,X5) != sK2(X0,X1,X2) | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X0)) | ~r2_hidden(sK2(X0,X1,X2),X2)) & ((k4_tarski(sK3(X0,X1,X2),sK4(X0,X1,X2)) = sK2(X0,X1,X2) & r2_hidden(sK4(X0,X1,X2),X1) & r2_hidden(sK3(X0,X1,X2),X0)) | r2_hidden(sK2(X0,X1,X2),X2)))) & (! [X8] : ((r2_hidden(X8,X2) | ! [X9,X10] : (k4_tarski(X9,X10) != X8 | ~r2_hidden(X10,X1) | ~r2_hidden(X9,X0))) & ((k4_tarski(sK5(X0,X1,X8),sK6(X0,X1,X8)) = X8 & r2_hidden(sK6(X0,X1,X8),X1) & r2_hidden(sK5(X0,X1,X8),X0)) | ~r2_hidden(X8,X2))) | k2_zfmisc_1(X0,X1) != X2))),
% 10.77/1.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5,sK6])],[f21,f24,f23,f22])).
% 10.77/1.99  
% 10.77/1.99  fof(f43,plain,(
% 10.77/1.99    ( ! [X2,X0,X1] : (k2_zfmisc_1(X0,X1) = X2 | r2_hidden(sK3(X0,X1,X2),X0) | r2_hidden(sK2(X0,X1,X2),X2)) )),
% 10.77/1.99    inference(cnf_transformation,[],[f25])).
% 10.77/1.99  
% 10.77/1.99  fof(f5,axiom,(
% 10.77/1.99    ! [X0,X1,X2,X3] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) <=> (r2_hidden(X1,X3) & r2_hidden(X0,X2)))),
% 10.77/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 10.77/1.99  
% 10.77/1.99  fof(f26,plain,(
% 10.77/1.99    ! [X0,X1,X2,X3] : ((r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | (~r2_hidden(X1,X3) | ~r2_hidden(X0,X2))) & ((r2_hidden(X1,X3) & r2_hidden(X0,X2)) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))))),
% 10.77/1.99    inference(nnf_transformation,[],[f5])).
% 10.77/1.99  
% 10.77/1.99  fof(f27,plain,(
% 10.77/1.99    ! [X0,X1,X2,X3] : ((r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | ~r2_hidden(X1,X3) | ~r2_hidden(X0,X2)) & ((r2_hidden(X1,X3) & r2_hidden(X0,X2)) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))))),
% 10.77/1.99    inference(flattening,[],[f26])).
% 10.77/1.99  
% 10.77/1.99  fof(f48,plain,(
% 10.77/1.99    ( ! [X2,X0,X3,X1] : (r2_hidden(X1,X3) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))) )),
% 10.77/1.99    inference(cnf_transformation,[],[f27])).
% 10.77/1.99  
% 10.77/1.99  fof(f1,axiom,(
% 10.77/1.99    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 10.77/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 10.77/1.99  
% 10.77/1.99  fof(f10,plain,(
% 10.77/1.99    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 10.77/1.99    inference(ennf_transformation,[],[f1])).
% 10.77/1.99  
% 10.77/1.99  fof(f14,plain,(
% 10.77/1.99    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 10.77/1.99    inference(nnf_transformation,[],[f10])).
% 10.77/1.99  
% 10.77/1.99  fof(f15,plain,(
% 10.77/1.99    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 10.77/1.99    inference(rectify,[],[f14])).
% 10.77/1.99  
% 10.77/1.99  fof(f16,plain,(
% 10.77/1.99    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 10.77/1.99    introduced(choice_axiom,[])).
% 10.77/1.99  
% 10.77/1.99  fof(f17,plain,(
% 10.77/1.99    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 10.77/1.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f15,f16])).
% 10.77/1.99  
% 10.77/1.99  fof(f32,plain,(
% 10.77/1.99    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,X1)) )),
% 10.77/1.99    inference(cnf_transformation,[],[f17])).
% 10.77/1.99  
% 10.77/1.99  fof(f49,plain,(
% 10.77/1.99    ( ! [X2,X0,X3,X1] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | ~r2_hidden(X1,X3) | ~r2_hidden(X0,X2)) )),
% 10.77/1.99    inference(cnf_transformation,[],[f27])).
% 10.77/1.99  
% 10.77/1.99  fof(f54,plain,(
% 10.77/1.99    k1_xboole_0 != k2_zfmisc_1(sK7,sK8)),
% 10.77/1.99    inference(cnf_transformation,[],[f31])).
% 10.77/1.99  
% 10.77/1.99  fof(f6,axiom,(
% 10.77/1.99    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 10.77/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 10.77/1.99  
% 10.77/1.99  fof(f28,plain,(
% 10.77/1.99    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 10.77/1.99    inference(nnf_transformation,[],[f6])).
% 10.77/1.99  
% 10.77/1.99  fof(f29,plain,(
% 10.77/1.99    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 10.77/1.99    inference(flattening,[],[f28])).
% 10.77/1.99  
% 10.77/1.99  fof(f50,plain,(
% 10.77/1.99    ( ! [X0,X1] : (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)) )),
% 10.77/1.99    inference(cnf_transformation,[],[f29])).
% 10.77/1.99  
% 10.77/1.99  fof(f51,plain,(
% 10.77/1.99    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X0) )),
% 10.77/1.99    inference(cnf_transformation,[],[f29])).
% 10.77/1.99  
% 10.77/1.99  fof(f62,plain,(
% 10.77/1.99    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 10.77/1.99    inference(equality_resolution,[],[f51])).
% 10.77/1.99  
% 10.77/1.99  fof(f3,axiom,(
% 10.77/1.99    ! [X0] : r1_xboole_0(X0,k1_xboole_0)),
% 10.77/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 10.77/1.99  
% 10.77/1.99  fof(f38,plain,(
% 10.77/1.99    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) )),
% 10.77/1.99    inference(cnf_transformation,[],[f3])).
% 10.77/1.99  
% 10.77/1.99  fof(f34,plain,(
% 10.77/1.99    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r2_hidden(sK0(X0,X1),X1)) )),
% 10.77/1.99    inference(cnf_transformation,[],[f17])).
% 10.77/1.99  
% 10.77/1.99  fof(f33,plain,(
% 10.77/1.99    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK0(X0,X1),X0)) )),
% 10.77/1.99    inference(cnf_transformation,[],[f17])).
% 10.77/1.99  
% 10.77/1.99  fof(f2,axiom,(
% 10.77/1.99    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 10.77/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 10.77/1.99  
% 10.77/1.99  fof(f9,plain,(
% 10.77/1.99    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 10.77/1.99    inference(rectify,[],[f2])).
% 10.77/1.99  
% 10.77/1.99  fof(f11,plain,(
% 10.77/1.99    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 10.77/1.99    inference(ennf_transformation,[],[f9])).
% 10.77/1.99  
% 10.77/1.99  fof(f18,plain,(
% 10.77/1.99    ! [X1,X0] : (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) => (r2_hidden(sK1(X0,X1),X1) & r2_hidden(sK1(X0,X1),X0)))),
% 10.77/1.99    introduced(choice_axiom,[])).
% 10.77/1.99  
% 10.77/1.99  fof(f19,plain,(
% 10.77/1.99    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & ((r2_hidden(sK1(X0,X1),X1) & r2_hidden(sK1(X0,X1),X0)) | r1_xboole_0(X0,X1)))),
% 10.77/1.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f11,f18])).
% 10.77/1.99  
% 10.77/1.99  fof(f37,plain,(
% 10.77/1.99    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) )),
% 10.77/1.99    inference(cnf_transformation,[],[f19])).
% 10.77/1.99  
% 10.77/1.99  fof(f44,plain,(
% 10.77/1.99    ( ! [X2,X0,X1] : (k2_zfmisc_1(X0,X1) = X2 | r2_hidden(sK4(X0,X1,X2),X1) | r2_hidden(sK2(X0,X1,X2),X2)) )),
% 10.77/1.99    inference(cnf_transformation,[],[f25])).
% 10.77/1.99  
% 10.77/1.99  fof(f40,plain,(
% 10.77/1.99    ( ! [X2,X0,X8,X1] : (r2_hidden(sK6(X0,X1,X8),X1) | ~r2_hidden(X8,X2) | k2_zfmisc_1(X0,X1) != X2) )),
% 10.77/1.99    inference(cnf_transformation,[],[f25])).
% 10.77/1.99  
% 10.77/1.99  fof(f59,plain,(
% 10.77/1.99    ( ! [X0,X8,X1] : (r2_hidden(sK6(X0,X1,X8),X1) | ~r2_hidden(X8,k2_zfmisc_1(X0,X1))) )),
% 10.77/1.99    inference(equality_resolution,[],[f40])).
% 10.77/1.99  
% 10.77/1.99  fof(f52,plain,(
% 10.77/1.99    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X1) )),
% 10.77/1.99    inference(cnf_transformation,[],[f29])).
% 10.77/1.99  
% 10.77/1.99  fof(f61,plain,(
% 10.77/1.99    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 10.77/1.99    inference(equality_resolution,[],[f52])).
% 10.77/1.99  
% 10.77/1.99  fof(f47,plain,(
% 10.77/1.99    ( ! [X2,X0,X3,X1] : (r2_hidden(X0,X2) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))) )),
% 10.77/1.99    inference(cnf_transformation,[],[f27])).
% 10.77/1.99  
% 10.77/1.99  fof(f55,plain,(
% 10.77/1.99    ~r1_tarski(sK8,sK10) | ~r1_tarski(sK7,sK9)),
% 10.77/1.99    inference(cnf_transformation,[],[f31])).
% 10.77/1.99  
% 10.77/1.99  cnf(c_444,plain,
% 10.77/1.99      ( X0 != X1 | X2 != X3 | k2_zfmisc_1(X0,X2) = k2_zfmisc_1(X1,X3) ),
% 10.77/1.99      theory(equality) ).
% 10.77/1.99  
% 10.77/1.99  cnf(c_441,plain,
% 10.77/1.99      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,X3) | X2 != X0 | X3 != X1 ),
% 10.77/1.99      theory(equality) ).
% 10.77/1.99  
% 10.77/1.99  cnf(c_5051,plain,
% 10.77/1.99      ( ~ r1_tarski(X0,k2_zfmisc_1(X1,X2))
% 10.77/1.99      | r1_tarski(X3,k2_zfmisc_1(X4,X5))
% 10.77/1.99      | X3 != X0
% 10.77/1.99      | X4 != X1
% 10.77/1.99      | X5 != X2 ),
% 10.77/1.99      inference(resolution,[status(thm)],[c_444,c_441]) ).
% 10.77/1.99  
% 10.77/1.99  cnf(c_23,negated_conjecture,
% 10.77/1.99      ( r1_tarski(k2_zfmisc_1(sK7,sK8),k2_zfmisc_1(sK9,sK10)) ),
% 10.77/1.99      inference(cnf_transformation,[],[f53]) ).
% 10.77/1.99  
% 10.77/1.99  cnf(c_31643,plain,
% 10.77/1.99      ( r1_tarski(X0,k2_zfmisc_1(X1,X2))
% 10.77/1.99      | X0 != k2_zfmisc_1(sK7,sK8)
% 10.77/1.99      | X1 != sK9
% 10.77/1.99      | X2 != sK10 ),
% 10.77/1.99      inference(resolution,[status(thm)],[c_5051,c_23]) ).
% 10.77/1.99  
% 10.77/1.99  cnf(c_10,plain,
% 10.77/1.99      ( r2_hidden(sK3(X0,X1,X2),X0)
% 10.77/1.99      | r2_hidden(sK2(X0,X1,X2),X2)
% 10.77/1.99      | k2_zfmisc_1(X0,X1) = X2 ),
% 10.77/1.99      inference(cnf_transformation,[],[f43]) ).
% 10.77/1.99  
% 10.77/1.99  cnf(c_16,plain,
% 10.77/1.99      ( r2_hidden(X0,X1)
% 10.77/1.99      | ~ r2_hidden(k4_tarski(X2,X0),k2_zfmisc_1(X3,X1)) ),
% 10.77/1.99      inference(cnf_transformation,[],[f48]) ).
% 10.77/1.99  
% 10.77/1.99  cnf(c_2,plain,
% 10.77/1.99      ( ~ r2_hidden(X0,X1) | r2_hidden(X0,X2) | ~ r1_tarski(X1,X2) ),
% 10.77/1.99      inference(cnf_transformation,[],[f32]) ).
% 10.77/1.99  
% 10.77/1.99  cnf(c_1141,plain,
% 10.77/1.99      ( r2_hidden(X0,k2_zfmisc_1(sK9,sK10))
% 10.77/1.99      | ~ r2_hidden(X0,k2_zfmisc_1(sK7,sK8)) ),
% 10.77/1.99      inference(resolution,[status(thm)],[c_2,c_23]) ).
% 10.77/1.99  
% 10.77/1.99  cnf(c_1285,plain,
% 10.77/1.99      ( r2_hidden(X0,sK10)
% 10.77/1.99      | ~ r2_hidden(k4_tarski(X1,X0),k2_zfmisc_1(sK7,sK8)) ),
% 10.77/1.99      inference(resolution,[status(thm)],[c_16,c_1141]) ).
% 10.77/1.99  
% 10.77/1.99  cnf(c_15,plain,
% 10.77/1.99      ( ~ r2_hidden(X0,X1)
% 10.77/1.99      | ~ r2_hidden(X2,X3)
% 10.77/1.99      | r2_hidden(k4_tarski(X2,X0),k2_zfmisc_1(X3,X1)) ),
% 10.77/1.99      inference(cnf_transformation,[],[f49]) ).
% 10.77/1.99  
% 10.77/1.99  cnf(c_2445,plain,
% 10.77/1.99      ( ~ r2_hidden(X0,sK7) | r2_hidden(X1,sK10) | ~ r2_hidden(X1,sK8) ),
% 10.77/1.99      inference(resolution,[status(thm)],[c_1285,c_15]) ).
% 10.77/1.99  
% 10.77/1.99  cnf(c_3544,plain,
% 10.77/1.99      ( r2_hidden(X0,sK10)
% 10.77/1.99      | ~ r2_hidden(X0,sK8)
% 10.77/1.99      | r2_hidden(sK2(sK7,X1,X2),X2)
% 10.77/1.99      | k2_zfmisc_1(sK7,X1) = X2 ),
% 10.77/1.99      inference(resolution,[status(thm)],[c_10,c_2445]) ).
% 10.77/1.99  
% 10.77/1.99  cnf(c_32828,plain,
% 10.77/1.99      ( r2_hidden(X0,sK10)
% 10.77/1.99      | ~ r2_hidden(X0,sK8)
% 10.77/1.99      | r2_hidden(sK2(sK7,X1,k2_zfmisc_1(sK7,sK8)),k2_zfmisc_1(sK7,sK8))
% 10.77/1.99      | r1_tarski(k2_zfmisc_1(sK7,X1),k2_zfmisc_1(X2,X3))
% 10.77/1.99      | X2 != sK9
% 10.77/1.99      | X3 != sK10 ),
% 10.77/1.99      inference(resolution,[status(thm)],[c_31643,c_3544]) ).
% 10.77/1.99  
% 10.77/1.99  cnf(c_22,negated_conjecture,
% 10.77/1.99      ( k1_xboole_0 != k2_zfmisc_1(sK7,sK8) ),
% 10.77/1.99      inference(cnf_transformation,[],[f54]) ).
% 10.77/1.99  
% 10.77/1.99  cnf(c_20,plain,
% 10.77/1.99      ( k2_zfmisc_1(X0,X1) != k1_xboole_0
% 10.77/1.99      | k1_xboole_0 = X1
% 10.77/1.99      | k1_xboole_0 = X0 ),
% 10.77/1.99      inference(cnf_transformation,[],[f50]) ).
% 10.77/1.99  
% 10.77/1.99  cnf(c_26,plain,
% 10.77/1.99      ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) != k1_xboole_0
% 10.77/1.99      | k1_xboole_0 = k1_xboole_0 ),
% 10.77/1.99      inference(instantiation,[status(thm)],[c_20]) ).
% 10.77/1.99  
% 10.77/1.99  cnf(c_19,plain,
% 10.77/1.99      ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
% 10.77/1.99      inference(cnf_transformation,[],[f62]) ).
% 10.77/1.99  
% 10.77/1.99  cnf(c_27,plain,
% 10.77/1.99      ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
% 10.77/1.99      inference(instantiation,[status(thm)],[c_19]) ).
% 10.77/1.99  
% 10.77/1.99  cnf(c_6,plain,
% 10.77/1.99      ( r1_xboole_0(X0,k1_xboole_0) ),
% 10.77/1.99      inference(cnf_transformation,[],[f38]) ).
% 10.77/1.99  
% 10.77/1.99  cnf(c_50,plain,
% 10.77/1.99      ( r1_xboole_0(k1_xboole_0,k1_xboole_0) ),
% 10.77/1.99      inference(instantiation,[status(thm)],[c_6]) ).
% 10.77/1.99  
% 10.77/1.99  cnf(c_440,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 10.77/1.99  
% 10.77/1.99  cnf(c_989,plain,
% 10.77/1.99      ( k2_zfmisc_1(sK7,sK8) != X0
% 10.77/1.99      | k1_xboole_0 != X0
% 10.77/1.99      | k1_xboole_0 = k2_zfmisc_1(sK7,sK8) ),
% 10.77/1.99      inference(instantiation,[status(thm)],[c_440]) ).
% 10.77/1.99  
% 10.77/1.99  cnf(c_990,plain,
% 10.77/1.99      ( k2_zfmisc_1(sK7,sK8) != k1_xboole_0
% 10.77/1.99      | k1_xboole_0 = k2_zfmisc_1(sK7,sK8)
% 10.77/1.99      | k1_xboole_0 != k1_xboole_0 ),
% 10.77/1.99      inference(instantiation,[status(thm)],[c_989]) ).
% 10.77/1.99  
% 10.77/1.99  cnf(c_0,plain,
% 10.77/1.99      ( ~ r2_hidden(sK0(X0,X1),X1) | r1_tarski(X0,X1) ),
% 10.77/1.99      inference(cnf_transformation,[],[f34]) ).
% 10.77/1.99  
% 10.77/1.99  cnf(c_1,plain,
% 10.77/1.99      ( r2_hidden(sK0(X0,X1),X0) | r1_tarski(X0,X1) ),
% 10.77/1.99      inference(cnf_transformation,[],[f33]) ).
% 10.77/1.99  
% 10.77/1.99  cnf(c_1019,plain,
% 10.77/1.99      ( r1_tarski(X0,X0) ),
% 10.77/1.99      inference(resolution,[status(thm)],[c_0,c_1]) ).
% 10.77/1.99  
% 10.77/1.99  cnf(c_1021,plain,
% 10.77/1.99      ( r1_tarski(k1_xboole_0,k1_xboole_0) ),
% 10.77/1.99      inference(instantiation,[status(thm)],[c_1019]) ).
% 10.77/1.99  
% 10.77/1.99  cnf(c_1055,plain,
% 10.77/1.99      ( r2_hidden(sK3(sK7,sK8,X0),sK7)
% 10.77/1.99      | r2_hidden(sK2(sK7,sK8,X0),X0)
% 10.77/1.99      | k2_zfmisc_1(sK7,sK8) = X0 ),
% 10.77/1.99      inference(instantiation,[status(thm)],[c_10]) ).
% 10.77/1.99  
% 10.77/1.99  cnf(c_1062,plain,
% 10.77/1.99      ( r2_hidden(sK3(sK7,sK8,k1_xboole_0),sK7)
% 10.77/1.99      | r2_hidden(sK2(sK7,sK8,k1_xboole_0),k1_xboole_0)
% 10.77/1.99      | k2_zfmisc_1(sK7,sK8) = k1_xboole_0 ),
% 10.77/1.99      inference(instantiation,[status(thm)],[c_1055]) ).
% 10.77/1.99  
% 10.77/1.99  cnf(c_3,plain,
% 10.77/1.99      ( ~ r1_xboole_0(X0,X1) | ~ r2_hidden(X2,X1) | ~ r2_hidden(X2,X0) ),
% 10.77/1.99      inference(cnf_transformation,[],[f37]) ).
% 10.77/1.99  
% 10.77/1.99  cnf(c_1296,plain,
% 10.77/1.99      ( ~ r1_xboole_0(X0,X1)
% 10.77/1.99      | ~ r2_hidden(sK2(sK7,sK8,X0),X0)
% 10.77/1.99      | ~ r2_hidden(sK2(sK7,sK8,X0),X1) ),
% 10.77/1.99      inference(instantiation,[status(thm)],[c_3]) ).
% 10.77/1.99  
% 10.77/1.99  cnf(c_1298,plain,
% 10.77/1.99      ( ~ r1_xboole_0(k1_xboole_0,k1_xboole_0)
% 10.77/1.99      | ~ r2_hidden(sK2(sK7,sK8,k1_xboole_0),k1_xboole_0) ),
% 10.77/1.99      inference(instantiation,[status(thm)],[c_1296]) ).
% 10.77/1.99  
% 10.77/1.99  cnf(c_1650,plain,
% 10.77/1.99      ( ~ r1_tarski(X0,X1) | r1_tarski(sK7,X2) | X2 != X1 | sK7 != X0 ),
% 10.77/1.99      inference(instantiation,[status(thm)],[c_441]) ).
% 10.77/1.99  
% 10.77/1.99  cnf(c_1652,plain,
% 10.77/1.99      ( r1_tarski(sK7,k1_xboole_0)
% 10.77/1.99      | ~ r1_tarski(k1_xboole_0,k1_xboole_0)
% 10.77/1.99      | sK7 != k1_xboole_0
% 10.77/1.99      | k1_xboole_0 != k1_xboole_0 ),
% 10.77/1.99      inference(instantiation,[status(thm)],[c_1650]) ).
% 10.77/1.99  
% 10.77/1.99  cnf(c_1658,plain,
% 10.77/1.99      ( ~ r1_xboole_0(sK7,X0)
% 10.77/1.99      | ~ r2_hidden(sK3(sK7,sK8,X1),X0)
% 10.77/1.99      | ~ r2_hidden(sK3(sK7,sK8,X1),sK7) ),
% 10.77/1.99      inference(instantiation,[status(thm)],[c_3]) ).
% 10.77/1.99  
% 10.77/1.99  cnf(c_1660,plain,
% 10.77/1.99      ( ~ r1_xboole_0(sK7,k1_xboole_0)
% 10.77/1.99      | ~ r2_hidden(sK3(sK7,sK8,k1_xboole_0),sK7)
% 10.77/1.99      | ~ r2_hidden(sK3(sK7,sK8,k1_xboole_0),k1_xboole_0) ),
% 10.77/1.99      inference(instantiation,[status(thm)],[c_1658]) ).
% 10.77/1.99  
% 10.77/1.99  cnf(c_1666,plain,
% 10.77/1.99      ( r2_hidden(sK3(sK7,sK8,X0),X1)
% 10.77/1.99      | ~ r2_hidden(sK3(sK7,sK8,X0),sK7)
% 10.77/1.99      | ~ r1_tarski(sK7,X1) ),
% 10.77/1.99      inference(instantiation,[status(thm)],[c_2]) ).
% 10.77/1.99  
% 10.77/1.99  cnf(c_1668,plain,
% 10.77/1.99      ( ~ r2_hidden(sK3(sK7,sK8,k1_xboole_0),sK7)
% 10.77/1.99      | r2_hidden(sK3(sK7,sK8,k1_xboole_0),k1_xboole_0)
% 10.77/1.99      | ~ r1_tarski(sK7,k1_xboole_0) ),
% 10.77/1.99      inference(instantiation,[status(thm)],[c_1666]) ).
% 10.77/1.99  
% 10.77/1.99  cnf(c_3566,plain,
% 10.77/1.99      ( r1_xboole_0(sK7,k1_xboole_0) ),
% 10.77/1.99      inference(instantiation,[status(thm)],[c_6]) ).
% 10.77/1.99  
% 10.77/1.99  cnf(c_9,plain,
% 10.77/1.99      ( r2_hidden(sK4(X0,X1,X2),X1)
% 10.77/1.99      | r2_hidden(sK2(X0,X1,X2),X2)
% 10.77/1.99      | k2_zfmisc_1(X0,X1) = X2 ),
% 10.77/1.99      inference(cnf_transformation,[],[f44]) ).
% 10.77/1.99  
% 10.77/1.99  cnf(c_809,plain,
% 10.77/1.99      ( k2_zfmisc_1(X0,X1) = X2
% 10.77/1.99      | r2_hidden(sK4(X0,X1,X2),X1) = iProver_top
% 10.77/1.99      | r2_hidden(sK2(X0,X1,X2),X2) = iProver_top ),
% 10.77/1.99      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 10.77/1.99  
% 10.77/1.99  cnf(c_13,plain,
% 10.77/1.99      ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
% 10.77/1.99      | r2_hidden(sK6(X1,X2,X0),X2) ),
% 10.77/1.99      inference(cnf_transformation,[],[f59]) ).
% 10.77/1.99  
% 10.77/1.99  cnf(c_805,plain,
% 10.77/1.99      ( r2_hidden(X0,k2_zfmisc_1(X1,X2)) != iProver_top
% 10.77/1.99      | r2_hidden(sK6(X1,X2,X0),X2) = iProver_top ),
% 10.77/1.99      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 10.77/1.99  
% 10.77/1.99  cnf(c_812,plain,
% 10.77/1.99      ( r1_xboole_0(X0,k1_xboole_0) = iProver_top ),
% 10.77/1.99      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 10.77/1.99  
% 10.77/1.99  cnf(c_815,plain,
% 10.77/1.99      ( r1_xboole_0(X0,X1) != iProver_top
% 10.77/1.99      | r2_hidden(X2,X1) != iProver_top
% 10.77/1.99      | r2_hidden(X2,X0) != iProver_top ),
% 10.77/1.99      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 10.77/1.99  
% 10.77/1.99  cnf(c_2199,plain,
% 10.77/1.99      ( r2_hidden(X0,X1) != iProver_top
% 10.77/1.99      | r2_hidden(X0,k1_xboole_0) != iProver_top ),
% 10.77/1.99      inference(superposition,[status(thm)],[c_812,c_815]) ).
% 10.77/1.99  
% 10.77/1.99  cnf(c_2477,plain,
% 10.77/1.99      ( r2_hidden(X0,k2_zfmisc_1(X1,X2)) != iProver_top
% 10.77/1.99      | r2_hidden(sK6(X1,X2,X0),k1_xboole_0) != iProver_top ),
% 10.77/1.99      inference(superposition,[status(thm)],[c_805,c_2199]) ).
% 10.77/1.99  
% 10.77/1.99  cnf(c_2672,plain,
% 10.77/1.99      ( r2_hidden(X0,k2_zfmisc_1(X1,k1_xboole_0)) != iProver_top ),
% 10.77/1.99      inference(superposition,[status(thm)],[c_805,c_2477]) ).
% 10.77/1.99  
% 10.77/1.99  cnf(c_18,plain,
% 10.77/1.99      ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
% 10.77/1.99      inference(cnf_transformation,[],[f61]) ).
% 10.77/1.99  
% 10.77/1.99  cnf(c_2673,plain,
% 10.77/1.99      ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
% 10.77/1.99      inference(demodulation,[status(thm)],[c_2672,c_18]) ).
% 10.77/1.99  
% 10.77/1.99  cnf(c_3085,plain,
% 10.77/1.99      ( k2_zfmisc_1(X0,k1_xboole_0) = X1
% 10.77/1.99      | r2_hidden(sK2(X0,k1_xboole_0,X1),X1) = iProver_top ),
% 10.77/1.99      inference(superposition,[status(thm)],[c_809,c_2673]) ).
% 10.77/1.99  
% 10.77/1.99  cnf(c_3104,plain,
% 10.77/1.99      ( k1_xboole_0 = X0
% 10.77/1.99      | r2_hidden(sK2(X1,k1_xboole_0,X0),X0) = iProver_top ),
% 10.77/1.99      inference(demodulation,[status(thm)],[c_3085,c_18]) ).
% 10.77/1.99  
% 10.77/1.99  cnf(c_800,plain,
% 10.77/1.99      ( r1_tarski(k2_zfmisc_1(sK7,sK8),k2_zfmisc_1(sK9,sK10)) = iProver_top ),
% 10.77/1.99      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 10.77/1.99  
% 10.77/1.99  cnf(c_807,plain,
% 10.77/1.99      ( r2_hidden(X0,X1) != iProver_top
% 10.77/1.99      | r2_hidden(X2,X3) != iProver_top
% 10.77/1.99      | r2_hidden(k4_tarski(X2,X0),k2_zfmisc_1(X3,X1)) = iProver_top ),
% 10.77/1.99      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 10.77/1.99  
% 10.77/1.99  cnf(c_816,plain,
% 10.77/1.99      ( r2_hidden(X0,X1) != iProver_top
% 10.77/1.99      | r2_hidden(X0,X2) = iProver_top
% 10.77/1.99      | r1_tarski(X1,X2) != iProver_top ),
% 10.77/1.99      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 10.77/1.99  
% 10.77/1.99  cnf(c_2048,plain,
% 10.77/1.99      ( r2_hidden(X0,X1) != iProver_top
% 10.77/1.99      | r2_hidden(X2,X3) != iProver_top
% 10.77/1.99      | r2_hidden(k4_tarski(X2,X0),X4) = iProver_top
% 10.77/1.99      | r1_tarski(k2_zfmisc_1(X3,X1),X4) != iProver_top ),
% 10.77/1.99      inference(superposition,[status(thm)],[c_807,c_816]) ).
% 10.77/1.99  
% 10.77/1.99  cnf(c_30547,plain,
% 10.77/1.99      ( r2_hidden(X0,sK7) != iProver_top
% 10.77/1.99      | r2_hidden(X1,sK8) != iProver_top
% 10.77/1.99      | r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(sK9,sK10)) = iProver_top ),
% 10.77/1.99      inference(superposition,[status(thm)],[c_800,c_2048]) ).
% 10.77/1.99  
% 10.77/1.99  cnf(c_803,plain,
% 10.77/1.99      ( r2_hidden(X0,X1) = iProver_top
% 10.77/1.99      | r2_hidden(k4_tarski(X2,X0),k2_zfmisc_1(X3,X1)) != iProver_top ),
% 10.77/1.99      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 10.77/1.99  
% 10.77/1.99  cnf(c_33531,plain,
% 10.77/1.99      ( r2_hidden(X0,sK7) != iProver_top
% 10.77/1.99      | r2_hidden(X1,sK10) = iProver_top
% 10.77/1.99      | r2_hidden(X1,sK8) != iProver_top ),
% 10.77/1.99      inference(superposition,[status(thm)],[c_30547,c_803]) ).
% 10.77/1.99  
% 10.77/1.99  cnf(c_33626,plain,
% 10.77/1.99      ( sK7 = k1_xboole_0
% 10.77/1.99      | r2_hidden(X0,sK10) = iProver_top
% 10.77/1.99      | r2_hidden(X0,sK8) != iProver_top ),
% 10.77/1.99      inference(superposition,[status(thm)],[c_3104,c_33531]) ).
% 10.77/1.99  
% 10.77/1.99  cnf(c_33802,plain,
% 10.77/1.99      ( r2_hidden(X0,sK10) | ~ r2_hidden(X0,sK8) | sK7 = k1_xboole_0 ),
% 10.77/1.99      inference(predicate_to_equality_rev,[status(thm)],[c_33626]) ).
% 10.77/1.99  
% 10.77/1.99  cnf(c_35295,plain,
% 10.77/1.99      ( r2_hidden(X0,sK10) | ~ r2_hidden(X0,sK8) ),
% 10.77/1.99      inference(global_propositional_subsumption,
% 10.77/1.99                [status(thm)],
% 10.77/1.99                [c_32828,c_22,c_26,c_27,c_50,c_990,c_1021,c_1062,c_1298,
% 10.77/1.99                 c_1652,c_1660,c_1668,c_3566,c_33802]) ).
% 10.77/1.99  
% 10.77/1.99  cnf(c_35313,plain,
% 10.77/1.99      ( ~ r2_hidden(sK0(X0,sK10),sK8) | r1_tarski(X0,sK10) ),
% 10.77/1.99      inference(resolution,[status(thm)],[c_35295,c_0]) ).
% 10.77/1.99  
% 10.77/1.99  cnf(c_37363,plain,
% 10.77/1.99      ( r1_tarski(sK8,sK10) ),
% 10.77/1.99      inference(resolution,[status(thm)],[c_35313,c_1]) ).
% 10.77/1.99  
% 10.77/1.99  cnf(c_817,plain,
% 10.77/1.99      ( r2_hidden(sK0(X0,X1),X0) = iProver_top
% 10.77/1.99      | r1_tarski(X0,X1) = iProver_top ),
% 10.77/1.99      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 10.77/1.99  
% 10.77/1.99  cnf(c_17,plain,
% 10.77/1.99      ( r2_hidden(X0,X1)
% 10.77/1.99      | ~ r2_hidden(k4_tarski(X0,X2),k2_zfmisc_1(X1,X3)) ),
% 10.77/1.99      inference(cnf_transformation,[],[f47]) ).
% 10.77/1.99  
% 10.77/1.99  cnf(c_802,plain,
% 10.77/1.99      ( r2_hidden(X0,X1) = iProver_top
% 10.77/1.99      | r2_hidden(k4_tarski(X0,X2),k2_zfmisc_1(X1,X3)) != iProver_top ),
% 10.77/1.99      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 10.77/1.99  
% 10.77/1.99  cnf(c_33534,plain,
% 10.77/1.99      ( r2_hidden(X0,sK9) = iProver_top
% 10.77/1.99      | r2_hidden(X0,sK7) != iProver_top
% 10.77/1.99      | r2_hidden(X1,sK8) != iProver_top ),
% 10.77/1.99      inference(superposition,[status(thm)],[c_30547,c_802]) ).
% 10.77/1.99  
% 10.77/1.99  cnf(c_49,plain,
% 10.77/1.99      ( r1_xboole_0(X0,k1_xboole_0) = iProver_top ),
% 10.77/1.99      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 10.77/1.99  
% 10.77/1.99  cnf(c_51,plain,
% 10.77/1.99      ( r1_xboole_0(k1_xboole_0,k1_xboole_0) = iProver_top ),
% 10.77/1.99      inference(instantiation,[status(thm)],[c_49]) ).
% 10.77/1.99  
% 10.77/1.99  cnf(c_1297,plain,
% 10.77/1.99      ( r1_xboole_0(X0,X1) != iProver_top
% 10.77/1.99      | r2_hidden(sK2(sK7,sK8,X0),X0) != iProver_top
% 10.77/1.99      | r2_hidden(sK2(sK7,sK8,X0),X1) != iProver_top ),
% 10.77/1.99      inference(predicate_to_equality,[status(thm)],[c_1296]) ).
% 10.77/1.99  
% 10.77/1.99  cnf(c_1299,plain,
% 10.77/1.99      ( r1_xboole_0(k1_xboole_0,k1_xboole_0) != iProver_top
% 10.77/1.99      | r2_hidden(sK2(sK7,sK8,k1_xboole_0),k1_xboole_0) != iProver_top ),
% 10.77/1.99      inference(instantiation,[status(thm)],[c_1297]) ).
% 10.77/1.99  
% 10.77/1.99  cnf(c_2283,plain,
% 10.77/1.99      ( X0 != k1_xboole_0 | k2_zfmisc_1(X1,k1_xboole_0) = X0 ),
% 10.77/1.99      inference(resolution,[status(thm)],[c_440,c_18]) ).
% 10.77/1.99  
% 10.77/1.99  cnf(c_32832,plain,
% 10.77/1.99      ( r1_tarski(k2_zfmisc_1(X0,k1_xboole_0),k2_zfmisc_1(X1,X2))
% 10.77/1.99      | X1 != sK9
% 10.77/1.99      | X2 != sK10
% 10.77/1.99      | k2_zfmisc_1(sK7,sK8) != k1_xboole_0 ),
% 10.77/1.99      inference(resolution,[status(thm)],[c_31643,c_2283]) ).
% 10.77/1.99  
% 10.77/1.99  cnf(c_33826,plain,
% 10.77/1.99      ( k2_zfmisc_1(sK7,sK8) != k1_xboole_0 ),
% 10.77/1.99      inference(global_propositional_subsumption,
% 10.77/1.99                [status(thm)],
% 10.77/1.99                [c_32832,c_22,c_26,c_27,c_990]) ).
% 10.77/1.99  
% 10.77/1.99  cnf(c_1409,plain,
% 10.77/1.99      ( r2_hidden(X0,sK9)
% 10.77/1.99      | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(sK7,sK8)) ),
% 10.77/1.99      inference(resolution,[status(thm)],[c_17,c_1141]) ).
% 10.77/1.99  
% 10.77/1.99  cnf(c_2454,plain,
% 10.77/1.99      ( r2_hidden(X0,sK9) | ~ r2_hidden(X0,sK7) | ~ r2_hidden(X1,sK8) ),
% 10.77/1.99      inference(resolution,[status(thm)],[c_1409,c_15]) ).
% 10.77/1.99  
% 10.77/1.99  cnf(c_3500,plain,
% 10.77/1.99      ( r2_hidden(X0,sK9)
% 10.77/1.99      | ~ r2_hidden(X0,sK7)
% 10.77/1.99      | r2_hidden(sK2(X1,sK8,X2),X2)
% 10.77/1.99      | k2_zfmisc_1(X1,sK8) = X2 ),
% 10.77/1.99      inference(resolution,[status(thm)],[c_9,c_2454]) ).
% 10.77/1.99  
% 10.77/1.99  cnf(c_33840,plain,
% 10.77/1.99      ( r2_hidden(X0,sK9)
% 10.77/1.99      | ~ r2_hidden(X0,sK7)
% 10.77/1.99      | r2_hidden(sK2(sK7,sK8,k1_xboole_0),k1_xboole_0) ),
% 10.77/1.99      inference(resolution,[status(thm)],[c_33826,c_3500]) ).
% 10.77/1.99  
% 10.77/1.99  cnf(c_33841,plain,
% 10.77/1.99      ( r2_hidden(X0,sK9) = iProver_top
% 10.77/1.99      | r2_hidden(X0,sK7) != iProver_top
% 10.77/1.99      | r2_hidden(sK2(sK7,sK8,k1_xboole_0),k1_xboole_0) = iProver_top ),
% 10.77/1.99      inference(predicate_to_equality,[status(thm)],[c_33840]) ).
% 10.77/1.99  
% 10.77/1.99  cnf(c_34383,plain,
% 10.77/1.99      ( r2_hidden(X0,sK7) != iProver_top
% 10.77/1.99      | r2_hidden(X0,sK9) = iProver_top ),
% 10.77/1.99      inference(global_propositional_subsumption,
% 10.77/1.99                [status(thm)],
% 10.77/1.99                [c_33534,c_51,c_1299,c_33841]) ).
% 10.77/1.99  
% 10.77/1.99  cnf(c_34384,plain,
% 10.77/1.99      ( r2_hidden(X0,sK9) = iProver_top
% 10.77/1.99      | r2_hidden(X0,sK7) != iProver_top ),
% 10.77/1.99      inference(renaming,[status(thm)],[c_34383]) ).
% 10.77/1.99  
% 10.77/1.99  cnf(c_34391,plain,
% 10.77/1.99      ( r2_hidden(sK0(sK7,X0),sK9) = iProver_top
% 10.77/1.99      | r1_tarski(sK7,X0) = iProver_top ),
% 10.77/1.99      inference(superposition,[status(thm)],[c_817,c_34384]) ).
% 10.77/1.99  
% 10.77/1.99  cnf(c_818,plain,
% 10.77/1.99      ( r2_hidden(sK0(X0,X1),X1) != iProver_top
% 10.77/1.99      | r1_tarski(X0,X1) = iProver_top ),
% 10.77/1.99      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 10.77/1.99  
% 10.77/1.99  cnf(c_37258,plain,
% 10.77/1.99      ( r1_tarski(sK7,sK9) = iProver_top ),
% 10.77/1.99      inference(superposition,[status(thm)],[c_34391,c_818]) ).
% 10.77/1.99  
% 10.77/1.99  cnf(c_37275,plain,
% 10.77/1.99      ( r1_tarski(sK7,sK9) ),
% 10.77/1.99      inference(predicate_to_equality_rev,[status(thm)],[c_37258]) ).
% 10.77/1.99  
% 10.77/1.99  cnf(c_21,negated_conjecture,
% 10.77/1.99      ( ~ r1_tarski(sK7,sK9) | ~ r1_tarski(sK8,sK10) ),
% 10.77/1.99      inference(cnf_transformation,[],[f55]) ).
% 10.77/1.99  
% 10.77/1.99  cnf(contradiction,plain,
% 10.77/1.99      ( $false ),
% 10.77/1.99      inference(minisat,[status(thm)],[c_37363,c_37275,c_21]) ).
% 10.77/1.99  
% 10.77/1.99  
% 10.77/1.99  % SZS output end CNFRefutation for theBenchmark.p
% 10.77/1.99  
% 10.77/1.99  ------                               Statistics
% 10.77/1.99  
% 10.77/1.99  ------ Selected
% 10.77/1.99  
% 10.77/1.99  total_time:                             1.092
% 10.77/1.99  
%------------------------------------------------------------------------------
