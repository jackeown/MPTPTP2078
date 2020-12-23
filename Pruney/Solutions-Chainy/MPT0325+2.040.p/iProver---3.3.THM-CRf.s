%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:37:52 EST 2020

% Result     : Theorem 2.78s
% Output     : CNFRefutation 2.78s
% Verified   : 
% Statistics : Number of formulae       :   67 ( 157 expanded)
%              Number of clauses        :   27 (  36 expanded)
%              Number of leaves         :   11 (  38 expanded)
%              Depth                    :   14
%              Number of atoms          :  250 ( 673 expanded)
%              Number of equality atoms :   44 ( 107 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal clause size      :   18 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f8,axiom,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
    <=> ( r2_hidden(X1,X3)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
        | ~ r2_hidden(X1,X3)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X3)
          & r2_hidden(X0,X2) )
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ) ),
    inference(nnf_transformation,[],[f8])).

fof(f32,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
        | ~ r2_hidden(X1,X3)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X3)
          & r2_hidden(X0,X2) )
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ) ),
    inference(flattening,[],[f31])).

fof(f52,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X0,X2)
      | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ),
    inference(cnf_transformation,[],[f32])).

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

fof(f17,plain,(
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

fof(f18,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f17])).

fof(f19,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK0(X0,X1),X1)
          & r2_hidden(sK0(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f18,f19])).

fof(f35,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f9,conjecture,(
    ! [X0,X1,X2,X3] :
      ( r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3))
     => ( ( r1_tarski(X1,X3)
          & r1_tarski(X0,X2) )
        | k1_xboole_0 = k2_zfmisc_1(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f10,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3))
       => ( ( r1_tarski(X1,X3)
            & r1_tarski(X0,X2) )
          | k1_xboole_0 = k2_zfmisc_1(X0,X1) ) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f15,plain,(
    ? [X0,X1,X2,X3] :
      ( ( ~ r1_tarski(X1,X3)
        | ~ r1_tarski(X0,X2) )
      & k1_xboole_0 != k2_zfmisc_1(X0,X1)
      & r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f16,plain,(
    ? [X0,X1,X2,X3] :
      ( ( ~ r1_tarski(X1,X3)
        | ~ r1_tarski(X0,X2) )
      & k1_xboole_0 != k2_zfmisc_1(X0,X1)
      & r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)) ) ),
    inference(flattening,[],[f15])).

fof(f33,plain,
    ( ? [X0,X1,X2,X3] :
        ( ( ~ r1_tarski(X1,X3)
          | ~ r1_tarski(X0,X2) )
        & k1_xboole_0 != k2_zfmisc_1(X0,X1)
        & r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)) )
   => ( ( ~ r1_tarski(sK9,sK11)
        | ~ r1_tarski(sK8,sK10) )
      & k1_xboole_0 != k2_zfmisc_1(sK8,sK9)
      & r1_tarski(k2_zfmisc_1(sK8,sK9),k2_zfmisc_1(sK10,sK11)) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,
    ( ( ~ r1_tarski(sK9,sK11)
      | ~ r1_tarski(sK8,sK10) )
    & k1_xboole_0 != k2_zfmisc_1(sK8,sK9)
    & r1_tarski(k2_zfmisc_1(sK8,sK9),k2_zfmisc_1(sK10,sK11)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8,sK9,sK10,sK11])],[f16,f33])).

fof(f55,plain,(
    r1_tarski(k2_zfmisc_1(sK8,sK9),k2_zfmisc_1(sK10,sK11)) ),
    inference(cnf_transformation,[],[f34])).

fof(f54,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
      | ~ r2_hidden(X1,X3)
      | ~ r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( k2_zfmisc_1(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ? [X4,X5] :
              ( k4_tarski(X4,X5) = X3
              & r2_hidden(X5,X1)
              & r2_hidden(X4,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
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
    inference(nnf_transformation,[],[f7])).

fof(f26,plain,(
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
    inference(rectify,[],[f25])).

fof(f29,plain,(
    ! [X8,X1,X0] :
      ( ? [X11,X12] :
          ( k4_tarski(X11,X12) = X8
          & r2_hidden(X12,X1)
          & r2_hidden(X11,X0) )
     => ( k4_tarski(sK6(X0,X1,X8),sK7(X0,X1,X8)) = X8
        & r2_hidden(sK7(X0,X1,X8),X1)
        & r2_hidden(sK6(X0,X1,X8),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X6,X7] :
          ( k4_tarski(X6,X7) = X3
          & r2_hidden(X7,X1)
          & r2_hidden(X6,X0) )
     => ( k4_tarski(sK4(X0,X1,X2),sK5(X0,X1,X2)) = X3
        & r2_hidden(sK5(X0,X1,X2),X1)
        & r2_hidden(sK4(X0,X1,X2),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,(
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
              ( k4_tarski(X4,X5) != sK3(X0,X1,X2)
              | ~ r2_hidden(X5,X1)
              | ~ r2_hidden(X4,X0) )
          | ~ r2_hidden(sK3(X0,X1,X2),X2) )
        & ( ? [X7,X6] :
              ( k4_tarski(X6,X7) = sK3(X0,X1,X2)
              & r2_hidden(X7,X1)
              & r2_hidden(X6,X0) )
          | r2_hidden(sK3(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( ( k2_zfmisc_1(X0,X1) = X2
        | ( ( ! [X4,X5] :
                ( k4_tarski(X4,X5) != sK3(X0,X1,X2)
                | ~ r2_hidden(X5,X1)
                | ~ r2_hidden(X4,X0) )
            | ~ r2_hidden(sK3(X0,X1,X2),X2) )
          & ( ( k4_tarski(sK4(X0,X1,X2),sK5(X0,X1,X2)) = sK3(X0,X1,X2)
              & r2_hidden(sK5(X0,X1,X2),X1)
              & r2_hidden(sK4(X0,X1,X2),X0) )
            | r2_hidden(sK3(X0,X1,X2),X2) ) ) )
      & ( ! [X8] :
            ( ( r2_hidden(X8,X2)
              | ! [X9,X10] :
                  ( k4_tarski(X9,X10) != X8
                  | ~ r2_hidden(X10,X1)
                  | ~ r2_hidden(X9,X0) ) )
            & ( ( k4_tarski(sK6(X0,X1,X8),sK7(X0,X1,X8)) = X8
                & r2_hidden(sK7(X0,X1,X8),X1)
                & r2_hidden(sK6(X0,X1,X8),X0) )
              | ~ r2_hidden(X8,X2) ) )
        | k2_zfmisc_1(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5,sK6,sK7])],[f26,f29,f28,f27])).

fof(f45,plain,(
    ! [X2,X0,X8,X1] :
      ( r2_hidden(sK7(X0,X1,X8),X1)
      | ~ r2_hidden(X8,X2)
      | k2_zfmisc_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f30])).

fof(f63,plain,(
    ! [X0,X8,X1] :
      ( r2_hidden(sK7(X0,X1,X8),X1)
      | ~ r2_hidden(X8,k2_zfmisc_1(X0,X1)) ) ),
    inference(equality_resolution,[],[f45])).

fof(f3,axiom,(
    ! [X0] :
      ~ ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f3])).

fof(f23,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK2(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    ! [X0] :
      ( r2_hidden(sK2(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f14,f23])).

fof(f40,plain,(
    ! [X0] :
      ( r2_hidden(sK2(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f24])).

fof(f56,plain,(
    k1_xboole_0 != k2_zfmisc_1(sK8,sK9) ),
    inference(cnf_transformation,[],[f34])).

fof(f37,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK0(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f36,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK0(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f53,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X1,X3)
      | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f44,plain,(
    ! [X2,X0,X8,X1] :
      ( r2_hidden(sK6(X0,X1,X8),X0)
      | ~ r2_hidden(X8,X2)
      | k2_zfmisc_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f30])).

fof(f64,plain,(
    ! [X0,X8,X1] :
      ( r2_hidden(sK6(X0,X1,X8),X0)
      | ~ r2_hidden(X8,k2_zfmisc_1(X0,X1)) ) ),
    inference(equality_resolution,[],[f44])).

fof(f57,plain,
    ( ~ r1_tarski(sK9,sK11)
    | ~ r1_tarski(sK8,sK10) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_18,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(k4_tarski(X0,X2),k2_zfmisc_1(X1,X3)) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_2,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | ~ r1_tarski(X1,X2) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_21,negated_conjecture,
    ( r1_tarski(k2_zfmisc_1(sK8,sK9),k2_zfmisc_1(sK10,sK11)) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_1124,plain,
    ( r2_hidden(X0,k2_zfmisc_1(sK10,sK11))
    | ~ r2_hidden(X0,k2_zfmisc_1(sK8,sK9)) ),
    inference(resolution,[status(thm)],[c_2,c_21])).

cnf(c_1266,plain,
    ( r2_hidden(X0,sK10)
    | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(sK8,sK9)) ),
    inference(resolution,[status(thm)],[c_18,c_1124])).

cnf(c_16,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X2,X3)
    | r2_hidden(k4_tarski(X2,X0),k2_zfmisc_1(X3,X1)) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_3265,plain,
    ( r2_hidden(X0,sK10)
    | ~ r2_hidden(X0,sK8)
    | ~ r2_hidden(X1,sK9) ),
    inference(resolution,[status(thm)],[c_1266,c_16])).

cnf(c_14,plain,
    ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
    | r2_hidden(sK7(X1,X2,X0),X2) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_3611,plain,
    ( ~ r2_hidden(X0,k2_zfmisc_1(X1,sK9))
    | r2_hidden(X2,sK10)
    | ~ r2_hidden(X2,sK8) ),
    inference(resolution,[status(thm)],[c_3265,c_14])).

cnf(c_5,plain,
    ( r2_hidden(sK2(X0),X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f40])).

cnf(c_20,negated_conjecture,
    ( k1_xboole_0 != k2_zfmisc_1(sK8,sK9) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_975,plain,
    ( r2_hidden(sK2(k2_zfmisc_1(sK8,sK9)),k2_zfmisc_1(sK8,sK9)) ),
    inference(resolution,[status(thm)],[c_5,c_20])).

cnf(c_6040,plain,
    ( r2_hidden(X0,sK10)
    | ~ r2_hidden(X0,sK8) ),
    inference(resolution,[status(thm)],[c_3611,c_975])).

cnf(c_0,plain,
    ( ~ r2_hidden(sK0(X0,X1),X1)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_6370,plain,
    ( ~ r2_hidden(sK0(X0,sK10),sK8)
    | r1_tarski(X0,sK10) ),
    inference(resolution,[status(thm)],[c_6040,c_0])).

cnf(c_1,plain,
    ( r2_hidden(sK0(X0,X1),X0)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_6380,plain,
    ( r1_tarski(sK8,sK10) ),
    inference(resolution,[status(thm)],[c_6370,c_1])).

cnf(c_17,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(k4_tarski(X2,X0),k2_zfmisc_1(X3,X1)) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_1256,plain,
    ( r2_hidden(X0,sK11)
    | ~ r2_hidden(k4_tarski(X1,X0),k2_zfmisc_1(sK8,sK9)) ),
    inference(resolution,[status(thm)],[c_17,c_1124])).

cnf(c_3256,plain,
    ( ~ r2_hidden(X0,sK8)
    | r2_hidden(X1,sK11)
    | ~ r2_hidden(X1,sK9) ),
    inference(resolution,[status(thm)],[c_1256,c_16])).

cnf(c_15,plain,
    ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
    | r2_hidden(sK6(X1,X2,X0),X1) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_3571,plain,
    ( ~ r2_hidden(X0,k2_zfmisc_1(sK8,X1))
    | r2_hidden(X2,sK11)
    | ~ r2_hidden(X2,sK9) ),
    inference(resolution,[status(thm)],[c_3256,c_15])).

cnf(c_4996,plain,
    ( r2_hidden(X0,sK11)
    | ~ r2_hidden(X0,sK9) ),
    inference(resolution,[status(thm)],[c_3571,c_975])).

cnf(c_5006,plain,
    ( ~ r2_hidden(sK0(X0,sK11),sK9)
    | r1_tarski(X0,sK11) ),
    inference(resolution,[status(thm)],[c_4996,c_0])).

cnf(c_5407,plain,
    ( r1_tarski(sK9,sK11) ),
    inference(resolution,[status(thm)],[c_5006,c_1])).

cnf(c_19,negated_conjecture,
    ( ~ r1_tarski(sK8,sK10)
    | ~ r1_tarski(sK9,sK11) ),
    inference(cnf_transformation,[],[f57])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_6380,c_5407,c_19])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.12  % Command    : iproveropt_run.sh %d %s
% 0.13/0.33  % Computer   : n011.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 18:51:42 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 2.78/0.98  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.78/0.98  
% 2.78/0.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.78/0.98  
% 2.78/0.98  ------  iProver source info
% 2.78/0.98  
% 2.78/0.98  git: date: 2020-06-30 10:37:57 +0100
% 2.78/0.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.78/0.98  git: non_committed_changes: false
% 2.78/0.98  git: last_make_outside_of_git: false
% 2.78/0.98  
% 2.78/0.98  ------ 
% 2.78/0.98  ------ Parsing...
% 2.78/0.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.78/0.98  
% 2.78/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e  sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 2.78/0.98  
% 2.78/0.98  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.78/0.98  
% 2.78/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.78/0.98  ------ Proving...
% 2.78/0.98  ------ Problem Properties 
% 2.78/0.98  
% 2.78/0.98  
% 2.78/0.98  clauses                                 21
% 2.78/0.98  conjectures                             3
% 2.78/0.98  EPR                                     3
% 2.78/0.98  Horn                                    15
% 2.78/0.98  unary                                   4
% 2.78/0.98  binary                                  11
% 2.78/0.98  lits                                    46
% 2.78/0.98  lits eq                                 10
% 2.78/0.98  fd_pure                                 0
% 2.78/0.98  fd_pseudo                               0
% 2.78/0.98  fd_cond                                 1
% 2.78/0.98  fd_pseudo_cond                          4
% 2.78/0.98  AC symbols                              0
% 2.78/0.98  
% 2.78/0.98  ------ Input Options Time Limit: Unbounded
% 2.78/0.98  
% 2.78/0.98  
% 2.78/0.98  ------ 
% 2.78/0.98  Current options:
% 2.78/0.98  ------ 
% 2.78/0.98  
% 2.78/0.98  
% 2.78/0.98  
% 2.78/0.98  
% 2.78/0.98  ------ Proving...
% 2.78/0.98  
% 2.78/0.98  
% 2.78/0.98  % SZS status Theorem for theBenchmark.p
% 2.78/0.98  
% 2.78/0.98  % SZS output start CNFRefutation for theBenchmark.p
% 2.78/0.98  
% 2.78/0.98  fof(f8,axiom,(
% 2.78/0.98    ! [X0,X1,X2,X3] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) <=> (r2_hidden(X1,X3) & r2_hidden(X0,X2)))),
% 2.78/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.78/0.98  
% 2.78/0.98  fof(f31,plain,(
% 2.78/0.98    ! [X0,X1,X2,X3] : ((r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | (~r2_hidden(X1,X3) | ~r2_hidden(X0,X2))) & ((r2_hidden(X1,X3) & r2_hidden(X0,X2)) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))))),
% 2.78/0.98    inference(nnf_transformation,[],[f8])).
% 2.78/0.98  
% 2.78/0.98  fof(f32,plain,(
% 2.78/0.98    ! [X0,X1,X2,X3] : ((r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | ~r2_hidden(X1,X3) | ~r2_hidden(X0,X2)) & ((r2_hidden(X1,X3) & r2_hidden(X0,X2)) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))))),
% 2.78/0.98    inference(flattening,[],[f31])).
% 2.78/0.98  
% 2.78/0.98  fof(f52,plain,(
% 2.78/0.98    ( ! [X2,X0,X3,X1] : (r2_hidden(X0,X2) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))) )),
% 2.78/0.98    inference(cnf_transformation,[],[f32])).
% 2.78/0.98  
% 2.78/0.98  fof(f1,axiom,(
% 2.78/0.98    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 2.78/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.78/0.98  
% 2.78/0.98  fof(f12,plain,(
% 2.78/0.98    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 2.78/0.98    inference(ennf_transformation,[],[f1])).
% 2.78/0.98  
% 2.78/0.98  fof(f17,plain,(
% 2.78/0.98    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 2.78/0.98    inference(nnf_transformation,[],[f12])).
% 2.78/0.98  
% 2.78/0.98  fof(f18,plain,(
% 2.78/0.98    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 2.78/0.98    inference(rectify,[],[f17])).
% 2.78/0.98  
% 2.78/0.98  fof(f19,plain,(
% 2.78/0.98    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 2.78/0.98    introduced(choice_axiom,[])).
% 2.78/0.98  
% 2.78/0.98  fof(f20,plain,(
% 2.78/0.98    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 2.78/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f18,f19])).
% 2.78/0.98  
% 2.78/0.98  fof(f35,plain,(
% 2.78/0.98    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,X1)) )),
% 2.78/0.98    inference(cnf_transformation,[],[f20])).
% 2.78/0.98  
% 2.78/0.98  fof(f9,conjecture,(
% 2.78/0.98    ! [X0,X1,X2,X3] : (r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)) => ((r1_tarski(X1,X3) & r1_tarski(X0,X2)) | k1_xboole_0 = k2_zfmisc_1(X0,X1)))),
% 2.78/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.78/0.98  
% 2.78/0.98  fof(f10,negated_conjecture,(
% 2.78/0.98    ~! [X0,X1,X2,X3] : (r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)) => ((r1_tarski(X1,X3) & r1_tarski(X0,X2)) | k1_xboole_0 = k2_zfmisc_1(X0,X1)))),
% 2.78/0.98    inference(negated_conjecture,[],[f9])).
% 2.78/0.98  
% 2.78/0.98  fof(f15,plain,(
% 2.78/0.98    ? [X0,X1,X2,X3] : (((~r1_tarski(X1,X3) | ~r1_tarski(X0,X2)) & k1_xboole_0 != k2_zfmisc_1(X0,X1)) & r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)))),
% 2.78/0.98    inference(ennf_transformation,[],[f10])).
% 2.78/0.98  
% 2.78/0.98  fof(f16,plain,(
% 2.78/0.98    ? [X0,X1,X2,X3] : ((~r1_tarski(X1,X3) | ~r1_tarski(X0,X2)) & k1_xboole_0 != k2_zfmisc_1(X0,X1) & r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)))),
% 2.78/0.98    inference(flattening,[],[f15])).
% 2.78/0.98  
% 2.78/0.98  fof(f33,plain,(
% 2.78/0.98    ? [X0,X1,X2,X3] : ((~r1_tarski(X1,X3) | ~r1_tarski(X0,X2)) & k1_xboole_0 != k2_zfmisc_1(X0,X1) & r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3))) => ((~r1_tarski(sK9,sK11) | ~r1_tarski(sK8,sK10)) & k1_xboole_0 != k2_zfmisc_1(sK8,sK9) & r1_tarski(k2_zfmisc_1(sK8,sK9),k2_zfmisc_1(sK10,sK11)))),
% 2.78/0.98    introduced(choice_axiom,[])).
% 2.78/0.98  
% 2.78/0.98  fof(f34,plain,(
% 2.78/0.98    (~r1_tarski(sK9,sK11) | ~r1_tarski(sK8,sK10)) & k1_xboole_0 != k2_zfmisc_1(sK8,sK9) & r1_tarski(k2_zfmisc_1(sK8,sK9),k2_zfmisc_1(sK10,sK11))),
% 2.78/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8,sK9,sK10,sK11])],[f16,f33])).
% 2.78/0.98  
% 2.78/0.98  fof(f55,plain,(
% 2.78/0.98    r1_tarski(k2_zfmisc_1(sK8,sK9),k2_zfmisc_1(sK10,sK11))),
% 2.78/0.98    inference(cnf_transformation,[],[f34])).
% 2.78/0.98  
% 2.78/0.98  fof(f54,plain,(
% 2.78/0.98    ( ! [X2,X0,X3,X1] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | ~r2_hidden(X1,X3) | ~r2_hidden(X0,X2)) )),
% 2.78/0.98    inference(cnf_transformation,[],[f32])).
% 2.78/0.98  
% 2.78/0.98  fof(f7,axiom,(
% 2.78/0.98    ! [X0,X1,X2] : (k2_zfmisc_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4,X5] : (k4_tarski(X4,X5) = X3 & r2_hidden(X5,X1) & r2_hidden(X4,X0))))),
% 2.78/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.78/0.98  
% 2.78/0.98  fof(f25,plain,(
% 2.78/0.98    ! [X0,X1,X2] : ((k2_zfmisc_1(X0,X1) = X2 | ? [X3] : ((! [X4,X5] : (k4_tarski(X4,X5) != X3 | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X0)) | ~r2_hidden(X3,X2)) & (? [X4,X5] : (k4_tarski(X4,X5) = X3 & r2_hidden(X5,X1) & r2_hidden(X4,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ! [X4,X5] : (k4_tarski(X4,X5) != X3 | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X0))) & (? [X4,X5] : (k4_tarski(X4,X5) = X3 & r2_hidden(X5,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X3,X2))) | k2_zfmisc_1(X0,X1) != X2))),
% 2.78/0.98    inference(nnf_transformation,[],[f7])).
% 2.78/0.98  
% 2.78/0.98  fof(f26,plain,(
% 2.78/0.98    ! [X0,X1,X2] : ((k2_zfmisc_1(X0,X1) = X2 | ? [X3] : ((! [X4,X5] : (k4_tarski(X4,X5) != X3 | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X0)) | ~r2_hidden(X3,X2)) & (? [X6,X7] : (k4_tarski(X6,X7) = X3 & r2_hidden(X7,X1) & r2_hidden(X6,X0)) | r2_hidden(X3,X2)))) & (! [X8] : ((r2_hidden(X8,X2) | ! [X9,X10] : (k4_tarski(X9,X10) != X8 | ~r2_hidden(X10,X1) | ~r2_hidden(X9,X0))) & (? [X11,X12] : (k4_tarski(X11,X12) = X8 & r2_hidden(X12,X1) & r2_hidden(X11,X0)) | ~r2_hidden(X8,X2))) | k2_zfmisc_1(X0,X1) != X2))),
% 2.78/0.98    inference(rectify,[],[f25])).
% 2.78/0.98  
% 2.78/0.98  fof(f29,plain,(
% 2.78/0.98    ! [X8,X1,X0] : (? [X11,X12] : (k4_tarski(X11,X12) = X8 & r2_hidden(X12,X1) & r2_hidden(X11,X0)) => (k4_tarski(sK6(X0,X1,X8),sK7(X0,X1,X8)) = X8 & r2_hidden(sK7(X0,X1,X8),X1) & r2_hidden(sK6(X0,X1,X8),X0)))),
% 2.78/0.98    introduced(choice_axiom,[])).
% 2.78/0.98  
% 2.78/0.98  fof(f28,plain,(
% 2.78/0.98    ( ! [X3] : (! [X2,X1,X0] : (? [X6,X7] : (k4_tarski(X6,X7) = X3 & r2_hidden(X7,X1) & r2_hidden(X6,X0)) => (k4_tarski(sK4(X0,X1,X2),sK5(X0,X1,X2)) = X3 & r2_hidden(sK5(X0,X1,X2),X1) & r2_hidden(sK4(X0,X1,X2),X0)))) )),
% 2.78/0.98    introduced(choice_axiom,[])).
% 2.78/0.98  
% 2.78/0.98  fof(f27,plain,(
% 2.78/0.98    ! [X2,X1,X0] : (? [X3] : ((! [X4,X5] : (k4_tarski(X4,X5) != X3 | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X0)) | ~r2_hidden(X3,X2)) & (? [X6,X7] : (k4_tarski(X6,X7) = X3 & r2_hidden(X7,X1) & r2_hidden(X6,X0)) | r2_hidden(X3,X2))) => ((! [X5,X4] : (k4_tarski(X4,X5) != sK3(X0,X1,X2) | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X0)) | ~r2_hidden(sK3(X0,X1,X2),X2)) & (? [X7,X6] : (k4_tarski(X6,X7) = sK3(X0,X1,X2) & r2_hidden(X7,X1) & r2_hidden(X6,X0)) | r2_hidden(sK3(X0,X1,X2),X2))))),
% 2.78/0.98    introduced(choice_axiom,[])).
% 2.78/0.98  
% 2.78/0.98  fof(f30,plain,(
% 2.78/0.98    ! [X0,X1,X2] : ((k2_zfmisc_1(X0,X1) = X2 | ((! [X4,X5] : (k4_tarski(X4,X5) != sK3(X0,X1,X2) | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X0)) | ~r2_hidden(sK3(X0,X1,X2),X2)) & ((k4_tarski(sK4(X0,X1,X2),sK5(X0,X1,X2)) = sK3(X0,X1,X2) & r2_hidden(sK5(X0,X1,X2),X1) & r2_hidden(sK4(X0,X1,X2),X0)) | r2_hidden(sK3(X0,X1,X2),X2)))) & (! [X8] : ((r2_hidden(X8,X2) | ! [X9,X10] : (k4_tarski(X9,X10) != X8 | ~r2_hidden(X10,X1) | ~r2_hidden(X9,X0))) & ((k4_tarski(sK6(X0,X1,X8),sK7(X0,X1,X8)) = X8 & r2_hidden(sK7(X0,X1,X8),X1) & r2_hidden(sK6(X0,X1,X8),X0)) | ~r2_hidden(X8,X2))) | k2_zfmisc_1(X0,X1) != X2))),
% 2.78/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5,sK6,sK7])],[f26,f29,f28,f27])).
% 2.78/0.98  
% 2.78/0.98  fof(f45,plain,(
% 2.78/0.98    ( ! [X2,X0,X8,X1] : (r2_hidden(sK7(X0,X1,X8),X1) | ~r2_hidden(X8,X2) | k2_zfmisc_1(X0,X1) != X2) )),
% 2.78/0.98    inference(cnf_transformation,[],[f30])).
% 2.78/0.98  
% 2.78/0.98  fof(f63,plain,(
% 2.78/0.98    ( ! [X0,X8,X1] : (r2_hidden(sK7(X0,X1,X8),X1) | ~r2_hidden(X8,k2_zfmisc_1(X0,X1))) )),
% 2.78/0.98    inference(equality_resolution,[],[f45])).
% 2.78/0.98  
% 2.78/0.98  fof(f3,axiom,(
% 2.78/0.98    ! [X0] : ~(! [X1] : ~r2_hidden(X1,X0) & k1_xboole_0 != X0)),
% 2.78/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.78/0.98  
% 2.78/0.98  fof(f14,plain,(
% 2.78/0.98    ! [X0] : (? [X1] : r2_hidden(X1,X0) | k1_xboole_0 = X0)),
% 2.78/0.98    inference(ennf_transformation,[],[f3])).
% 2.78/0.98  
% 2.78/0.98  fof(f23,plain,(
% 2.78/0.98    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK2(X0),X0))),
% 2.78/0.98    introduced(choice_axiom,[])).
% 2.78/0.98  
% 2.78/0.98  fof(f24,plain,(
% 2.78/0.98    ! [X0] : (r2_hidden(sK2(X0),X0) | k1_xboole_0 = X0)),
% 2.78/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f14,f23])).
% 2.78/0.98  
% 2.78/0.98  fof(f40,plain,(
% 2.78/0.98    ( ! [X0] : (r2_hidden(sK2(X0),X0) | k1_xboole_0 = X0) )),
% 2.78/0.98    inference(cnf_transformation,[],[f24])).
% 2.78/0.98  
% 2.78/0.98  fof(f56,plain,(
% 2.78/0.98    k1_xboole_0 != k2_zfmisc_1(sK8,sK9)),
% 2.78/0.98    inference(cnf_transformation,[],[f34])).
% 2.78/0.98  
% 2.78/0.98  fof(f37,plain,(
% 2.78/0.98    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r2_hidden(sK0(X0,X1),X1)) )),
% 2.78/0.98    inference(cnf_transformation,[],[f20])).
% 2.78/0.98  
% 2.78/0.98  fof(f36,plain,(
% 2.78/0.98    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK0(X0,X1),X0)) )),
% 2.78/0.98    inference(cnf_transformation,[],[f20])).
% 2.78/0.98  
% 2.78/0.98  fof(f53,plain,(
% 2.78/0.98    ( ! [X2,X0,X3,X1] : (r2_hidden(X1,X3) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))) )),
% 2.78/0.98    inference(cnf_transformation,[],[f32])).
% 2.78/0.98  
% 2.78/0.98  fof(f44,plain,(
% 2.78/0.98    ( ! [X2,X0,X8,X1] : (r2_hidden(sK6(X0,X1,X8),X0) | ~r2_hidden(X8,X2) | k2_zfmisc_1(X0,X1) != X2) )),
% 2.78/0.98    inference(cnf_transformation,[],[f30])).
% 2.78/0.98  
% 2.78/0.98  fof(f64,plain,(
% 2.78/0.98    ( ! [X0,X8,X1] : (r2_hidden(sK6(X0,X1,X8),X0) | ~r2_hidden(X8,k2_zfmisc_1(X0,X1))) )),
% 2.78/0.98    inference(equality_resolution,[],[f44])).
% 2.78/0.98  
% 2.78/0.98  fof(f57,plain,(
% 2.78/0.98    ~r1_tarski(sK9,sK11) | ~r1_tarski(sK8,sK10)),
% 2.78/0.98    inference(cnf_transformation,[],[f34])).
% 2.78/0.98  
% 2.78/0.98  cnf(c_18,plain,
% 2.78/0.98      ( r2_hidden(X0,X1)
% 2.78/0.98      | ~ r2_hidden(k4_tarski(X0,X2),k2_zfmisc_1(X1,X3)) ),
% 2.78/0.98      inference(cnf_transformation,[],[f52]) ).
% 2.78/0.98  
% 2.78/0.98  cnf(c_2,plain,
% 2.78/0.98      ( ~ r2_hidden(X0,X1) | r2_hidden(X0,X2) | ~ r1_tarski(X1,X2) ),
% 2.78/0.98      inference(cnf_transformation,[],[f35]) ).
% 2.78/0.98  
% 2.78/0.98  cnf(c_21,negated_conjecture,
% 2.78/0.98      ( r1_tarski(k2_zfmisc_1(sK8,sK9),k2_zfmisc_1(sK10,sK11)) ),
% 2.78/0.98      inference(cnf_transformation,[],[f55]) ).
% 2.78/0.98  
% 2.78/0.98  cnf(c_1124,plain,
% 2.78/0.98      ( r2_hidden(X0,k2_zfmisc_1(sK10,sK11))
% 2.78/0.98      | ~ r2_hidden(X0,k2_zfmisc_1(sK8,sK9)) ),
% 2.78/0.98      inference(resolution,[status(thm)],[c_2,c_21]) ).
% 2.78/0.98  
% 2.78/0.98  cnf(c_1266,plain,
% 2.78/0.98      ( r2_hidden(X0,sK10)
% 2.78/0.98      | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(sK8,sK9)) ),
% 2.78/0.98      inference(resolution,[status(thm)],[c_18,c_1124]) ).
% 2.78/0.98  
% 2.78/0.98  cnf(c_16,plain,
% 2.78/0.98      ( ~ r2_hidden(X0,X1)
% 2.78/0.98      | ~ r2_hidden(X2,X3)
% 2.78/0.98      | r2_hidden(k4_tarski(X2,X0),k2_zfmisc_1(X3,X1)) ),
% 2.78/0.98      inference(cnf_transformation,[],[f54]) ).
% 2.78/0.98  
% 2.78/0.98  cnf(c_3265,plain,
% 2.78/0.98      ( r2_hidden(X0,sK10) | ~ r2_hidden(X0,sK8) | ~ r2_hidden(X1,sK9) ),
% 2.78/0.98      inference(resolution,[status(thm)],[c_1266,c_16]) ).
% 2.78/0.98  
% 2.78/0.98  cnf(c_14,plain,
% 2.78/0.98      ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
% 2.78/0.98      | r2_hidden(sK7(X1,X2,X0),X2) ),
% 2.78/0.98      inference(cnf_transformation,[],[f63]) ).
% 2.78/0.98  
% 2.78/0.98  cnf(c_3611,plain,
% 2.78/0.98      ( ~ r2_hidden(X0,k2_zfmisc_1(X1,sK9))
% 2.78/0.98      | r2_hidden(X2,sK10)
% 2.78/0.98      | ~ r2_hidden(X2,sK8) ),
% 2.78/0.98      inference(resolution,[status(thm)],[c_3265,c_14]) ).
% 2.78/0.98  
% 2.78/0.98  cnf(c_5,plain,
% 2.78/0.98      ( r2_hidden(sK2(X0),X0) | k1_xboole_0 = X0 ),
% 2.78/0.98      inference(cnf_transformation,[],[f40]) ).
% 2.78/0.98  
% 2.78/0.98  cnf(c_20,negated_conjecture,
% 2.78/0.98      ( k1_xboole_0 != k2_zfmisc_1(sK8,sK9) ),
% 2.78/0.98      inference(cnf_transformation,[],[f56]) ).
% 2.78/0.98  
% 2.78/0.98  cnf(c_975,plain,
% 2.78/0.98      ( r2_hidden(sK2(k2_zfmisc_1(sK8,sK9)),k2_zfmisc_1(sK8,sK9)) ),
% 2.78/0.98      inference(resolution,[status(thm)],[c_5,c_20]) ).
% 2.78/0.98  
% 2.78/0.98  cnf(c_6040,plain,
% 2.78/0.98      ( r2_hidden(X0,sK10) | ~ r2_hidden(X0,sK8) ),
% 2.78/0.98      inference(resolution,[status(thm)],[c_3611,c_975]) ).
% 2.78/0.98  
% 2.78/0.98  cnf(c_0,plain,
% 2.78/0.98      ( ~ r2_hidden(sK0(X0,X1),X1) | r1_tarski(X0,X1) ),
% 2.78/0.98      inference(cnf_transformation,[],[f37]) ).
% 2.78/0.98  
% 2.78/0.98  cnf(c_6370,plain,
% 2.78/0.98      ( ~ r2_hidden(sK0(X0,sK10),sK8) | r1_tarski(X0,sK10) ),
% 2.78/0.98      inference(resolution,[status(thm)],[c_6040,c_0]) ).
% 2.78/0.98  
% 2.78/0.98  cnf(c_1,plain,
% 2.78/0.98      ( r2_hidden(sK0(X0,X1),X0) | r1_tarski(X0,X1) ),
% 2.78/0.98      inference(cnf_transformation,[],[f36]) ).
% 2.78/0.98  
% 2.78/0.98  cnf(c_6380,plain,
% 2.78/0.98      ( r1_tarski(sK8,sK10) ),
% 2.78/0.98      inference(resolution,[status(thm)],[c_6370,c_1]) ).
% 2.78/0.98  
% 2.78/0.98  cnf(c_17,plain,
% 2.78/0.98      ( r2_hidden(X0,X1)
% 2.78/0.98      | ~ r2_hidden(k4_tarski(X2,X0),k2_zfmisc_1(X3,X1)) ),
% 2.78/0.98      inference(cnf_transformation,[],[f53]) ).
% 2.78/0.98  
% 2.78/0.98  cnf(c_1256,plain,
% 2.78/0.98      ( r2_hidden(X0,sK11)
% 2.78/0.98      | ~ r2_hidden(k4_tarski(X1,X0),k2_zfmisc_1(sK8,sK9)) ),
% 2.78/0.98      inference(resolution,[status(thm)],[c_17,c_1124]) ).
% 2.78/0.98  
% 2.78/0.98  cnf(c_3256,plain,
% 2.78/0.98      ( ~ r2_hidden(X0,sK8) | r2_hidden(X1,sK11) | ~ r2_hidden(X1,sK9) ),
% 2.78/0.98      inference(resolution,[status(thm)],[c_1256,c_16]) ).
% 2.78/0.98  
% 2.78/0.98  cnf(c_15,plain,
% 2.78/0.98      ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
% 2.78/0.98      | r2_hidden(sK6(X1,X2,X0),X1) ),
% 2.78/0.98      inference(cnf_transformation,[],[f64]) ).
% 2.78/0.98  
% 2.78/0.98  cnf(c_3571,plain,
% 2.78/0.98      ( ~ r2_hidden(X0,k2_zfmisc_1(sK8,X1))
% 2.78/0.98      | r2_hidden(X2,sK11)
% 2.78/0.98      | ~ r2_hidden(X2,sK9) ),
% 2.78/0.98      inference(resolution,[status(thm)],[c_3256,c_15]) ).
% 2.78/0.98  
% 2.78/0.98  cnf(c_4996,plain,
% 2.78/0.98      ( r2_hidden(X0,sK11) | ~ r2_hidden(X0,sK9) ),
% 2.78/0.98      inference(resolution,[status(thm)],[c_3571,c_975]) ).
% 2.78/0.98  
% 2.78/0.98  cnf(c_5006,plain,
% 2.78/0.98      ( ~ r2_hidden(sK0(X0,sK11),sK9) | r1_tarski(X0,sK11) ),
% 2.78/0.98      inference(resolution,[status(thm)],[c_4996,c_0]) ).
% 2.78/0.98  
% 2.78/0.98  cnf(c_5407,plain,
% 2.78/0.98      ( r1_tarski(sK9,sK11) ),
% 2.78/0.98      inference(resolution,[status(thm)],[c_5006,c_1]) ).
% 2.78/0.98  
% 2.78/0.98  cnf(c_19,negated_conjecture,
% 2.78/0.98      ( ~ r1_tarski(sK8,sK10) | ~ r1_tarski(sK9,sK11) ),
% 2.78/0.98      inference(cnf_transformation,[],[f57]) ).
% 2.78/0.98  
% 2.78/0.98  cnf(contradiction,plain,
% 2.78/0.98      ( $false ),
% 2.78/0.98      inference(minisat,[status(thm)],[c_6380,c_5407,c_19]) ).
% 2.78/0.98  
% 2.78/0.98  
% 2.78/0.98  % SZS output end CNFRefutation for theBenchmark.p
% 2.78/0.98  
% 2.78/0.98  ------                               Statistics
% 2.78/0.98  
% 2.78/0.98  ------ Selected
% 2.78/0.98  
% 2.78/0.98  total_time:                             0.196
% 2.78/0.98  
%------------------------------------------------------------------------------
