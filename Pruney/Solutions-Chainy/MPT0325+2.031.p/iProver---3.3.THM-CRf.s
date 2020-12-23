%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:37:50 EST 2020

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

fof(f33,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
        | ~ r2_hidden(X1,X3)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X3)
          & r2_hidden(X0,X2) )
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ) ),
    inference(nnf_transformation,[],[f8])).

fof(f34,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
        | ~ r2_hidden(X1,X3)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X3)
          & r2_hidden(X0,X2) )
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ) ),
    inference(flattening,[],[f33])).

fof(f59,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X0,X2)
      | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f11])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f15])).

fof(f17,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK0(X0,X1),X1)
          & r2_hidden(sK0(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f16,f17])).

fof(f37,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

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

fof(f13,plain,(
    ? [X0,X1,X2,X3] :
      ( ( ~ r1_tarski(X1,X3)
        | ~ r1_tarski(X0,X2) )
      & k1_xboole_0 != k2_zfmisc_1(X0,X1)
      & r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f14,plain,(
    ? [X0,X1,X2,X3] :
      ( ( ~ r1_tarski(X1,X3)
        | ~ r1_tarski(X0,X2) )
      & k1_xboole_0 != k2_zfmisc_1(X0,X1)
      & r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)) ) ),
    inference(flattening,[],[f13])).

fof(f35,plain,
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

fof(f36,plain,
    ( ( ~ r1_tarski(sK9,sK11)
      | ~ r1_tarski(sK8,sK10) )
    & k1_xboole_0 != k2_zfmisc_1(sK8,sK9)
    & r1_tarski(k2_zfmisc_1(sK8,sK9),k2_zfmisc_1(sK10,sK11)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8,sK9,sK10,sK11])],[f14,f35])).

fof(f62,plain,(
    r1_tarski(k2_zfmisc_1(sK8,sK9),k2_zfmisc_1(sK10,sK11)) ),
    inference(cnf_transformation,[],[f36])).

fof(f61,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
      | ~ r2_hidden(X1,X3)
      | ~ r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f34])).

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

fof(f27,plain,(
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

fof(f28,plain,(
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
    inference(rectify,[],[f27])).

fof(f31,plain,(
    ! [X8,X1,X0] :
      ( ? [X11,X12] :
          ( k4_tarski(X11,X12) = X8
          & r2_hidden(X12,X1)
          & r2_hidden(X11,X0) )
     => ( k4_tarski(sK6(X0,X1,X8),sK7(X0,X1,X8)) = X8
        & r2_hidden(sK7(X0,X1,X8),X1)
        & r2_hidden(sK6(X0,X1,X8),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X6,X7] :
          ( k4_tarski(X6,X7) = X3
          & r2_hidden(X7,X1)
          & r2_hidden(X6,X0) )
     => ( k4_tarski(sK4(X0,X1,X2),sK5(X0,X1,X2)) = X3
        & r2_hidden(sK5(X0,X1,X2),X1)
        & r2_hidden(sK4(X0,X1,X2),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,(
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

fof(f32,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5,sK6,sK7])],[f28,f31,f30,f29])).

fof(f52,plain,(
    ! [X2,X0,X8,X1] :
      ( r2_hidden(sK7(X0,X1,X8),X1)
      | ~ r2_hidden(X8,X2)
      | k2_zfmisc_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f32])).

fof(f71,plain,(
    ! [X0,X8,X1] :
      ( r2_hidden(sK7(X0,X1,X8),X1)
      | ~ r2_hidden(X8,k2_zfmisc_1(X0,X1)) ) ),
    inference(equality_resolution,[],[f52])).

fof(f3,axiom,(
    ! [X0] :
      ~ ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f3])).

fof(f24,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK2(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
    ! [X0] :
      ( r2_hidden(sK2(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f12,f24])).

fof(f46,plain,(
    ! [X0] :
      ( r2_hidden(sK2(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f63,plain,(
    k1_xboole_0 != k2_zfmisc_1(sK8,sK9) ),
    inference(cnf_transformation,[],[f36])).

fof(f39,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK0(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f38,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK0(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f60,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X1,X3)
      | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f51,plain,(
    ! [X2,X0,X8,X1] :
      ( r2_hidden(sK6(X0,X1,X8),X0)
      | ~ r2_hidden(X8,X2)
      | k2_zfmisc_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f32])).

fof(f72,plain,(
    ! [X0,X8,X1] :
      ( r2_hidden(sK6(X0,X1,X8),X0)
      | ~ r2_hidden(X8,k2_zfmisc_1(X0,X1)) ) ),
    inference(equality_resolution,[],[f51])).

fof(f64,plain,
    ( ~ r1_tarski(sK9,sK11)
    | ~ r1_tarski(sK8,sK10) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_24,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(k4_tarski(X0,X2),k2_zfmisc_1(X1,X3)) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_2,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | ~ r1_tarski(X1,X2) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_27,negated_conjecture,
    ( r1_tarski(k2_zfmisc_1(sK8,sK9),k2_zfmisc_1(sK10,sK11)) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_1619,plain,
    ( r2_hidden(X0,k2_zfmisc_1(sK10,sK11))
    | ~ r2_hidden(X0,k2_zfmisc_1(sK8,sK9)) ),
    inference(resolution,[status(thm)],[c_2,c_27])).

cnf(c_2368,plain,
    ( r2_hidden(X0,sK10)
    | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(sK8,sK9)) ),
    inference(resolution,[status(thm)],[c_24,c_1619])).

cnf(c_22,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X2,X3)
    | r2_hidden(k4_tarski(X2,X0),k2_zfmisc_1(X3,X1)) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_3449,plain,
    ( r2_hidden(X0,sK10)
    | ~ r2_hidden(X0,sK8)
    | ~ r2_hidden(X1,sK9) ),
    inference(resolution,[status(thm)],[c_2368,c_22])).

cnf(c_20,plain,
    ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
    | r2_hidden(sK7(X1,X2,X0),X2) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_3553,plain,
    ( ~ r2_hidden(X0,k2_zfmisc_1(X1,sK9))
    | r2_hidden(X2,sK10)
    | ~ r2_hidden(X2,sK8) ),
    inference(resolution,[status(thm)],[c_3449,c_20])).

cnf(c_9,plain,
    ( r2_hidden(sK2(X0),X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f46])).

cnf(c_26,negated_conjecture,
    ( k1_xboole_0 != k2_zfmisc_1(sK8,sK9) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_1350,plain,
    ( r2_hidden(sK2(k2_zfmisc_1(sK8,sK9)),k2_zfmisc_1(sK8,sK9)) ),
    inference(resolution,[status(thm)],[c_9,c_26])).

cnf(c_5383,plain,
    ( r2_hidden(X0,sK10)
    | ~ r2_hidden(X0,sK8) ),
    inference(resolution,[status(thm)],[c_3553,c_1350])).

cnf(c_0,plain,
    ( ~ r2_hidden(sK0(X0,X1),X1)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_5394,plain,
    ( ~ r2_hidden(sK0(X0,sK10),sK8)
    | r1_tarski(X0,sK10) ),
    inference(resolution,[status(thm)],[c_5383,c_0])).

cnf(c_1,plain,
    ( r2_hidden(sK0(X0,X1),X0)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_5404,plain,
    ( r1_tarski(sK8,sK10) ),
    inference(resolution,[status(thm)],[c_5394,c_1])).

cnf(c_23,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(k4_tarski(X2,X0),k2_zfmisc_1(X3,X1)) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_2203,plain,
    ( r2_hidden(X0,sK11)
    | ~ r2_hidden(k4_tarski(X1,X0),k2_zfmisc_1(sK8,sK9)) ),
    inference(resolution,[status(thm)],[c_23,c_1619])).

cnf(c_3440,plain,
    ( ~ r2_hidden(X0,sK8)
    | r2_hidden(X1,sK11)
    | ~ r2_hidden(X1,sK9) ),
    inference(resolution,[status(thm)],[c_2203,c_22])).

cnf(c_21,plain,
    ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
    | r2_hidden(sK6(X1,X2,X0),X1) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_3529,plain,
    ( ~ r2_hidden(X0,k2_zfmisc_1(sK8,X1))
    | r2_hidden(X2,sK11)
    | ~ r2_hidden(X2,sK9) ),
    inference(resolution,[status(thm)],[c_3440,c_21])).

cnf(c_4269,plain,
    ( r2_hidden(X0,sK11)
    | ~ r2_hidden(X0,sK9) ),
    inference(resolution,[status(thm)],[c_3529,c_1350])).

cnf(c_4280,plain,
    ( ~ r2_hidden(sK0(X0,sK11),sK9)
    | r1_tarski(X0,sK11) ),
    inference(resolution,[status(thm)],[c_4269,c_0])).

cnf(c_4487,plain,
    ( r1_tarski(sK9,sK11) ),
    inference(resolution,[status(thm)],[c_4280,c_1])).

cnf(c_25,negated_conjecture,
    ( ~ r1_tarski(sK8,sK10)
    | ~ r1_tarski(sK9,sK11) ),
    inference(cnf_transformation,[],[f64])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_5404,c_4487,c_25])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 11:48:23 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 2.78/1.00  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.78/1.00  
% 2.78/1.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.78/1.00  
% 2.78/1.00  ------  iProver source info
% 2.78/1.00  
% 2.78/1.00  git: date: 2020-06-30 10:37:57 +0100
% 2.78/1.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.78/1.00  git: non_committed_changes: false
% 2.78/1.00  git: last_make_outside_of_git: false
% 2.78/1.00  
% 2.78/1.00  ------ 
% 2.78/1.00  ------ Parsing...
% 2.78/1.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.78/1.00  
% 2.78/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e  sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 2.78/1.00  
% 2.78/1.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.78/1.00  
% 2.78/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.78/1.00  ------ Proving...
% 2.78/1.00  ------ Problem Properties 
% 2.78/1.00  
% 2.78/1.00  
% 2.78/1.00  clauses                                 27
% 2.78/1.00  conjectures                             3
% 2.78/1.00  EPR                                     2
% 2.78/1.00  Horn                                    18
% 2.78/1.00  unary                                   4
% 2.78/1.00  binary                                  13
% 2.78/1.00  lits                                    63
% 2.78/1.00  lits eq                                 16
% 2.78/1.00  fd_pure                                 0
% 2.78/1.00  fd_pseudo                               0
% 2.78/1.00  fd_cond                                 1
% 2.78/1.00  fd_pseudo_cond                          7
% 2.78/1.00  AC symbols                              0
% 2.78/1.00  
% 2.78/1.00  ------ Input Options Time Limit: Unbounded
% 2.78/1.00  
% 2.78/1.00  
% 2.78/1.00  ------ 
% 2.78/1.00  Current options:
% 2.78/1.00  ------ 
% 2.78/1.00  
% 2.78/1.00  
% 2.78/1.00  
% 2.78/1.00  
% 2.78/1.00  ------ Proving...
% 2.78/1.00  
% 2.78/1.00  
% 2.78/1.00  % SZS status Theorem for theBenchmark.p
% 2.78/1.00  
% 2.78/1.00  % SZS output start CNFRefutation for theBenchmark.p
% 2.78/1.00  
% 2.78/1.00  fof(f8,axiom,(
% 2.78/1.00    ! [X0,X1,X2,X3] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) <=> (r2_hidden(X1,X3) & r2_hidden(X0,X2)))),
% 2.78/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.78/1.00  
% 2.78/1.00  fof(f33,plain,(
% 2.78/1.00    ! [X0,X1,X2,X3] : ((r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | (~r2_hidden(X1,X3) | ~r2_hidden(X0,X2))) & ((r2_hidden(X1,X3) & r2_hidden(X0,X2)) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))))),
% 2.78/1.00    inference(nnf_transformation,[],[f8])).
% 2.78/1.00  
% 2.78/1.00  fof(f34,plain,(
% 2.78/1.00    ! [X0,X1,X2,X3] : ((r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | ~r2_hidden(X1,X3) | ~r2_hidden(X0,X2)) & ((r2_hidden(X1,X3) & r2_hidden(X0,X2)) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))))),
% 2.78/1.00    inference(flattening,[],[f33])).
% 2.78/1.00  
% 2.78/1.00  fof(f59,plain,(
% 2.78/1.00    ( ! [X2,X0,X3,X1] : (r2_hidden(X0,X2) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))) )),
% 2.78/1.00    inference(cnf_transformation,[],[f34])).
% 2.78/1.00  
% 2.78/1.00  fof(f1,axiom,(
% 2.78/1.00    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 2.78/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.78/1.00  
% 2.78/1.00  fof(f11,plain,(
% 2.78/1.00    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 2.78/1.00    inference(ennf_transformation,[],[f1])).
% 2.78/1.00  
% 2.78/1.00  fof(f15,plain,(
% 2.78/1.00    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 2.78/1.00    inference(nnf_transformation,[],[f11])).
% 2.78/1.00  
% 2.78/1.00  fof(f16,plain,(
% 2.78/1.00    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 2.78/1.00    inference(rectify,[],[f15])).
% 2.78/1.00  
% 2.78/1.00  fof(f17,plain,(
% 2.78/1.00    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 2.78/1.00    introduced(choice_axiom,[])).
% 2.78/1.00  
% 2.78/1.00  fof(f18,plain,(
% 2.78/1.00    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 2.78/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f16,f17])).
% 2.78/1.00  
% 2.78/1.00  fof(f37,plain,(
% 2.78/1.00    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,X1)) )),
% 2.78/1.00    inference(cnf_transformation,[],[f18])).
% 2.78/1.00  
% 2.78/1.00  fof(f9,conjecture,(
% 2.78/1.00    ! [X0,X1,X2,X3] : (r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)) => ((r1_tarski(X1,X3) & r1_tarski(X0,X2)) | k1_xboole_0 = k2_zfmisc_1(X0,X1)))),
% 2.78/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.78/1.00  
% 2.78/1.00  fof(f10,negated_conjecture,(
% 2.78/1.00    ~! [X0,X1,X2,X3] : (r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)) => ((r1_tarski(X1,X3) & r1_tarski(X0,X2)) | k1_xboole_0 = k2_zfmisc_1(X0,X1)))),
% 2.78/1.00    inference(negated_conjecture,[],[f9])).
% 2.78/1.00  
% 2.78/1.00  fof(f13,plain,(
% 2.78/1.00    ? [X0,X1,X2,X3] : (((~r1_tarski(X1,X3) | ~r1_tarski(X0,X2)) & k1_xboole_0 != k2_zfmisc_1(X0,X1)) & r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)))),
% 2.78/1.00    inference(ennf_transformation,[],[f10])).
% 2.78/1.00  
% 2.78/1.00  fof(f14,plain,(
% 2.78/1.00    ? [X0,X1,X2,X3] : ((~r1_tarski(X1,X3) | ~r1_tarski(X0,X2)) & k1_xboole_0 != k2_zfmisc_1(X0,X1) & r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)))),
% 2.78/1.00    inference(flattening,[],[f13])).
% 2.78/1.00  
% 2.78/1.00  fof(f35,plain,(
% 2.78/1.00    ? [X0,X1,X2,X3] : ((~r1_tarski(X1,X3) | ~r1_tarski(X0,X2)) & k1_xboole_0 != k2_zfmisc_1(X0,X1) & r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3))) => ((~r1_tarski(sK9,sK11) | ~r1_tarski(sK8,sK10)) & k1_xboole_0 != k2_zfmisc_1(sK8,sK9) & r1_tarski(k2_zfmisc_1(sK8,sK9),k2_zfmisc_1(sK10,sK11)))),
% 2.78/1.00    introduced(choice_axiom,[])).
% 2.78/1.00  
% 2.78/1.00  fof(f36,plain,(
% 2.78/1.00    (~r1_tarski(sK9,sK11) | ~r1_tarski(sK8,sK10)) & k1_xboole_0 != k2_zfmisc_1(sK8,sK9) & r1_tarski(k2_zfmisc_1(sK8,sK9),k2_zfmisc_1(sK10,sK11))),
% 2.78/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8,sK9,sK10,sK11])],[f14,f35])).
% 2.78/1.00  
% 2.78/1.00  fof(f62,plain,(
% 2.78/1.00    r1_tarski(k2_zfmisc_1(sK8,sK9),k2_zfmisc_1(sK10,sK11))),
% 2.78/1.00    inference(cnf_transformation,[],[f36])).
% 2.78/1.00  
% 2.78/1.00  fof(f61,plain,(
% 2.78/1.00    ( ! [X2,X0,X3,X1] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | ~r2_hidden(X1,X3) | ~r2_hidden(X0,X2)) )),
% 2.78/1.00    inference(cnf_transformation,[],[f34])).
% 2.78/1.00  
% 2.78/1.00  fof(f7,axiom,(
% 2.78/1.00    ! [X0,X1,X2] : (k2_zfmisc_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4,X5] : (k4_tarski(X4,X5) = X3 & r2_hidden(X5,X1) & r2_hidden(X4,X0))))),
% 2.78/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.78/1.00  
% 2.78/1.00  fof(f27,plain,(
% 2.78/1.00    ! [X0,X1,X2] : ((k2_zfmisc_1(X0,X1) = X2 | ? [X3] : ((! [X4,X5] : (k4_tarski(X4,X5) != X3 | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X0)) | ~r2_hidden(X3,X2)) & (? [X4,X5] : (k4_tarski(X4,X5) = X3 & r2_hidden(X5,X1) & r2_hidden(X4,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ! [X4,X5] : (k4_tarski(X4,X5) != X3 | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X0))) & (? [X4,X5] : (k4_tarski(X4,X5) = X3 & r2_hidden(X5,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X3,X2))) | k2_zfmisc_1(X0,X1) != X2))),
% 2.78/1.00    inference(nnf_transformation,[],[f7])).
% 2.78/1.00  
% 2.78/1.00  fof(f28,plain,(
% 2.78/1.00    ! [X0,X1,X2] : ((k2_zfmisc_1(X0,X1) = X2 | ? [X3] : ((! [X4,X5] : (k4_tarski(X4,X5) != X3 | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X0)) | ~r2_hidden(X3,X2)) & (? [X6,X7] : (k4_tarski(X6,X7) = X3 & r2_hidden(X7,X1) & r2_hidden(X6,X0)) | r2_hidden(X3,X2)))) & (! [X8] : ((r2_hidden(X8,X2) | ! [X9,X10] : (k4_tarski(X9,X10) != X8 | ~r2_hidden(X10,X1) | ~r2_hidden(X9,X0))) & (? [X11,X12] : (k4_tarski(X11,X12) = X8 & r2_hidden(X12,X1) & r2_hidden(X11,X0)) | ~r2_hidden(X8,X2))) | k2_zfmisc_1(X0,X1) != X2))),
% 2.78/1.00    inference(rectify,[],[f27])).
% 2.78/1.00  
% 2.78/1.00  fof(f31,plain,(
% 2.78/1.00    ! [X8,X1,X0] : (? [X11,X12] : (k4_tarski(X11,X12) = X8 & r2_hidden(X12,X1) & r2_hidden(X11,X0)) => (k4_tarski(sK6(X0,X1,X8),sK7(X0,X1,X8)) = X8 & r2_hidden(sK7(X0,X1,X8),X1) & r2_hidden(sK6(X0,X1,X8),X0)))),
% 2.78/1.00    introduced(choice_axiom,[])).
% 2.78/1.00  
% 2.78/1.00  fof(f30,plain,(
% 2.78/1.00    ( ! [X3] : (! [X2,X1,X0] : (? [X6,X7] : (k4_tarski(X6,X7) = X3 & r2_hidden(X7,X1) & r2_hidden(X6,X0)) => (k4_tarski(sK4(X0,X1,X2),sK5(X0,X1,X2)) = X3 & r2_hidden(sK5(X0,X1,X2),X1) & r2_hidden(sK4(X0,X1,X2),X0)))) )),
% 2.78/1.00    introduced(choice_axiom,[])).
% 2.78/1.00  
% 2.78/1.00  fof(f29,plain,(
% 2.78/1.00    ! [X2,X1,X0] : (? [X3] : ((! [X4,X5] : (k4_tarski(X4,X5) != X3 | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X0)) | ~r2_hidden(X3,X2)) & (? [X6,X7] : (k4_tarski(X6,X7) = X3 & r2_hidden(X7,X1) & r2_hidden(X6,X0)) | r2_hidden(X3,X2))) => ((! [X5,X4] : (k4_tarski(X4,X5) != sK3(X0,X1,X2) | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X0)) | ~r2_hidden(sK3(X0,X1,X2),X2)) & (? [X7,X6] : (k4_tarski(X6,X7) = sK3(X0,X1,X2) & r2_hidden(X7,X1) & r2_hidden(X6,X0)) | r2_hidden(sK3(X0,X1,X2),X2))))),
% 2.78/1.00    introduced(choice_axiom,[])).
% 2.78/1.00  
% 2.78/1.00  fof(f32,plain,(
% 2.78/1.00    ! [X0,X1,X2] : ((k2_zfmisc_1(X0,X1) = X2 | ((! [X4,X5] : (k4_tarski(X4,X5) != sK3(X0,X1,X2) | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X0)) | ~r2_hidden(sK3(X0,X1,X2),X2)) & ((k4_tarski(sK4(X0,X1,X2),sK5(X0,X1,X2)) = sK3(X0,X1,X2) & r2_hidden(sK5(X0,X1,X2),X1) & r2_hidden(sK4(X0,X1,X2),X0)) | r2_hidden(sK3(X0,X1,X2),X2)))) & (! [X8] : ((r2_hidden(X8,X2) | ! [X9,X10] : (k4_tarski(X9,X10) != X8 | ~r2_hidden(X10,X1) | ~r2_hidden(X9,X0))) & ((k4_tarski(sK6(X0,X1,X8),sK7(X0,X1,X8)) = X8 & r2_hidden(sK7(X0,X1,X8),X1) & r2_hidden(sK6(X0,X1,X8),X0)) | ~r2_hidden(X8,X2))) | k2_zfmisc_1(X0,X1) != X2))),
% 2.78/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5,sK6,sK7])],[f28,f31,f30,f29])).
% 2.78/1.00  
% 2.78/1.00  fof(f52,plain,(
% 2.78/1.00    ( ! [X2,X0,X8,X1] : (r2_hidden(sK7(X0,X1,X8),X1) | ~r2_hidden(X8,X2) | k2_zfmisc_1(X0,X1) != X2) )),
% 2.78/1.00    inference(cnf_transformation,[],[f32])).
% 2.78/1.00  
% 2.78/1.00  fof(f71,plain,(
% 2.78/1.00    ( ! [X0,X8,X1] : (r2_hidden(sK7(X0,X1,X8),X1) | ~r2_hidden(X8,k2_zfmisc_1(X0,X1))) )),
% 2.78/1.00    inference(equality_resolution,[],[f52])).
% 2.78/1.00  
% 2.78/1.00  fof(f3,axiom,(
% 2.78/1.00    ! [X0] : ~(! [X1] : ~r2_hidden(X1,X0) & k1_xboole_0 != X0)),
% 2.78/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.78/1.00  
% 2.78/1.00  fof(f12,plain,(
% 2.78/1.00    ! [X0] : (? [X1] : r2_hidden(X1,X0) | k1_xboole_0 = X0)),
% 2.78/1.00    inference(ennf_transformation,[],[f3])).
% 2.78/1.00  
% 2.78/1.00  fof(f24,plain,(
% 2.78/1.00    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK2(X0),X0))),
% 2.78/1.00    introduced(choice_axiom,[])).
% 2.78/1.00  
% 2.78/1.00  fof(f25,plain,(
% 2.78/1.00    ! [X0] : (r2_hidden(sK2(X0),X0) | k1_xboole_0 = X0)),
% 2.78/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f12,f24])).
% 2.78/1.00  
% 2.78/1.00  fof(f46,plain,(
% 2.78/1.00    ( ! [X0] : (r2_hidden(sK2(X0),X0) | k1_xboole_0 = X0) )),
% 2.78/1.00    inference(cnf_transformation,[],[f25])).
% 2.78/1.00  
% 2.78/1.00  fof(f63,plain,(
% 2.78/1.00    k1_xboole_0 != k2_zfmisc_1(sK8,sK9)),
% 2.78/1.00    inference(cnf_transformation,[],[f36])).
% 2.78/1.00  
% 2.78/1.00  fof(f39,plain,(
% 2.78/1.00    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r2_hidden(sK0(X0,X1),X1)) )),
% 2.78/1.00    inference(cnf_transformation,[],[f18])).
% 2.78/1.00  
% 2.78/1.00  fof(f38,plain,(
% 2.78/1.00    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK0(X0,X1),X0)) )),
% 2.78/1.00    inference(cnf_transformation,[],[f18])).
% 2.78/1.00  
% 2.78/1.00  fof(f60,plain,(
% 2.78/1.00    ( ! [X2,X0,X3,X1] : (r2_hidden(X1,X3) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))) )),
% 2.78/1.00    inference(cnf_transformation,[],[f34])).
% 2.78/1.00  
% 2.78/1.00  fof(f51,plain,(
% 2.78/1.00    ( ! [X2,X0,X8,X1] : (r2_hidden(sK6(X0,X1,X8),X0) | ~r2_hidden(X8,X2) | k2_zfmisc_1(X0,X1) != X2) )),
% 2.78/1.00    inference(cnf_transformation,[],[f32])).
% 2.78/1.00  
% 2.78/1.00  fof(f72,plain,(
% 2.78/1.00    ( ! [X0,X8,X1] : (r2_hidden(sK6(X0,X1,X8),X0) | ~r2_hidden(X8,k2_zfmisc_1(X0,X1))) )),
% 2.78/1.00    inference(equality_resolution,[],[f51])).
% 2.78/1.00  
% 2.78/1.00  fof(f64,plain,(
% 2.78/1.00    ~r1_tarski(sK9,sK11) | ~r1_tarski(sK8,sK10)),
% 2.78/1.00    inference(cnf_transformation,[],[f36])).
% 2.78/1.00  
% 2.78/1.00  cnf(c_24,plain,
% 2.78/1.00      ( r2_hidden(X0,X1)
% 2.78/1.00      | ~ r2_hidden(k4_tarski(X0,X2),k2_zfmisc_1(X1,X3)) ),
% 2.78/1.00      inference(cnf_transformation,[],[f59]) ).
% 2.78/1.00  
% 2.78/1.00  cnf(c_2,plain,
% 2.78/1.00      ( ~ r2_hidden(X0,X1) | r2_hidden(X0,X2) | ~ r1_tarski(X1,X2) ),
% 2.78/1.00      inference(cnf_transformation,[],[f37]) ).
% 2.78/1.00  
% 2.78/1.00  cnf(c_27,negated_conjecture,
% 2.78/1.00      ( r1_tarski(k2_zfmisc_1(sK8,sK9),k2_zfmisc_1(sK10,sK11)) ),
% 2.78/1.00      inference(cnf_transformation,[],[f62]) ).
% 2.78/1.00  
% 2.78/1.00  cnf(c_1619,plain,
% 2.78/1.00      ( r2_hidden(X0,k2_zfmisc_1(sK10,sK11))
% 2.78/1.00      | ~ r2_hidden(X0,k2_zfmisc_1(sK8,sK9)) ),
% 2.78/1.00      inference(resolution,[status(thm)],[c_2,c_27]) ).
% 2.78/1.00  
% 2.78/1.00  cnf(c_2368,plain,
% 2.78/1.00      ( r2_hidden(X0,sK10)
% 2.78/1.00      | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(sK8,sK9)) ),
% 2.78/1.00      inference(resolution,[status(thm)],[c_24,c_1619]) ).
% 2.78/1.00  
% 2.78/1.00  cnf(c_22,plain,
% 2.78/1.00      ( ~ r2_hidden(X0,X1)
% 2.78/1.00      | ~ r2_hidden(X2,X3)
% 2.78/1.00      | r2_hidden(k4_tarski(X2,X0),k2_zfmisc_1(X3,X1)) ),
% 2.78/1.00      inference(cnf_transformation,[],[f61]) ).
% 2.78/1.00  
% 2.78/1.00  cnf(c_3449,plain,
% 2.78/1.00      ( r2_hidden(X0,sK10) | ~ r2_hidden(X0,sK8) | ~ r2_hidden(X1,sK9) ),
% 2.78/1.00      inference(resolution,[status(thm)],[c_2368,c_22]) ).
% 2.78/1.00  
% 2.78/1.00  cnf(c_20,plain,
% 2.78/1.00      ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
% 2.78/1.00      | r2_hidden(sK7(X1,X2,X0),X2) ),
% 2.78/1.00      inference(cnf_transformation,[],[f71]) ).
% 2.78/1.00  
% 2.78/1.00  cnf(c_3553,plain,
% 2.78/1.00      ( ~ r2_hidden(X0,k2_zfmisc_1(X1,sK9))
% 2.78/1.00      | r2_hidden(X2,sK10)
% 2.78/1.00      | ~ r2_hidden(X2,sK8) ),
% 2.78/1.00      inference(resolution,[status(thm)],[c_3449,c_20]) ).
% 2.78/1.00  
% 2.78/1.00  cnf(c_9,plain,
% 2.78/1.00      ( r2_hidden(sK2(X0),X0) | k1_xboole_0 = X0 ),
% 2.78/1.00      inference(cnf_transformation,[],[f46]) ).
% 2.78/1.00  
% 2.78/1.00  cnf(c_26,negated_conjecture,
% 2.78/1.00      ( k1_xboole_0 != k2_zfmisc_1(sK8,sK9) ),
% 2.78/1.00      inference(cnf_transformation,[],[f63]) ).
% 2.78/1.00  
% 2.78/1.00  cnf(c_1350,plain,
% 2.78/1.00      ( r2_hidden(sK2(k2_zfmisc_1(sK8,sK9)),k2_zfmisc_1(sK8,sK9)) ),
% 2.78/1.00      inference(resolution,[status(thm)],[c_9,c_26]) ).
% 2.78/1.00  
% 2.78/1.00  cnf(c_5383,plain,
% 2.78/1.00      ( r2_hidden(X0,sK10) | ~ r2_hidden(X0,sK8) ),
% 2.78/1.00      inference(resolution,[status(thm)],[c_3553,c_1350]) ).
% 2.78/1.00  
% 2.78/1.00  cnf(c_0,plain,
% 2.78/1.00      ( ~ r2_hidden(sK0(X0,X1),X1) | r1_tarski(X0,X1) ),
% 2.78/1.00      inference(cnf_transformation,[],[f39]) ).
% 2.78/1.00  
% 2.78/1.00  cnf(c_5394,plain,
% 2.78/1.00      ( ~ r2_hidden(sK0(X0,sK10),sK8) | r1_tarski(X0,sK10) ),
% 2.78/1.00      inference(resolution,[status(thm)],[c_5383,c_0]) ).
% 2.78/1.00  
% 2.78/1.00  cnf(c_1,plain,
% 2.78/1.00      ( r2_hidden(sK0(X0,X1),X0) | r1_tarski(X0,X1) ),
% 2.78/1.00      inference(cnf_transformation,[],[f38]) ).
% 2.78/1.00  
% 2.78/1.00  cnf(c_5404,plain,
% 2.78/1.00      ( r1_tarski(sK8,sK10) ),
% 2.78/1.00      inference(resolution,[status(thm)],[c_5394,c_1]) ).
% 2.78/1.00  
% 2.78/1.00  cnf(c_23,plain,
% 2.78/1.00      ( r2_hidden(X0,X1)
% 2.78/1.00      | ~ r2_hidden(k4_tarski(X2,X0),k2_zfmisc_1(X3,X1)) ),
% 2.78/1.00      inference(cnf_transformation,[],[f60]) ).
% 2.78/1.00  
% 2.78/1.00  cnf(c_2203,plain,
% 2.78/1.00      ( r2_hidden(X0,sK11)
% 2.78/1.00      | ~ r2_hidden(k4_tarski(X1,X0),k2_zfmisc_1(sK8,sK9)) ),
% 2.78/1.00      inference(resolution,[status(thm)],[c_23,c_1619]) ).
% 2.78/1.00  
% 2.78/1.00  cnf(c_3440,plain,
% 2.78/1.00      ( ~ r2_hidden(X0,sK8) | r2_hidden(X1,sK11) | ~ r2_hidden(X1,sK9) ),
% 2.78/1.00      inference(resolution,[status(thm)],[c_2203,c_22]) ).
% 2.78/1.00  
% 2.78/1.00  cnf(c_21,plain,
% 2.78/1.00      ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
% 2.78/1.00      | r2_hidden(sK6(X1,X2,X0),X1) ),
% 2.78/1.00      inference(cnf_transformation,[],[f72]) ).
% 2.78/1.00  
% 2.78/1.00  cnf(c_3529,plain,
% 2.78/1.00      ( ~ r2_hidden(X0,k2_zfmisc_1(sK8,X1))
% 2.78/1.00      | r2_hidden(X2,sK11)
% 2.78/1.00      | ~ r2_hidden(X2,sK9) ),
% 2.78/1.00      inference(resolution,[status(thm)],[c_3440,c_21]) ).
% 2.78/1.00  
% 2.78/1.00  cnf(c_4269,plain,
% 2.78/1.00      ( r2_hidden(X0,sK11) | ~ r2_hidden(X0,sK9) ),
% 2.78/1.00      inference(resolution,[status(thm)],[c_3529,c_1350]) ).
% 2.78/1.00  
% 2.78/1.00  cnf(c_4280,plain,
% 2.78/1.00      ( ~ r2_hidden(sK0(X0,sK11),sK9) | r1_tarski(X0,sK11) ),
% 2.78/1.00      inference(resolution,[status(thm)],[c_4269,c_0]) ).
% 2.78/1.00  
% 2.78/1.00  cnf(c_4487,plain,
% 2.78/1.00      ( r1_tarski(sK9,sK11) ),
% 2.78/1.00      inference(resolution,[status(thm)],[c_4280,c_1]) ).
% 2.78/1.00  
% 2.78/1.00  cnf(c_25,negated_conjecture,
% 2.78/1.00      ( ~ r1_tarski(sK8,sK10) | ~ r1_tarski(sK9,sK11) ),
% 2.78/1.00      inference(cnf_transformation,[],[f64]) ).
% 2.78/1.00  
% 2.78/1.00  cnf(contradiction,plain,
% 2.78/1.00      ( $false ),
% 2.78/1.00      inference(minisat,[status(thm)],[c_5404,c_4487,c_25]) ).
% 2.78/1.00  
% 2.78/1.00  
% 2.78/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 2.78/1.00  
% 2.78/1.00  ------                               Statistics
% 2.78/1.00  
% 2.78/1.00  ------ Selected
% 2.78/1.00  
% 2.78/1.00  total_time:                             0.144
% 2.78/1.00  
%------------------------------------------------------------------------------
