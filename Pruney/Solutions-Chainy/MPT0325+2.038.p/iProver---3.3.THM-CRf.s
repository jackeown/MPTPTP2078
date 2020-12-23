%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:37:51 EST 2020

% Result     : Theorem 2.93s
% Output     : CNFRefutation 2.93s
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
fof(f9,axiom,(
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
    inference(nnf_transformation,[],[f9])).

fof(f34,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
        | ~ r2_hidden(X1,X3)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X3)
          & r2_hidden(X0,X2) )
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ) ),
    inference(flattening,[],[f33])).

fof(f56,plain,(
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

fof(f13,plain,(
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
    inference(nnf_transformation,[],[f13])).

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
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f10,conjecture,(
    ! [X0,X1,X2,X3] :
      ( r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3))
     => ( ( r1_tarski(X1,X3)
          & r1_tarski(X0,X2) )
        | k1_xboole_0 = k2_zfmisc_1(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f11,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3))
       => ( ( r1_tarski(X1,X3)
            & r1_tarski(X0,X2) )
          | k1_xboole_0 = k2_zfmisc_1(X0,X1) ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f16,plain,(
    ? [X0,X1,X2,X3] :
      ( ( ~ r1_tarski(X1,X3)
        | ~ r1_tarski(X0,X2) )
      & k1_xboole_0 != k2_zfmisc_1(X0,X1)
      & r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f17,plain,(
    ? [X0,X1,X2,X3] :
      ( ( ~ r1_tarski(X1,X3)
        | ~ r1_tarski(X0,X2) )
      & k1_xboole_0 != k2_zfmisc_1(X0,X1)
      & r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)) ) ),
    inference(flattening,[],[f16])).

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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8,sK9,sK10,sK11])],[f17,f35])).

fof(f59,plain,(
    r1_tarski(k2_zfmisc_1(sK8,sK9),k2_zfmisc_1(sK10,sK11)) ),
    inference(cnf_transformation,[],[f36])).

fof(f58,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
      | ~ r2_hidden(X1,X3)
      | ~ r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f8,axiom,(
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
    inference(nnf_transformation,[],[f8])).

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

fof(f49,plain,(
    ! [X2,X0,X8,X1] :
      ( r2_hidden(sK7(X0,X1,X8),X1)
      | ~ r2_hidden(X8,X2)
      | k2_zfmisc_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f32])).

fof(f68,plain,(
    ! [X0,X8,X1] :
      ( r2_hidden(sK7(X0,X1,X8),X1)
      | ~ r2_hidden(X8,k2_zfmisc_1(X0,X1)) ) ),
    inference(equality_resolution,[],[f49])).

fof(f3,axiom,(
    ! [X0] :
      ~ ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f15,f24])).

fof(f42,plain,(
    ! [X0] :
      ( r2_hidden(sK2(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f60,plain,(
    k1_xboole_0 != k2_zfmisc_1(sK8,sK9) ),
    inference(cnf_transformation,[],[f36])).

fof(f39,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK0(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f38,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK0(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f57,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X1,X3)
      | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f48,plain,(
    ! [X2,X0,X8,X1] :
      ( r2_hidden(sK6(X0,X1,X8),X0)
      | ~ r2_hidden(X8,X2)
      | k2_zfmisc_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f32])).

fof(f69,plain,(
    ! [X0,X8,X1] :
      ( r2_hidden(sK6(X0,X1,X8),X0)
      | ~ r2_hidden(X8,k2_zfmisc_1(X0,X1)) ) ),
    inference(equality_resolution,[],[f48])).

fof(f61,plain,
    ( ~ r1_tarski(sK9,sK11)
    | ~ r1_tarski(sK8,sK10) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_20,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(k4_tarski(X0,X2),k2_zfmisc_1(X1,X3)) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_2,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | ~ r1_tarski(X1,X2) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_23,negated_conjecture,
    ( r1_tarski(k2_zfmisc_1(sK8,sK9),k2_zfmisc_1(sK10,sK11)) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_1501,plain,
    ( r2_hidden(X0,k2_zfmisc_1(sK10,sK11))
    | ~ r2_hidden(X0,k2_zfmisc_1(sK8,sK9)) ),
    inference(resolution,[status(thm)],[c_2,c_23])).

cnf(c_2074,plain,
    ( r2_hidden(X0,sK10)
    | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(sK8,sK9)) ),
    inference(resolution,[status(thm)],[c_20,c_1501])).

cnf(c_18,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X2,X3)
    | r2_hidden(k4_tarski(X2,X0),k2_zfmisc_1(X3,X1)) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_3505,plain,
    ( r2_hidden(X0,sK10)
    | ~ r2_hidden(X0,sK8)
    | ~ r2_hidden(X1,sK9) ),
    inference(resolution,[status(thm)],[c_2074,c_18])).

cnf(c_16,plain,
    ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
    | r2_hidden(sK7(X1,X2,X0),X2) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_3813,plain,
    ( ~ r2_hidden(X0,k2_zfmisc_1(X1,sK9))
    | r2_hidden(X2,sK10)
    | ~ r2_hidden(X2,sK8) ),
    inference(resolution,[status(thm)],[c_3505,c_16])).

cnf(c_5,plain,
    ( r2_hidden(sK2(X0),X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f42])).

cnf(c_22,negated_conjecture,
    ( k1_xboole_0 != k2_zfmisc_1(sK8,sK9) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_1237,plain,
    ( r2_hidden(sK2(k2_zfmisc_1(sK8,sK9)),k2_zfmisc_1(sK8,sK9)) ),
    inference(resolution,[status(thm)],[c_5,c_22])).

cnf(c_6259,plain,
    ( r2_hidden(X0,sK10)
    | ~ r2_hidden(X0,sK8) ),
    inference(resolution,[status(thm)],[c_3813,c_1237])).

cnf(c_0,plain,
    ( ~ r2_hidden(sK0(X0,X1),X1)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_6269,plain,
    ( ~ r2_hidden(sK0(X0,sK10),sK8)
    | r1_tarski(X0,sK10) ),
    inference(resolution,[status(thm)],[c_6259,c_0])).

cnf(c_1,plain,
    ( r2_hidden(sK0(X0,X1),X0)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_6279,plain,
    ( r1_tarski(sK8,sK10) ),
    inference(resolution,[status(thm)],[c_6269,c_1])).

cnf(c_19,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(k4_tarski(X2,X0),k2_zfmisc_1(X3,X1)) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_1971,plain,
    ( r2_hidden(X0,sK11)
    | ~ r2_hidden(k4_tarski(X1,X0),k2_zfmisc_1(sK8,sK9)) ),
    inference(resolution,[status(thm)],[c_19,c_1501])).

cnf(c_3496,plain,
    ( ~ r2_hidden(X0,sK8)
    | r2_hidden(X1,sK11)
    | ~ r2_hidden(X1,sK9) ),
    inference(resolution,[status(thm)],[c_1971,c_18])).

cnf(c_17,plain,
    ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
    | r2_hidden(sK6(X1,X2,X0),X1) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_3785,plain,
    ( ~ r2_hidden(X0,k2_zfmisc_1(sK8,X1))
    | r2_hidden(X2,sK11)
    | ~ r2_hidden(X2,sK9) ),
    inference(resolution,[status(thm)],[c_3496,c_17])).

cnf(c_4440,plain,
    ( r2_hidden(X0,sK11)
    | ~ r2_hidden(X0,sK9) ),
    inference(resolution,[status(thm)],[c_3785,c_1237])).

cnf(c_5119,plain,
    ( ~ r2_hidden(sK0(X0,sK11),sK9)
    | r1_tarski(X0,sK11) ),
    inference(resolution,[status(thm)],[c_4440,c_0])).

cnf(c_5129,plain,
    ( r1_tarski(sK9,sK11) ),
    inference(resolution,[status(thm)],[c_5119,c_1])).

cnf(c_21,negated_conjecture,
    ( ~ r1_tarski(sK8,sK10)
    | ~ r1_tarski(sK9,sK11) ),
    inference(cnf_transformation,[],[f61])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_6279,c_5129,c_21])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.13/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n023.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 16:52:21 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 2.93/1.03  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.93/1.03  
% 2.93/1.03  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.93/1.03  
% 2.93/1.03  ------  iProver source info
% 2.93/1.03  
% 2.93/1.03  git: date: 2020-06-30 10:37:57 +0100
% 2.93/1.03  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.93/1.03  git: non_committed_changes: false
% 2.93/1.03  git: last_make_outside_of_git: false
% 2.93/1.03  
% 2.93/1.03  ------ 
% 2.93/1.03  ------ Parsing...
% 2.93/1.03  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.93/1.03  
% 2.93/1.03  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e  sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 2.93/1.03  
% 2.93/1.03  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.93/1.03  
% 2.93/1.03  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.93/1.03  ------ Proving...
% 2.93/1.03  ------ Problem Properties 
% 2.93/1.03  
% 2.93/1.03  
% 2.93/1.03  clauses                                 23
% 2.93/1.03  conjectures                             3
% 2.93/1.03  EPR                                     2
% 2.93/1.03  Horn                                    17
% 2.93/1.03  unary                                   4
% 2.93/1.03  binary                                  13
% 2.93/1.03  lits                                    50
% 2.93/1.03  lits eq                                 13
% 2.93/1.03  fd_pure                                 0
% 2.93/1.03  fd_pseudo                               0
% 2.93/1.03  fd_cond                                 1
% 2.93/1.03  fd_pseudo_cond                          4
% 2.93/1.03  AC symbols                              0
% 2.93/1.03  
% 2.93/1.03  ------ Input Options Time Limit: Unbounded
% 2.93/1.03  
% 2.93/1.03  
% 2.93/1.03  ------ 
% 2.93/1.03  Current options:
% 2.93/1.03  ------ 
% 2.93/1.03  
% 2.93/1.03  
% 2.93/1.03  
% 2.93/1.03  
% 2.93/1.03  ------ Proving...
% 2.93/1.03  
% 2.93/1.03  
% 2.93/1.03  % SZS status Theorem for theBenchmark.p
% 2.93/1.03  
% 2.93/1.03  % SZS output start CNFRefutation for theBenchmark.p
% 2.93/1.03  
% 2.93/1.03  fof(f9,axiom,(
% 2.93/1.03    ! [X0,X1,X2,X3] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) <=> (r2_hidden(X1,X3) & r2_hidden(X0,X2)))),
% 2.93/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.93/1.03  
% 2.93/1.03  fof(f33,plain,(
% 2.93/1.03    ! [X0,X1,X2,X3] : ((r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | (~r2_hidden(X1,X3) | ~r2_hidden(X0,X2))) & ((r2_hidden(X1,X3) & r2_hidden(X0,X2)) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))))),
% 2.93/1.03    inference(nnf_transformation,[],[f9])).
% 2.93/1.03  
% 2.93/1.03  fof(f34,plain,(
% 2.93/1.03    ! [X0,X1,X2,X3] : ((r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | ~r2_hidden(X1,X3) | ~r2_hidden(X0,X2)) & ((r2_hidden(X1,X3) & r2_hidden(X0,X2)) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))))),
% 2.93/1.03    inference(flattening,[],[f33])).
% 2.93/1.03  
% 2.93/1.03  fof(f56,plain,(
% 2.93/1.03    ( ! [X2,X0,X3,X1] : (r2_hidden(X0,X2) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))) )),
% 2.93/1.03    inference(cnf_transformation,[],[f34])).
% 2.93/1.03  
% 2.93/1.03  fof(f1,axiom,(
% 2.93/1.03    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 2.93/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.93/1.03  
% 2.93/1.03  fof(f13,plain,(
% 2.93/1.03    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 2.93/1.03    inference(ennf_transformation,[],[f1])).
% 2.93/1.03  
% 2.93/1.03  fof(f18,plain,(
% 2.93/1.03    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 2.93/1.03    inference(nnf_transformation,[],[f13])).
% 2.93/1.03  
% 2.93/1.03  fof(f19,plain,(
% 2.93/1.03    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 2.93/1.03    inference(rectify,[],[f18])).
% 2.93/1.03  
% 2.93/1.03  fof(f20,plain,(
% 2.93/1.03    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 2.93/1.03    introduced(choice_axiom,[])).
% 2.93/1.03  
% 2.93/1.03  fof(f21,plain,(
% 2.93/1.03    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 2.93/1.03    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f19,f20])).
% 2.93/1.03  
% 2.93/1.03  fof(f37,plain,(
% 2.93/1.03    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,X1)) )),
% 2.93/1.03    inference(cnf_transformation,[],[f21])).
% 2.93/1.03  
% 2.93/1.03  fof(f10,conjecture,(
% 2.93/1.03    ! [X0,X1,X2,X3] : (r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)) => ((r1_tarski(X1,X3) & r1_tarski(X0,X2)) | k1_xboole_0 = k2_zfmisc_1(X0,X1)))),
% 2.93/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.93/1.03  
% 2.93/1.03  fof(f11,negated_conjecture,(
% 2.93/1.03    ~! [X0,X1,X2,X3] : (r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)) => ((r1_tarski(X1,X3) & r1_tarski(X0,X2)) | k1_xboole_0 = k2_zfmisc_1(X0,X1)))),
% 2.93/1.03    inference(negated_conjecture,[],[f10])).
% 2.93/1.03  
% 2.93/1.03  fof(f16,plain,(
% 2.93/1.03    ? [X0,X1,X2,X3] : (((~r1_tarski(X1,X3) | ~r1_tarski(X0,X2)) & k1_xboole_0 != k2_zfmisc_1(X0,X1)) & r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)))),
% 2.93/1.03    inference(ennf_transformation,[],[f11])).
% 2.93/1.03  
% 2.93/1.03  fof(f17,plain,(
% 2.93/1.03    ? [X0,X1,X2,X3] : ((~r1_tarski(X1,X3) | ~r1_tarski(X0,X2)) & k1_xboole_0 != k2_zfmisc_1(X0,X1) & r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)))),
% 2.93/1.03    inference(flattening,[],[f16])).
% 2.93/1.03  
% 2.93/1.03  fof(f35,plain,(
% 2.93/1.03    ? [X0,X1,X2,X3] : ((~r1_tarski(X1,X3) | ~r1_tarski(X0,X2)) & k1_xboole_0 != k2_zfmisc_1(X0,X1) & r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3))) => ((~r1_tarski(sK9,sK11) | ~r1_tarski(sK8,sK10)) & k1_xboole_0 != k2_zfmisc_1(sK8,sK9) & r1_tarski(k2_zfmisc_1(sK8,sK9),k2_zfmisc_1(sK10,sK11)))),
% 2.93/1.03    introduced(choice_axiom,[])).
% 2.93/1.03  
% 2.93/1.03  fof(f36,plain,(
% 2.93/1.03    (~r1_tarski(sK9,sK11) | ~r1_tarski(sK8,sK10)) & k1_xboole_0 != k2_zfmisc_1(sK8,sK9) & r1_tarski(k2_zfmisc_1(sK8,sK9),k2_zfmisc_1(sK10,sK11))),
% 2.93/1.03    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8,sK9,sK10,sK11])],[f17,f35])).
% 2.93/1.03  
% 2.93/1.03  fof(f59,plain,(
% 2.93/1.03    r1_tarski(k2_zfmisc_1(sK8,sK9),k2_zfmisc_1(sK10,sK11))),
% 2.93/1.03    inference(cnf_transformation,[],[f36])).
% 2.93/1.03  
% 2.93/1.03  fof(f58,plain,(
% 2.93/1.03    ( ! [X2,X0,X3,X1] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | ~r2_hidden(X1,X3) | ~r2_hidden(X0,X2)) )),
% 2.93/1.03    inference(cnf_transformation,[],[f34])).
% 2.93/1.03  
% 2.93/1.03  fof(f8,axiom,(
% 2.93/1.03    ! [X0,X1,X2] : (k2_zfmisc_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4,X5] : (k4_tarski(X4,X5) = X3 & r2_hidden(X5,X1) & r2_hidden(X4,X0))))),
% 2.93/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.93/1.03  
% 2.93/1.03  fof(f27,plain,(
% 2.93/1.03    ! [X0,X1,X2] : ((k2_zfmisc_1(X0,X1) = X2 | ? [X3] : ((! [X4,X5] : (k4_tarski(X4,X5) != X3 | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X0)) | ~r2_hidden(X3,X2)) & (? [X4,X5] : (k4_tarski(X4,X5) = X3 & r2_hidden(X5,X1) & r2_hidden(X4,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ! [X4,X5] : (k4_tarski(X4,X5) != X3 | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X0))) & (? [X4,X5] : (k4_tarski(X4,X5) = X3 & r2_hidden(X5,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X3,X2))) | k2_zfmisc_1(X0,X1) != X2))),
% 2.93/1.03    inference(nnf_transformation,[],[f8])).
% 2.93/1.03  
% 2.93/1.03  fof(f28,plain,(
% 2.93/1.03    ! [X0,X1,X2] : ((k2_zfmisc_1(X0,X1) = X2 | ? [X3] : ((! [X4,X5] : (k4_tarski(X4,X5) != X3 | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X0)) | ~r2_hidden(X3,X2)) & (? [X6,X7] : (k4_tarski(X6,X7) = X3 & r2_hidden(X7,X1) & r2_hidden(X6,X0)) | r2_hidden(X3,X2)))) & (! [X8] : ((r2_hidden(X8,X2) | ! [X9,X10] : (k4_tarski(X9,X10) != X8 | ~r2_hidden(X10,X1) | ~r2_hidden(X9,X0))) & (? [X11,X12] : (k4_tarski(X11,X12) = X8 & r2_hidden(X12,X1) & r2_hidden(X11,X0)) | ~r2_hidden(X8,X2))) | k2_zfmisc_1(X0,X1) != X2))),
% 2.93/1.03    inference(rectify,[],[f27])).
% 2.93/1.03  
% 2.93/1.03  fof(f31,plain,(
% 2.93/1.03    ! [X8,X1,X0] : (? [X11,X12] : (k4_tarski(X11,X12) = X8 & r2_hidden(X12,X1) & r2_hidden(X11,X0)) => (k4_tarski(sK6(X0,X1,X8),sK7(X0,X1,X8)) = X8 & r2_hidden(sK7(X0,X1,X8),X1) & r2_hidden(sK6(X0,X1,X8),X0)))),
% 2.93/1.03    introduced(choice_axiom,[])).
% 2.93/1.03  
% 2.93/1.03  fof(f30,plain,(
% 2.93/1.03    ( ! [X3] : (! [X2,X1,X0] : (? [X6,X7] : (k4_tarski(X6,X7) = X3 & r2_hidden(X7,X1) & r2_hidden(X6,X0)) => (k4_tarski(sK4(X0,X1,X2),sK5(X0,X1,X2)) = X3 & r2_hidden(sK5(X0,X1,X2),X1) & r2_hidden(sK4(X0,X1,X2),X0)))) )),
% 2.93/1.03    introduced(choice_axiom,[])).
% 2.93/1.03  
% 2.93/1.03  fof(f29,plain,(
% 2.93/1.03    ! [X2,X1,X0] : (? [X3] : ((! [X4,X5] : (k4_tarski(X4,X5) != X3 | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X0)) | ~r2_hidden(X3,X2)) & (? [X6,X7] : (k4_tarski(X6,X7) = X3 & r2_hidden(X7,X1) & r2_hidden(X6,X0)) | r2_hidden(X3,X2))) => ((! [X5,X4] : (k4_tarski(X4,X5) != sK3(X0,X1,X2) | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X0)) | ~r2_hidden(sK3(X0,X1,X2),X2)) & (? [X7,X6] : (k4_tarski(X6,X7) = sK3(X0,X1,X2) & r2_hidden(X7,X1) & r2_hidden(X6,X0)) | r2_hidden(sK3(X0,X1,X2),X2))))),
% 2.93/1.03    introduced(choice_axiom,[])).
% 2.93/1.03  
% 2.93/1.03  fof(f32,plain,(
% 2.93/1.03    ! [X0,X1,X2] : ((k2_zfmisc_1(X0,X1) = X2 | ((! [X4,X5] : (k4_tarski(X4,X5) != sK3(X0,X1,X2) | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X0)) | ~r2_hidden(sK3(X0,X1,X2),X2)) & ((k4_tarski(sK4(X0,X1,X2),sK5(X0,X1,X2)) = sK3(X0,X1,X2) & r2_hidden(sK5(X0,X1,X2),X1) & r2_hidden(sK4(X0,X1,X2),X0)) | r2_hidden(sK3(X0,X1,X2),X2)))) & (! [X8] : ((r2_hidden(X8,X2) | ! [X9,X10] : (k4_tarski(X9,X10) != X8 | ~r2_hidden(X10,X1) | ~r2_hidden(X9,X0))) & ((k4_tarski(sK6(X0,X1,X8),sK7(X0,X1,X8)) = X8 & r2_hidden(sK7(X0,X1,X8),X1) & r2_hidden(sK6(X0,X1,X8),X0)) | ~r2_hidden(X8,X2))) | k2_zfmisc_1(X0,X1) != X2))),
% 2.93/1.03    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5,sK6,sK7])],[f28,f31,f30,f29])).
% 2.93/1.03  
% 2.93/1.03  fof(f49,plain,(
% 2.93/1.03    ( ! [X2,X0,X8,X1] : (r2_hidden(sK7(X0,X1,X8),X1) | ~r2_hidden(X8,X2) | k2_zfmisc_1(X0,X1) != X2) )),
% 2.93/1.03    inference(cnf_transformation,[],[f32])).
% 2.93/1.03  
% 2.93/1.03  fof(f68,plain,(
% 2.93/1.03    ( ! [X0,X8,X1] : (r2_hidden(sK7(X0,X1,X8),X1) | ~r2_hidden(X8,k2_zfmisc_1(X0,X1))) )),
% 2.93/1.03    inference(equality_resolution,[],[f49])).
% 2.93/1.03  
% 2.93/1.03  fof(f3,axiom,(
% 2.93/1.03    ! [X0] : ~(! [X1] : ~r2_hidden(X1,X0) & k1_xboole_0 != X0)),
% 2.93/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.93/1.03  
% 2.93/1.03  fof(f15,plain,(
% 2.93/1.03    ! [X0] : (? [X1] : r2_hidden(X1,X0) | k1_xboole_0 = X0)),
% 2.93/1.03    inference(ennf_transformation,[],[f3])).
% 2.93/1.03  
% 2.93/1.03  fof(f24,plain,(
% 2.93/1.03    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK2(X0),X0))),
% 2.93/1.03    introduced(choice_axiom,[])).
% 2.93/1.03  
% 2.93/1.03  fof(f25,plain,(
% 2.93/1.03    ! [X0] : (r2_hidden(sK2(X0),X0) | k1_xboole_0 = X0)),
% 2.93/1.03    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f15,f24])).
% 2.93/1.03  
% 2.93/1.03  fof(f42,plain,(
% 2.93/1.03    ( ! [X0] : (r2_hidden(sK2(X0),X0) | k1_xboole_0 = X0) )),
% 2.93/1.03    inference(cnf_transformation,[],[f25])).
% 2.93/1.03  
% 2.93/1.03  fof(f60,plain,(
% 2.93/1.03    k1_xboole_0 != k2_zfmisc_1(sK8,sK9)),
% 2.93/1.03    inference(cnf_transformation,[],[f36])).
% 2.93/1.03  
% 2.93/1.03  fof(f39,plain,(
% 2.93/1.03    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r2_hidden(sK0(X0,X1),X1)) )),
% 2.93/1.03    inference(cnf_transformation,[],[f21])).
% 2.93/1.03  
% 2.93/1.03  fof(f38,plain,(
% 2.93/1.03    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK0(X0,X1),X0)) )),
% 2.93/1.03    inference(cnf_transformation,[],[f21])).
% 2.93/1.03  
% 2.93/1.03  fof(f57,plain,(
% 2.93/1.03    ( ! [X2,X0,X3,X1] : (r2_hidden(X1,X3) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))) )),
% 2.93/1.03    inference(cnf_transformation,[],[f34])).
% 2.93/1.03  
% 2.93/1.03  fof(f48,plain,(
% 2.93/1.03    ( ! [X2,X0,X8,X1] : (r2_hidden(sK6(X0,X1,X8),X0) | ~r2_hidden(X8,X2) | k2_zfmisc_1(X0,X1) != X2) )),
% 2.93/1.03    inference(cnf_transformation,[],[f32])).
% 2.93/1.03  
% 2.93/1.03  fof(f69,plain,(
% 2.93/1.03    ( ! [X0,X8,X1] : (r2_hidden(sK6(X0,X1,X8),X0) | ~r2_hidden(X8,k2_zfmisc_1(X0,X1))) )),
% 2.93/1.03    inference(equality_resolution,[],[f48])).
% 2.93/1.03  
% 2.93/1.03  fof(f61,plain,(
% 2.93/1.03    ~r1_tarski(sK9,sK11) | ~r1_tarski(sK8,sK10)),
% 2.93/1.03    inference(cnf_transformation,[],[f36])).
% 2.93/1.03  
% 2.93/1.03  cnf(c_20,plain,
% 2.93/1.03      ( r2_hidden(X0,X1)
% 2.93/1.03      | ~ r2_hidden(k4_tarski(X0,X2),k2_zfmisc_1(X1,X3)) ),
% 2.93/1.03      inference(cnf_transformation,[],[f56]) ).
% 2.93/1.03  
% 2.93/1.03  cnf(c_2,plain,
% 2.93/1.03      ( ~ r2_hidden(X0,X1) | r2_hidden(X0,X2) | ~ r1_tarski(X1,X2) ),
% 2.93/1.03      inference(cnf_transformation,[],[f37]) ).
% 2.93/1.03  
% 2.93/1.03  cnf(c_23,negated_conjecture,
% 2.93/1.03      ( r1_tarski(k2_zfmisc_1(sK8,sK9),k2_zfmisc_1(sK10,sK11)) ),
% 2.93/1.03      inference(cnf_transformation,[],[f59]) ).
% 2.93/1.03  
% 2.93/1.03  cnf(c_1501,plain,
% 2.93/1.03      ( r2_hidden(X0,k2_zfmisc_1(sK10,sK11))
% 2.93/1.03      | ~ r2_hidden(X0,k2_zfmisc_1(sK8,sK9)) ),
% 2.93/1.03      inference(resolution,[status(thm)],[c_2,c_23]) ).
% 2.93/1.03  
% 2.93/1.03  cnf(c_2074,plain,
% 2.93/1.03      ( r2_hidden(X0,sK10)
% 2.93/1.03      | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(sK8,sK9)) ),
% 2.93/1.03      inference(resolution,[status(thm)],[c_20,c_1501]) ).
% 2.93/1.03  
% 2.93/1.03  cnf(c_18,plain,
% 2.93/1.03      ( ~ r2_hidden(X0,X1)
% 2.93/1.03      | ~ r2_hidden(X2,X3)
% 2.93/1.03      | r2_hidden(k4_tarski(X2,X0),k2_zfmisc_1(X3,X1)) ),
% 2.93/1.03      inference(cnf_transformation,[],[f58]) ).
% 2.93/1.03  
% 2.93/1.03  cnf(c_3505,plain,
% 2.93/1.03      ( r2_hidden(X0,sK10) | ~ r2_hidden(X0,sK8) | ~ r2_hidden(X1,sK9) ),
% 2.93/1.03      inference(resolution,[status(thm)],[c_2074,c_18]) ).
% 2.93/1.03  
% 2.93/1.03  cnf(c_16,plain,
% 2.93/1.03      ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
% 2.93/1.03      | r2_hidden(sK7(X1,X2,X0),X2) ),
% 2.93/1.03      inference(cnf_transformation,[],[f68]) ).
% 2.93/1.03  
% 2.93/1.03  cnf(c_3813,plain,
% 2.93/1.03      ( ~ r2_hidden(X0,k2_zfmisc_1(X1,sK9))
% 2.93/1.03      | r2_hidden(X2,sK10)
% 2.93/1.03      | ~ r2_hidden(X2,sK8) ),
% 2.93/1.03      inference(resolution,[status(thm)],[c_3505,c_16]) ).
% 2.93/1.03  
% 2.93/1.03  cnf(c_5,plain,
% 2.93/1.03      ( r2_hidden(sK2(X0),X0) | k1_xboole_0 = X0 ),
% 2.93/1.03      inference(cnf_transformation,[],[f42]) ).
% 2.93/1.03  
% 2.93/1.03  cnf(c_22,negated_conjecture,
% 2.93/1.03      ( k1_xboole_0 != k2_zfmisc_1(sK8,sK9) ),
% 2.93/1.03      inference(cnf_transformation,[],[f60]) ).
% 2.93/1.03  
% 2.93/1.03  cnf(c_1237,plain,
% 2.93/1.03      ( r2_hidden(sK2(k2_zfmisc_1(sK8,sK9)),k2_zfmisc_1(sK8,sK9)) ),
% 2.93/1.03      inference(resolution,[status(thm)],[c_5,c_22]) ).
% 2.93/1.03  
% 2.93/1.03  cnf(c_6259,plain,
% 2.93/1.03      ( r2_hidden(X0,sK10) | ~ r2_hidden(X0,sK8) ),
% 2.93/1.03      inference(resolution,[status(thm)],[c_3813,c_1237]) ).
% 2.93/1.03  
% 2.93/1.03  cnf(c_0,plain,
% 2.93/1.03      ( ~ r2_hidden(sK0(X0,X1),X1) | r1_tarski(X0,X1) ),
% 2.93/1.03      inference(cnf_transformation,[],[f39]) ).
% 2.93/1.03  
% 2.93/1.03  cnf(c_6269,plain,
% 2.93/1.03      ( ~ r2_hidden(sK0(X0,sK10),sK8) | r1_tarski(X0,sK10) ),
% 2.93/1.03      inference(resolution,[status(thm)],[c_6259,c_0]) ).
% 2.93/1.03  
% 2.93/1.03  cnf(c_1,plain,
% 2.93/1.03      ( r2_hidden(sK0(X0,X1),X0) | r1_tarski(X0,X1) ),
% 2.93/1.03      inference(cnf_transformation,[],[f38]) ).
% 2.93/1.03  
% 2.93/1.03  cnf(c_6279,plain,
% 2.93/1.03      ( r1_tarski(sK8,sK10) ),
% 2.93/1.03      inference(resolution,[status(thm)],[c_6269,c_1]) ).
% 2.93/1.03  
% 2.93/1.03  cnf(c_19,plain,
% 2.93/1.03      ( r2_hidden(X0,X1)
% 2.93/1.03      | ~ r2_hidden(k4_tarski(X2,X0),k2_zfmisc_1(X3,X1)) ),
% 2.93/1.03      inference(cnf_transformation,[],[f57]) ).
% 2.93/1.03  
% 2.93/1.03  cnf(c_1971,plain,
% 2.93/1.03      ( r2_hidden(X0,sK11)
% 2.93/1.03      | ~ r2_hidden(k4_tarski(X1,X0),k2_zfmisc_1(sK8,sK9)) ),
% 2.93/1.03      inference(resolution,[status(thm)],[c_19,c_1501]) ).
% 2.93/1.03  
% 2.93/1.03  cnf(c_3496,plain,
% 2.93/1.03      ( ~ r2_hidden(X0,sK8) | r2_hidden(X1,sK11) | ~ r2_hidden(X1,sK9) ),
% 2.93/1.03      inference(resolution,[status(thm)],[c_1971,c_18]) ).
% 2.93/1.03  
% 2.93/1.03  cnf(c_17,plain,
% 2.93/1.03      ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
% 2.93/1.03      | r2_hidden(sK6(X1,X2,X0),X1) ),
% 2.93/1.03      inference(cnf_transformation,[],[f69]) ).
% 2.93/1.03  
% 2.93/1.03  cnf(c_3785,plain,
% 2.93/1.03      ( ~ r2_hidden(X0,k2_zfmisc_1(sK8,X1))
% 2.93/1.03      | r2_hidden(X2,sK11)
% 2.93/1.03      | ~ r2_hidden(X2,sK9) ),
% 2.93/1.03      inference(resolution,[status(thm)],[c_3496,c_17]) ).
% 2.93/1.03  
% 2.93/1.03  cnf(c_4440,plain,
% 2.93/1.03      ( r2_hidden(X0,sK11) | ~ r2_hidden(X0,sK9) ),
% 2.93/1.03      inference(resolution,[status(thm)],[c_3785,c_1237]) ).
% 2.93/1.03  
% 2.93/1.03  cnf(c_5119,plain,
% 2.93/1.03      ( ~ r2_hidden(sK0(X0,sK11),sK9) | r1_tarski(X0,sK11) ),
% 2.93/1.03      inference(resolution,[status(thm)],[c_4440,c_0]) ).
% 2.93/1.03  
% 2.93/1.03  cnf(c_5129,plain,
% 2.93/1.03      ( r1_tarski(sK9,sK11) ),
% 2.93/1.03      inference(resolution,[status(thm)],[c_5119,c_1]) ).
% 2.93/1.03  
% 2.93/1.03  cnf(c_21,negated_conjecture,
% 2.93/1.03      ( ~ r1_tarski(sK8,sK10) | ~ r1_tarski(sK9,sK11) ),
% 2.93/1.03      inference(cnf_transformation,[],[f61]) ).
% 2.93/1.03  
% 2.93/1.03  cnf(contradiction,plain,
% 2.93/1.03      ( $false ),
% 2.93/1.03      inference(minisat,[status(thm)],[c_6279,c_5129,c_21]) ).
% 2.93/1.03  
% 2.93/1.03  
% 2.93/1.03  % SZS output end CNFRefutation for theBenchmark.p
% 2.93/1.03  
% 2.93/1.03  ------                               Statistics
% 2.93/1.03  
% 2.93/1.03  ------ Selected
% 2.93/1.03  
% 2.93/1.03  total_time:                             0.204
% 2.93/1.03  
%------------------------------------------------------------------------------
