%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:36:55 EST 2020

% Result     : Theorem 4.07s
% Output     : CNFRefutation 4.07s
% Verified   : 
% Statistics : Number of formulae       :  102 ( 386 expanded)
%              Number of clauses        :   50 ( 152 expanded)
%              Number of leaves         :   16 (  84 expanded)
%              Depth                    :   21
%              Number of atoms          :  355 (1421 expanded)
%              Number of equality atoms :  191 ( 731 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal clause size      :   18 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( k2_zfmisc_1(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ? [X4,X5] :
              ( k4_tarski(X4,X5) = X3
              & r2_hidden(X5,X1)
              & r2_hidden(X4,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
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
    inference(nnf_transformation,[],[f11])).

fof(f42,plain,(
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
    inference(rectify,[],[f41])).

fof(f45,plain,(
    ! [X8,X1,X0] :
      ( ? [X11,X12] :
          ( k4_tarski(X11,X12) = X8
          & r2_hidden(X12,X1)
          & r2_hidden(X11,X0) )
     => ( k4_tarski(sK7(X0,X1,X8),sK8(X0,X1,X8)) = X8
        & r2_hidden(sK8(X0,X1,X8),X1)
        & r2_hidden(sK7(X0,X1,X8),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f44,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X6,X7] :
          ( k4_tarski(X6,X7) = X3
          & r2_hidden(X7,X1)
          & r2_hidden(X6,X0) )
     => ( k4_tarski(sK5(X0,X1,X2),sK6(X0,X1,X2)) = X3
        & r2_hidden(sK6(X0,X1,X2),X1)
        & r2_hidden(sK5(X0,X1,X2),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f43,plain,(
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
              ( k4_tarski(X4,X5) != sK4(X0,X1,X2)
              | ~ r2_hidden(X5,X1)
              | ~ r2_hidden(X4,X0) )
          | ~ r2_hidden(sK4(X0,X1,X2),X2) )
        & ( ? [X7,X6] :
              ( k4_tarski(X6,X7) = sK4(X0,X1,X2)
              & r2_hidden(X7,X1)
              & r2_hidden(X6,X0) )
          | r2_hidden(sK4(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f46,plain,(
    ! [X0,X1,X2] :
      ( ( k2_zfmisc_1(X0,X1) = X2
        | ( ( ! [X4,X5] :
                ( k4_tarski(X4,X5) != sK4(X0,X1,X2)
                | ~ r2_hidden(X5,X1)
                | ~ r2_hidden(X4,X0) )
            | ~ r2_hidden(sK4(X0,X1,X2),X2) )
          & ( ( k4_tarski(sK5(X0,X1,X2),sK6(X0,X1,X2)) = sK4(X0,X1,X2)
              & r2_hidden(sK6(X0,X1,X2),X1)
              & r2_hidden(sK5(X0,X1,X2),X0) )
            | r2_hidden(sK4(X0,X1,X2),X2) ) ) )
      & ( ! [X8] :
            ( ( r2_hidden(X8,X2)
              | ! [X9,X10] :
                  ( k4_tarski(X9,X10) != X8
                  | ~ r2_hidden(X10,X1)
                  | ~ r2_hidden(X9,X0) ) )
            & ( ( k4_tarski(sK7(X0,X1,X8),sK8(X0,X1,X8)) = X8
                & r2_hidden(sK8(X0,X1,X8),X1)
                & r2_hidden(sK7(X0,X1,X8),X0) )
              | ~ r2_hidden(X8,X2) ) )
        | k2_zfmisc_1(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6,sK7,sK8])],[f42,f45,f44,f43])).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( k2_zfmisc_1(X0,X1) = X2
      | r2_hidden(sK5(X0,X1,X2),X0)
      | r2_hidden(sK4(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f16,conjecture,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,negated_conjecture,(
    ~ ! [X0,X1] :
        ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      <=> ( k1_xboole_0 = X1
          | k1_xboole_0 = X0 ) ) ),
    inference(negated_conjecture,[],[f16])).

fof(f25,plain,(
    ? [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <~> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f49,plain,(
    ? [X0,X1] :
      ( ( ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 )
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 = k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f25])).

fof(f50,plain,(
    ? [X0,X1] :
      ( ( ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 )
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 = k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f49])).

fof(f51,plain,
    ( ? [X0,X1] :
        ( ( ( k1_xboole_0 != X1
            & k1_xboole_0 != X0 )
          | k1_xboole_0 != k2_zfmisc_1(X0,X1) )
        & ( k1_xboole_0 = X1
          | k1_xboole_0 = X0
          | k1_xboole_0 = k2_zfmisc_1(X0,X1) ) )
   => ( ( ( k1_xboole_0 != sK12
          & k1_xboole_0 != sK11 )
        | k1_xboole_0 != k2_zfmisc_1(sK11,sK12) )
      & ( k1_xboole_0 = sK12
        | k1_xboole_0 = sK11
        | k1_xboole_0 = k2_zfmisc_1(sK11,sK12) ) ) ),
    introduced(choice_axiom,[])).

fof(f52,plain,
    ( ( ( k1_xboole_0 != sK12
        & k1_xboole_0 != sK11 )
      | k1_xboole_0 != k2_zfmisc_1(sK11,sK12) )
    & ( k1_xboole_0 = sK12
      | k1_xboole_0 = sK11
      | k1_xboole_0 = k2_zfmisc_1(sK11,sK12) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK11,sK12])],[f50,f51])).

fof(f86,plain,
    ( k1_xboole_0 = sK12
    | k1_xboole_0 = sK11
    | k1_xboole_0 = k2_zfmisc_1(sK11,sK12) ),
    inference(cnf_transformation,[],[f52])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3] :
      ~ ( ! [X4,X5] :
            ~ ( k4_tarski(X4,X5) = X3
              & r2_hidden(X5,X2)
              & r2_hidden(X4,X1) )
        & r2_hidden(X3,X0)
        & r1_tarski(X0,k2_zfmisc_1(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1,X2,X3] :
      ( ? [X4,X5] :
          ( k4_tarski(X4,X5) = X3
          & r2_hidden(X5,X2)
          & r2_hidden(X4,X1) )
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f47,plain,(
    ! [X3,X2,X1] :
      ( ? [X4,X5] :
          ( k4_tarski(X4,X5) = X3
          & r2_hidden(X5,X2)
          & r2_hidden(X4,X1) )
     => ( k4_tarski(sK9(X1,X2,X3),sK10(X1,X2,X3)) = X3
        & r2_hidden(sK10(X1,X2,X3),X2)
        & r2_hidden(sK9(X1,X2,X3),X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f48,plain,(
    ! [X0,X1,X2,X3] :
      ( ( k4_tarski(sK9(X1,X2,X3),sK10(X1,X2,X3)) = X3
        & r2_hidden(sK10(X1,X2,X3),X2)
        & r2_hidden(sK9(X1,X2,X3),X1) )
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK9,sK10])],[f22,f47])).

fof(f81,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(sK10(X1,X2,X3),X2)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f4,axiom,(
    ! [X0] :
      ~ ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f4])).

fof(f33,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK2(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,(
    ! [X0] :
      ( r2_hidden(sK2(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f21,f33])).

fof(f60,plain,(
    ! [X0] :
      ( r2_hidden(sK2(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f34])).

fof(f75,plain,(
    ! [X2,X0,X10,X8,X1,X9] :
      ( r2_hidden(X8,X2)
      | k4_tarski(X9,X10) != X8
      | ~ r2_hidden(X10,X1)
      | ~ r2_hidden(X9,X0)
      | k2_zfmisc_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f46])).

fof(f101,plain,(
    ! [X2,X0,X10,X1,X9] :
      ( r2_hidden(k4_tarski(X9,X10),X2)
      | ~ r2_hidden(X10,X1)
      | ~ r2_hidden(X9,X0)
      | k2_zfmisc_1(X0,X1) != X2 ) ),
    inference(equality_resolution,[],[f75])).

fof(f102,plain,(
    ! [X0,X10,X1,X9] :
      ( r2_hidden(k4_tarski(X9,X10),k2_zfmisc_1(X0,X1))
      | ~ r2_hidden(X10,X1)
      | ~ r2_hidden(X9,X0) ) ),
    inference(equality_resolution,[],[f101])).

fof(f6,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f64,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f7,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f65,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f7])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f35])).

fof(f63,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f3])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f31,plain,(
    ! [X1,X0] :
      ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
     => r2_hidden(sK1(X0,X1),k3_xboole_0(X0,X1)) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( r2_hidden(sK1(X0,X1),k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f20,f31])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,k3_xboole_0(X0,X1)) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k3_xboole_0(X0,X1) != k1_xboole_0 )
      & ( k3_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f57,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k3_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f30])).

fof(f87,plain,
    ( k1_xboole_0 != sK11
    | k1_xboole_0 != k2_zfmisc_1(sK11,sK12) ),
    inference(cnf_transformation,[],[f52])).

fof(f72,plain,(
    ! [X2,X0,X8,X1] :
      ( r2_hidden(sK7(X0,X1,X8),X0)
      | ~ r2_hidden(X8,X2)
      | k2_zfmisc_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f46])).

fof(f105,plain,(
    ! [X0,X8,X1] :
      ( r2_hidden(sK7(X0,X1,X8),X0)
      | ~ r2_hidden(X8,k2_zfmisc_1(X0,X1)) ) ),
    inference(equality_resolution,[],[f72])).

fof(f88,plain,
    ( k1_xboole_0 != sK12
    | k1_xboole_0 != k2_zfmisc_1(sK11,sK12) ),
    inference(cnf_transformation,[],[f52])).

fof(f73,plain,(
    ! [X2,X0,X8,X1] :
      ( r2_hidden(sK8(X0,X1,X8),X1)
      | ~ r2_hidden(X8,X2)
      | k2_zfmisc_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f46])).

fof(f104,plain,(
    ! [X0,X8,X1] :
      ( r2_hidden(sK8(X0,X1,X8),X1)
      | ~ r2_hidden(X8,k2_zfmisc_1(X0,X1)) ) ),
    inference(equality_resolution,[],[f73])).

cnf(c_21,plain,
    ( r2_hidden(sK5(X0,X1,X2),X0)
    | r2_hidden(sK4(X0,X1,X2),X2)
    | k2_zfmisc_1(X0,X1) = X2 ),
    inference(cnf_transformation,[],[f76])).

cnf(c_1423,plain,
    ( k2_zfmisc_1(X0,X1) = X2
    | r2_hidden(sK5(X0,X1,X2),X0) = iProver_top
    | r2_hidden(sK4(X0,X1,X2),X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_34,negated_conjecture,
    ( k1_xboole_0 = k2_zfmisc_1(sK11,sK12)
    | k1_xboole_0 = sK11
    | k1_xboole_0 = sK12 ),
    inference(cnf_transformation,[],[f86])).

cnf(c_27,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(sK10(X2,X3,X0),X3)
    | ~ r1_tarski(X1,k2_zfmisc_1(X2,X3)) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_1417,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(sK10(X2,X3,X0),X3) = iProver_top
    | r1_tarski(X1,k2_zfmisc_1(X2,X3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_2339,plain,
    ( sK11 = k1_xboole_0
    | sK12 = k1_xboole_0
    | r2_hidden(X0,X1) != iProver_top
    | r2_hidden(sK10(sK11,sK12,X0),sK12) = iProver_top
    | r1_tarski(X1,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_34,c_1417])).

cnf(c_5092,plain,
    ( k2_zfmisc_1(X0,X1) = X2
    | sK11 = k1_xboole_0
    | sK12 = k1_xboole_0
    | r2_hidden(sK10(sK11,sK12,sK4(X0,X1,X2)),sK12) = iProver_top
    | r2_hidden(sK5(X0,X1,X2),X0) = iProver_top
    | r1_tarski(X2,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1423,c_2339])).

cnf(c_6886,plain,
    ( k2_zfmisc_1(X0,X1) = X2
    | sK11 = k1_xboole_0
    | sK12 = k1_xboole_0
    | r2_hidden(sK10(sK11,sK12,sK5(X0,X1,X2)),sK12) = iProver_top
    | r2_hidden(sK10(sK11,sK12,sK4(X0,X1,X2)),sK12) = iProver_top
    | r1_tarski(X0,k1_xboole_0) != iProver_top
    | r1_tarski(X2,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_5092,c_2339])).

cnf(c_8,plain,
    ( r2_hidden(sK2(X0),X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f60])).

cnf(c_1435,plain,
    ( k1_xboole_0 = X0
    | r2_hidden(sK2(X0),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_22,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X2,X3)
    | r2_hidden(k4_tarski(X2,X0),k2_zfmisc_1(X3,X1)) ),
    inference(cnf_transformation,[],[f102])).

cnf(c_1422,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X2,X3) != iProver_top
    | r2_hidden(k4_tarski(X2,X0),k2_zfmisc_1(X3,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_4526,plain,
    ( sK11 = k1_xboole_0
    | sK12 = k1_xboole_0
    | r2_hidden(X0,sK11) != iProver_top
    | r2_hidden(X1,sK12) != iProver_top
    | r2_hidden(k4_tarski(X0,X1),k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_34,c_1422])).

cnf(c_12,plain,
    ( r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_1432,plain,
    ( r1_tarski(k3_xboole_0(X0,X1),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_13,plain,
    ( r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_1431,plain,
    ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_9,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f63])).

cnf(c_1434,plain,
    ( X0 = X1
    | r1_tarski(X1,X0) != iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_3358,plain,
    ( k1_xboole_0 = X0
    | r1_tarski(X0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1431,c_1434])).

cnf(c_5459,plain,
    ( k3_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1432,c_3358])).

cnf(c_6,plain,
    ( ~ r1_xboole_0(X0,X1)
    | ~ r2_hidden(X2,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_1437,plain,
    ( r1_xboole_0(X0,X1) != iProver_top
    | r2_hidden(X2,k3_xboole_0(X0,X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_6186,plain,
    ( r1_xboole_0(k1_xboole_0,X0) != iProver_top
    | r2_hidden(X1,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_5459,c_1437])).

cnf(c_4,plain,
    ( r1_xboole_0(X0,X1)
    | k3_xboole_0(X0,X1) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f57])).

cnf(c_1439,plain,
    ( k3_xboole_0(X0,X1) != k1_xboole_0
    | r1_xboole_0(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_6188,plain,
    ( r1_xboole_0(k1_xboole_0,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_5459,c_1439])).

cnf(c_7505,plain,
    ( r2_hidden(X1,k1_xboole_0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6186,c_6188])).

cnf(c_7506,plain,
    ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
    inference(renaming,[status(thm)],[c_7505])).

cnf(c_7527,plain,
    ( sK11 = k1_xboole_0
    | sK12 = k1_xboole_0
    | r2_hidden(X0,sK11) != iProver_top
    | r2_hidden(X1,sK12) != iProver_top ),
    inference(superposition,[status(thm)],[c_4526,c_7506])).

cnf(c_7929,plain,
    ( sK11 = k1_xboole_0
    | sK12 = k1_xboole_0
    | r2_hidden(X0,sK12) != iProver_top ),
    inference(superposition,[status(thm)],[c_1435,c_7527])).

cnf(c_10636,plain,
    ( sK11 = k1_xboole_0
    | sK12 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1435,c_7929])).

cnf(c_33,negated_conjecture,
    ( k1_xboole_0 != k2_zfmisc_1(sK11,sK12)
    | k1_xboole_0 != sK11 ),
    inference(cnf_transformation,[],[f87])).

cnf(c_10887,plain,
    ( k2_zfmisc_1(k1_xboole_0,sK12) != k1_xboole_0
    | sK11 != k1_xboole_0
    | sK12 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_10636,c_33])).

cnf(c_25,plain,
    ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
    | r2_hidden(sK7(X1,X2,X0),X1) ),
    inference(cnf_transformation,[],[f105])).

cnf(c_1419,plain,
    ( r2_hidden(X0,k2_zfmisc_1(X1,X2)) != iProver_top
    | r2_hidden(sK7(X1,X2,X0),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_7524,plain,
    ( r2_hidden(X0,k2_zfmisc_1(k1_xboole_0,X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1419,c_7506])).

cnf(c_8611,plain,
    ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1435,c_7524])).

cnf(c_10889,plain,
    ( sK11 != k1_xboole_0
    | sK12 = k1_xboole_0
    | k1_xboole_0 != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_10887,c_8611])).

cnf(c_10890,plain,
    ( sK11 != k1_xboole_0
    | sK12 = k1_xboole_0 ),
    inference(equality_resolution_simp,[status(thm)],[c_10889])).

cnf(c_11087,plain,
    ( sK12 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_6886,c_10636,c_10890])).

cnf(c_32,negated_conjecture,
    ( k1_xboole_0 != k2_zfmisc_1(sK11,sK12)
    | k1_xboole_0 != sK12 ),
    inference(cnf_transformation,[],[f88])).

cnf(c_11091,plain,
    ( k2_zfmisc_1(sK11,k1_xboole_0) != k1_xboole_0
    | k1_xboole_0 != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_11087,c_32])).

cnf(c_11092,plain,
    ( k2_zfmisc_1(sK11,k1_xboole_0) != k1_xboole_0 ),
    inference(equality_resolution_simp,[status(thm)],[c_11091])).

cnf(c_24,plain,
    ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
    | r2_hidden(sK8(X1,X2,X0),X2) ),
    inference(cnf_transformation,[],[f104])).

cnf(c_1420,plain,
    ( r2_hidden(X0,k2_zfmisc_1(X1,X2)) != iProver_top
    | r2_hidden(sK8(X1,X2,X0),X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_7523,plain,
    ( r2_hidden(X0,k2_zfmisc_1(X1,k1_xboole_0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1420,c_7506])).

cnf(c_7754,plain,
    ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1435,c_7523])).

cnf(c_11093,plain,
    ( k1_xboole_0 != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_11092,c_7754])).

cnf(c_11094,plain,
    ( $false ),
    inference(equality_resolution_simp,[status(thm)],[c_11093])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n021.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 19:26:19 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 4.07/1.00  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.07/1.00  
% 4.07/1.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 4.07/1.00  
% 4.07/1.00  ------  iProver source info
% 4.07/1.00  
% 4.07/1.00  git: date: 2020-06-30 10:37:57 +0100
% 4.07/1.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 4.07/1.00  git: non_committed_changes: false
% 4.07/1.00  git: last_make_outside_of_git: false
% 4.07/1.00  
% 4.07/1.00  ------ 
% 4.07/1.00  
% 4.07/1.00  ------ Input Options
% 4.07/1.00  
% 4.07/1.00  --out_options                           all
% 4.07/1.00  --tptp_safe_out                         true
% 4.07/1.00  --problem_path                          ""
% 4.07/1.00  --include_path                          ""
% 4.07/1.00  --clausifier                            res/vclausify_rel
% 4.07/1.00  --clausifier_options                    ""
% 4.07/1.00  --stdin                                 false
% 4.07/1.00  --stats_out                             all
% 4.07/1.00  
% 4.07/1.00  ------ General Options
% 4.07/1.00  
% 4.07/1.00  --fof                                   false
% 4.07/1.00  --time_out_real                         305.
% 4.07/1.00  --time_out_virtual                      -1.
% 4.07/1.00  --symbol_type_check                     false
% 4.07/1.00  --clausify_out                          false
% 4.07/1.00  --sig_cnt_out                           false
% 4.07/1.00  --trig_cnt_out                          false
% 4.07/1.00  --trig_cnt_out_tolerance                1.
% 4.07/1.00  --trig_cnt_out_sk_spl                   false
% 4.07/1.00  --abstr_cl_out                          false
% 4.07/1.00  
% 4.07/1.00  ------ Global Options
% 4.07/1.00  
% 4.07/1.00  --schedule                              default
% 4.07/1.00  --add_important_lit                     false
% 4.07/1.00  --prop_solver_per_cl                    1000
% 4.07/1.00  --min_unsat_core                        false
% 4.07/1.00  --soft_assumptions                      false
% 4.07/1.00  --soft_lemma_size                       3
% 4.07/1.00  --prop_impl_unit_size                   0
% 4.07/1.00  --prop_impl_unit                        []
% 4.07/1.00  --share_sel_clauses                     true
% 4.07/1.00  --reset_solvers                         false
% 4.07/1.00  --bc_imp_inh                            [conj_cone]
% 4.07/1.00  --conj_cone_tolerance                   3.
% 4.07/1.00  --extra_neg_conj                        none
% 4.07/1.00  --large_theory_mode                     true
% 4.07/1.00  --prolific_symb_bound                   200
% 4.07/1.00  --lt_threshold                          2000
% 4.07/1.00  --clause_weak_htbl                      true
% 4.07/1.00  --gc_record_bc_elim                     false
% 4.07/1.00  
% 4.07/1.00  ------ Preprocessing Options
% 4.07/1.00  
% 4.07/1.00  --preprocessing_flag                    true
% 4.07/1.00  --time_out_prep_mult                    0.1
% 4.07/1.00  --splitting_mode                        input
% 4.07/1.00  --splitting_grd                         true
% 4.07/1.00  --splitting_cvd                         false
% 4.07/1.00  --splitting_cvd_svl                     false
% 4.07/1.00  --splitting_nvd                         32
% 4.07/1.00  --sub_typing                            true
% 4.07/1.00  --prep_gs_sim                           true
% 4.07/1.00  --prep_unflatten                        true
% 4.07/1.00  --prep_res_sim                          true
% 4.07/1.00  --prep_upred                            true
% 4.07/1.00  --prep_sem_filter                       exhaustive
% 4.07/1.00  --prep_sem_filter_out                   false
% 4.07/1.00  --pred_elim                             true
% 4.07/1.00  --res_sim_input                         true
% 4.07/1.00  --eq_ax_congr_red                       true
% 4.07/1.00  --pure_diseq_elim                       true
% 4.07/1.00  --brand_transform                       false
% 4.07/1.00  --non_eq_to_eq                          false
% 4.07/1.00  --prep_def_merge                        true
% 4.07/1.00  --prep_def_merge_prop_impl              false
% 4.07/1.00  --prep_def_merge_mbd                    true
% 4.07/1.00  --prep_def_merge_tr_red                 false
% 4.07/1.00  --prep_def_merge_tr_cl                  false
% 4.07/1.00  --smt_preprocessing                     true
% 4.07/1.00  --smt_ac_axioms                         fast
% 4.07/1.00  --preprocessed_out                      false
% 4.07/1.00  --preprocessed_stats                    false
% 4.07/1.00  
% 4.07/1.00  ------ Abstraction refinement Options
% 4.07/1.00  
% 4.07/1.00  --abstr_ref                             []
% 4.07/1.00  --abstr_ref_prep                        false
% 4.07/1.00  --abstr_ref_until_sat                   false
% 4.07/1.00  --abstr_ref_sig_restrict                funpre
% 4.07/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 4.07/1.00  --abstr_ref_under                       []
% 4.07/1.00  
% 4.07/1.00  ------ SAT Options
% 4.07/1.00  
% 4.07/1.00  --sat_mode                              false
% 4.07/1.00  --sat_fm_restart_options                ""
% 4.07/1.00  --sat_gr_def                            false
% 4.07/1.00  --sat_epr_types                         true
% 4.07/1.00  --sat_non_cyclic_types                  false
% 4.07/1.00  --sat_finite_models                     false
% 4.07/1.00  --sat_fm_lemmas                         false
% 4.07/1.00  --sat_fm_prep                           false
% 4.07/1.00  --sat_fm_uc_incr                        true
% 4.07/1.00  --sat_out_model                         small
% 4.07/1.00  --sat_out_clauses                       false
% 4.07/1.00  
% 4.07/1.00  ------ QBF Options
% 4.07/1.00  
% 4.07/1.00  --qbf_mode                              false
% 4.07/1.00  --qbf_elim_univ                         false
% 4.07/1.00  --qbf_dom_inst                          none
% 4.07/1.00  --qbf_dom_pre_inst                      false
% 4.07/1.00  --qbf_sk_in                             false
% 4.07/1.00  --qbf_pred_elim                         true
% 4.07/1.00  --qbf_split                             512
% 4.07/1.00  
% 4.07/1.00  ------ BMC1 Options
% 4.07/1.00  
% 4.07/1.00  --bmc1_incremental                      false
% 4.07/1.00  --bmc1_axioms                           reachable_all
% 4.07/1.00  --bmc1_min_bound                        0
% 4.07/1.00  --bmc1_max_bound                        -1
% 4.07/1.00  --bmc1_max_bound_default                -1
% 4.07/1.00  --bmc1_symbol_reachability              true
% 4.07/1.00  --bmc1_property_lemmas                  false
% 4.07/1.00  --bmc1_k_induction                      false
% 4.07/1.00  --bmc1_non_equiv_states                 false
% 4.07/1.00  --bmc1_deadlock                         false
% 4.07/1.00  --bmc1_ucm                              false
% 4.07/1.00  --bmc1_add_unsat_core                   none
% 4.07/1.00  --bmc1_unsat_core_children              false
% 4.07/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 4.07/1.00  --bmc1_out_stat                         full
% 4.07/1.00  --bmc1_ground_init                      false
% 4.07/1.00  --bmc1_pre_inst_next_state              false
% 4.07/1.00  --bmc1_pre_inst_state                   false
% 4.07/1.00  --bmc1_pre_inst_reach_state             false
% 4.07/1.00  --bmc1_out_unsat_core                   false
% 4.07/1.00  --bmc1_aig_witness_out                  false
% 4.07/1.00  --bmc1_verbose                          false
% 4.07/1.00  --bmc1_dump_clauses_tptp                false
% 4.07/1.00  --bmc1_dump_unsat_core_tptp             false
% 4.07/1.00  --bmc1_dump_file                        -
% 4.07/1.00  --bmc1_ucm_expand_uc_limit              128
% 4.07/1.00  --bmc1_ucm_n_expand_iterations          6
% 4.07/1.00  --bmc1_ucm_extend_mode                  1
% 4.07/1.00  --bmc1_ucm_init_mode                    2
% 4.07/1.00  --bmc1_ucm_cone_mode                    none
% 4.07/1.00  --bmc1_ucm_reduced_relation_type        0
% 4.07/1.00  --bmc1_ucm_relax_model                  4
% 4.07/1.00  --bmc1_ucm_full_tr_after_sat            true
% 4.07/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 4.07/1.00  --bmc1_ucm_layered_model                none
% 4.07/1.00  --bmc1_ucm_max_lemma_size               10
% 4.07/1.00  
% 4.07/1.00  ------ AIG Options
% 4.07/1.00  
% 4.07/1.00  --aig_mode                              false
% 4.07/1.00  
% 4.07/1.00  ------ Instantiation Options
% 4.07/1.00  
% 4.07/1.00  --instantiation_flag                    true
% 4.07/1.00  --inst_sos_flag                         true
% 4.07/1.00  --inst_sos_phase                        true
% 4.07/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 4.07/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 4.07/1.00  --inst_lit_sel_side                     num_symb
% 4.07/1.00  --inst_solver_per_active                1400
% 4.07/1.00  --inst_solver_calls_frac                1.
% 4.07/1.00  --inst_passive_queue_type               priority_queues
% 4.07/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 4.07/1.00  --inst_passive_queues_freq              [25;2]
% 4.07/1.00  --inst_dismatching                      true
% 4.07/1.00  --inst_eager_unprocessed_to_passive     true
% 4.07/1.00  --inst_prop_sim_given                   true
% 4.07/1.00  --inst_prop_sim_new                     false
% 4.07/1.00  --inst_subs_new                         false
% 4.07/1.00  --inst_eq_res_simp                      false
% 4.07/1.00  --inst_subs_given                       false
% 4.07/1.00  --inst_orphan_elimination               true
% 4.07/1.00  --inst_learning_loop_flag               true
% 4.07/1.00  --inst_learning_start                   3000
% 4.07/1.00  --inst_learning_factor                  2
% 4.07/1.00  --inst_start_prop_sim_after_learn       3
% 4.07/1.00  --inst_sel_renew                        solver
% 4.07/1.00  --inst_lit_activity_flag                true
% 4.07/1.00  --inst_restr_to_given                   false
% 4.07/1.00  --inst_activity_threshold               500
% 4.07/1.00  --inst_out_proof                        true
% 4.07/1.00  
% 4.07/1.00  ------ Resolution Options
% 4.07/1.00  
% 4.07/1.00  --resolution_flag                       true
% 4.07/1.00  --res_lit_sel                           adaptive
% 4.07/1.00  --res_lit_sel_side                      none
% 4.07/1.00  --res_ordering                          kbo
% 4.07/1.00  --res_to_prop_solver                    active
% 4.07/1.00  --res_prop_simpl_new                    false
% 4.07/1.00  --res_prop_simpl_given                  true
% 4.07/1.00  --res_passive_queue_type                priority_queues
% 4.07/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 4.07/1.00  --res_passive_queues_freq               [15;5]
% 4.07/1.00  --res_forward_subs                      full
% 4.07/1.00  --res_backward_subs                     full
% 4.07/1.00  --res_forward_subs_resolution           true
% 4.07/1.00  --res_backward_subs_resolution          true
% 4.07/1.00  --res_orphan_elimination                true
% 4.07/1.00  --res_time_limit                        2.
% 4.07/1.00  --res_out_proof                         true
% 4.07/1.00  
% 4.07/1.00  ------ Superposition Options
% 4.07/1.00  
% 4.07/1.00  --superposition_flag                    true
% 4.07/1.00  --sup_passive_queue_type                priority_queues
% 4.07/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 4.07/1.00  --sup_passive_queues_freq               [8;1;4]
% 4.07/1.00  --demod_completeness_check              fast
% 4.07/1.00  --demod_use_ground                      true
% 4.07/1.00  --sup_to_prop_solver                    passive
% 4.07/1.00  --sup_prop_simpl_new                    true
% 4.07/1.00  --sup_prop_simpl_given                  true
% 4.07/1.00  --sup_fun_splitting                     true
% 4.07/1.00  --sup_smt_interval                      50000
% 4.07/1.00  
% 4.07/1.00  ------ Superposition Simplification Setup
% 4.07/1.00  
% 4.07/1.00  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 4.07/1.00  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 4.07/1.00  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 4.07/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 4.07/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 4.07/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 4.07/1.00  --sup_full_bw                           [BwDemod;BwSubsumption]
% 4.07/1.00  --sup_immed_triv                        [TrivRules]
% 4.07/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 4.07/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 4.07/1.00  --sup_immed_bw_main                     []
% 4.07/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 4.07/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 4.07/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 4.07/1.00  --sup_input_bw                          []
% 4.07/1.00  
% 4.07/1.00  ------ Combination Options
% 4.07/1.00  
% 4.07/1.00  --comb_res_mult                         3
% 4.07/1.00  --comb_sup_mult                         2
% 4.07/1.00  --comb_inst_mult                        10
% 4.07/1.00  
% 4.07/1.00  ------ Debug Options
% 4.07/1.00  
% 4.07/1.00  --dbg_backtrace                         false
% 4.07/1.00  --dbg_dump_prop_clauses                 false
% 4.07/1.00  --dbg_dump_prop_clauses_file            -
% 4.07/1.00  --dbg_out_stat                          false
% 4.07/1.00  ------ Parsing...
% 4.07/1.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 4.07/1.00  
% 4.07/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e  sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 4.07/1.00  
% 4.07/1.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 4.07/1.00  
% 4.07/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 4.07/1.00  ------ Proving...
% 4.07/1.00  ------ Problem Properties 
% 4.07/1.00  
% 4.07/1.00  
% 4.07/1.00  clauses                                 34
% 4.07/1.00  conjectures                             3
% 4.07/1.00  EPR                                     4
% 4.07/1.00  Horn                                    25
% 4.07/1.00  unary                                   6
% 4.07/1.00  binary                                  14
% 4.07/1.00  lits                                    78
% 4.07/1.00  lits eq                                 27
% 4.07/1.00  fd_pure                                 0
% 4.07/1.00  fd_pseudo                               0
% 4.07/1.00  fd_cond                                 1
% 4.07/1.00  fd_pseudo_cond                          7
% 4.07/1.00  AC symbols                              0
% 4.07/1.00  
% 4.07/1.00  ------ Schedule dynamic 5 is on 
% 4.07/1.00  
% 4.07/1.00  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 4.07/1.00  
% 4.07/1.00  
% 4.07/1.00  ------ 
% 4.07/1.00  Current options:
% 4.07/1.00  ------ 
% 4.07/1.00  
% 4.07/1.00  ------ Input Options
% 4.07/1.00  
% 4.07/1.00  --out_options                           all
% 4.07/1.00  --tptp_safe_out                         true
% 4.07/1.00  --problem_path                          ""
% 4.07/1.00  --include_path                          ""
% 4.07/1.00  --clausifier                            res/vclausify_rel
% 4.07/1.00  --clausifier_options                    ""
% 4.07/1.00  --stdin                                 false
% 4.07/1.00  --stats_out                             all
% 4.07/1.00  
% 4.07/1.00  ------ General Options
% 4.07/1.00  
% 4.07/1.00  --fof                                   false
% 4.07/1.00  --time_out_real                         305.
% 4.07/1.00  --time_out_virtual                      -1.
% 4.07/1.00  --symbol_type_check                     false
% 4.07/1.00  --clausify_out                          false
% 4.07/1.00  --sig_cnt_out                           false
% 4.07/1.00  --trig_cnt_out                          false
% 4.07/1.00  --trig_cnt_out_tolerance                1.
% 4.07/1.00  --trig_cnt_out_sk_spl                   false
% 4.07/1.00  --abstr_cl_out                          false
% 4.07/1.00  
% 4.07/1.00  ------ Global Options
% 4.07/1.00  
% 4.07/1.00  --schedule                              default
% 4.07/1.00  --add_important_lit                     false
% 4.07/1.00  --prop_solver_per_cl                    1000
% 4.07/1.00  --min_unsat_core                        false
% 4.07/1.00  --soft_assumptions                      false
% 4.07/1.00  --soft_lemma_size                       3
% 4.07/1.00  --prop_impl_unit_size                   0
% 4.07/1.00  --prop_impl_unit                        []
% 4.07/1.00  --share_sel_clauses                     true
% 4.07/1.00  --reset_solvers                         false
% 4.07/1.00  --bc_imp_inh                            [conj_cone]
% 4.07/1.00  --conj_cone_tolerance                   3.
% 4.07/1.00  --extra_neg_conj                        none
% 4.07/1.00  --large_theory_mode                     true
% 4.07/1.00  --prolific_symb_bound                   200
% 4.07/1.00  --lt_threshold                          2000
% 4.07/1.00  --clause_weak_htbl                      true
% 4.07/1.00  --gc_record_bc_elim                     false
% 4.07/1.00  
% 4.07/1.00  ------ Preprocessing Options
% 4.07/1.00  
% 4.07/1.00  --preprocessing_flag                    true
% 4.07/1.00  --time_out_prep_mult                    0.1
% 4.07/1.00  --splitting_mode                        input
% 4.07/1.00  --splitting_grd                         true
% 4.07/1.00  --splitting_cvd                         false
% 4.07/1.00  --splitting_cvd_svl                     false
% 4.07/1.00  --splitting_nvd                         32
% 4.07/1.00  --sub_typing                            true
% 4.07/1.00  --prep_gs_sim                           true
% 4.07/1.00  --prep_unflatten                        true
% 4.07/1.00  --prep_res_sim                          true
% 4.07/1.00  --prep_upred                            true
% 4.07/1.00  --prep_sem_filter                       exhaustive
% 4.07/1.00  --prep_sem_filter_out                   false
% 4.07/1.00  --pred_elim                             true
% 4.07/1.00  --res_sim_input                         true
% 4.07/1.00  --eq_ax_congr_red                       true
% 4.07/1.00  --pure_diseq_elim                       true
% 4.07/1.00  --brand_transform                       false
% 4.07/1.00  --non_eq_to_eq                          false
% 4.07/1.00  --prep_def_merge                        true
% 4.07/1.00  --prep_def_merge_prop_impl              false
% 4.07/1.00  --prep_def_merge_mbd                    true
% 4.07/1.00  --prep_def_merge_tr_red                 false
% 4.07/1.00  --prep_def_merge_tr_cl                  false
% 4.07/1.00  --smt_preprocessing                     true
% 4.07/1.00  --smt_ac_axioms                         fast
% 4.07/1.00  --preprocessed_out                      false
% 4.07/1.00  --preprocessed_stats                    false
% 4.07/1.00  
% 4.07/1.00  ------ Abstraction refinement Options
% 4.07/1.00  
% 4.07/1.00  --abstr_ref                             []
% 4.07/1.00  --abstr_ref_prep                        false
% 4.07/1.00  --abstr_ref_until_sat                   false
% 4.07/1.00  --abstr_ref_sig_restrict                funpre
% 4.07/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 4.07/1.00  --abstr_ref_under                       []
% 4.07/1.00  
% 4.07/1.00  ------ SAT Options
% 4.07/1.00  
% 4.07/1.00  --sat_mode                              false
% 4.07/1.00  --sat_fm_restart_options                ""
% 4.07/1.00  --sat_gr_def                            false
% 4.07/1.00  --sat_epr_types                         true
% 4.07/1.00  --sat_non_cyclic_types                  false
% 4.07/1.00  --sat_finite_models                     false
% 4.07/1.00  --sat_fm_lemmas                         false
% 4.07/1.00  --sat_fm_prep                           false
% 4.07/1.00  --sat_fm_uc_incr                        true
% 4.07/1.00  --sat_out_model                         small
% 4.07/1.00  --sat_out_clauses                       false
% 4.07/1.00  
% 4.07/1.00  ------ QBF Options
% 4.07/1.00  
% 4.07/1.00  --qbf_mode                              false
% 4.07/1.00  --qbf_elim_univ                         false
% 4.07/1.00  --qbf_dom_inst                          none
% 4.07/1.00  --qbf_dom_pre_inst                      false
% 4.07/1.00  --qbf_sk_in                             false
% 4.07/1.00  --qbf_pred_elim                         true
% 4.07/1.00  --qbf_split                             512
% 4.07/1.00  
% 4.07/1.00  ------ BMC1 Options
% 4.07/1.00  
% 4.07/1.00  --bmc1_incremental                      false
% 4.07/1.00  --bmc1_axioms                           reachable_all
% 4.07/1.00  --bmc1_min_bound                        0
% 4.07/1.00  --bmc1_max_bound                        -1
% 4.07/1.00  --bmc1_max_bound_default                -1
% 4.07/1.00  --bmc1_symbol_reachability              true
% 4.07/1.00  --bmc1_property_lemmas                  false
% 4.07/1.00  --bmc1_k_induction                      false
% 4.07/1.00  --bmc1_non_equiv_states                 false
% 4.07/1.00  --bmc1_deadlock                         false
% 4.07/1.00  --bmc1_ucm                              false
% 4.07/1.00  --bmc1_add_unsat_core                   none
% 4.07/1.00  --bmc1_unsat_core_children              false
% 4.07/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 4.07/1.00  --bmc1_out_stat                         full
% 4.07/1.00  --bmc1_ground_init                      false
% 4.07/1.00  --bmc1_pre_inst_next_state              false
% 4.07/1.00  --bmc1_pre_inst_state                   false
% 4.07/1.00  --bmc1_pre_inst_reach_state             false
% 4.07/1.00  --bmc1_out_unsat_core                   false
% 4.07/1.00  --bmc1_aig_witness_out                  false
% 4.07/1.00  --bmc1_verbose                          false
% 4.07/1.00  --bmc1_dump_clauses_tptp                false
% 4.07/1.00  --bmc1_dump_unsat_core_tptp             false
% 4.07/1.00  --bmc1_dump_file                        -
% 4.07/1.00  --bmc1_ucm_expand_uc_limit              128
% 4.07/1.00  --bmc1_ucm_n_expand_iterations          6
% 4.07/1.00  --bmc1_ucm_extend_mode                  1
% 4.07/1.00  --bmc1_ucm_init_mode                    2
% 4.07/1.00  --bmc1_ucm_cone_mode                    none
% 4.07/1.00  --bmc1_ucm_reduced_relation_type        0
% 4.07/1.00  --bmc1_ucm_relax_model                  4
% 4.07/1.00  --bmc1_ucm_full_tr_after_sat            true
% 4.07/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 4.07/1.00  --bmc1_ucm_layered_model                none
% 4.07/1.00  --bmc1_ucm_max_lemma_size               10
% 4.07/1.00  
% 4.07/1.00  ------ AIG Options
% 4.07/1.00  
% 4.07/1.00  --aig_mode                              false
% 4.07/1.00  
% 4.07/1.00  ------ Instantiation Options
% 4.07/1.00  
% 4.07/1.00  --instantiation_flag                    true
% 4.07/1.00  --inst_sos_flag                         true
% 4.07/1.00  --inst_sos_phase                        true
% 4.07/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 4.07/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 4.07/1.00  --inst_lit_sel_side                     none
% 4.07/1.00  --inst_solver_per_active                1400
% 4.07/1.00  --inst_solver_calls_frac                1.
% 4.07/1.00  --inst_passive_queue_type               priority_queues
% 4.07/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 4.07/1.00  --inst_passive_queues_freq              [25;2]
% 4.07/1.00  --inst_dismatching                      true
% 4.07/1.00  --inst_eager_unprocessed_to_passive     true
% 4.07/1.00  --inst_prop_sim_given                   true
% 4.07/1.00  --inst_prop_sim_new                     false
% 4.07/1.00  --inst_subs_new                         false
% 4.07/1.00  --inst_eq_res_simp                      false
% 4.07/1.00  --inst_subs_given                       false
% 4.07/1.00  --inst_orphan_elimination               true
% 4.07/1.00  --inst_learning_loop_flag               true
% 4.07/1.00  --inst_learning_start                   3000
% 4.07/1.00  --inst_learning_factor                  2
% 4.07/1.00  --inst_start_prop_sim_after_learn       3
% 4.07/1.00  --inst_sel_renew                        solver
% 4.07/1.00  --inst_lit_activity_flag                true
% 4.07/1.00  --inst_restr_to_given                   false
% 4.07/1.00  --inst_activity_threshold               500
% 4.07/1.00  --inst_out_proof                        true
% 4.07/1.00  
% 4.07/1.00  ------ Resolution Options
% 4.07/1.00  
% 4.07/1.00  --resolution_flag                       false
% 4.07/1.00  --res_lit_sel                           adaptive
% 4.07/1.00  --res_lit_sel_side                      none
% 4.07/1.00  --res_ordering                          kbo
% 4.07/1.00  --res_to_prop_solver                    active
% 4.07/1.00  --res_prop_simpl_new                    false
% 4.07/1.00  --res_prop_simpl_given                  true
% 4.07/1.00  --res_passive_queue_type                priority_queues
% 4.07/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 4.07/1.00  --res_passive_queues_freq               [15;5]
% 4.07/1.00  --res_forward_subs                      full
% 4.07/1.00  --res_backward_subs                     full
% 4.07/1.00  --res_forward_subs_resolution           true
% 4.07/1.00  --res_backward_subs_resolution          true
% 4.07/1.00  --res_orphan_elimination                true
% 4.07/1.00  --res_time_limit                        2.
% 4.07/1.00  --res_out_proof                         true
% 4.07/1.00  
% 4.07/1.00  ------ Superposition Options
% 4.07/1.00  
% 4.07/1.00  --superposition_flag                    true
% 4.07/1.00  --sup_passive_queue_type                priority_queues
% 4.07/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 4.07/1.00  --sup_passive_queues_freq               [8;1;4]
% 4.07/1.00  --demod_completeness_check              fast
% 4.07/1.00  --demod_use_ground                      true
% 4.07/1.00  --sup_to_prop_solver                    passive
% 4.07/1.00  --sup_prop_simpl_new                    true
% 4.07/1.00  --sup_prop_simpl_given                  true
% 4.07/1.00  --sup_fun_splitting                     true
% 4.07/1.00  --sup_smt_interval                      50000
% 4.07/1.00  
% 4.07/1.00  ------ Superposition Simplification Setup
% 4.07/1.00  
% 4.07/1.00  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 4.07/1.00  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 4.07/1.00  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 4.07/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 4.07/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 4.07/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 4.07/1.00  --sup_full_bw                           [BwDemod;BwSubsumption]
% 4.07/1.00  --sup_immed_triv                        [TrivRules]
% 4.07/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 4.07/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 4.07/1.00  --sup_immed_bw_main                     []
% 4.07/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 4.07/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 4.07/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 4.07/1.00  --sup_input_bw                          []
% 4.07/1.00  
% 4.07/1.00  ------ Combination Options
% 4.07/1.00  
% 4.07/1.00  --comb_res_mult                         3
% 4.07/1.00  --comb_sup_mult                         2
% 4.07/1.00  --comb_inst_mult                        10
% 4.07/1.00  
% 4.07/1.00  ------ Debug Options
% 4.07/1.00  
% 4.07/1.00  --dbg_backtrace                         false
% 4.07/1.00  --dbg_dump_prop_clauses                 false
% 4.07/1.00  --dbg_dump_prop_clauses_file            -
% 4.07/1.00  --dbg_out_stat                          false
% 4.07/1.00  
% 4.07/1.00  
% 4.07/1.00  
% 4.07/1.00  
% 4.07/1.00  ------ Proving...
% 4.07/1.00  
% 4.07/1.00  
% 4.07/1.00  % SZS status Theorem for theBenchmark.p
% 4.07/1.00  
% 4.07/1.00   Resolution empty clause
% 4.07/1.00  
% 4.07/1.00  % SZS output start CNFRefutation for theBenchmark.p
% 4.07/1.00  
% 4.07/1.00  fof(f11,axiom,(
% 4.07/1.00    ! [X0,X1,X2] : (k2_zfmisc_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4,X5] : (k4_tarski(X4,X5) = X3 & r2_hidden(X5,X1) & r2_hidden(X4,X0))))),
% 4.07/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.07/1.00  
% 4.07/1.00  fof(f41,plain,(
% 4.07/1.00    ! [X0,X1,X2] : ((k2_zfmisc_1(X0,X1) = X2 | ? [X3] : ((! [X4,X5] : (k4_tarski(X4,X5) != X3 | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X0)) | ~r2_hidden(X3,X2)) & (? [X4,X5] : (k4_tarski(X4,X5) = X3 & r2_hidden(X5,X1) & r2_hidden(X4,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ! [X4,X5] : (k4_tarski(X4,X5) != X3 | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X0))) & (? [X4,X5] : (k4_tarski(X4,X5) = X3 & r2_hidden(X5,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X3,X2))) | k2_zfmisc_1(X0,X1) != X2))),
% 4.07/1.00    inference(nnf_transformation,[],[f11])).
% 4.07/1.00  
% 4.07/1.00  fof(f42,plain,(
% 4.07/1.00    ! [X0,X1,X2] : ((k2_zfmisc_1(X0,X1) = X2 | ? [X3] : ((! [X4,X5] : (k4_tarski(X4,X5) != X3 | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X0)) | ~r2_hidden(X3,X2)) & (? [X6,X7] : (k4_tarski(X6,X7) = X3 & r2_hidden(X7,X1) & r2_hidden(X6,X0)) | r2_hidden(X3,X2)))) & (! [X8] : ((r2_hidden(X8,X2) | ! [X9,X10] : (k4_tarski(X9,X10) != X8 | ~r2_hidden(X10,X1) | ~r2_hidden(X9,X0))) & (? [X11,X12] : (k4_tarski(X11,X12) = X8 & r2_hidden(X12,X1) & r2_hidden(X11,X0)) | ~r2_hidden(X8,X2))) | k2_zfmisc_1(X0,X1) != X2))),
% 4.07/1.00    inference(rectify,[],[f41])).
% 4.07/1.00  
% 4.07/1.00  fof(f45,plain,(
% 4.07/1.00    ! [X8,X1,X0] : (? [X11,X12] : (k4_tarski(X11,X12) = X8 & r2_hidden(X12,X1) & r2_hidden(X11,X0)) => (k4_tarski(sK7(X0,X1,X8),sK8(X0,X1,X8)) = X8 & r2_hidden(sK8(X0,X1,X8),X1) & r2_hidden(sK7(X0,X1,X8),X0)))),
% 4.07/1.00    introduced(choice_axiom,[])).
% 4.07/1.00  
% 4.07/1.00  fof(f44,plain,(
% 4.07/1.00    ( ! [X3] : (! [X2,X1,X0] : (? [X6,X7] : (k4_tarski(X6,X7) = X3 & r2_hidden(X7,X1) & r2_hidden(X6,X0)) => (k4_tarski(sK5(X0,X1,X2),sK6(X0,X1,X2)) = X3 & r2_hidden(sK6(X0,X1,X2),X1) & r2_hidden(sK5(X0,X1,X2),X0)))) )),
% 4.07/1.00    introduced(choice_axiom,[])).
% 4.07/1.00  
% 4.07/1.00  fof(f43,plain,(
% 4.07/1.00    ! [X2,X1,X0] : (? [X3] : ((! [X4,X5] : (k4_tarski(X4,X5) != X3 | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X0)) | ~r2_hidden(X3,X2)) & (? [X6,X7] : (k4_tarski(X6,X7) = X3 & r2_hidden(X7,X1) & r2_hidden(X6,X0)) | r2_hidden(X3,X2))) => ((! [X5,X4] : (k4_tarski(X4,X5) != sK4(X0,X1,X2) | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X0)) | ~r2_hidden(sK4(X0,X1,X2),X2)) & (? [X7,X6] : (k4_tarski(X6,X7) = sK4(X0,X1,X2) & r2_hidden(X7,X1) & r2_hidden(X6,X0)) | r2_hidden(sK4(X0,X1,X2),X2))))),
% 4.07/1.00    introduced(choice_axiom,[])).
% 4.07/1.00  
% 4.07/1.00  fof(f46,plain,(
% 4.07/1.00    ! [X0,X1,X2] : ((k2_zfmisc_1(X0,X1) = X2 | ((! [X4,X5] : (k4_tarski(X4,X5) != sK4(X0,X1,X2) | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X0)) | ~r2_hidden(sK4(X0,X1,X2),X2)) & ((k4_tarski(sK5(X0,X1,X2),sK6(X0,X1,X2)) = sK4(X0,X1,X2) & r2_hidden(sK6(X0,X1,X2),X1) & r2_hidden(sK5(X0,X1,X2),X0)) | r2_hidden(sK4(X0,X1,X2),X2)))) & (! [X8] : ((r2_hidden(X8,X2) | ! [X9,X10] : (k4_tarski(X9,X10) != X8 | ~r2_hidden(X10,X1) | ~r2_hidden(X9,X0))) & ((k4_tarski(sK7(X0,X1,X8),sK8(X0,X1,X8)) = X8 & r2_hidden(sK8(X0,X1,X8),X1) & r2_hidden(sK7(X0,X1,X8),X0)) | ~r2_hidden(X8,X2))) | k2_zfmisc_1(X0,X1) != X2))),
% 4.07/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6,sK7,sK8])],[f42,f45,f44,f43])).
% 4.07/1.00  
% 4.07/1.00  fof(f76,plain,(
% 4.07/1.00    ( ! [X2,X0,X1] : (k2_zfmisc_1(X0,X1) = X2 | r2_hidden(sK5(X0,X1,X2),X0) | r2_hidden(sK4(X0,X1,X2),X2)) )),
% 4.07/1.00    inference(cnf_transformation,[],[f46])).
% 4.07/1.00  
% 4.07/1.00  fof(f16,conjecture,(
% 4.07/1.00    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 4.07/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.07/1.00  
% 4.07/1.00  fof(f17,negated_conjecture,(
% 4.07/1.00    ~! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 4.07/1.00    inference(negated_conjecture,[],[f16])).
% 4.07/1.00  
% 4.07/1.00  fof(f25,plain,(
% 4.07/1.00    ? [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <~> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 4.07/1.00    inference(ennf_transformation,[],[f17])).
% 4.07/1.00  
% 4.07/1.00  fof(f49,plain,(
% 4.07/1.00    ? [X0,X1] : (((k1_xboole_0 != X1 & k1_xboole_0 != X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 = k2_zfmisc_1(X0,X1)))),
% 4.07/1.00    inference(nnf_transformation,[],[f25])).
% 4.07/1.00  
% 4.07/1.00  fof(f50,plain,(
% 4.07/1.00    ? [X0,X1] : (((k1_xboole_0 != X1 & k1_xboole_0 != X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 = k2_zfmisc_1(X0,X1)))),
% 4.07/1.00    inference(flattening,[],[f49])).
% 4.07/1.00  
% 4.07/1.00  fof(f51,plain,(
% 4.07/1.00    ? [X0,X1] : (((k1_xboole_0 != X1 & k1_xboole_0 != X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 = k2_zfmisc_1(X0,X1))) => (((k1_xboole_0 != sK12 & k1_xboole_0 != sK11) | k1_xboole_0 != k2_zfmisc_1(sK11,sK12)) & (k1_xboole_0 = sK12 | k1_xboole_0 = sK11 | k1_xboole_0 = k2_zfmisc_1(sK11,sK12)))),
% 4.07/1.00    introduced(choice_axiom,[])).
% 4.07/1.00  
% 4.07/1.00  fof(f52,plain,(
% 4.07/1.00    ((k1_xboole_0 != sK12 & k1_xboole_0 != sK11) | k1_xboole_0 != k2_zfmisc_1(sK11,sK12)) & (k1_xboole_0 = sK12 | k1_xboole_0 = sK11 | k1_xboole_0 = k2_zfmisc_1(sK11,sK12))),
% 4.07/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK11,sK12])],[f50,f51])).
% 4.07/1.00  
% 4.07/1.00  fof(f86,plain,(
% 4.07/1.00    k1_xboole_0 = sK12 | k1_xboole_0 = sK11 | k1_xboole_0 = k2_zfmisc_1(sK11,sK12)),
% 4.07/1.00    inference(cnf_transformation,[],[f52])).
% 4.07/1.00  
% 4.07/1.00  fof(f12,axiom,(
% 4.07/1.00    ! [X0,X1,X2,X3] : ~(! [X4,X5] : ~(k4_tarski(X4,X5) = X3 & r2_hidden(X5,X2) & r2_hidden(X4,X1)) & r2_hidden(X3,X0) & r1_tarski(X0,k2_zfmisc_1(X1,X2)))),
% 4.07/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.07/1.00  
% 4.07/1.00  fof(f22,plain,(
% 4.07/1.00    ! [X0,X1,X2,X3] : (? [X4,X5] : (k4_tarski(X4,X5) = X3 & r2_hidden(X5,X2) & r2_hidden(X4,X1)) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,k2_zfmisc_1(X1,X2)))),
% 4.07/1.00    inference(ennf_transformation,[],[f12])).
% 4.07/1.00  
% 4.07/1.00  fof(f47,plain,(
% 4.07/1.00    ! [X3,X2,X1] : (? [X4,X5] : (k4_tarski(X4,X5) = X3 & r2_hidden(X5,X2) & r2_hidden(X4,X1)) => (k4_tarski(sK9(X1,X2,X3),sK10(X1,X2,X3)) = X3 & r2_hidden(sK10(X1,X2,X3),X2) & r2_hidden(sK9(X1,X2,X3),X1)))),
% 4.07/1.00    introduced(choice_axiom,[])).
% 4.07/1.00  
% 4.07/1.00  fof(f48,plain,(
% 4.07/1.00    ! [X0,X1,X2,X3] : ((k4_tarski(sK9(X1,X2,X3),sK10(X1,X2,X3)) = X3 & r2_hidden(sK10(X1,X2,X3),X2) & r2_hidden(sK9(X1,X2,X3),X1)) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,k2_zfmisc_1(X1,X2)))),
% 4.07/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK9,sK10])],[f22,f47])).
% 4.07/1.00  
% 4.07/1.00  fof(f81,plain,(
% 4.07/1.00    ( ! [X2,X0,X3,X1] : (r2_hidden(sK10(X1,X2,X3),X2) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,k2_zfmisc_1(X1,X2))) )),
% 4.07/1.00    inference(cnf_transformation,[],[f48])).
% 4.07/1.00  
% 4.07/1.00  fof(f4,axiom,(
% 4.07/1.00    ! [X0] : ~(! [X1] : ~r2_hidden(X1,X0) & k1_xboole_0 != X0)),
% 4.07/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.07/1.00  
% 4.07/1.00  fof(f21,plain,(
% 4.07/1.00    ! [X0] : (? [X1] : r2_hidden(X1,X0) | k1_xboole_0 = X0)),
% 4.07/1.00    inference(ennf_transformation,[],[f4])).
% 4.07/1.00  
% 4.07/1.00  fof(f33,plain,(
% 4.07/1.00    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK2(X0),X0))),
% 4.07/1.00    introduced(choice_axiom,[])).
% 4.07/1.00  
% 4.07/1.00  fof(f34,plain,(
% 4.07/1.00    ! [X0] : (r2_hidden(sK2(X0),X0) | k1_xboole_0 = X0)),
% 4.07/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f21,f33])).
% 4.07/1.00  
% 4.07/1.00  fof(f60,plain,(
% 4.07/1.00    ( ! [X0] : (r2_hidden(sK2(X0),X0) | k1_xboole_0 = X0) )),
% 4.07/1.00    inference(cnf_transformation,[],[f34])).
% 4.07/1.00  
% 4.07/1.00  fof(f75,plain,(
% 4.07/1.00    ( ! [X2,X0,X10,X8,X1,X9] : (r2_hidden(X8,X2) | k4_tarski(X9,X10) != X8 | ~r2_hidden(X10,X1) | ~r2_hidden(X9,X0) | k2_zfmisc_1(X0,X1) != X2) )),
% 4.07/1.00    inference(cnf_transformation,[],[f46])).
% 4.07/1.00  
% 4.07/1.00  fof(f101,plain,(
% 4.07/1.00    ( ! [X2,X0,X10,X1,X9] : (r2_hidden(k4_tarski(X9,X10),X2) | ~r2_hidden(X10,X1) | ~r2_hidden(X9,X0) | k2_zfmisc_1(X0,X1) != X2) )),
% 4.07/1.00    inference(equality_resolution,[],[f75])).
% 4.07/1.00  
% 4.07/1.00  fof(f102,plain,(
% 4.07/1.00    ( ! [X0,X10,X1,X9] : (r2_hidden(k4_tarski(X9,X10),k2_zfmisc_1(X0,X1)) | ~r2_hidden(X10,X1) | ~r2_hidden(X9,X0)) )),
% 4.07/1.00    inference(equality_resolution,[],[f101])).
% 4.07/1.00  
% 4.07/1.00  fof(f6,axiom,(
% 4.07/1.00    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 4.07/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.07/1.00  
% 4.07/1.00  fof(f64,plain,(
% 4.07/1.00    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 4.07/1.00    inference(cnf_transformation,[],[f6])).
% 4.07/1.00  
% 4.07/1.00  fof(f7,axiom,(
% 4.07/1.00    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 4.07/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.07/1.00  
% 4.07/1.00  fof(f65,plain,(
% 4.07/1.00    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 4.07/1.00    inference(cnf_transformation,[],[f7])).
% 4.07/1.00  
% 4.07/1.00  fof(f5,axiom,(
% 4.07/1.00    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 4.07/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.07/1.00  
% 4.07/1.00  fof(f35,plain,(
% 4.07/1.00    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 4.07/1.00    inference(nnf_transformation,[],[f5])).
% 4.07/1.00  
% 4.07/1.00  fof(f36,plain,(
% 4.07/1.00    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 4.07/1.00    inference(flattening,[],[f35])).
% 4.07/1.00  
% 4.07/1.00  fof(f63,plain,(
% 4.07/1.00    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 4.07/1.00    inference(cnf_transformation,[],[f36])).
% 4.07/1.00  
% 4.07/1.00  fof(f3,axiom,(
% 4.07/1.00    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 4.07/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.07/1.00  
% 4.07/1.00  fof(f18,plain,(
% 4.07/1.00    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X3] : ~r2_hidden(X3,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 4.07/1.00    inference(rectify,[],[f3])).
% 4.07/1.00  
% 4.07/1.00  fof(f20,plain,(
% 4.07/1.00    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 4.07/1.00    inference(ennf_transformation,[],[f18])).
% 4.07/1.00  
% 4.07/1.00  fof(f31,plain,(
% 4.07/1.00    ! [X1,X0] : (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) => r2_hidden(sK1(X0,X1),k3_xboole_0(X0,X1)))),
% 4.07/1.00    introduced(choice_axiom,[])).
% 4.07/1.00  
% 4.07/1.00  fof(f32,plain,(
% 4.07/1.00    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (r2_hidden(sK1(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 4.07/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f20,f31])).
% 4.07/1.00  
% 4.07/1.00  fof(f59,plain,(
% 4.07/1.00    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,k3_xboole_0(X0,X1))) )),
% 4.07/1.00    inference(cnf_transformation,[],[f32])).
% 4.07/1.00  
% 4.07/1.00  fof(f2,axiom,(
% 4.07/1.00    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 4.07/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.07/1.00  
% 4.07/1.00  fof(f30,plain,(
% 4.07/1.00    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) & (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)))),
% 4.07/1.00    inference(nnf_transformation,[],[f2])).
% 4.07/1.00  
% 4.07/1.00  fof(f57,plain,(
% 4.07/1.00    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) )),
% 4.07/1.00    inference(cnf_transformation,[],[f30])).
% 4.07/1.00  
% 4.07/1.00  fof(f87,plain,(
% 4.07/1.00    k1_xboole_0 != sK11 | k1_xboole_0 != k2_zfmisc_1(sK11,sK12)),
% 4.07/1.00    inference(cnf_transformation,[],[f52])).
% 4.07/1.00  
% 4.07/1.00  fof(f72,plain,(
% 4.07/1.00    ( ! [X2,X0,X8,X1] : (r2_hidden(sK7(X0,X1,X8),X0) | ~r2_hidden(X8,X2) | k2_zfmisc_1(X0,X1) != X2) )),
% 4.07/1.00    inference(cnf_transformation,[],[f46])).
% 4.07/1.00  
% 4.07/1.00  fof(f105,plain,(
% 4.07/1.00    ( ! [X0,X8,X1] : (r2_hidden(sK7(X0,X1,X8),X0) | ~r2_hidden(X8,k2_zfmisc_1(X0,X1))) )),
% 4.07/1.00    inference(equality_resolution,[],[f72])).
% 4.07/1.00  
% 4.07/1.00  fof(f88,plain,(
% 4.07/1.00    k1_xboole_0 != sK12 | k1_xboole_0 != k2_zfmisc_1(sK11,sK12)),
% 4.07/1.00    inference(cnf_transformation,[],[f52])).
% 4.07/1.00  
% 4.07/1.00  fof(f73,plain,(
% 4.07/1.00    ( ! [X2,X0,X8,X1] : (r2_hidden(sK8(X0,X1,X8),X1) | ~r2_hidden(X8,X2) | k2_zfmisc_1(X0,X1) != X2) )),
% 4.07/1.00    inference(cnf_transformation,[],[f46])).
% 4.07/1.00  
% 4.07/1.00  fof(f104,plain,(
% 4.07/1.00    ( ! [X0,X8,X1] : (r2_hidden(sK8(X0,X1,X8),X1) | ~r2_hidden(X8,k2_zfmisc_1(X0,X1))) )),
% 4.07/1.00    inference(equality_resolution,[],[f73])).
% 4.07/1.00  
% 4.07/1.00  cnf(c_21,plain,
% 4.07/1.00      ( r2_hidden(sK5(X0,X1,X2),X0)
% 4.07/1.00      | r2_hidden(sK4(X0,X1,X2),X2)
% 4.07/1.00      | k2_zfmisc_1(X0,X1) = X2 ),
% 4.07/1.00      inference(cnf_transformation,[],[f76]) ).
% 4.07/1.00  
% 4.07/1.00  cnf(c_1423,plain,
% 4.07/1.00      ( k2_zfmisc_1(X0,X1) = X2
% 4.07/1.00      | r2_hidden(sK5(X0,X1,X2),X0) = iProver_top
% 4.07/1.00      | r2_hidden(sK4(X0,X1,X2),X2) = iProver_top ),
% 4.07/1.00      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 4.07/1.00  
% 4.07/1.00  cnf(c_34,negated_conjecture,
% 4.07/1.00      ( k1_xboole_0 = k2_zfmisc_1(sK11,sK12)
% 4.07/1.00      | k1_xboole_0 = sK11
% 4.07/1.00      | k1_xboole_0 = sK12 ),
% 4.07/1.00      inference(cnf_transformation,[],[f86]) ).
% 4.07/1.00  
% 4.07/1.00  cnf(c_27,plain,
% 4.07/1.00      ( ~ r2_hidden(X0,X1)
% 4.07/1.00      | r2_hidden(sK10(X2,X3,X0),X3)
% 4.07/1.00      | ~ r1_tarski(X1,k2_zfmisc_1(X2,X3)) ),
% 4.07/1.00      inference(cnf_transformation,[],[f81]) ).
% 4.07/1.00  
% 4.07/1.00  cnf(c_1417,plain,
% 4.07/1.00      ( r2_hidden(X0,X1) != iProver_top
% 4.07/1.00      | r2_hidden(sK10(X2,X3,X0),X3) = iProver_top
% 4.07/1.00      | r1_tarski(X1,k2_zfmisc_1(X2,X3)) != iProver_top ),
% 4.07/1.00      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 4.07/1.00  
% 4.07/1.00  cnf(c_2339,plain,
% 4.07/1.00      ( sK11 = k1_xboole_0
% 4.07/1.00      | sK12 = k1_xboole_0
% 4.07/1.00      | r2_hidden(X0,X1) != iProver_top
% 4.07/1.00      | r2_hidden(sK10(sK11,sK12,X0),sK12) = iProver_top
% 4.07/1.00      | r1_tarski(X1,k1_xboole_0) != iProver_top ),
% 4.07/1.00      inference(superposition,[status(thm)],[c_34,c_1417]) ).
% 4.07/1.00  
% 4.07/1.00  cnf(c_5092,plain,
% 4.07/1.00      ( k2_zfmisc_1(X0,X1) = X2
% 4.07/1.00      | sK11 = k1_xboole_0
% 4.07/1.00      | sK12 = k1_xboole_0
% 4.07/1.00      | r2_hidden(sK10(sK11,sK12,sK4(X0,X1,X2)),sK12) = iProver_top
% 4.07/1.00      | r2_hidden(sK5(X0,X1,X2),X0) = iProver_top
% 4.07/1.00      | r1_tarski(X2,k1_xboole_0) != iProver_top ),
% 4.07/1.00      inference(superposition,[status(thm)],[c_1423,c_2339]) ).
% 4.07/1.00  
% 4.07/1.00  cnf(c_6886,plain,
% 4.07/1.00      ( k2_zfmisc_1(X0,X1) = X2
% 4.07/1.00      | sK11 = k1_xboole_0
% 4.07/1.00      | sK12 = k1_xboole_0
% 4.07/1.00      | r2_hidden(sK10(sK11,sK12,sK5(X0,X1,X2)),sK12) = iProver_top
% 4.07/1.00      | r2_hidden(sK10(sK11,sK12,sK4(X0,X1,X2)),sK12) = iProver_top
% 4.07/1.00      | r1_tarski(X0,k1_xboole_0) != iProver_top
% 4.07/1.00      | r1_tarski(X2,k1_xboole_0) != iProver_top ),
% 4.07/1.00      inference(superposition,[status(thm)],[c_5092,c_2339]) ).
% 4.07/1.00  
% 4.07/1.00  cnf(c_8,plain,
% 4.07/1.00      ( r2_hidden(sK2(X0),X0) | k1_xboole_0 = X0 ),
% 4.07/1.00      inference(cnf_transformation,[],[f60]) ).
% 4.07/1.00  
% 4.07/1.00  cnf(c_1435,plain,
% 4.07/1.00      ( k1_xboole_0 = X0 | r2_hidden(sK2(X0),X0) = iProver_top ),
% 4.07/1.00      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 4.07/1.00  
% 4.07/1.00  cnf(c_22,plain,
% 4.07/1.00      ( ~ r2_hidden(X0,X1)
% 4.07/1.00      | ~ r2_hidden(X2,X3)
% 4.07/1.00      | r2_hidden(k4_tarski(X2,X0),k2_zfmisc_1(X3,X1)) ),
% 4.07/1.00      inference(cnf_transformation,[],[f102]) ).
% 4.07/1.00  
% 4.07/1.00  cnf(c_1422,plain,
% 4.07/1.00      ( r2_hidden(X0,X1) != iProver_top
% 4.07/1.00      | r2_hidden(X2,X3) != iProver_top
% 4.07/1.00      | r2_hidden(k4_tarski(X2,X0),k2_zfmisc_1(X3,X1)) = iProver_top ),
% 4.07/1.00      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 4.07/1.00  
% 4.07/1.00  cnf(c_4526,plain,
% 4.07/1.00      ( sK11 = k1_xboole_0
% 4.07/1.00      | sK12 = k1_xboole_0
% 4.07/1.00      | r2_hidden(X0,sK11) != iProver_top
% 4.07/1.00      | r2_hidden(X1,sK12) != iProver_top
% 4.07/1.00      | r2_hidden(k4_tarski(X0,X1),k1_xboole_0) = iProver_top ),
% 4.07/1.00      inference(superposition,[status(thm)],[c_34,c_1422]) ).
% 4.07/1.00  
% 4.07/1.00  cnf(c_12,plain,
% 4.07/1.00      ( r1_tarski(k3_xboole_0(X0,X1),X0) ),
% 4.07/1.00      inference(cnf_transformation,[],[f64]) ).
% 4.07/1.00  
% 4.07/1.00  cnf(c_1432,plain,
% 4.07/1.00      ( r1_tarski(k3_xboole_0(X0,X1),X0) = iProver_top ),
% 4.07/1.00      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 4.07/1.00  
% 4.07/1.00  cnf(c_13,plain,
% 4.07/1.00      ( r1_tarski(k1_xboole_0,X0) ),
% 4.07/1.00      inference(cnf_transformation,[],[f65]) ).
% 4.07/1.00  
% 4.07/1.00  cnf(c_1431,plain,
% 4.07/1.00      ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
% 4.07/1.00      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 4.07/1.00  
% 4.07/1.00  cnf(c_9,plain,
% 4.07/1.00      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X1 = X0 ),
% 4.07/1.00      inference(cnf_transformation,[],[f63]) ).
% 4.07/1.00  
% 4.07/1.00  cnf(c_1434,plain,
% 4.07/1.00      ( X0 = X1
% 4.07/1.00      | r1_tarski(X1,X0) != iProver_top
% 4.07/1.00      | r1_tarski(X0,X1) != iProver_top ),
% 4.07/1.00      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 4.07/1.00  
% 4.07/1.00  cnf(c_3358,plain,
% 4.07/1.00      ( k1_xboole_0 = X0 | r1_tarski(X0,k1_xboole_0) != iProver_top ),
% 4.07/1.00      inference(superposition,[status(thm)],[c_1431,c_1434]) ).
% 4.07/1.00  
% 4.07/1.00  cnf(c_5459,plain,
% 4.07/1.00      ( k3_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
% 4.07/1.00      inference(superposition,[status(thm)],[c_1432,c_3358]) ).
% 4.07/1.00  
% 4.07/1.00  cnf(c_6,plain,
% 4.07/1.00      ( ~ r1_xboole_0(X0,X1) | ~ r2_hidden(X2,k3_xboole_0(X0,X1)) ),
% 4.07/1.00      inference(cnf_transformation,[],[f59]) ).
% 4.07/1.00  
% 4.07/1.00  cnf(c_1437,plain,
% 4.07/1.00      ( r1_xboole_0(X0,X1) != iProver_top
% 4.07/1.00      | r2_hidden(X2,k3_xboole_0(X0,X1)) != iProver_top ),
% 4.07/1.00      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 4.07/1.00  
% 4.07/1.00  cnf(c_6186,plain,
% 4.07/1.00      ( r1_xboole_0(k1_xboole_0,X0) != iProver_top
% 4.07/1.00      | r2_hidden(X1,k1_xboole_0) != iProver_top ),
% 4.07/1.00      inference(superposition,[status(thm)],[c_5459,c_1437]) ).
% 4.07/1.00  
% 4.07/1.00  cnf(c_4,plain,
% 4.07/1.00      ( r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0 ),
% 4.07/1.00      inference(cnf_transformation,[],[f57]) ).
% 4.07/1.00  
% 4.07/1.00  cnf(c_1439,plain,
% 4.07/1.00      ( k3_xboole_0(X0,X1) != k1_xboole_0 | r1_xboole_0(X0,X1) = iProver_top ),
% 4.07/1.00      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 4.07/1.00  
% 4.07/1.00  cnf(c_6188,plain,
% 4.07/1.00      ( r1_xboole_0(k1_xboole_0,X0) = iProver_top ),
% 4.07/1.00      inference(superposition,[status(thm)],[c_5459,c_1439]) ).
% 4.07/1.00  
% 4.07/1.00  cnf(c_7505,plain,
% 4.07/1.00      ( r2_hidden(X1,k1_xboole_0) != iProver_top ),
% 4.07/1.00      inference(global_propositional_subsumption,[status(thm)],[c_6186,c_6188]) ).
% 4.07/1.00  
% 4.07/1.00  cnf(c_7506,plain,
% 4.07/1.00      ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
% 4.07/1.00      inference(renaming,[status(thm)],[c_7505]) ).
% 4.07/1.00  
% 4.07/1.00  cnf(c_7527,plain,
% 4.07/1.00      ( sK11 = k1_xboole_0
% 4.07/1.00      | sK12 = k1_xboole_0
% 4.07/1.00      | r2_hidden(X0,sK11) != iProver_top
% 4.07/1.00      | r2_hidden(X1,sK12) != iProver_top ),
% 4.07/1.00      inference(superposition,[status(thm)],[c_4526,c_7506]) ).
% 4.07/1.00  
% 4.07/1.00  cnf(c_7929,plain,
% 4.07/1.00      ( sK11 = k1_xboole_0
% 4.07/1.00      | sK12 = k1_xboole_0
% 4.07/1.00      | r2_hidden(X0,sK12) != iProver_top ),
% 4.07/1.00      inference(superposition,[status(thm)],[c_1435,c_7527]) ).
% 4.07/1.00  
% 4.07/1.00  cnf(c_10636,plain,
% 4.07/1.00      ( sK11 = k1_xboole_0 | sK12 = k1_xboole_0 ),
% 4.07/1.00      inference(superposition,[status(thm)],[c_1435,c_7929]) ).
% 4.07/1.00  
% 4.07/1.00  cnf(c_33,negated_conjecture,
% 4.07/1.00      ( k1_xboole_0 != k2_zfmisc_1(sK11,sK12) | k1_xboole_0 != sK11 ),
% 4.07/1.00      inference(cnf_transformation,[],[f87]) ).
% 4.07/1.00  
% 4.07/1.00  cnf(c_10887,plain,
% 4.07/1.00      ( k2_zfmisc_1(k1_xboole_0,sK12) != k1_xboole_0
% 4.07/1.00      | sK11 != k1_xboole_0
% 4.07/1.00      | sK12 = k1_xboole_0 ),
% 4.07/1.00      inference(superposition,[status(thm)],[c_10636,c_33]) ).
% 4.07/1.00  
% 4.07/1.00  cnf(c_25,plain,
% 4.07/1.00      ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) | r2_hidden(sK7(X1,X2,X0),X1) ),
% 4.07/1.00      inference(cnf_transformation,[],[f105]) ).
% 4.07/1.00  
% 4.07/1.00  cnf(c_1419,plain,
% 4.07/1.00      ( r2_hidden(X0,k2_zfmisc_1(X1,X2)) != iProver_top
% 4.07/1.00      | r2_hidden(sK7(X1,X2,X0),X1) = iProver_top ),
% 4.07/1.00      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 4.07/1.00  
% 4.07/1.00  cnf(c_7524,plain,
% 4.07/1.00      ( r2_hidden(X0,k2_zfmisc_1(k1_xboole_0,X1)) != iProver_top ),
% 4.07/1.00      inference(superposition,[status(thm)],[c_1419,c_7506]) ).
% 4.07/1.00  
% 4.07/1.00  cnf(c_8611,plain,
% 4.07/1.00      ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
% 4.07/1.00      inference(superposition,[status(thm)],[c_1435,c_7524]) ).
% 4.07/1.00  
% 4.07/1.00  cnf(c_10889,plain,
% 4.07/1.00      ( sK11 != k1_xboole_0 | sK12 = k1_xboole_0 | k1_xboole_0 != k1_xboole_0 ),
% 4.07/1.00      inference(demodulation,[status(thm)],[c_10887,c_8611]) ).
% 4.07/1.00  
% 4.07/1.00  cnf(c_10890,plain,
% 4.07/1.00      ( sK11 != k1_xboole_0 | sK12 = k1_xboole_0 ),
% 4.07/1.00      inference(equality_resolution_simp,[status(thm)],[c_10889]) ).
% 4.07/1.00  
% 4.07/1.00  cnf(c_11087,plain,
% 4.07/1.00      ( sK12 = k1_xboole_0 ),
% 4.07/1.00      inference(global_propositional_subsumption,
% 4.07/1.00                [status(thm)],
% 4.07/1.00                [c_6886,c_10636,c_10890]) ).
% 4.07/1.00  
% 4.07/1.00  cnf(c_32,negated_conjecture,
% 4.07/1.00      ( k1_xboole_0 != k2_zfmisc_1(sK11,sK12) | k1_xboole_0 != sK12 ),
% 4.07/1.00      inference(cnf_transformation,[],[f88]) ).
% 4.07/1.00  
% 4.07/1.00  cnf(c_11091,plain,
% 4.07/1.00      ( k2_zfmisc_1(sK11,k1_xboole_0) != k1_xboole_0
% 4.07/1.00      | k1_xboole_0 != k1_xboole_0 ),
% 4.07/1.00      inference(demodulation,[status(thm)],[c_11087,c_32]) ).
% 4.07/1.00  
% 4.07/1.00  cnf(c_11092,plain,
% 4.07/1.00      ( k2_zfmisc_1(sK11,k1_xboole_0) != k1_xboole_0 ),
% 4.07/1.00      inference(equality_resolution_simp,[status(thm)],[c_11091]) ).
% 4.07/1.00  
% 4.07/1.00  cnf(c_24,plain,
% 4.07/1.00      ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) | r2_hidden(sK8(X1,X2,X0),X2) ),
% 4.07/1.00      inference(cnf_transformation,[],[f104]) ).
% 4.07/1.00  
% 4.07/1.00  cnf(c_1420,plain,
% 4.07/1.00      ( r2_hidden(X0,k2_zfmisc_1(X1,X2)) != iProver_top
% 4.07/1.00      | r2_hidden(sK8(X1,X2,X0),X2) = iProver_top ),
% 4.07/1.00      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 4.07/1.00  
% 4.07/1.00  cnf(c_7523,plain,
% 4.07/1.00      ( r2_hidden(X0,k2_zfmisc_1(X1,k1_xboole_0)) != iProver_top ),
% 4.07/1.00      inference(superposition,[status(thm)],[c_1420,c_7506]) ).
% 4.07/1.00  
% 4.07/1.00  cnf(c_7754,plain,
% 4.07/1.00      ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
% 4.07/1.00      inference(superposition,[status(thm)],[c_1435,c_7523]) ).
% 4.07/1.00  
% 4.07/1.00  cnf(c_11093,plain,
% 4.07/1.00      ( k1_xboole_0 != k1_xboole_0 ),
% 4.07/1.00      inference(demodulation,[status(thm)],[c_11092,c_7754]) ).
% 4.07/1.00  
% 4.07/1.00  cnf(c_11094,plain,
% 4.07/1.00      ( $false ),
% 4.07/1.00      inference(equality_resolution_simp,[status(thm)],[c_11093]) ).
% 4.07/1.00  
% 4.07/1.00  
% 4.07/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 4.07/1.00  
% 4.07/1.00  ------                               Statistics
% 4.07/1.00  
% 4.07/1.00  ------ General
% 4.07/1.00  
% 4.07/1.00  abstr_ref_over_cycles:                  0
% 4.07/1.00  abstr_ref_under_cycles:                 0
% 4.07/1.00  gc_basic_clause_elim:                   0
% 4.07/1.00  forced_gc_time:                         0
% 4.07/1.00  parsing_time:                           0.008
% 4.07/1.00  unif_index_cands_time:                  0.
% 4.07/1.00  unif_index_add_time:                    0.
% 4.07/1.00  orderings_time:                         0.
% 4.07/1.00  out_proof_time:                         0.009
% 4.07/1.00  total_time:                             0.4
% 4.07/1.00  num_of_symbols:                         53
% 4.07/1.00  num_of_terms:                           14449
% 4.07/1.00  
% 4.07/1.00  ------ Preprocessing
% 4.07/1.00  
% 4.07/1.00  num_of_splits:                          0
% 4.07/1.00  num_of_split_atoms:                     0
% 4.07/1.00  num_of_reused_defs:                     0
% 4.07/1.00  num_eq_ax_congr_red:                    99
% 4.07/1.00  num_of_sem_filtered_clauses:            1
% 4.07/1.00  num_of_subtypes:                        0
% 4.07/1.00  monotx_restored_types:                  0
% 4.07/1.00  sat_num_of_epr_types:                   0
% 4.07/1.00  sat_num_of_non_cyclic_types:            0
% 4.07/1.00  sat_guarded_non_collapsed_types:        0
% 4.07/1.00  num_pure_diseq_elim:                    0
% 4.07/1.00  simp_replaced_by:                       0
% 4.07/1.00  res_preprocessed:                       153
% 4.07/1.00  prep_upred:                             0
% 4.07/1.00  prep_unflattend:                        8
% 4.07/1.00  smt_new_axioms:                         0
% 4.07/1.00  pred_elim_cands:                        3
% 4.07/1.00  pred_elim:                              0
% 4.07/1.00  pred_elim_cl:                           0
% 4.07/1.00  pred_elim_cycles:                       2
% 4.07/1.00  merged_defs:                            8
% 4.07/1.00  merged_defs_ncl:                        0
% 4.07/1.00  bin_hyper_res:                          8
% 4.07/1.00  prep_cycles:                            4
% 4.07/1.00  pred_elim_time:                         0.003
% 4.07/1.00  splitting_time:                         0.
% 4.07/1.00  sem_filter_time:                        0.
% 4.07/1.00  monotx_time:                            0.
% 4.07/1.00  subtype_inf_time:                       0.
% 4.07/1.00  
% 4.07/1.00  ------ Problem properties
% 4.07/1.00  
% 4.07/1.00  clauses:                                34
% 4.07/1.00  conjectures:                            3
% 4.07/1.00  epr:                                    4
% 4.07/1.00  horn:                                   25
% 4.07/1.00  ground:                                 3
% 4.07/1.00  unary:                                  6
% 4.07/1.00  binary:                                 14
% 4.07/1.00  lits:                                   78
% 4.07/1.00  lits_eq:                                27
% 4.07/1.00  fd_pure:                                0
% 4.07/1.00  fd_pseudo:                              0
% 4.07/1.00  fd_cond:                                1
% 4.07/1.00  fd_pseudo_cond:                         7
% 4.07/1.00  ac_symbols:                             0
% 4.07/1.00  
% 4.07/1.00  ------ Propositional Solver
% 4.07/1.00  
% 4.07/1.00  prop_solver_calls:                      31
% 4.07/1.00  prop_fast_solver_calls:                 1323
% 4.07/1.00  smt_solver_calls:                       0
% 4.07/1.00  smt_fast_solver_calls:                  0
% 4.07/1.00  prop_num_of_clauses:                    5387
% 4.07/1.00  prop_preprocess_simplified:             12258
% 4.07/1.00  prop_fo_subsumed:                       79
% 4.07/1.00  prop_solver_time:                       0.
% 4.07/1.00  smt_solver_time:                        0.
% 4.07/1.00  smt_fast_solver_time:                   0.
% 4.07/1.00  prop_fast_solver_time:                  0.
% 4.07/1.00  prop_unsat_core_time:                   0.
% 4.07/1.00  
% 4.07/1.00  ------ QBF
% 4.07/1.00  
% 4.07/1.00  qbf_q_res:                              0
% 4.07/1.00  qbf_num_tautologies:                    0
% 4.07/1.00  qbf_prep_cycles:                        0
% 4.07/1.00  
% 4.07/1.00  ------ BMC1
% 4.07/1.00  
% 4.07/1.00  bmc1_current_bound:                     -1
% 4.07/1.00  bmc1_last_solved_bound:                 -1
% 4.07/1.00  bmc1_unsat_core_size:                   -1
% 4.07/1.00  bmc1_unsat_core_parents_size:           -1
% 4.07/1.00  bmc1_merge_next_fun:                    0
% 4.07/1.00  bmc1_unsat_core_clauses_time:           0.
% 4.07/1.00  
% 4.07/1.00  ------ Instantiation
% 4.07/1.00  
% 4.07/1.00  inst_num_of_clauses:                    1148
% 4.07/1.00  inst_num_in_passive:                    483
% 4.07/1.00  inst_num_in_active:                     434
% 4.07/1.00  inst_num_in_unprocessed:                231
% 4.07/1.00  inst_num_of_loops:                      590
% 4.07/1.00  inst_num_of_learning_restarts:          0
% 4.07/1.00  inst_num_moves_active_passive:          154
% 4.07/1.00  inst_lit_activity:                      0
% 4.07/1.00  inst_lit_activity_moves:                0
% 4.07/1.00  inst_num_tautologies:                   0
% 4.07/1.00  inst_num_prop_implied:                  0
% 4.07/1.00  inst_num_existing_simplified:           0
% 4.07/1.00  inst_num_eq_res_simplified:             0
% 4.07/1.00  inst_num_child_elim:                    0
% 4.07/1.00  inst_num_of_dismatching_blockings:      586
% 4.07/1.00  inst_num_of_non_proper_insts:           1383
% 4.07/1.00  inst_num_of_duplicates:                 0
% 4.07/1.00  inst_inst_num_from_inst_to_res:         0
% 4.07/1.00  inst_dismatching_checking_time:         0.
% 4.07/1.00  
% 4.07/1.00  ------ Resolution
% 4.07/1.00  
% 4.07/1.00  res_num_of_clauses:                     0
% 4.07/1.00  res_num_in_passive:                     0
% 4.07/1.00  res_num_in_active:                      0
% 4.07/1.00  res_num_of_loops:                       157
% 4.07/1.00  res_forward_subset_subsumed:            52
% 4.07/1.00  res_backward_subset_subsumed:           0
% 4.07/1.00  res_forward_subsumed:                   0
% 4.07/1.00  res_backward_subsumed:                  0
% 4.07/1.00  res_forward_subsumption_resolution:     0
% 4.07/1.00  res_backward_subsumption_resolution:    0
% 4.07/1.00  res_clause_to_clause_subsumption:       2267
% 4.07/1.00  res_orphan_elimination:                 0
% 4.07/1.00  res_tautology_del:                      97
% 4.07/1.00  res_num_eq_res_simplified:              0
% 4.07/1.00  res_num_sel_changes:                    0
% 4.07/1.00  res_moves_from_active_to_pass:          0
% 4.07/1.00  
% 4.07/1.00  ------ Superposition
% 4.07/1.00  
% 4.07/1.00  sup_time_total:                         0.
% 4.07/1.00  sup_time_generating:                    0.
% 4.07/1.00  sup_time_sim_full:                      0.
% 4.07/1.00  sup_time_sim_immed:                     0.
% 4.07/1.00  
% 4.07/1.00  sup_num_of_clauses:                     485
% 4.07/1.00  sup_num_in_active:                      54
% 4.07/1.00  sup_num_in_passive:                     431
% 4.07/1.00  sup_num_of_loops:                       116
% 4.07/1.00  sup_fw_superposition:                   390
% 4.07/1.00  sup_bw_superposition:                   444
% 4.07/1.00  sup_immediate_simplified:               225
% 4.07/1.00  sup_given_eliminated:                   3
% 4.07/1.00  comparisons_done:                       0
% 4.07/1.00  comparisons_avoided:                    222
% 4.07/1.00  
% 4.07/1.00  ------ Simplifications
% 4.07/1.00  
% 4.07/1.00  
% 4.07/1.00  sim_fw_subset_subsumed:                 42
% 4.07/1.00  sim_bw_subset_subsumed:                 71
% 4.07/1.00  sim_fw_subsumed:                        107
% 4.07/1.00  sim_bw_subsumed:                        75
% 4.07/1.00  sim_fw_subsumption_res:                 0
% 4.07/1.00  sim_bw_subsumption_res:                 0
% 4.07/1.00  sim_tautology_del:                      7
% 4.07/1.00  sim_eq_tautology_del:                   13
% 4.07/1.00  sim_eq_res_simp:                        2
% 4.07/1.00  sim_fw_demodulated:                     49
% 4.07/1.00  sim_bw_demodulated:                     34
% 4.07/1.00  sim_light_normalised:                   1
% 4.07/1.00  sim_joinable_taut:                      0
% 4.07/1.00  sim_joinable_simp:                      0
% 4.07/1.00  sim_ac_normalised:                      0
% 4.07/1.00  sim_smt_subsumption:                    0
% 4.07/1.00  
%------------------------------------------------------------------------------
