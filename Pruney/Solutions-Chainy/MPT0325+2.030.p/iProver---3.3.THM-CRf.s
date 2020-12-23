%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:37:50 EST 2020

% Result     : Theorem 3.10s
% Output     : CNFRefutation 3.10s
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
fof(f7,axiom,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
    <=> ( r2_hidden(X1,X3)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
        | ~ r2_hidden(X1,X3)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X3)
          & r2_hidden(X0,X2) )
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ) ),
    inference(nnf_transformation,[],[f7])).

fof(f36,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
        | ~ r2_hidden(X1,X3)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X3)
          & r2_hidden(X0,X2) )
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ) ),
    inference(flattening,[],[f35])).

fof(f60,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X0,X2)
      | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ),
    inference(cnf_transformation,[],[f36])).

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

fof(f16,plain,(
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

fof(f17,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f16])).

fof(f18,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK0(X0,X1),X1)
          & r2_hidden(sK0(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f17,f18])).

fof(f39,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f8,conjecture,(
    ! [X0,X1,X2,X3] :
      ( r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3))
     => ( ( r1_tarski(X1,X3)
          & r1_tarski(X0,X2) )
        | k1_xboole_0 = k2_zfmisc_1(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f9,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3))
       => ( ( r1_tarski(X1,X3)
            & r1_tarski(X0,X2) )
          | k1_xboole_0 = k2_zfmisc_1(X0,X1) ) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f14,plain,(
    ? [X0,X1,X2,X3] :
      ( ( ~ r1_tarski(X1,X3)
        | ~ r1_tarski(X0,X2) )
      & k1_xboole_0 != k2_zfmisc_1(X0,X1)
      & r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f15,plain,(
    ? [X0,X1,X2,X3] :
      ( ( ~ r1_tarski(X1,X3)
        | ~ r1_tarski(X0,X2) )
      & k1_xboole_0 != k2_zfmisc_1(X0,X1)
      & r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)) ) ),
    inference(flattening,[],[f14])).

fof(f37,plain,
    ( ? [X0,X1,X2,X3] :
        ( ( ~ r1_tarski(X1,X3)
          | ~ r1_tarski(X0,X2) )
        & k1_xboole_0 != k2_zfmisc_1(X0,X1)
        & r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)) )
   => ( ( ~ r1_tarski(sK10,sK12)
        | ~ r1_tarski(sK9,sK11) )
      & k1_xboole_0 != k2_zfmisc_1(sK9,sK10)
      & r1_tarski(k2_zfmisc_1(sK9,sK10),k2_zfmisc_1(sK11,sK12)) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,
    ( ( ~ r1_tarski(sK10,sK12)
      | ~ r1_tarski(sK9,sK11) )
    & k1_xboole_0 != k2_zfmisc_1(sK9,sK10)
    & r1_tarski(k2_zfmisc_1(sK9,sK10),k2_zfmisc_1(sK11,sK12)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK9,sK10,sK11,sK12])],[f15,f37])).

fof(f63,plain,(
    r1_tarski(k2_zfmisc_1(sK9,sK10),k2_zfmisc_1(sK11,sK12)) ),
    inference(cnf_transformation,[],[f38])).

fof(f62,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
      | ~ r2_hidden(X1,X3)
      | ~ r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( k2_zfmisc_1(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ? [X4,X5] :
              ( k4_tarski(X4,X5) = X3
              & r2_hidden(X5,X1)
              & r2_hidden(X4,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
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

fof(f30,plain,(
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
    inference(rectify,[],[f29])).

fof(f33,plain,(
    ! [X8,X1,X0] :
      ( ? [X11,X12] :
          ( k4_tarski(X11,X12) = X8
          & r2_hidden(X12,X1)
          & r2_hidden(X11,X0) )
     => ( k4_tarski(sK7(X0,X1,X8),sK8(X0,X1,X8)) = X8
        & r2_hidden(sK8(X0,X1,X8),X1)
        & r2_hidden(sK7(X0,X1,X8),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X6,X7] :
          ( k4_tarski(X6,X7) = X3
          & r2_hidden(X7,X1)
          & r2_hidden(X6,X0) )
     => ( k4_tarski(sK5(X0,X1,X2),sK6(X0,X1,X2)) = X3
        & r2_hidden(sK6(X0,X1,X2),X1)
        & r2_hidden(sK5(X0,X1,X2),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
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

fof(f34,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6,sK7,sK8])],[f30,f33,f32,f31])).

fof(f53,plain,(
    ! [X2,X0,X8,X1] :
      ( r2_hidden(sK8(X0,X1,X8),X1)
      | ~ r2_hidden(X8,X2)
      | k2_zfmisc_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f34])).

fof(f72,plain,(
    ! [X0,X8,X1] :
      ( r2_hidden(sK8(X0,X1,X8),X1)
      | ~ r2_hidden(X8,k2_zfmisc_1(X0,X1)) ) ),
    inference(equality_resolution,[],[f53])).

fof(f4,axiom,(
    ! [X0] :
      ~ ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f4])).

fof(f27,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK3(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,(
    ! [X0] :
      ( r2_hidden(sK3(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f13,f27])).

fof(f50,plain,(
    ! [X0] :
      ( r2_hidden(sK3(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f28])).

fof(f64,plain,(
    k1_xboole_0 != k2_zfmisc_1(sK9,sK10) ),
    inference(cnf_transformation,[],[f38])).

fof(f41,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK0(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f40,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK0(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f61,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X1,X3)
      | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f52,plain,(
    ! [X2,X0,X8,X1] :
      ( r2_hidden(sK7(X0,X1,X8),X0)
      | ~ r2_hidden(X8,X2)
      | k2_zfmisc_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f34])).

fof(f73,plain,(
    ! [X0,X8,X1] :
      ( r2_hidden(sK7(X0,X1,X8),X0)
      | ~ r2_hidden(X8,k2_zfmisc_1(X0,X1)) ) ),
    inference(equality_resolution,[],[f52])).

fof(f65,plain,
    ( ~ r1_tarski(sK10,sK12)
    | ~ r1_tarski(sK9,sK11) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_23,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(k4_tarski(X0,X2),k2_zfmisc_1(X1,X3)) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_2,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | ~ r1_tarski(X1,X2) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_26,negated_conjecture,
    ( r1_tarski(k2_zfmisc_1(sK9,sK10),k2_zfmisc_1(sK11,sK12)) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_1463,plain,
    ( r2_hidden(X0,k2_zfmisc_1(sK11,sK12))
    | ~ r2_hidden(X0,k2_zfmisc_1(sK9,sK10)) ),
    inference(resolution,[status(thm)],[c_2,c_26])).

cnf(c_2034,plain,
    ( r2_hidden(X0,sK11)
    | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(sK9,sK10)) ),
    inference(resolution,[status(thm)],[c_23,c_1463])).

cnf(c_21,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X2,X3)
    | r2_hidden(k4_tarski(X2,X0),k2_zfmisc_1(X3,X1)) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_3606,plain,
    ( r2_hidden(X0,sK11)
    | ~ r2_hidden(X0,sK9)
    | ~ r2_hidden(X1,sK10) ),
    inference(resolution,[status(thm)],[c_2034,c_21])).

cnf(c_19,plain,
    ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
    | r2_hidden(sK8(X1,X2,X0),X2) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_3971,plain,
    ( ~ r2_hidden(X0,k2_zfmisc_1(X1,sK10))
    | r2_hidden(X2,sK11)
    | ~ r2_hidden(X2,sK9) ),
    inference(resolution,[status(thm)],[c_3606,c_19])).

cnf(c_11,plain,
    ( r2_hidden(sK3(X0),X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f50])).

cnf(c_25,negated_conjecture,
    ( k1_xboole_0 != k2_zfmisc_1(sK9,sK10) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_1168,plain,
    ( r2_hidden(sK3(k2_zfmisc_1(sK9,sK10)),k2_zfmisc_1(sK9,sK10)) ),
    inference(resolution,[status(thm)],[c_11,c_25])).

cnf(c_7090,plain,
    ( r2_hidden(X0,sK11)
    | ~ r2_hidden(X0,sK9) ),
    inference(resolution,[status(thm)],[c_3971,c_1168])).

cnf(c_0,plain,
    ( ~ r2_hidden(sK0(X0,X1),X1)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_7100,plain,
    ( ~ r2_hidden(sK0(X0,sK11),sK9)
    | r1_tarski(X0,sK11) ),
    inference(resolution,[status(thm)],[c_7090,c_0])).

cnf(c_1,plain,
    ( r2_hidden(sK0(X0,X1),X0)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_7110,plain,
    ( r1_tarski(sK9,sK11) ),
    inference(resolution,[status(thm)],[c_7100,c_1])).

cnf(c_22,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(k4_tarski(X2,X0),k2_zfmisc_1(X3,X1)) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_1838,plain,
    ( r2_hidden(X0,sK12)
    | ~ r2_hidden(k4_tarski(X1,X0),k2_zfmisc_1(sK9,sK10)) ),
    inference(resolution,[status(thm)],[c_22,c_1463])).

cnf(c_3597,plain,
    ( ~ r2_hidden(X0,sK9)
    | r2_hidden(X1,sK12)
    | ~ r2_hidden(X1,sK10) ),
    inference(resolution,[status(thm)],[c_1838,c_21])).

cnf(c_20,plain,
    ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
    | r2_hidden(sK7(X1,X2,X0),X1) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_3951,plain,
    ( ~ r2_hidden(X0,k2_zfmisc_1(sK9,X1))
    | r2_hidden(X2,sK12)
    | ~ r2_hidden(X2,sK10) ),
    inference(resolution,[status(thm)],[c_3597,c_20])).

cnf(c_5004,plain,
    ( r2_hidden(X0,sK12)
    | ~ r2_hidden(X0,sK10) ),
    inference(resolution,[status(thm)],[c_3951,c_1168])).

cnf(c_5525,plain,
    ( ~ r2_hidden(sK0(X0,sK12),sK10)
    | r1_tarski(X0,sK12) ),
    inference(resolution,[status(thm)],[c_5004,c_0])).

cnf(c_5535,plain,
    ( r1_tarski(sK10,sK12) ),
    inference(resolution,[status(thm)],[c_5525,c_1])).

cnf(c_24,negated_conjecture,
    ( ~ r1_tarski(sK9,sK11)
    | ~ r1_tarski(sK10,sK12) ),
    inference(cnf_transformation,[],[f65])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_7110,c_5535,c_24])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n022.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 20:28:26 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 3.10/0.99  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.10/0.99  
% 3.10/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.10/0.99  
% 3.10/0.99  ------  iProver source info
% 3.10/0.99  
% 3.10/0.99  git: date: 2020-06-30 10:37:57 +0100
% 3.10/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.10/0.99  git: non_committed_changes: false
% 3.10/0.99  git: last_make_outside_of_git: false
% 3.10/0.99  
% 3.10/0.99  ------ 
% 3.10/0.99  ------ Parsing...
% 3.10/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.10/0.99  
% 3.10/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 3.10/0.99  
% 3.10/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.10/0.99  
% 3.10/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.10/0.99  ------ Proving...
% 3.10/0.99  ------ Problem Properties 
% 3.10/0.99  
% 3.10/0.99  
% 3.10/0.99  clauses                                 25
% 3.10/0.99  conjectures                             3
% 3.10/0.99  EPR                                     2
% 3.10/0.99  Horn                                    18
% 3.10/0.99  unary                                   3
% 3.10/0.99  binary                                  12
% 3.10/0.99  lits                                    60
% 3.10/0.99  lits eq                                 12
% 3.10/0.99  fd_pure                                 0
% 3.10/0.99  fd_pseudo                               0
% 3.10/0.99  fd_cond                                 1
% 3.10/0.99  fd_pseudo_cond                          7
% 3.10/0.99  AC symbols                              0
% 3.10/0.99  
% 3.10/0.99  ------ Input Options Time Limit: Unbounded
% 3.10/0.99  
% 3.10/0.99  
% 3.10/0.99  ------ 
% 3.10/0.99  Current options:
% 3.10/0.99  ------ 
% 3.10/0.99  
% 3.10/0.99  
% 3.10/0.99  
% 3.10/0.99  
% 3.10/0.99  ------ Proving...
% 3.10/0.99  
% 3.10/0.99  
% 3.10/0.99  % SZS status Theorem for theBenchmark.p
% 3.10/0.99  
% 3.10/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 3.10/0.99  
% 3.10/0.99  fof(f7,axiom,(
% 3.10/0.99    ! [X0,X1,X2,X3] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) <=> (r2_hidden(X1,X3) & r2_hidden(X0,X2)))),
% 3.10/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.10/0.99  
% 3.10/0.99  fof(f35,plain,(
% 3.10/0.99    ! [X0,X1,X2,X3] : ((r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | (~r2_hidden(X1,X3) | ~r2_hidden(X0,X2))) & ((r2_hidden(X1,X3) & r2_hidden(X0,X2)) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))))),
% 3.10/0.99    inference(nnf_transformation,[],[f7])).
% 3.10/0.99  
% 3.10/0.99  fof(f36,plain,(
% 3.10/0.99    ! [X0,X1,X2,X3] : ((r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | ~r2_hidden(X1,X3) | ~r2_hidden(X0,X2)) & ((r2_hidden(X1,X3) & r2_hidden(X0,X2)) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))))),
% 3.10/0.99    inference(flattening,[],[f35])).
% 3.10/0.99  
% 3.10/0.99  fof(f60,plain,(
% 3.10/0.99    ( ! [X2,X0,X3,X1] : (r2_hidden(X0,X2) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))) )),
% 3.10/0.99    inference(cnf_transformation,[],[f36])).
% 3.10/0.99  
% 3.10/0.99  fof(f1,axiom,(
% 3.10/0.99    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 3.10/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.10/0.99  
% 3.10/0.99  fof(f11,plain,(
% 3.10/0.99    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 3.10/0.99    inference(ennf_transformation,[],[f1])).
% 3.10/0.99  
% 3.10/0.99  fof(f16,plain,(
% 3.10/0.99    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 3.10/0.99    inference(nnf_transformation,[],[f11])).
% 3.10/0.99  
% 3.10/0.99  fof(f17,plain,(
% 3.10/0.99    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 3.10/0.99    inference(rectify,[],[f16])).
% 3.10/0.99  
% 3.10/0.99  fof(f18,plain,(
% 3.10/0.99    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 3.10/0.99    introduced(choice_axiom,[])).
% 3.10/0.99  
% 3.10/0.99  fof(f19,plain,(
% 3.10/0.99    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 3.10/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f17,f18])).
% 3.10/0.99  
% 3.10/0.99  fof(f39,plain,(
% 3.10/0.99    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,X1)) )),
% 3.10/0.99    inference(cnf_transformation,[],[f19])).
% 3.10/0.99  
% 3.10/0.99  fof(f8,conjecture,(
% 3.10/0.99    ! [X0,X1,X2,X3] : (r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)) => ((r1_tarski(X1,X3) & r1_tarski(X0,X2)) | k1_xboole_0 = k2_zfmisc_1(X0,X1)))),
% 3.10/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.10/0.99  
% 3.10/0.99  fof(f9,negated_conjecture,(
% 3.10/0.99    ~! [X0,X1,X2,X3] : (r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)) => ((r1_tarski(X1,X3) & r1_tarski(X0,X2)) | k1_xboole_0 = k2_zfmisc_1(X0,X1)))),
% 3.10/0.99    inference(negated_conjecture,[],[f8])).
% 3.10/0.99  
% 3.10/0.99  fof(f14,plain,(
% 3.10/0.99    ? [X0,X1,X2,X3] : (((~r1_tarski(X1,X3) | ~r1_tarski(X0,X2)) & k1_xboole_0 != k2_zfmisc_1(X0,X1)) & r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)))),
% 3.10/0.99    inference(ennf_transformation,[],[f9])).
% 3.10/0.99  
% 3.10/0.99  fof(f15,plain,(
% 3.10/0.99    ? [X0,X1,X2,X3] : ((~r1_tarski(X1,X3) | ~r1_tarski(X0,X2)) & k1_xboole_0 != k2_zfmisc_1(X0,X1) & r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)))),
% 3.10/0.99    inference(flattening,[],[f14])).
% 3.10/0.99  
% 3.10/0.99  fof(f37,plain,(
% 3.10/0.99    ? [X0,X1,X2,X3] : ((~r1_tarski(X1,X3) | ~r1_tarski(X0,X2)) & k1_xboole_0 != k2_zfmisc_1(X0,X1) & r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3))) => ((~r1_tarski(sK10,sK12) | ~r1_tarski(sK9,sK11)) & k1_xboole_0 != k2_zfmisc_1(sK9,sK10) & r1_tarski(k2_zfmisc_1(sK9,sK10),k2_zfmisc_1(sK11,sK12)))),
% 3.10/0.99    introduced(choice_axiom,[])).
% 3.10/0.99  
% 3.10/0.99  fof(f38,plain,(
% 3.10/0.99    (~r1_tarski(sK10,sK12) | ~r1_tarski(sK9,sK11)) & k1_xboole_0 != k2_zfmisc_1(sK9,sK10) & r1_tarski(k2_zfmisc_1(sK9,sK10),k2_zfmisc_1(sK11,sK12))),
% 3.10/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK9,sK10,sK11,sK12])],[f15,f37])).
% 3.10/0.99  
% 3.10/0.99  fof(f63,plain,(
% 3.10/0.99    r1_tarski(k2_zfmisc_1(sK9,sK10),k2_zfmisc_1(sK11,sK12))),
% 3.10/0.99    inference(cnf_transformation,[],[f38])).
% 3.10/0.99  
% 3.10/0.99  fof(f62,plain,(
% 3.10/0.99    ( ! [X2,X0,X3,X1] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | ~r2_hidden(X1,X3) | ~r2_hidden(X0,X2)) )),
% 3.10/0.99    inference(cnf_transformation,[],[f36])).
% 3.10/0.99  
% 3.10/0.99  fof(f6,axiom,(
% 3.10/0.99    ! [X0,X1,X2] : (k2_zfmisc_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4,X5] : (k4_tarski(X4,X5) = X3 & r2_hidden(X5,X1) & r2_hidden(X4,X0))))),
% 3.10/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.10/0.99  
% 3.10/0.99  fof(f29,plain,(
% 3.10/0.99    ! [X0,X1,X2] : ((k2_zfmisc_1(X0,X1) = X2 | ? [X3] : ((! [X4,X5] : (k4_tarski(X4,X5) != X3 | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X0)) | ~r2_hidden(X3,X2)) & (? [X4,X5] : (k4_tarski(X4,X5) = X3 & r2_hidden(X5,X1) & r2_hidden(X4,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ! [X4,X5] : (k4_tarski(X4,X5) != X3 | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X0))) & (? [X4,X5] : (k4_tarski(X4,X5) = X3 & r2_hidden(X5,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X3,X2))) | k2_zfmisc_1(X0,X1) != X2))),
% 3.10/0.99    inference(nnf_transformation,[],[f6])).
% 3.10/0.99  
% 3.10/0.99  fof(f30,plain,(
% 3.10/0.99    ! [X0,X1,X2] : ((k2_zfmisc_1(X0,X1) = X2 | ? [X3] : ((! [X4,X5] : (k4_tarski(X4,X5) != X3 | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X0)) | ~r2_hidden(X3,X2)) & (? [X6,X7] : (k4_tarski(X6,X7) = X3 & r2_hidden(X7,X1) & r2_hidden(X6,X0)) | r2_hidden(X3,X2)))) & (! [X8] : ((r2_hidden(X8,X2) | ! [X9,X10] : (k4_tarski(X9,X10) != X8 | ~r2_hidden(X10,X1) | ~r2_hidden(X9,X0))) & (? [X11,X12] : (k4_tarski(X11,X12) = X8 & r2_hidden(X12,X1) & r2_hidden(X11,X0)) | ~r2_hidden(X8,X2))) | k2_zfmisc_1(X0,X1) != X2))),
% 3.10/0.99    inference(rectify,[],[f29])).
% 3.10/0.99  
% 3.10/0.99  fof(f33,plain,(
% 3.10/0.99    ! [X8,X1,X0] : (? [X11,X12] : (k4_tarski(X11,X12) = X8 & r2_hidden(X12,X1) & r2_hidden(X11,X0)) => (k4_tarski(sK7(X0,X1,X8),sK8(X0,X1,X8)) = X8 & r2_hidden(sK8(X0,X1,X8),X1) & r2_hidden(sK7(X0,X1,X8),X0)))),
% 3.10/0.99    introduced(choice_axiom,[])).
% 3.10/0.99  
% 3.10/0.99  fof(f32,plain,(
% 3.10/0.99    ( ! [X3] : (! [X2,X1,X0] : (? [X6,X7] : (k4_tarski(X6,X7) = X3 & r2_hidden(X7,X1) & r2_hidden(X6,X0)) => (k4_tarski(sK5(X0,X1,X2),sK6(X0,X1,X2)) = X3 & r2_hidden(sK6(X0,X1,X2),X1) & r2_hidden(sK5(X0,X1,X2),X0)))) )),
% 3.10/0.99    introduced(choice_axiom,[])).
% 3.10/0.99  
% 3.10/0.99  fof(f31,plain,(
% 3.10/0.99    ! [X2,X1,X0] : (? [X3] : ((! [X4,X5] : (k4_tarski(X4,X5) != X3 | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X0)) | ~r2_hidden(X3,X2)) & (? [X6,X7] : (k4_tarski(X6,X7) = X3 & r2_hidden(X7,X1) & r2_hidden(X6,X0)) | r2_hidden(X3,X2))) => ((! [X5,X4] : (k4_tarski(X4,X5) != sK4(X0,X1,X2) | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X0)) | ~r2_hidden(sK4(X0,X1,X2),X2)) & (? [X7,X6] : (k4_tarski(X6,X7) = sK4(X0,X1,X2) & r2_hidden(X7,X1) & r2_hidden(X6,X0)) | r2_hidden(sK4(X0,X1,X2),X2))))),
% 3.10/0.99    introduced(choice_axiom,[])).
% 3.10/0.99  
% 3.10/0.99  fof(f34,plain,(
% 3.10/0.99    ! [X0,X1,X2] : ((k2_zfmisc_1(X0,X1) = X2 | ((! [X4,X5] : (k4_tarski(X4,X5) != sK4(X0,X1,X2) | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X0)) | ~r2_hidden(sK4(X0,X1,X2),X2)) & ((k4_tarski(sK5(X0,X1,X2),sK6(X0,X1,X2)) = sK4(X0,X1,X2) & r2_hidden(sK6(X0,X1,X2),X1) & r2_hidden(sK5(X0,X1,X2),X0)) | r2_hidden(sK4(X0,X1,X2),X2)))) & (! [X8] : ((r2_hidden(X8,X2) | ! [X9,X10] : (k4_tarski(X9,X10) != X8 | ~r2_hidden(X10,X1) | ~r2_hidden(X9,X0))) & ((k4_tarski(sK7(X0,X1,X8),sK8(X0,X1,X8)) = X8 & r2_hidden(sK8(X0,X1,X8),X1) & r2_hidden(sK7(X0,X1,X8),X0)) | ~r2_hidden(X8,X2))) | k2_zfmisc_1(X0,X1) != X2))),
% 3.10/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6,sK7,sK8])],[f30,f33,f32,f31])).
% 3.10/0.99  
% 3.10/0.99  fof(f53,plain,(
% 3.10/0.99    ( ! [X2,X0,X8,X1] : (r2_hidden(sK8(X0,X1,X8),X1) | ~r2_hidden(X8,X2) | k2_zfmisc_1(X0,X1) != X2) )),
% 3.10/0.99    inference(cnf_transformation,[],[f34])).
% 3.10/0.99  
% 3.10/0.99  fof(f72,plain,(
% 3.10/0.99    ( ! [X0,X8,X1] : (r2_hidden(sK8(X0,X1,X8),X1) | ~r2_hidden(X8,k2_zfmisc_1(X0,X1))) )),
% 3.10/0.99    inference(equality_resolution,[],[f53])).
% 3.10/0.99  
% 3.10/0.99  fof(f4,axiom,(
% 3.10/0.99    ! [X0] : ~(! [X1] : ~r2_hidden(X1,X0) & k1_xboole_0 != X0)),
% 3.10/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.10/0.99  
% 3.10/0.99  fof(f13,plain,(
% 3.10/0.99    ! [X0] : (? [X1] : r2_hidden(X1,X0) | k1_xboole_0 = X0)),
% 3.10/0.99    inference(ennf_transformation,[],[f4])).
% 3.10/0.99  
% 3.10/0.99  fof(f27,plain,(
% 3.10/0.99    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK3(X0),X0))),
% 3.10/0.99    introduced(choice_axiom,[])).
% 3.10/0.99  
% 3.10/0.99  fof(f28,plain,(
% 3.10/0.99    ! [X0] : (r2_hidden(sK3(X0),X0) | k1_xboole_0 = X0)),
% 3.10/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f13,f27])).
% 3.10/0.99  
% 3.10/0.99  fof(f50,plain,(
% 3.10/0.99    ( ! [X0] : (r2_hidden(sK3(X0),X0) | k1_xboole_0 = X0) )),
% 3.10/0.99    inference(cnf_transformation,[],[f28])).
% 3.10/0.99  
% 3.10/0.99  fof(f64,plain,(
% 3.10/0.99    k1_xboole_0 != k2_zfmisc_1(sK9,sK10)),
% 3.10/0.99    inference(cnf_transformation,[],[f38])).
% 3.10/0.99  
% 3.10/0.99  fof(f41,plain,(
% 3.10/0.99    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r2_hidden(sK0(X0,X1),X1)) )),
% 3.10/0.99    inference(cnf_transformation,[],[f19])).
% 3.10/0.99  
% 3.10/0.99  fof(f40,plain,(
% 3.10/0.99    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK0(X0,X1),X0)) )),
% 3.10/0.99    inference(cnf_transformation,[],[f19])).
% 3.10/0.99  
% 3.10/0.99  fof(f61,plain,(
% 3.10/0.99    ( ! [X2,X0,X3,X1] : (r2_hidden(X1,X3) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))) )),
% 3.10/0.99    inference(cnf_transformation,[],[f36])).
% 3.10/0.99  
% 3.10/0.99  fof(f52,plain,(
% 3.10/0.99    ( ! [X2,X0,X8,X1] : (r2_hidden(sK7(X0,X1,X8),X0) | ~r2_hidden(X8,X2) | k2_zfmisc_1(X0,X1) != X2) )),
% 3.10/0.99    inference(cnf_transformation,[],[f34])).
% 3.10/0.99  
% 3.10/0.99  fof(f73,plain,(
% 3.10/0.99    ( ! [X0,X8,X1] : (r2_hidden(sK7(X0,X1,X8),X0) | ~r2_hidden(X8,k2_zfmisc_1(X0,X1))) )),
% 3.10/0.99    inference(equality_resolution,[],[f52])).
% 3.10/0.99  
% 3.10/0.99  fof(f65,plain,(
% 3.10/0.99    ~r1_tarski(sK10,sK12) | ~r1_tarski(sK9,sK11)),
% 3.10/0.99    inference(cnf_transformation,[],[f38])).
% 3.10/0.99  
% 3.10/0.99  cnf(c_23,plain,
% 3.10/0.99      ( r2_hidden(X0,X1)
% 3.10/0.99      | ~ r2_hidden(k4_tarski(X0,X2),k2_zfmisc_1(X1,X3)) ),
% 3.10/0.99      inference(cnf_transformation,[],[f60]) ).
% 3.10/0.99  
% 3.10/0.99  cnf(c_2,plain,
% 3.10/0.99      ( ~ r2_hidden(X0,X1) | r2_hidden(X0,X2) | ~ r1_tarski(X1,X2) ),
% 3.10/0.99      inference(cnf_transformation,[],[f39]) ).
% 3.10/0.99  
% 3.10/0.99  cnf(c_26,negated_conjecture,
% 3.10/0.99      ( r1_tarski(k2_zfmisc_1(sK9,sK10),k2_zfmisc_1(sK11,sK12)) ),
% 3.10/0.99      inference(cnf_transformation,[],[f63]) ).
% 3.10/0.99  
% 3.10/0.99  cnf(c_1463,plain,
% 3.10/0.99      ( r2_hidden(X0,k2_zfmisc_1(sK11,sK12))
% 3.10/0.99      | ~ r2_hidden(X0,k2_zfmisc_1(sK9,sK10)) ),
% 3.10/0.99      inference(resolution,[status(thm)],[c_2,c_26]) ).
% 3.10/0.99  
% 3.10/0.99  cnf(c_2034,plain,
% 3.10/0.99      ( r2_hidden(X0,sK11)
% 3.10/0.99      | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(sK9,sK10)) ),
% 3.10/0.99      inference(resolution,[status(thm)],[c_23,c_1463]) ).
% 3.10/0.99  
% 3.10/0.99  cnf(c_21,plain,
% 3.10/0.99      ( ~ r2_hidden(X0,X1)
% 3.10/0.99      | ~ r2_hidden(X2,X3)
% 3.10/0.99      | r2_hidden(k4_tarski(X2,X0),k2_zfmisc_1(X3,X1)) ),
% 3.10/0.99      inference(cnf_transformation,[],[f62]) ).
% 3.10/0.99  
% 3.10/0.99  cnf(c_3606,plain,
% 3.10/0.99      ( r2_hidden(X0,sK11) | ~ r2_hidden(X0,sK9) | ~ r2_hidden(X1,sK10) ),
% 3.10/0.99      inference(resolution,[status(thm)],[c_2034,c_21]) ).
% 3.10/0.99  
% 3.10/0.99  cnf(c_19,plain,
% 3.10/0.99      ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
% 3.10/0.99      | r2_hidden(sK8(X1,X2,X0),X2) ),
% 3.10/0.99      inference(cnf_transformation,[],[f72]) ).
% 3.10/0.99  
% 3.10/0.99  cnf(c_3971,plain,
% 3.10/0.99      ( ~ r2_hidden(X0,k2_zfmisc_1(X1,sK10))
% 3.10/0.99      | r2_hidden(X2,sK11)
% 3.10/0.99      | ~ r2_hidden(X2,sK9) ),
% 3.10/0.99      inference(resolution,[status(thm)],[c_3606,c_19]) ).
% 3.10/0.99  
% 3.10/0.99  cnf(c_11,plain,
% 3.10/0.99      ( r2_hidden(sK3(X0),X0) | k1_xboole_0 = X0 ),
% 3.10/0.99      inference(cnf_transformation,[],[f50]) ).
% 3.10/0.99  
% 3.10/0.99  cnf(c_25,negated_conjecture,
% 3.10/0.99      ( k1_xboole_0 != k2_zfmisc_1(sK9,sK10) ),
% 3.10/0.99      inference(cnf_transformation,[],[f64]) ).
% 3.10/0.99  
% 3.10/0.99  cnf(c_1168,plain,
% 3.10/0.99      ( r2_hidden(sK3(k2_zfmisc_1(sK9,sK10)),k2_zfmisc_1(sK9,sK10)) ),
% 3.10/0.99      inference(resolution,[status(thm)],[c_11,c_25]) ).
% 3.10/0.99  
% 3.10/0.99  cnf(c_7090,plain,
% 3.10/0.99      ( r2_hidden(X0,sK11) | ~ r2_hidden(X0,sK9) ),
% 3.10/0.99      inference(resolution,[status(thm)],[c_3971,c_1168]) ).
% 3.10/0.99  
% 3.10/0.99  cnf(c_0,plain,
% 3.10/0.99      ( ~ r2_hidden(sK0(X0,X1),X1) | r1_tarski(X0,X1) ),
% 3.10/0.99      inference(cnf_transformation,[],[f41]) ).
% 3.10/0.99  
% 3.10/0.99  cnf(c_7100,plain,
% 3.10/0.99      ( ~ r2_hidden(sK0(X0,sK11),sK9) | r1_tarski(X0,sK11) ),
% 3.10/0.99      inference(resolution,[status(thm)],[c_7090,c_0]) ).
% 3.10/0.99  
% 3.10/0.99  cnf(c_1,plain,
% 3.10/0.99      ( r2_hidden(sK0(X0,X1),X0) | r1_tarski(X0,X1) ),
% 3.10/0.99      inference(cnf_transformation,[],[f40]) ).
% 3.10/0.99  
% 3.10/0.99  cnf(c_7110,plain,
% 3.10/0.99      ( r1_tarski(sK9,sK11) ),
% 3.10/0.99      inference(resolution,[status(thm)],[c_7100,c_1]) ).
% 3.10/0.99  
% 3.10/0.99  cnf(c_22,plain,
% 3.10/0.99      ( r2_hidden(X0,X1)
% 3.10/0.99      | ~ r2_hidden(k4_tarski(X2,X0),k2_zfmisc_1(X3,X1)) ),
% 3.10/0.99      inference(cnf_transformation,[],[f61]) ).
% 3.10/0.99  
% 3.10/0.99  cnf(c_1838,plain,
% 3.10/0.99      ( r2_hidden(X0,sK12)
% 3.10/0.99      | ~ r2_hidden(k4_tarski(X1,X0),k2_zfmisc_1(sK9,sK10)) ),
% 3.10/0.99      inference(resolution,[status(thm)],[c_22,c_1463]) ).
% 3.10/0.99  
% 3.10/0.99  cnf(c_3597,plain,
% 3.10/0.99      ( ~ r2_hidden(X0,sK9) | r2_hidden(X1,sK12) | ~ r2_hidden(X1,sK10) ),
% 3.10/0.99      inference(resolution,[status(thm)],[c_1838,c_21]) ).
% 3.10/0.99  
% 3.10/0.99  cnf(c_20,plain,
% 3.10/0.99      ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
% 3.10/0.99      | r2_hidden(sK7(X1,X2,X0),X1) ),
% 3.10/0.99      inference(cnf_transformation,[],[f73]) ).
% 3.10/0.99  
% 3.10/0.99  cnf(c_3951,plain,
% 3.10/0.99      ( ~ r2_hidden(X0,k2_zfmisc_1(sK9,X1))
% 3.10/0.99      | r2_hidden(X2,sK12)
% 3.10/0.99      | ~ r2_hidden(X2,sK10) ),
% 3.10/0.99      inference(resolution,[status(thm)],[c_3597,c_20]) ).
% 3.10/0.99  
% 3.10/0.99  cnf(c_5004,plain,
% 3.10/0.99      ( r2_hidden(X0,sK12) | ~ r2_hidden(X0,sK10) ),
% 3.10/0.99      inference(resolution,[status(thm)],[c_3951,c_1168]) ).
% 3.10/0.99  
% 3.10/0.99  cnf(c_5525,plain,
% 3.10/0.99      ( ~ r2_hidden(sK0(X0,sK12),sK10) | r1_tarski(X0,sK12) ),
% 3.10/0.99      inference(resolution,[status(thm)],[c_5004,c_0]) ).
% 3.10/0.99  
% 3.10/0.99  cnf(c_5535,plain,
% 3.10/0.99      ( r1_tarski(sK10,sK12) ),
% 3.10/0.99      inference(resolution,[status(thm)],[c_5525,c_1]) ).
% 3.10/0.99  
% 3.10/0.99  cnf(c_24,negated_conjecture,
% 3.10/0.99      ( ~ r1_tarski(sK9,sK11) | ~ r1_tarski(sK10,sK12) ),
% 3.10/0.99      inference(cnf_transformation,[],[f65]) ).
% 3.10/0.99  
% 3.10/0.99  cnf(contradiction,plain,
% 3.10/0.99      ( $false ),
% 3.10/0.99      inference(minisat,[status(thm)],[c_7110,c_5535,c_24]) ).
% 3.10/0.99  
% 3.10/0.99  
% 3.10/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 3.10/0.99  
% 3.10/0.99  ------                               Statistics
% 3.10/0.99  
% 3.10/0.99  ------ Selected
% 3.10/0.99  
% 3.10/0.99  total_time:                             0.225
% 3.10/0.99  
%------------------------------------------------------------------------------
