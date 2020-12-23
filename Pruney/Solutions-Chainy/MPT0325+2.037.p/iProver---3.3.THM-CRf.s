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
% DateTime   : Thu Dec  3 11:37:51 EST 2020

% Result     : Theorem 3.58s
% Output     : CNFRefutation 3.58s
% Verified   : 
% Statistics : Number of formulae       :  112 ( 360 expanded)
%              Number of clauses        :   61 ( 107 expanded)
%              Number of leaves         :   18 (  86 expanded)
%              Depth                    :   15
%              Number of atoms          :  374 (1368 expanded)
%              Number of equality atoms :   78 ( 186 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal clause size      :   18 (   2 average)
%              Maximal term depth       :    4 (   1 average)

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

fof(f57,plain,(
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

fof(f60,plain,(
    r1_tarski(k2_zfmisc_1(sK8,sK9),k2_zfmisc_1(sK10,sK11)) ),
    inference(cnf_transformation,[],[f36])).

fof(f59,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
      | ~ r2_hidden(X1,X3)
      | ~ r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f38,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK0(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f61,plain,(
    k1_xboole_0 != k2_zfmisc_1(sK8,sK9) ),
    inference(cnf_transformation,[],[f36])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k4_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k4_xboole_0(X0,X1) != X0 )
      & ( k4_xboole_0(X0,X1) = X0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f7])).

fof(f48,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k4_xboole_0(X0,X1) != X0 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f5,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f5])).

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

fof(f43,plain,(
    ! [X0] :
      ( r2_hidden(sK2(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f39,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK0(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f21])).

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

fof(f50,plain,(
    ! [X2,X0,X8,X1] :
      ( r2_hidden(sK7(X0,X1,X8),X1)
      | ~ r2_hidden(X8,X2)
      | k2_zfmisc_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f32])).

fof(f67,plain,(
    ! [X0,X8,X1] :
      ( r2_hidden(sK7(X0,X1,X8),X1)
      | ~ r2_hidden(X8,k2_zfmisc_1(X0,X1)) ) ),
    inference(equality_resolution,[],[f50])).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
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

fof(f14,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f22,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
     => ( r2_hidden(sK1(X0,X1),X1)
        & r2_hidden(sK1(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ( r2_hidden(sK1(X0,X1),X1)
          & r2_hidden(sK1(X0,X1),X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f14,f22])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f58,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X1,X3)
      | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f49,plain,(
    ! [X2,X0,X8,X1] :
      ( r2_hidden(sK6(X0,X1,X8),X0)
      | ~ r2_hidden(X8,X2)
      | k2_zfmisc_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f32])).

fof(f68,plain,(
    ! [X0,X8,X1] :
      ( r2_hidden(sK6(X0,X1,X8),X0)
      | ~ r2_hidden(X8,k2_zfmisc_1(X0,X1)) ) ),
    inference(equality_resolution,[],[f49])).

fof(f62,plain,
    ( ~ r1_tarski(sK9,sK11)
    | ~ r1_tarski(sK8,sK10) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_21,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(k4_tarski(X0,X2),k2_zfmisc_1(X1,X3)) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_2,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | ~ r1_tarski(X1,X2) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_24,negated_conjecture,
    ( r1_tarski(k2_zfmisc_1(sK8,sK9),k2_zfmisc_1(sK10,sK11)) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_1826,plain,
    ( r2_hidden(X0,k2_zfmisc_1(sK10,sK11))
    | ~ r2_hidden(X0,k2_zfmisc_1(sK8,sK9)) ),
    inference(resolution,[status(thm)],[c_2,c_24])).

cnf(c_2154,plain,
    ( r2_hidden(X0,sK10)
    | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(sK8,sK9)) ),
    inference(resolution,[status(thm)],[c_21,c_1826])).

cnf(c_19,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X2,X3)
    | r2_hidden(k4_tarski(X2,X0),k2_zfmisc_1(X3,X1)) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_3525,plain,
    ( r2_hidden(X0,sK10)
    | ~ r2_hidden(X0,sK8)
    | ~ r2_hidden(X1,sK9) ),
    inference(resolution,[status(thm)],[c_2154,c_19])).

cnf(c_1,plain,
    ( r2_hidden(sK0(X0,X1),X0)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_4668,plain,
    ( r2_hidden(X0,sK10)
    | ~ r2_hidden(X0,sK8)
    | r1_tarski(sK9,X1) ),
    inference(resolution,[status(thm)],[c_3525,c_1])).

cnf(c_23,negated_conjecture,
    ( k1_xboole_0 != k2_zfmisc_1(sK8,sK9) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_9,plain,
    ( r1_xboole_0(X0,X1)
    | k4_xboole_0(X0,X1) != X0 ),
    inference(cnf_transformation,[],[f48])).

cnf(c_60,plain,
    ( r1_xboole_0(k1_xboole_0,k1_xboole_0)
    | k4_xboole_0(k1_xboole_0,k1_xboole_0) != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_8,plain,
    ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f45])).

cnf(c_62,plain,
    ( k4_xboole_0(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_630,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_643,plain,
    ( k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_630])).

cnf(c_6,plain,
    ( r2_hidden(sK2(X0),X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f43])).

cnf(c_1314,plain,
    ( r2_hidden(sK2(k2_zfmisc_1(sK8,sK9)),k2_zfmisc_1(sK8,sK9))
    | k1_xboole_0 = k2_zfmisc_1(sK8,sK9) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_0,plain,
    ( ~ r2_hidden(sK0(X0,X1),X1)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_1370,plain,
    ( r1_tarski(X0,X0) ),
    inference(resolution,[status(thm)],[c_0,c_1])).

cnf(c_1372,plain,
    ( r1_tarski(k1_xboole_0,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_1370])).

cnf(c_17,plain,
    ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
    | r2_hidden(sK7(X1,X2,X0),X2) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_1403,plain,
    ( r2_hidden(sK7(sK8,sK9,sK2(k2_zfmisc_1(sK8,sK9))),sK9)
    | ~ r2_hidden(sK2(k2_zfmisc_1(sK8,sK9)),k2_zfmisc_1(sK8,sK9)) ),
    inference(instantiation,[status(thm)],[c_17])).

cnf(c_1572,plain,
    ( r2_hidden(sK7(sK8,sK9,sK2(k2_zfmisc_1(sK8,sK9))),X0)
    | ~ r2_hidden(sK7(sK8,sK9,sK2(k2_zfmisc_1(sK8,sK9))),sK9)
    | ~ r1_tarski(sK9,X0) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_1574,plain,
    ( ~ r2_hidden(sK7(sK8,sK9,sK2(k2_zfmisc_1(sK8,sK9))),sK9)
    | r2_hidden(sK7(sK8,sK9,sK2(k2_zfmisc_1(sK8,sK9))),k1_xboole_0)
    | ~ r1_tarski(sK9,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_1572])).

cnf(c_632,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_1616,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(sK9,X2)
    | X2 != X1
    | sK9 != X0 ),
    inference(instantiation,[status(thm)],[c_632])).

cnf(c_1618,plain,
    ( r1_tarski(sK9,k1_xboole_0)
    | ~ r1_tarski(k1_xboole_0,k1_xboole_0)
    | sK9 != k1_xboole_0
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1616])).

cnf(c_3,plain,
    ( ~ r1_xboole_0(X0,X1)
    | ~ r2_hidden(X2,X1)
    | ~ r2_hidden(X2,X0) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_2504,plain,
    ( ~ r1_xboole_0(X0,X1)
    | ~ r2_hidden(sK7(sK8,sK9,sK2(k2_zfmisc_1(sK8,sK9))),X0)
    | ~ r2_hidden(sK7(sK8,sK9,sK2(k2_zfmisc_1(sK8,sK9))),X1) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_2506,plain,
    ( ~ r1_xboole_0(k1_xboole_0,k1_xboole_0)
    | ~ r2_hidden(sK7(sK8,sK9,sK2(k2_zfmisc_1(sK8,sK9))),k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_2504])).

cnf(c_631,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_2469,plain,
    ( X0 != X1
    | X1 = X0 ),
    inference(resolution,[status(thm)],[c_631,c_630])).

cnf(c_2475,plain,
    ( r2_hidden(sK2(X0),X0)
    | X0 = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_2469,c_6])).

cnf(c_4681,plain,
    ( r2_hidden(X0,sK10)
    | ~ r2_hidden(X0,sK8)
    | sK9 = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_3525,c_2475])).

cnf(c_7079,plain,
    ( ~ r2_hidden(X0,sK8)
    | r2_hidden(X0,sK10) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4668,c_23,c_60,c_62,c_643,c_1314,c_1372,c_1403,c_1574,c_1618,c_2506,c_4681])).

cnf(c_7080,plain,
    ( r2_hidden(X0,sK10)
    | ~ r2_hidden(X0,sK8) ),
    inference(renaming,[status(thm)],[c_7079])).

cnf(c_7302,plain,
    ( ~ r2_hidden(sK0(X0,sK10),sK8)
    | r1_tarski(X0,sK10) ),
    inference(resolution,[status(thm)],[c_7080,c_0])).

cnf(c_12975,plain,
    ( r1_tarski(sK8,sK10) ),
    inference(resolution,[status(thm)],[c_7302,c_1])).

cnf(c_20,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(k4_tarski(X2,X0),k2_zfmisc_1(X3,X1)) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_2014,plain,
    ( r2_hidden(X0,sK11)
    | ~ r2_hidden(k4_tarski(X1,X0),k2_zfmisc_1(sK8,sK9)) ),
    inference(resolution,[status(thm)],[c_20,c_1826])).

cnf(c_3516,plain,
    ( ~ r2_hidden(X0,sK8)
    | r2_hidden(X1,sK11)
    | ~ r2_hidden(X1,sK9) ),
    inference(resolution,[status(thm)],[c_2014,c_19])).

cnf(c_4624,plain,
    ( r2_hidden(X0,sK11)
    | ~ r2_hidden(X0,sK9)
    | r1_tarski(sK8,X1) ),
    inference(resolution,[status(thm)],[c_3516,c_1])).

cnf(c_18,plain,
    ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
    | r2_hidden(sK6(X1,X2,X0),X1) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_1402,plain,
    ( r2_hidden(sK6(sK8,sK9,sK2(k2_zfmisc_1(sK8,sK9))),sK8)
    | ~ r2_hidden(sK2(k2_zfmisc_1(sK8,sK9)),k2_zfmisc_1(sK8,sK9)) ),
    inference(instantiation,[status(thm)],[c_18])).

cnf(c_1541,plain,
    ( ~ r1_xboole_0(sK8,X0)
    | ~ r2_hidden(sK6(sK8,sK9,sK2(k2_zfmisc_1(sK8,sK9))),X0)
    | ~ r2_hidden(sK6(sK8,sK9,sK2(k2_zfmisc_1(sK8,sK9))),sK8) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_1543,plain,
    ( ~ r1_xboole_0(sK8,k1_xboole_0)
    | ~ r2_hidden(sK6(sK8,sK9,sK2(k2_zfmisc_1(sK8,sK9))),sK8)
    | ~ r2_hidden(sK6(sK8,sK9,sK2(k2_zfmisc_1(sK8,sK9))),k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_1541])).

cnf(c_1547,plain,
    ( r2_hidden(sK6(sK8,sK9,sK2(k2_zfmisc_1(sK8,sK9))),X0)
    | ~ r2_hidden(sK6(sK8,sK9,sK2(k2_zfmisc_1(sK8,sK9))),sK8)
    | ~ r1_tarski(sK8,X0) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_1549,plain,
    ( ~ r2_hidden(sK6(sK8,sK9,sK2(k2_zfmisc_1(sK8,sK9))),sK8)
    | r2_hidden(sK6(sK8,sK9,sK2(k2_zfmisc_1(sK8,sK9))),k1_xboole_0)
    | ~ r1_tarski(sK8,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_1547])).

cnf(c_2088,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(sK8,X2)
    | X2 != X1
    | sK8 != X0 ),
    inference(instantiation,[status(thm)],[c_632])).

cnf(c_2090,plain,
    ( r1_tarski(sK8,k1_xboole_0)
    | ~ r1_tarski(k1_xboole_0,k1_xboole_0)
    | sK8 != k1_xboole_0
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_2088])).

cnf(c_2100,plain,
    ( k4_xboole_0(sK8,k1_xboole_0) = sK8 ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_4637,plain,
    ( r2_hidden(X0,sK11)
    | ~ r2_hidden(X0,sK9)
    | sK8 = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_3516,c_2475])).

cnf(c_5393,plain,
    ( r1_xboole_0(sK8,X0)
    | k4_xboole_0(sK8,X0) != sK8 ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_5395,plain,
    ( r1_xboole_0(sK8,k1_xboole_0)
    | k4_xboole_0(sK8,k1_xboole_0) != sK8 ),
    inference(instantiation,[status(thm)],[c_5393])).

cnf(c_6413,plain,
    ( ~ r2_hidden(X0,sK9)
    | r2_hidden(X0,sK11) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4624,c_23,c_643,c_1314,c_1372,c_1402,c_1543,c_1549,c_2090,c_2100,c_4637,c_5395])).

cnf(c_6414,plain,
    ( r2_hidden(X0,sK11)
    | ~ r2_hidden(X0,sK9) ),
    inference(renaming,[status(thm)],[c_6413])).

cnf(c_6795,plain,
    ( ~ r2_hidden(sK0(X0,sK11),sK9)
    | r1_tarski(X0,sK11) ),
    inference(resolution,[status(thm)],[c_6414,c_0])).

cnf(c_12967,plain,
    ( r1_tarski(sK9,sK11) ),
    inference(resolution,[status(thm)],[c_6795,c_1])).

cnf(c_22,negated_conjecture,
    ( ~ r1_tarski(sK8,sK10)
    | ~ r1_tarski(sK9,sK11) ),
    inference(cnf_transformation,[],[f62])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_12975,c_12967,c_22])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : iproveropt_run.sh %d %s
% 0.14/0.34  % Computer   : n011.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 16:20:27 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running in FOF mode
% 3.58/0.99  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.58/0.99  
% 3.58/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.58/0.99  
% 3.58/0.99  ------  iProver source info
% 3.58/0.99  
% 3.58/0.99  git: date: 2020-06-30 10:37:57 +0100
% 3.58/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.58/0.99  git: non_committed_changes: false
% 3.58/0.99  git: last_make_outside_of_git: false
% 3.58/0.99  
% 3.58/0.99  ------ 
% 3.58/0.99  ------ Parsing...
% 3.58/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.58/0.99  
% 3.58/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e  sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 3.58/0.99  
% 3.58/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.58/0.99  
% 3.58/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.58/0.99  ------ Proving...
% 3.58/0.99  ------ Problem Properties 
% 3.58/0.99  
% 3.58/0.99  
% 3.58/0.99  clauses                                 24
% 3.58/0.99  conjectures                             3
% 3.58/0.99  EPR                                     3
% 3.58/0.99  Horn                                    17
% 3.58/0.99  unary                                   4
% 3.58/0.99  binary                                  13
% 3.58/0.99  lits                                    53
% 3.58/0.99  lits eq                                 13
% 3.58/0.99  fd_pure                                 0
% 3.58/0.99  fd_pseudo                               0
% 3.58/0.99  fd_cond                                 1
% 3.58/0.99  fd_pseudo_cond                          4
% 3.58/0.99  AC symbols                              0
% 3.58/0.99  
% 3.58/0.99  ------ Input Options Time Limit: Unbounded
% 3.58/0.99  
% 3.58/0.99  
% 3.58/0.99  ------ 
% 3.58/0.99  Current options:
% 3.58/0.99  ------ 
% 3.58/0.99  
% 3.58/0.99  
% 3.58/0.99  
% 3.58/0.99  
% 3.58/0.99  ------ Proving...
% 3.58/0.99  
% 3.58/0.99  
% 3.58/0.99  % SZS status Theorem for theBenchmark.p
% 3.58/0.99  
% 3.58/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 3.58/0.99  
% 3.58/0.99  fof(f9,axiom,(
% 3.58/0.99    ! [X0,X1,X2,X3] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) <=> (r2_hidden(X1,X3) & r2_hidden(X0,X2)))),
% 3.58/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.58/0.99  
% 3.58/0.99  fof(f33,plain,(
% 3.58/0.99    ! [X0,X1,X2,X3] : ((r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | (~r2_hidden(X1,X3) | ~r2_hidden(X0,X2))) & ((r2_hidden(X1,X3) & r2_hidden(X0,X2)) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))))),
% 3.58/0.99    inference(nnf_transformation,[],[f9])).
% 3.58/0.99  
% 3.58/0.99  fof(f34,plain,(
% 3.58/0.99    ! [X0,X1,X2,X3] : ((r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | ~r2_hidden(X1,X3) | ~r2_hidden(X0,X2)) & ((r2_hidden(X1,X3) & r2_hidden(X0,X2)) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))))),
% 3.58/0.99    inference(flattening,[],[f33])).
% 3.58/0.99  
% 3.58/0.99  fof(f57,plain,(
% 3.58/0.99    ( ! [X2,X0,X3,X1] : (r2_hidden(X0,X2) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))) )),
% 3.58/0.99    inference(cnf_transformation,[],[f34])).
% 3.58/0.99  
% 3.58/0.99  fof(f1,axiom,(
% 3.58/0.99    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 3.58/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.58/0.99  
% 3.58/0.99  fof(f13,plain,(
% 3.58/0.99    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 3.58/0.99    inference(ennf_transformation,[],[f1])).
% 3.58/0.99  
% 3.58/0.99  fof(f18,plain,(
% 3.58/0.99    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 3.58/0.99    inference(nnf_transformation,[],[f13])).
% 3.58/0.99  
% 3.58/0.99  fof(f19,plain,(
% 3.58/0.99    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 3.58/0.99    inference(rectify,[],[f18])).
% 3.58/0.99  
% 3.58/0.99  fof(f20,plain,(
% 3.58/0.99    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 3.58/0.99    introduced(choice_axiom,[])).
% 3.58/0.99  
% 3.58/0.99  fof(f21,plain,(
% 3.58/0.99    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 3.58/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f19,f20])).
% 3.58/0.99  
% 3.58/0.99  fof(f37,plain,(
% 3.58/0.99    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,X1)) )),
% 3.58/0.99    inference(cnf_transformation,[],[f21])).
% 3.58/0.99  
% 3.58/0.99  fof(f10,conjecture,(
% 3.58/0.99    ! [X0,X1,X2,X3] : (r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)) => ((r1_tarski(X1,X3) & r1_tarski(X0,X2)) | k1_xboole_0 = k2_zfmisc_1(X0,X1)))),
% 3.58/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.58/0.99  
% 3.58/0.99  fof(f11,negated_conjecture,(
% 3.58/0.99    ~! [X0,X1,X2,X3] : (r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)) => ((r1_tarski(X1,X3) & r1_tarski(X0,X2)) | k1_xboole_0 = k2_zfmisc_1(X0,X1)))),
% 3.58/0.99    inference(negated_conjecture,[],[f10])).
% 3.58/0.99  
% 3.58/0.99  fof(f16,plain,(
% 3.58/0.99    ? [X0,X1,X2,X3] : (((~r1_tarski(X1,X3) | ~r1_tarski(X0,X2)) & k1_xboole_0 != k2_zfmisc_1(X0,X1)) & r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)))),
% 3.58/0.99    inference(ennf_transformation,[],[f11])).
% 3.58/0.99  
% 3.58/0.99  fof(f17,plain,(
% 3.58/0.99    ? [X0,X1,X2,X3] : ((~r1_tarski(X1,X3) | ~r1_tarski(X0,X2)) & k1_xboole_0 != k2_zfmisc_1(X0,X1) & r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)))),
% 3.58/0.99    inference(flattening,[],[f16])).
% 3.58/0.99  
% 3.58/0.99  fof(f35,plain,(
% 3.58/0.99    ? [X0,X1,X2,X3] : ((~r1_tarski(X1,X3) | ~r1_tarski(X0,X2)) & k1_xboole_0 != k2_zfmisc_1(X0,X1) & r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3))) => ((~r1_tarski(sK9,sK11) | ~r1_tarski(sK8,sK10)) & k1_xboole_0 != k2_zfmisc_1(sK8,sK9) & r1_tarski(k2_zfmisc_1(sK8,sK9),k2_zfmisc_1(sK10,sK11)))),
% 3.58/0.99    introduced(choice_axiom,[])).
% 3.58/0.99  
% 3.58/0.99  fof(f36,plain,(
% 3.58/0.99    (~r1_tarski(sK9,sK11) | ~r1_tarski(sK8,sK10)) & k1_xboole_0 != k2_zfmisc_1(sK8,sK9) & r1_tarski(k2_zfmisc_1(sK8,sK9),k2_zfmisc_1(sK10,sK11))),
% 3.58/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8,sK9,sK10,sK11])],[f17,f35])).
% 3.58/0.99  
% 3.58/0.99  fof(f60,plain,(
% 3.58/0.99    r1_tarski(k2_zfmisc_1(sK8,sK9),k2_zfmisc_1(sK10,sK11))),
% 3.58/0.99    inference(cnf_transformation,[],[f36])).
% 3.58/0.99  
% 3.58/0.99  fof(f59,plain,(
% 3.58/0.99    ( ! [X2,X0,X3,X1] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | ~r2_hidden(X1,X3) | ~r2_hidden(X0,X2)) )),
% 3.58/0.99    inference(cnf_transformation,[],[f34])).
% 3.58/0.99  
% 3.58/0.99  fof(f38,plain,(
% 3.58/0.99    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK0(X0,X1),X0)) )),
% 3.58/0.99    inference(cnf_transformation,[],[f21])).
% 3.58/0.99  
% 3.58/0.99  fof(f61,plain,(
% 3.58/0.99    k1_xboole_0 != k2_zfmisc_1(sK8,sK9)),
% 3.58/0.99    inference(cnf_transformation,[],[f36])).
% 3.58/0.99  
% 3.58/0.99  fof(f7,axiom,(
% 3.58/0.99    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k4_xboole_0(X0,X1) = X0)),
% 3.58/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.58/0.99  
% 3.58/0.99  fof(f26,plain,(
% 3.58/0.99    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) != X0) & (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)))),
% 3.58/0.99    inference(nnf_transformation,[],[f7])).
% 3.58/0.99  
% 3.58/0.99  fof(f48,plain,(
% 3.58/0.99    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) != X0) )),
% 3.58/0.99    inference(cnf_transformation,[],[f26])).
% 3.58/0.99  
% 3.58/0.99  fof(f5,axiom,(
% 3.58/0.99    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 3.58/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.58/0.99  
% 3.58/0.99  fof(f45,plain,(
% 3.58/0.99    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 3.58/0.99    inference(cnf_transformation,[],[f5])).
% 3.58/0.99  
% 3.58/0.99  fof(f3,axiom,(
% 3.58/0.99    ! [X0] : ~(! [X1] : ~r2_hidden(X1,X0) & k1_xboole_0 != X0)),
% 3.58/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.58/0.99  
% 3.58/0.99  fof(f15,plain,(
% 3.58/0.99    ! [X0] : (? [X1] : r2_hidden(X1,X0) | k1_xboole_0 = X0)),
% 3.58/0.99    inference(ennf_transformation,[],[f3])).
% 3.58/0.99  
% 3.58/0.99  fof(f24,plain,(
% 3.58/0.99    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK2(X0),X0))),
% 3.58/0.99    introduced(choice_axiom,[])).
% 3.58/0.99  
% 3.58/0.99  fof(f25,plain,(
% 3.58/0.99    ! [X0] : (r2_hidden(sK2(X0),X0) | k1_xboole_0 = X0)),
% 3.58/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f15,f24])).
% 3.58/0.99  
% 3.58/0.99  fof(f43,plain,(
% 3.58/0.99    ( ! [X0] : (r2_hidden(sK2(X0),X0) | k1_xboole_0 = X0) )),
% 3.58/0.99    inference(cnf_transformation,[],[f25])).
% 3.58/0.99  
% 3.58/0.99  fof(f39,plain,(
% 3.58/0.99    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r2_hidden(sK0(X0,X1),X1)) )),
% 3.58/0.99    inference(cnf_transformation,[],[f21])).
% 3.58/0.99  
% 3.58/0.99  fof(f8,axiom,(
% 3.58/0.99    ! [X0,X1,X2] : (k2_zfmisc_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4,X5] : (k4_tarski(X4,X5) = X3 & r2_hidden(X5,X1) & r2_hidden(X4,X0))))),
% 3.58/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.58/0.99  
% 3.58/0.99  fof(f27,plain,(
% 3.58/0.99    ! [X0,X1,X2] : ((k2_zfmisc_1(X0,X1) = X2 | ? [X3] : ((! [X4,X5] : (k4_tarski(X4,X5) != X3 | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X0)) | ~r2_hidden(X3,X2)) & (? [X4,X5] : (k4_tarski(X4,X5) = X3 & r2_hidden(X5,X1) & r2_hidden(X4,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ! [X4,X5] : (k4_tarski(X4,X5) != X3 | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X0))) & (? [X4,X5] : (k4_tarski(X4,X5) = X3 & r2_hidden(X5,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X3,X2))) | k2_zfmisc_1(X0,X1) != X2))),
% 3.58/0.99    inference(nnf_transformation,[],[f8])).
% 3.58/0.99  
% 3.58/0.99  fof(f28,plain,(
% 3.58/0.99    ! [X0,X1,X2] : ((k2_zfmisc_1(X0,X1) = X2 | ? [X3] : ((! [X4,X5] : (k4_tarski(X4,X5) != X3 | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X0)) | ~r2_hidden(X3,X2)) & (? [X6,X7] : (k4_tarski(X6,X7) = X3 & r2_hidden(X7,X1) & r2_hidden(X6,X0)) | r2_hidden(X3,X2)))) & (! [X8] : ((r2_hidden(X8,X2) | ! [X9,X10] : (k4_tarski(X9,X10) != X8 | ~r2_hidden(X10,X1) | ~r2_hidden(X9,X0))) & (? [X11,X12] : (k4_tarski(X11,X12) = X8 & r2_hidden(X12,X1) & r2_hidden(X11,X0)) | ~r2_hidden(X8,X2))) | k2_zfmisc_1(X0,X1) != X2))),
% 3.58/0.99    inference(rectify,[],[f27])).
% 3.58/0.99  
% 3.58/0.99  fof(f31,plain,(
% 3.58/0.99    ! [X8,X1,X0] : (? [X11,X12] : (k4_tarski(X11,X12) = X8 & r2_hidden(X12,X1) & r2_hidden(X11,X0)) => (k4_tarski(sK6(X0,X1,X8),sK7(X0,X1,X8)) = X8 & r2_hidden(sK7(X0,X1,X8),X1) & r2_hidden(sK6(X0,X1,X8),X0)))),
% 3.58/0.99    introduced(choice_axiom,[])).
% 3.58/0.99  
% 3.58/0.99  fof(f30,plain,(
% 3.58/0.99    ( ! [X3] : (! [X2,X1,X0] : (? [X6,X7] : (k4_tarski(X6,X7) = X3 & r2_hidden(X7,X1) & r2_hidden(X6,X0)) => (k4_tarski(sK4(X0,X1,X2),sK5(X0,X1,X2)) = X3 & r2_hidden(sK5(X0,X1,X2),X1) & r2_hidden(sK4(X0,X1,X2),X0)))) )),
% 3.58/0.99    introduced(choice_axiom,[])).
% 3.58/0.99  
% 3.58/0.99  fof(f29,plain,(
% 3.58/0.99    ! [X2,X1,X0] : (? [X3] : ((! [X4,X5] : (k4_tarski(X4,X5) != X3 | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X0)) | ~r2_hidden(X3,X2)) & (? [X6,X7] : (k4_tarski(X6,X7) = X3 & r2_hidden(X7,X1) & r2_hidden(X6,X0)) | r2_hidden(X3,X2))) => ((! [X5,X4] : (k4_tarski(X4,X5) != sK3(X0,X1,X2) | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X0)) | ~r2_hidden(sK3(X0,X1,X2),X2)) & (? [X7,X6] : (k4_tarski(X6,X7) = sK3(X0,X1,X2) & r2_hidden(X7,X1) & r2_hidden(X6,X0)) | r2_hidden(sK3(X0,X1,X2),X2))))),
% 3.58/0.99    introduced(choice_axiom,[])).
% 3.58/0.99  
% 3.58/0.99  fof(f32,plain,(
% 3.58/0.99    ! [X0,X1,X2] : ((k2_zfmisc_1(X0,X1) = X2 | ((! [X4,X5] : (k4_tarski(X4,X5) != sK3(X0,X1,X2) | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X0)) | ~r2_hidden(sK3(X0,X1,X2),X2)) & ((k4_tarski(sK4(X0,X1,X2),sK5(X0,X1,X2)) = sK3(X0,X1,X2) & r2_hidden(sK5(X0,X1,X2),X1) & r2_hidden(sK4(X0,X1,X2),X0)) | r2_hidden(sK3(X0,X1,X2),X2)))) & (! [X8] : ((r2_hidden(X8,X2) | ! [X9,X10] : (k4_tarski(X9,X10) != X8 | ~r2_hidden(X10,X1) | ~r2_hidden(X9,X0))) & ((k4_tarski(sK6(X0,X1,X8),sK7(X0,X1,X8)) = X8 & r2_hidden(sK7(X0,X1,X8),X1) & r2_hidden(sK6(X0,X1,X8),X0)) | ~r2_hidden(X8,X2))) | k2_zfmisc_1(X0,X1) != X2))),
% 3.58/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5,sK6,sK7])],[f28,f31,f30,f29])).
% 3.58/0.99  
% 3.58/0.99  fof(f50,plain,(
% 3.58/0.99    ( ! [X2,X0,X8,X1] : (r2_hidden(sK7(X0,X1,X8),X1) | ~r2_hidden(X8,X2) | k2_zfmisc_1(X0,X1) != X2) )),
% 3.58/0.99    inference(cnf_transformation,[],[f32])).
% 3.58/0.99  
% 3.58/0.99  fof(f67,plain,(
% 3.58/0.99    ( ! [X0,X8,X1] : (r2_hidden(sK7(X0,X1,X8),X1) | ~r2_hidden(X8,k2_zfmisc_1(X0,X1))) )),
% 3.58/0.99    inference(equality_resolution,[],[f50])).
% 3.58/0.99  
% 3.58/0.99  fof(f2,axiom,(
% 3.58/0.99    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 3.58/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.58/0.99  
% 3.58/0.99  fof(f12,plain,(
% 3.58/0.99    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 3.58/0.99    inference(rectify,[],[f2])).
% 3.58/0.99  
% 3.58/0.99  fof(f14,plain,(
% 3.58/0.99    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 3.58/0.99    inference(ennf_transformation,[],[f12])).
% 3.58/0.99  
% 3.58/0.99  fof(f22,plain,(
% 3.58/0.99    ! [X1,X0] : (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) => (r2_hidden(sK1(X0,X1),X1) & r2_hidden(sK1(X0,X1),X0)))),
% 3.58/0.99    introduced(choice_axiom,[])).
% 3.58/0.99  
% 3.58/0.99  fof(f23,plain,(
% 3.58/0.99    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & ((r2_hidden(sK1(X0,X1),X1) & r2_hidden(sK1(X0,X1),X0)) | r1_xboole_0(X0,X1)))),
% 3.58/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f14,f22])).
% 3.58/0.99  
% 3.58/0.99  fof(f42,plain,(
% 3.58/0.99    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) )),
% 3.58/0.99    inference(cnf_transformation,[],[f23])).
% 3.58/0.99  
% 3.58/0.99  fof(f58,plain,(
% 3.58/0.99    ( ! [X2,X0,X3,X1] : (r2_hidden(X1,X3) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))) )),
% 3.58/0.99    inference(cnf_transformation,[],[f34])).
% 3.58/0.99  
% 3.58/0.99  fof(f49,plain,(
% 3.58/0.99    ( ! [X2,X0,X8,X1] : (r2_hidden(sK6(X0,X1,X8),X0) | ~r2_hidden(X8,X2) | k2_zfmisc_1(X0,X1) != X2) )),
% 3.58/0.99    inference(cnf_transformation,[],[f32])).
% 3.58/0.99  
% 3.58/0.99  fof(f68,plain,(
% 3.58/0.99    ( ! [X0,X8,X1] : (r2_hidden(sK6(X0,X1,X8),X0) | ~r2_hidden(X8,k2_zfmisc_1(X0,X1))) )),
% 3.58/0.99    inference(equality_resolution,[],[f49])).
% 3.58/0.99  
% 3.58/0.99  fof(f62,plain,(
% 3.58/0.99    ~r1_tarski(sK9,sK11) | ~r1_tarski(sK8,sK10)),
% 3.58/0.99    inference(cnf_transformation,[],[f36])).
% 3.58/0.99  
% 3.58/0.99  cnf(c_21,plain,
% 3.58/0.99      ( r2_hidden(X0,X1)
% 3.58/0.99      | ~ r2_hidden(k4_tarski(X0,X2),k2_zfmisc_1(X1,X3)) ),
% 3.58/0.99      inference(cnf_transformation,[],[f57]) ).
% 3.58/0.99  
% 3.58/0.99  cnf(c_2,plain,
% 3.58/0.99      ( ~ r2_hidden(X0,X1) | r2_hidden(X0,X2) | ~ r1_tarski(X1,X2) ),
% 3.58/0.99      inference(cnf_transformation,[],[f37]) ).
% 3.58/0.99  
% 3.58/0.99  cnf(c_24,negated_conjecture,
% 3.58/0.99      ( r1_tarski(k2_zfmisc_1(sK8,sK9),k2_zfmisc_1(sK10,sK11)) ),
% 3.58/0.99      inference(cnf_transformation,[],[f60]) ).
% 3.58/0.99  
% 3.58/0.99  cnf(c_1826,plain,
% 3.58/0.99      ( r2_hidden(X0,k2_zfmisc_1(sK10,sK11))
% 3.58/0.99      | ~ r2_hidden(X0,k2_zfmisc_1(sK8,sK9)) ),
% 3.58/0.99      inference(resolution,[status(thm)],[c_2,c_24]) ).
% 3.58/0.99  
% 3.58/0.99  cnf(c_2154,plain,
% 3.58/0.99      ( r2_hidden(X0,sK10)
% 3.58/0.99      | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(sK8,sK9)) ),
% 3.58/0.99      inference(resolution,[status(thm)],[c_21,c_1826]) ).
% 3.58/0.99  
% 3.58/0.99  cnf(c_19,plain,
% 3.58/0.99      ( ~ r2_hidden(X0,X1)
% 3.58/0.99      | ~ r2_hidden(X2,X3)
% 3.58/0.99      | r2_hidden(k4_tarski(X2,X0),k2_zfmisc_1(X3,X1)) ),
% 3.58/0.99      inference(cnf_transformation,[],[f59]) ).
% 3.58/0.99  
% 3.58/0.99  cnf(c_3525,plain,
% 3.58/0.99      ( r2_hidden(X0,sK10) | ~ r2_hidden(X0,sK8) | ~ r2_hidden(X1,sK9) ),
% 3.58/0.99      inference(resolution,[status(thm)],[c_2154,c_19]) ).
% 3.58/0.99  
% 3.58/0.99  cnf(c_1,plain,
% 3.58/0.99      ( r2_hidden(sK0(X0,X1),X0) | r1_tarski(X0,X1) ),
% 3.58/0.99      inference(cnf_transformation,[],[f38]) ).
% 3.58/0.99  
% 3.58/0.99  cnf(c_4668,plain,
% 3.58/0.99      ( r2_hidden(X0,sK10) | ~ r2_hidden(X0,sK8) | r1_tarski(sK9,X1) ),
% 3.58/0.99      inference(resolution,[status(thm)],[c_3525,c_1]) ).
% 3.58/0.99  
% 3.58/0.99  cnf(c_23,negated_conjecture,
% 3.58/0.99      ( k1_xboole_0 != k2_zfmisc_1(sK8,sK9) ),
% 3.58/0.99      inference(cnf_transformation,[],[f61]) ).
% 3.58/0.99  
% 3.58/0.99  cnf(c_9,plain,
% 3.58/0.99      ( r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) != X0 ),
% 3.58/0.99      inference(cnf_transformation,[],[f48]) ).
% 3.58/0.99  
% 3.58/0.99  cnf(c_60,plain,
% 3.58/0.99      ( r1_xboole_0(k1_xboole_0,k1_xboole_0)
% 3.58/0.99      | k4_xboole_0(k1_xboole_0,k1_xboole_0) != k1_xboole_0 ),
% 3.58/0.99      inference(instantiation,[status(thm)],[c_9]) ).
% 3.58/0.99  
% 3.58/0.99  cnf(c_8,plain,
% 3.58/0.99      ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
% 3.58/0.99      inference(cnf_transformation,[],[f45]) ).
% 3.58/0.99  
% 3.58/0.99  cnf(c_62,plain,
% 3.58/0.99      ( k4_xboole_0(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
% 3.58/0.99      inference(instantiation,[status(thm)],[c_8]) ).
% 3.58/0.99  
% 3.58/0.99  cnf(c_630,plain,( X0 = X0 ),theory(equality) ).
% 3.58/0.99  
% 3.58/0.99  cnf(c_643,plain,
% 3.58/0.99      ( k1_xboole_0 = k1_xboole_0 ),
% 3.58/0.99      inference(instantiation,[status(thm)],[c_630]) ).
% 3.58/0.99  
% 3.58/0.99  cnf(c_6,plain,
% 3.58/0.99      ( r2_hidden(sK2(X0),X0) | k1_xboole_0 = X0 ),
% 3.58/0.99      inference(cnf_transformation,[],[f43]) ).
% 3.58/0.99  
% 3.58/0.99  cnf(c_1314,plain,
% 3.58/0.99      ( r2_hidden(sK2(k2_zfmisc_1(sK8,sK9)),k2_zfmisc_1(sK8,sK9))
% 3.58/0.99      | k1_xboole_0 = k2_zfmisc_1(sK8,sK9) ),
% 3.58/0.99      inference(instantiation,[status(thm)],[c_6]) ).
% 3.58/0.99  
% 3.58/0.99  cnf(c_0,plain,
% 3.58/0.99      ( ~ r2_hidden(sK0(X0,X1),X1) | r1_tarski(X0,X1) ),
% 3.58/0.99      inference(cnf_transformation,[],[f39]) ).
% 3.58/0.99  
% 3.58/0.99  cnf(c_1370,plain,
% 3.58/0.99      ( r1_tarski(X0,X0) ),
% 3.58/0.99      inference(resolution,[status(thm)],[c_0,c_1]) ).
% 3.58/0.99  
% 3.58/0.99  cnf(c_1372,plain,
% 3.58/0.99      ( r1_tarski(k1_xboole_0,k1_xboole_0) ),
% 3.58/0.99      inference(instantiation,[status(thm)],[c_1370]) ).
% 3.58/0.99  
% 3.58/0.99  cnf(c_17,plain,
% 3.58/0.99      ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
% 3.58/0.99      | r2_hidden(sK7(X1,X2,X0),X2) ),
% 3.58/0.99      inference(cnf_transformation,[],[f67]) ).
% 3.58/0.99  
% 3.58/0.99  cnf(c_1403,plain,
% 3.58/0.99      ( r2_hidden(sK7(sK8,sK9,sK2(k2_zfmisc_1(sK8,sK9))),sK9)
% 3.58/0.99      | ~ r2_hidden(sK2(k2_zfmisc_1(sK8,sK9)),k2_zfmisc_1(sK8,sK9)) ),
% 3.58/0.99      inference(instantiation,[status(thm)],[c_17]) ).
% 3.58/0.99  
% 3.58/0.99  cnf(c_1572,plain,
% 3.58/0.99      ( r2_hidden(sK7(sK8,sK9,sK2(k2_zfmisc_1(sK8,sK9))),X0)
% 3.58/0.99      | ~ r2_hidden(sK7(sK8,sK9,sK2(k2_zfmisc_1(sK8,sK9))),sK9)
% 3.58/0.99      | ~ r1_tarski(sK9,X0) ),
% 3.58/0.99      inference(instantiation,[status(thm)],[c_2]) ).
% 3.58/0.99  
% 3.58/0.99  cnf(c_1574,plain,
% 3.58/0.99      ( ~ r2_hidden(sK7(sK8,sK9,sK2(k2_zfmisc_1(sK8,sK9))),sK9)
% 3.58/0.99      | r2_hidden(sK7(sK8,sK9,sK2(k2_zfmisc_1(sK8,sK9))),k1_xboole_0)
% 3.58/0.99      | ~ r1_tarski(sK9,k1_xboole_0) ),
% 3.58/0.99      inference(instantiation,[status(thm)],[c_1572]) ).
% 3.58/0.99  
% 3.58/0.99  cnf(c_632,plain,
% 3.58/0.99      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,X3) | X2 != X0 | X3 != X1 ),
% 3.58/0.99      theory(equality) ).
% 3.58/0.99  
% 3.58/0.99  cnf(c_1616,plain,
% 3.58/0.99      ( ~ r1_tarski(X0,X1) | r1_tarski(sK9,X2) | X2 != X1 | sK9 != X0 ),
% 3.58/0.99      inference(instantiation,[status(thm)],[c_632]) ).
% 3.58/0.99  
% 3.58/0.99  cnf(c_1618,plain,
% 3.58/0.99      ( r1_tarski(sK9,k1_xboole_0)
% 3.58/0.99      | ~ r1_tarski(k1_xboole_0,k1_xboole_0)
% 3.58/0.99      | sK9 != k1_xboole_0
% 3.58/0.99      | k1_xboole_0 != k1_xboole_0 ),
% 3.58/0.99      inference(instantiation,[status(thm)],[c_1616]) ).
% 3.58/0.99  
% 3.58/0.99  cnf(c_3,plain,
% 3.58/0.99      ( ~ r1_xboole_0(X0,X1) | ~ r2_hidden(X2,X1) | ~ r2_hidden(X2,X0) ),
% 3.58/0.99      inference(cnf_transformation,[],[f42]) ).
% 3.58/0.99  
% 3.58/0.99  cnf(c_2504,plain,
% 3.58/0.99      ( ~ r1_xboole_0(X0,X1)
% 3.58/0.99      | ~ r2_hidden(sK7(sK8,sK9,sK2(k2_zfmisc_1(sK8,sK9))),X0)
% 3.58/0.99      | ~ r2_hidden(sK7(sK8,sK9,sK2(k2_zfmisc_1(sK8,sK9))),X1) ),
% 3.58/0.99      inference(instantiation,[status(thm)],[c_3]) ).
% 3.58/0.99  
% 3.58/0.99  cnf(c_2506,plain,
% 3.58/0.99      ( ~ r1_xboole_0(k1_xboole_0,k1_xboole_0)
% 3.58/0.99      | ~ r2_hidden(sK7(sK8,sK9,sK2(k2_zfmisc_1(sK8,sK9))),k1_xboole_0) ),
% 3.58/0.99      inference(instantiation,[status(thm)],[c_2504]) ).
% 3.58/0.99  
% 3.58/0.99  cnf(c_631,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 3.58/0.99  
% 3.58/0.99  cnf(c_2469,plain,
% 3.58/0.99      ( X0 != X1 | X1 = X0 ),
% 3.58/0.99      inference(resolution,[status(thm)],[c_631,c_630]) ).
% 3.58/0.99  
% 3.58/0.99  cnf(c_2475,plain,
% 3.58/0.99      ( r2_hidden(sK2(X0),X0) | X0 = k1_xboole_0 ),
% 3.58/0.99      inference(resolution,[status(thm)],[c_2469,c_6]) ).
% 3.58/0.99  
% 3.58/0.99  cnf(c_4681,plain,
% 3.58/0.99      ( r2_hidden(X0,sK10) | ~ r2_hidden(X0,sK8) | sK9 = k1_xboole_0 ),
% 3.58/0.99      inference(resolution,[status(thm)],[c_3525,c_2475]) ).
% 3.58/0.99  
% 3.58/0.99  cnf(c_7079,plain,
% 3.58/0.99      ( ~ r2_hidden(X0,sK8) | r2_hidden(X0,sK10) ),
% 3.58/0.99      inference(global_propositional_subsumption,
% 3.58/0.99                [status(thm)],
% 3.58/0.99                [c_4668,c_23,c_60,c_62,c_643,c_1314,c_1372,c_1403,c_1574,
% 3.58/0.99                 c_1618,c_2506,c_4681]) ).
% 3.58/0.99  
% 3.58/0.99  cnf(c_7080,plain,
% 3.58/0.99      ( r2_hidden(X0,sK10) | ~ r2_hidden(X0,sK8) ),
% 3.58/0.99      inference(renaming,[status(thm)],[c_7079]) ).
% 3.58/0.99  
% 3.58/0.99  cnf(c_7302,plain,
% 3.58/0.99      ( ~ r2_hidden(sK0(X0,sK10),sK8) | r1_tarski(X0,sK10) ),
% 3.58/0.99      inference(resolution,[status(thm)],[c_7080,c_0]) ).
% 3.58/0.99  
% 3.58/0.99  cnf(c_12975,plain,
% 3.58/0.99      ( r1_tarski(sK8,sK10) ),
% 3.58/0.99      inference(resolution,[status(thm)],[c_7302,c_1]) ).
% 3.58/0.99  
% 3.58/0.99  cnf(c_20,plain,
% 3.58/0.99      ( r2_hidden(X0,X1)
% 3.58/0.99      | ~ r2_hidden(k4_tarski(X2,X0),k2_zfmisc_1(X3,X1)) ),
% 3.58/0.99      inference(cnf_transformation,[],[f58]) ).
% 3.58/0.99  
% 3.58/0.99  cnf(c_2014,plain,
% 3.58/0.99      ( r2_hidden(X0,sK11)
% 3.58/0.99      | ~ r2_hidden(k4_tarski(X1,X0),k2_zfmisc_1(sK8,sK9)) ),
% 3.58/0.99      inference(resolution,[status(thm)],[c_20,c_1826]) ).
% 3.58/0.99  
% 3.58/0.99  cnf(c_3516,plain,
% 3.58/0.99      ( ~ r2_hidden(X0,sK8) | r2_hidden(X1,sK11) | ~ r2_hidden(X1,sK9) ),
% 3.58/0.99      inference(resolution,[status(thm)],[c_2014,c_19]) ).
% 3.58/0.99  
% 3.58/0.99  cnf(c_4624,plain,
% 3.58/0.99      ( r2_hidden(X0,sK11) | ~ r2_hidden(X0,sK9) | r1_tarski(sK8,X1) ),
% 3.58/0.99      inference(resolution,[status(thm)],[c_3516,c_1]) ).
% 3.58/0.99  
% 3.58/0.99  cnf(c_18,plain,
% 3.58/0.99      ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
% 3.58/0.99      | r2_hidden(sK6(X1,X2,X0),X1) ),
% 3.58/0.99      inference(cnf_transformation,[],[f68]) ).
% 3.58/0.99  
% 3.58/0.99  cnf(c_1402,plain,
% 3.58/0.99      ( r2_hidden(sK6(sK8,sK9,sK2(k2_zfmisc_1(sK8,sK9))),sK8)
% 3.58/0.99      | ~ r2_hidden(sK2(k2_zfmisc_1(sK8,sK9)),k2_zfmisc_1(sK8,sK9)) ),
% 3.58/0.99      inference(instantiation,[status(thm)],[c_18]) ).
% 3.58/0.99  
% 3.58/0.99  cnf(c_1541,plain,
% 3.58/0.99      ( ~ r1_xboole_0(sK8,X0)
% 3.58/0.99      | ~ r2_hidden(sK6(sK8,sK9,sK2(k2_zfmisc_1(sK8,sK9))),X0)
% 3.58/0.99      | ~ r2_hidden(sK6(sK8,sK9,sK2(k2_zfmisc_1(sK8,sK9))),sK8) ),
% 3.58/0.99      inference(instantiation,[status(thm)],[c_3]) ).
% 3.58/0.99  
% 3.58/0.99  cnf(c_1543,plain,
% 3.58/0.99      ( ~ r1_xboole_0(sK8,k1_xboole_0)
% 3.58/0.99      | ~ r2_hidden(sK6(sK8,sK9,sK2(k2_zfmisc_1(sK8,sK9))),sK8)
% 3.58/0.99      | ~ r2_hidden(sK6(sK8,sK9,sK2(k2_zfmisc_1(sK8,sK9))),k1_xboole_0) ),
% 3.58/0.99      inference(instantiation,[status(thm)],[c_1541]) ).
% 3.58/0.99  
% 3.58/0.99  cnf(c_1547,plain,
% 3.58/0.99      ( r2_hidden(sK6(sK8,sK9,sK2(k2_zfmisc_1(sK8,sK9))),X0)
% 3.58/0.99      | ~ r2_hidden(sK6(sK8,sK9,sK2(k2_zfmisc_1(sK8,sK9))),sK8)
% 3.58/0.99      | ~ r1_tarski(sK8,X0) ),
% 3.58/0.99      inference(instantiation,[status(thm)],[c_2]) ).
% 3.58/0.99  
% 3.58/0.99  cnf(c_1549,plain,
% 3.58/0.99      ( ~ r2_hidden(sK6(sK8,sK9,sK2(k2_zfmisc_1(sK8,sK9))),sK8)
% 3.58/0.99      | r2_hidden(sK6(sK8,sK9,sK2(k2_zfmisc_1(sK8,sK9))),k1_xboole_0)
% 3.58/0.99      | ~ r1_tarski(sK8,k1_xboole_0) ),
% 3.58/0.99      inference(instantiation,[status(thm)],[c_1547]) ).
% 3.58/0.99  
% 3.58/0.99  cnf(c_2088,plain,
% 3.58/0.99      ( ~ r1_tarski(X0,X1) | r1_tarski(sK8,X2) | X2 != X1 | sK8 != X0 ),
% 3.58/0.99      inference(instantiation,[status(thm)],[c_632]) ).
% 3.58/0.99  
% 3.58/0.99  cnf(c_2090,plain,
% 3.58/0.99      ( r1_tarski(sK8,k1_xboole_0)
% 3.58/0.99      | ~ r1_tarski(k1_xboole_0,k1_xboole_0)
% 3.58/0.99      | sK8 != k1_xboole_0
% 3.58/0.99      | k1_xboole_0 != k1_xboole_0 ),
% 3.58/0.99      inference(instantiation,[status(thm)],[c_2088]) ).
% 3.58/0.99  
% 3.58/0.99  cnf(c_2100,plain,
% 3.58/0.99      ( k4_xboole_0(sK8,k1_xboole_0) = sK8 ),
% 3.58/0.99      inference(instantiation,[status(thm)],[c_8]) ).
% 3.58/0.99  
% 3.58/0.99  cnf(c_4637,plain,
% 3.58/0.99      ( r2_hidden(X0,sK11) | ~ r2_hidden(X0,sK9) | sK8 = k1_xboole_0 ),
% 3.58/0.99      inference(resolution,[status(thm)],[c_3516,c_2475]) ).
% 3.58/0.99  
% 3.58/0.99  cnf(c_5393,plain,
% 3.58/0.99      ( r1_xboole_0(sK8,X0) | k4_xboole_0(sK8,X0) != sK8 ),
% 3.58/0.99      inference(instantiation,[status(thm)],[c_9]) ).
% 3.58/0.99  
% 3.58/0.99  cnf(c_5395,plain,
% 3.58/0.99      ( r1_xboole_0(sK8,k1_xboole_0)
% 3.58/0.99      | k4_xboole_0(sK8,k1_xboole_0) != sK8 ),
% 3.58/0.99      inference(instantiation,[status(thm)],[c_5393]) ).
% 3.58/0.99  
% 3.58/0.99  cnf(c_6413,plain,
% 3.58/0.99      ( ~ r2_hidden(X0,sK9) | r2_hidden(X0,sK11) ),
% 3.58/0.99      inference(global_propositional_subsumption,
% 3.58/0.99                [status(thm)],
% 3.58/0.99                [c_4624,c_23,c_643,c_1314,c_1372,c_1402,c_1543,c_1549,
% 3.58/0.99                 c_2090,c_2100,c_4637,c_5395]) ).
% 3.58/0.99  
% 3.58/0.99  cnf(c_6414,plain,
% 3.58/0.99      ( r2_hidden(X0,sK11) | ~ r2_hidden(X0,sK9) ),
% 3.58/0.99      inference(renaming,[status(thm)],[c_6413]) ).
% 3.58/0.99  
% 3.58/0.99  cnf(c_6795,plain,
% 3.58/0.99      ( ~ r2_hidden(sK0(X0,sK11),sK9) | r1_tarski(X0,sK11) ),
% 3.58/0.99      inference(resolution,[status(thm)],[c_6414,c_0]) ).
% 3.58/0.99  
% 3.58/0.99  cnf(c_12967,plain,
% 3.58/0.99      ( r1_tarski(sK9,sK11) ),
% 3.58/0.99      inference(resolution,[status(thm)],[c_6795,c_1]) ).
% 3.58/0.99  
% 3.58/0.99  cnf(c_22,negated_conjecture,
% 3.58/0.99      ( ~ r1_tarski(sK8,sK10) | ~ r1_tarski(sK9,sK11) ),
% 3.58/0.99      inference(cnf_transformation,[],[f62]) ).
% 3.58/0.99  
% 3.58/0.99  cnf(contradiction,plain,
% 3.58/0.99      ( $false ),
% 3.58/0.99      inference(minisat,[status(thm)],[c_12975,c_12967,c_22]) ).
% 3.58/0.99  
% 3.58/0.99  
% 3.58/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 3.58/0.99  
% 3.58/0.99  ------                               Statistics
% 3.58/0.99  
% 3.58/0.99  ------ Selected
% 3.58/0.99  
% 3.58/0.99  total_time:                             0.387
% 3.58/0.99  
%------------------------------------------------------------------------------
