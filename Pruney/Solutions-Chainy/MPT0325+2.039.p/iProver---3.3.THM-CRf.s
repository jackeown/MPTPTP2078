%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:37:52 EST 2020

% Result     : Theorem 3.46s
% Output     : CNFRefutation 3.46s
% Verified   : 
% Statistics : Number of formulae       :  101 ( 290 expanded)
%              Number of clauses        :   54 (  90 expanded)
%              Number of leaves         :   16 (  70 expanded)
%              Depth                    :   14
%              Number of atoms          :  348 (1167 expanded)
%              Number of equality atoms :   83 ( 201 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal clause size      :   18 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f5,axiom,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
    <=> ( r2_hidden(X1,X3)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
        | ~ r2_hidden(X1,X3)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X3)
          & r2_hidden(X0,X2) )
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f28,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
        | ~ r2_hidden(X1,X3)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X3)
          & r2_hidden(X0,X2) )
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ) ),
    inference(flattening,[],[f27])).

fof(f45,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X0,X2)
      | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f9,plain,(
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
    inference(nnf_transformation,[],[f9])).

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

fof(f31,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f7,conjecture,(
    ! [X0,X1,X2,X3] :
      ( r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3))
     => ( ( r1_tarski(X1,X3)
          & r1_tarski(X0,X2) )
        | k1_xboole_0 = k2_zfmisc_1(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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

fof(f29,plain,
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

fof(f30,plain,
    ( ( ~ r1_tarski(sK8,sK10)
      | ~ r1_tarski(sK7,sK9) )
    & k1_xboole_0 != k2_zfmisc_1(sK7,sK8)
    & r1_tarski(k2_zfmisc_1(sK7,sK8),k2_zfmisc_1(sK9,sK10)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7,sK8,sK9,sK10])],[f13,f29])).

fof(f49,plain,(
    r1_tarski(k2_zfmisc_1(sK7,sK8),k2_zfmisc_1(sK9,sK10)) ),
    inference(cnf_transformation,[],[f30])).

fof(f47,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
      | ~ r2_hidden(X1,X3)
      | ~ r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( k2_zfmisc_1(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ? [X4,X5] :
              ( k4_tarski(X4,X5) = X3
              & r2_hidden(X5,X1)
              & r2_hidden(X4,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
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

fof(f22,plain,(
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
    inference(rectify,[],[f21])).

fof(f25,plain,(
    ! [X8,X1,X0] :
      ( ? [X11,X12] :
          ( k4_tarski(X11,X12) = X8
          & r2_hidden(X12,X1)
          & r2_hidden(X11,X0) )
     => ( k4_tarski(sK5(X0,X1,X8),sK6(X0,X1,X8)) = X8
        & r2_hidden(sK6(X0,X1,X8),X1)
        & r2_hidden(sK5(X0,X1,X8),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X6,X7] :
          ( k4_tarski(X6,X7) = X3
          & r2_hidden(X7,X1)
          & r2_hidden(X6,X0) )
     => ( k4_tarski(sK3(X0,X1,X2),sK4(X0,X1,X2)) = X3
        & r2_hidden(sK4(X0,X1,X2),X1)
        & r2_hidden(sK3(X0,X1,X2),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
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

fof(f26,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5,sK6])],[f22,f25,f24,f23])).

fof(f38,plain,(
    ! [X2,X0,X8,X1] :
      ( r2_hidden(sK6(X0,X1,X8),X1)
      | ~ r2_hidden(X8,X2)
      | k2_zfmisc_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f55,plain,(
    ! [X0,X8,X1] :
      ( r2_hidden(sK6(X0,X1,X8),X1)
      | ~ r2_hidden(X8,k2_zfmisc_1(X0,X1)) ) ),
    inference(equality_resolution,[],[f38])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
        <=> r2_hidden(X2,X1) )
     => X0 = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f10,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ? [X2] :
          ( r2_hidden(X2,X0)
        <~> r2_hidden(X2,X1) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f18,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ? [X2] :
          ( ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
          & ( r2_hidden(X2,X1)
            | r2_hidden(X2,X0) ) ) ) ),
    inference(nnf_transformation,[],[f10])).

fof(f19,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
          & ( r2_hidden(X2,X1)
            | r2_hidden(X2,X0) ) )
     => ( ( ~ r2_hidden(sK1(X0,X1),X1)
          | ~ r2_hidden(sK1(X0,X1),X0) )
        & ( r2_hidden(sK1(X0,X1),X1)
          | r2_hidden(sK1(X0,X1),X0) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ( ( ~ r2_hidden(sK1(X0,X1),X1)
          | ~ r2_hidden(sK1(X0,X1),X0) )
        & ( r2_hidden(sK1(X0,X1),X1)
          | r2_hidden(sK1(X0,X1),X0) ) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f18,f19])).

fof(f34,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | r2_hidden(sK1(X0,X1),X1)
      | r2_hidden(sK1(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f3,axiom,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f3])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ~ ( r2_hidden(X0,X2)
        & r1_xboole_0(k2_tarski(X0,X1),X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X0,X1,X2] :
      ( ~ r2_hidden(X0,X2)
      | ~ r1_xboole_0(k2_tarski(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X2)
      | ~ r1_xboole_0(k2_tarski(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f33,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK0(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( k2_zfmisc_1(X0,X1) = X2
      | r2_hidden(sK4(X0,X1,X2),X1)
      | r2_hidden(sK2(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f46,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X1,X3)
      | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f50,plain,(
    k1_xboole_0 != k2_zfmisc_1(sK7,sK8) ),
    inference(cnf_transformation,[],[f30])).

fof(f37,plain,(
    ! [X2,X0,X8,X1] :
      ( r2_hidden(sK5(X0,X1,X8),X0)
      | ~ r2_hidden(X8,X2)
      | k2_zfmisc_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f56,plain,(
    ! [X0,X8,X1] :
      ( r2_hidden(sK5(X0,X1,X8),X0)
      | ~ r2_hidden(X8,k2_zfmisc_1(X0,X1)) ) ),
    inference(equality_resolution,[],[f37])).

fof(f32,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK0(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f51,plain,
    ( ~ r1_tarski(sK8,sK10)
    | ~ r1_tarski(sK7,sK9) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_16,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(k4_tarski(X0,X2),k2_zfmisc_1(X1,X3)) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_2,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | ~ r1_tarski(X1,X2) ),
    inference(cnf_transformation,[],[f31])).

cnf(c_20,negated_conjecture,
    ( r1_tarski(k2_zfmisc_1(sK7,sK8),k2_zfmisc_1(sK9,sK10)) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_1061,plain,
    ( r2_hidden(X0,k2_zfmisc_1(sK9,sK10))
    | ~ r2_hidden(X0,k2_zfmisc_1(sK7,sK8)) ),
    inference(resolution,[status(thm)],[c_2,c_20])).

cnf(c_1180,plain,
    ( r2_hidden(X0,sK9)
    | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(sK7,sK8)) ),
    inference(resolution,[status(thm)],[c_16,c_1061])).

cnf(c_14,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X2,X3)
    | r2_hidden(k4_tarski(X2,X0),k2_zfmisc_1(X3,X1)) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_2950,plain,
    ( r2_hidden(X0,sK9)
    | ~ r2_hidden(X0,sK7)
    | ~ r2_hidden(X1,sK8) ),
    inference(resolution,[status(thm)],[c_1180,c_14])).

cnf(c_12,plain,
    ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
    | r2_hidden(sK6(X1,X2,X0),X2) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_3208,plain,
    ( ~ r2_hidden(X0,k2_zfmisc_1(X1,sK8))
    | r2_hidden(X2,sK9)
    | ~ r2_hidden(X2,sK7) ),
    inference(resolution,[status(thm)],[c_2950,c_12])).

cnf(c_4,plain,
    ( r2_hidden(sK1(X0,X1),X1)
    | r2_hidden(sK1(X0,X1),X0)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f34])).

cnf(c_5,plain,
    ( r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_17,plain,
    ( ~ r1_xboole_0(k2_tarski(X0,X1),X2)
    | ~ r2_hidden(X0,X2) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_224,plain,
    ( ~ r2_hidden(X0,X1)
    | k2_tarski(X0,X2) != X3
    | k1_xboole_0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_5,c_17])).

cnf(c_225,plain,
    ( ~ r2_hidden(X0,k1_xboole_0) ),
    inference(unflattening,[status(thm)],[c_224])).

cnf(c_1337,plain,
    ( r2_hidden(sK1(k1_xboole_0,X0),X0)
    | X0 = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_4,c_225])).

cnf(c_4147,plain,
    ( r2_hidden(X0,sK9)
    | ~ r2_hidden(X0,sK7)
    | k2_zfmisc_1(X1,sK8) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_3208,c_1337])).

cnf(c_0,plain,
    ( ~ r2_hidden(sK0(X0,X1),X1)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_7767,plain,
    ( ~ r2_hidden(sK0(X0,sK9),sK7)
    | r1_tarski(X0,sK9)
    | k2_zfmisc_1(X1,sK8) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_4147,c_0])).

cnf(c_7769,plain,
    ( ~ r2_hidden(sK0(sK7,sK9),sK7)
    | r1_tarski(sK7,sK9)
    | k2_zfmisc_1(sK7,sK8) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_7767])).

cnf(c_8,plain,
    ( r2_hidden(sK4(X0,X1,X2),X1)
    | r2_hidden(sK2(X0,X1,X2),X2)
    | k2_zfmisc_1(X0,X1) = X2 ),
    inference(cnf_transformation,[],[f42])).

cnf(c_15,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(k4_tarski(X2,X0),k2_zfmisc_1(X3,X1)) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_1170,plain,
    ( r2_hidden(X0,sK10)
    | ~ r2_hidden(k4_tarski(X1,X0),k2_zfmisc_1(sK7,sK8)) ),
    inference(resolution,[status(thm)],[c_15,c_1061])).

cnf(c_2941,plain,
    ( ~ r2_hidden(X0,sK7)
    | r2_hidden(X1,sK10)
    | ~ r2_hidden(X1,sK8) ),
    inference(resolution,[status(thm)],[c_1170,c_14])).

cnf(c_4284,plain,
    ( r2_hidden(X0,sK10)
    | ~ r2_hidden(X0,sK8)
    | r2_hidden(sK4(X1,X2,sK7),X2)
    | k2_zfmisc_1(X1,X2) = sK7 ),
    inference(resolution,[status(thm)],[c_8,c_2941])).

cnf(c_19,negated_conjecture,
    ( k1_xboole_0 != k2_zfmisc_1(sK7,sK8) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_359,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_370,plain,
    ( sK7 = sK7 ),
    inference(instantiation,[status(thm)],[c_359])).

cnf(c_859,plain,
    ( r2_hidden(sK1(k2_zfmisc_1(sK7,sK8),k1_xboole_0),k2_zfmisc_1(sK7,sK8))
    | r2_hidden(sK1(k2_zfmisc_1(sK7,sK8),k1_xboole_0),k1_xboole_0)
    | k1_xboole_0 = k2_zfmisc_1(sK7,sK8) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_13,plain,
    ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
    | r2_hidden(sK5(X1,X2,X0),X1) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_941,plain,
    ( r2_hidden(sK5(sK7,sK8,sK1(k2_zfmisc_1(sK7,sK8),k1_xboole_0)),sK7)
    | ~ r2_hidden(sK1(k2_zfmisc_1(sK7,sK8),k1_xboole_0),k2_zfmisc_1(sK7,sK8)) ),
    inference(instantiation,[status(thm)],[c_13])).

cnf(c_1,plain,
    ( r2_hidden(sK0(X0,X1),X0)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_961,plain,
    ( r1_tarski(X0,X0) ),
    inference(resolution,[status(thm)],[c_0,c_1])).

cnf(c_963,plain,
    ( r1_tarski(sK7,sK7) ),
    inference(instantiation,[status(thm)],[c_961])).

cnf(c_980,plain,
    ( k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_359])).

cnf(c_1040,plain,
    ( ~ r2_hidden(sK1(k2_zfmisc_1(sK7,sK8),k1_xboole_0),k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_225])).

cnf(c_3184,plain,
    ( r2_hidden(X0,sK10)
    | ~ r2_hidden(X0,sK8)
    | sK7 = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_2941,c_1337])).

cnf(c_360,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_981,plain,
    ( X0 != X1
    | k1_xboole_0 != X1
    | k1_xboole_0 = X0 ),
    inference(instantiation,[status(thm)],[c_360])).

cnf(c_3419,plain,
    ( X0 != k1_xboole_0
    | k1_xboole_0 = X0
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_981])).

cnf(c_3420,plain,
    ( sK7 != k1_xboole_0
    | k1_xboole_0 = sK7
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_3419])).

cnf(c_361,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_4157,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(sK7,k1_xboole_0)
    | sK7 != X0
    | k1_xboole_0 != X1 ),
    inference(instantiation,[status(thm)],[c_361])).

cnf(c_4159,plain,
    ( ~ r1_tarski(sK7,sK7)
    | r1_tarski(sK7,k1_xboole_0)
    | sK7 != sK7
    | k1_xboole_0 != sK7 ),
    inference(instantiation,[status(thm)],[c_4157])).

cnf(c_1365,plain,
    ( r2_hidden(sK5(sK7,sK8,sK1(k2_zfmisc_1(sK7,sK8),k1_xboole_0)),X0)
    | ~ r2_hidden(sK5(sK7,sK8,sK1(k2_zfmisc_1(sK7,sK8),k1_xboole_0)),sK7)
    | ~ r1_tarski(sK7,X0) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_5097,plain,
    ( ~ r2_hidden(sK5(sK7,sK8,sK1(k2_zfmisc_1(sK7,sK8),k1_xboole_0)),sK7)
    | r2_hidden(sK5(sK7,sK8,sK1(k2_zfmisc_1(sK7,sK8),k1_xboole_0)),k1_xboole_0)
    | ~ r1_tarski(sK7,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_1365])).

cnf(c_5098,plain,
    ( ~ r2_hidden(sK5(sK7,sK8,sK1(k2_zfmisc_1(sK7,sK8),k1_xboole_0)),k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_225])).

cnf(c_5653,plain,
    ( r2_hidden(X0,sK10)
    | ~ r2_hidden(X0,sK8) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4284,c_19,c_370,c_859,c_941,c_963,c_980,c_1040,c_3184,c_3420,c_4159,c_5097,c_5098])).

cnf(c_5671,plain,
    ( ~ r2_hidden(sK0(X0,sK10),sK8)
    | r1_tarski(X0,sK10) ),
    inference(resolution,[status(thm)],[c_5653,c_0])).

cnf(c_6803,plain,
    ( r1_tarski(sK8,sK10) ),
    inference(resolution,[status(thm)],[c_5671,c_1])).

cnf(c_857,plain,
    ( k2_zfmisc_1(sK7,sK8) != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = k2_zfmisc_1(sK7,sK8) ),
    inference(instantiation,[status(thm)],[c_360])).

cnf(c_979,plain,
    ( k2_zfmisc_1(sK7,sK8) != k1_xboole_0
    | k1_xboole_0 = k2_zfmisc_1(sK7,sK8)
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_857])).

cnf(c_909,plain,
    ( r2_hidden(sK0(sK7,sK9),sK7)
    | r1_tarski(sK7,sK9) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_18,negated_conjecture,
    ( ~ r1_tarski(sK7,sK9)
    | ~ r1_tarski(sK8,sK10) ),
    inference(cnf_transformation,[],[f51])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_7769,c_6803,c_980,c_979,c_909,c_18,c_19])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.33  % Computer   : n001.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 15:49:00 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 3.46/1.00  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.46/1.00  
% 3.46/1.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.46/1.00  
% 3.46/1.00  ------  iProver source info
% 3.46/1.00  
% 3.46/1.00  git: date: 2020-06-30 10:37:57 +0100
% 3.46/1.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.46/1.00  git: non_committed_changes: false
% 3.46/1.00  git: last_make_outside_of_git: false
% 3.46/1.00  
% 3.46/1.00  ------ 
% 3.46/1.00  ------ Parsing...
% 3.46/1.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.46/1.00  
% 3.46/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 3.46/1.00  
% 3.46/1.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.46/1.00  
% 3.46/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.46/1.00  ------ Proving...
% 3.46/1.00  ------ Problem Properties 
% 3.46/1.00  
% 3.46/1.00  
% 3.46/1.00  clauses                                 19
% 3.46/1.00  conjectures                             3
% 3.46/1.00  EPR                                     3
% 3.46/1.00  Horn                                    14
% 3.46/1.00  unary                                   3
% 3.46/1.00  binary                                  8
% 3.46/1.00  lits                                    45
% 3.46/1.00  lits eq                                 10
% 3.46/1.00  fd_pure                                 0
% 3.46/1.00  fd_pseudo                               0
% 3.46/1.00  fd_cond                                 0
% 3.46/1.00  fd_pseudo_cond                          6
% 3.46/1.00  AC symbols                              0
% 3.46/1.00  
% 3.46/1.00  ------ Input Options Time Limit: Unbounded
% 3.46/1.00  
% 3.46/1.00  
% 3.46/1.00  ------ 
% 3.46/1.00  Current options:
% 3.46/1.00  ------ 
% 3.46/1.00  
% 3.46/1.00  
% 3.46/1.00  
% 3.46/1.00  
% 3.46/1.00  ------ Proving...
% 3.46/1.00  
% 3.46/1.00  
% 3.46/1.00  % SZS status Theorem for theBenchmark.p
% 3.46/1.00  
% 3.46/1.00  % SZS output start CNFRefutation for theBenchmark.p
% 3.46/1.00  
% 3.46/1.00  fof(f5,axiom,(
% 3.46/1.00    ! [X0,X1,X2,X3] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) <=> (r2_hidden(X1,X3) & r2_hidden(X0,X2)))),
% 3.46/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.46/1.00  
% 3.46/1.00  fof(f27,plain,(
% 3.46/1.00    ! [X0,X1,X2,X3] : ((r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | (~r2_hidden(X1,X3) | ~r2_hidden(X0,X2))) & ((r2_hidden(X1,X3) & r2_hidden(X0,X2)) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))))),
% 3.46/1.00    inference(nnf_transformation,[],[f5])).
% 3.46/1.00  
% 3.46/1.00  fof(f28,plain,(
% 3.46/1.00    ! [X0,X1,X2,X3] : ((r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | ~r2_hidden(X1,X3) | ~r2_hidden(X0,X2)) & ((r2_hidden(X1,X3) & r2_hidden(X0,X2)) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))))),
% 3.46/1.00    inference(flattening,[],[f27])).
% 3.46/1.00  
% 3.46/1.00  fof(f45,plain,(
% 3.46/1.00    ( ! [X2,X0,X3,X1] : (r2_hidden(X0,X2) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))) )),
% 3.46/1.00    inference(cnf_transformation,[],[f28])).
% 3.46/1.00  
% 3.46/1.00  fof(f1,axiom,(
% 3.46/1.00    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 3.46/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.46/1.00  
% 3.46/1.00  fof(f9,plain,(
% 3.46/1.00    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 3.46/1.00    inference(ennf_transformation,[],[f1])).
% 3.46/1.00  
% 3.46/1.00  fof(f14,plain,(
% 3.46/1.00    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 3.46/1.00    inference(nnf_transformation,[],[f9])).
% 3.46/1.00  
% 3.46/1.00  fof(f15,plain,(
% 3.46/1.00    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 3.46/1.00    inference(rectify,[],[f14])).
% 3.46/1.00  
% 3.46/1.00  fof(f16,plain,(
% 3.46/1.00    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 3.46/1.00    introduced(choice_axiom,[])).
% 3.46/1.00  
% 3.46/1.00  fof(f17,plain,(
% 3.46/1.00    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 3.46/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f15,f16])).
% 3.46/1.00  
% 3.46/1.00  fof(f31,plain,(
% 3.46/1.00    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,X1)) )),
% 3.46/1.00    inference(cnf_transformation,[],[f17])).
% 3.46/1.00  
% 3.46/1.00  fof(f7,conjecture,(
% 3.46/1.00    ! [X0,X1,X2,X3] : (r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)) => ((r1_tarski(X1,X3) & r1_tarski(X0,X2)) | k1_xboole_0 = k2_zfmisc_1(X0,X1)))),
% 3.46/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.46/1.00  
% 3.46/1.00  fof(f8,negated_conjecture,(
% 3.46/1.00    ~! [X0,X1,X2,X3] : (r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)) => ((r1_tarski(X1,X3) & r1_tarski(X0,X2)) | k1_xboole_0 = k2_zfmisc_1(X0,X1)))),
% 3.46/1.00    inference(negated_conjecture,[],[f7])).
% 3.46/1.00  
% 3.46/1.00  fof(f12,plain,(
% 3.46/1.00    ? [X0,X1,X2,X3] : (((~r1_tarski(X1,X3) | ~r1_tarski(X0,X2)) & k1_xboole_0 != k2_zfmisc_1(X0,X1)) & r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)))),
% 3.46/1.00    inference(ennf_transformation,[],[f8])).
% 3.46/1.00  
% 3.46/1.00  fof(f13,plain,(
% 3.46/1.00    ? [X0,X1,X2,X3] : ((~r1_tarski(X1,X3) | ~r1_tarski(X0,X2)) & k1_xboole_0 != k2_zfmisc_1(X0,X1) & r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)))),
% 3.46/1.00    inference(flattening,[],[f12])).
% 3.46/1.00  
% 3.46/1.00  fof(f29,plain,(
% 3.46/1.00    ? [X0,X1,X2,X3] : ((~r1_tarski(X1,X3) | ~r1_tarski(X0,X2)) & k1_xboole_0 != k2_zfmisc_1(X0,X1) & r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3))) => ((~r1_tarski(sK8,sK10) | ~r1_tarski(sK7,sK9)) & k1_xboole_0 != k2_zfmisc_1(sK7,sK8) & r1_tarski(k2_zfmisc_1(sK7,sK8),k2_zfmisc_1(sK9,sK10)))),
% 3.46/1.00    introduced(choice_axiom,[])).
% 3.46/1.00  
% 3.46/1.00  fof(f30,plain,(
% 3.46/1.00    (~r1_tarski(sK8,sK10) | ~r1_tarski(sK7,sK9)) & k1_xboole_0 != k2_zfmisc_1(sK7,sK8) & r1_tarski(k2_zfmisc_1(sK7,sK8),k2_zfmisc_1(sK9,sK10))),
% 3.46/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7,sK8,sK9,sK10])],[f13,f29])).
% 3.46/1.00  
% 3.46/1.00  fof(f49,plain,(
% 3.46/1.00    r1_tarski(k2_zfmisc_1(sK7,sK8),k2_zfmisc_1(sK9,sK10))),
% 3.46/1.00    inference(cnf_transformation,[],[f30])).
% 3.46/1.00  
% 3.46/1.00  fof(f47,plain,(
% 3.46/1.00    ( ! [X2,X0,X3,X1] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | ~r2_hidden(X1,X3) | ~r2_hidden(X0,X2)) )),
% 3.46/1.00    inference(cnf_transformation,[],[f28])).
% 3.46/1.00  
% 3.46/1.00  fof(f4,axiom,(
% 3.46/1.00    ! [X0,X1,X2] : (k2_zfmisc_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4,X5] : (k4_tarski(X4,X5) = X3 & r2_hidden(X5,X1) & r2_hidden(X4,X0))))),
% 3.46/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.46/1.00  
% 3.46/1.00  fof(f21,plain,(
% 3.46/1.00    ! [X0,X1,X2] : ((k2_zfmisc_1(X0,X1) = X2 | ? [X3] : ((! [X4,X5] : (k4_tarski(X4,X5) != X3 | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X0)) | ~r2_hidden(X3,X2)) & (? [X4,X5] : (k4_tarski(X4,X5) = X3 & r2_hidden(X5,X1) & r2_hidden(X4,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ! [X4,X5] : (k4_tarski(X4,X5) != X3 | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X0))) & (? [X4,X5] : (k4_tarski(X4,X5) = X3 & r2_hidden(X5,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X3,X2))) | k2_zfmisc_1(X0,X1) != X2))),
% 3.46/1.00    inference(nnf_transformation,[],[f4])).
% 3.46/1.00  
% 3.46/1.00  fof(f22,plain,(
% 3.46/1.00    ! [X0,X1,X2] : ((k2_zfmisc_1(X0,X1) = X2 | ? [X3] : ((! [X4,X5] : (k4_tarski(X4,X5) != X3 | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X0)) | ~r2_hidden(X3,X2)) & (? [X6,X7] : (k4_tarski(X6,X7) = X3 & r2_hidden(X7,X1) & r2_hidden(X6,X0)) | r2_hidden(X3,X2)))) & (! [X8] : ((r2_hidden(X8,X2) | ! [X9,X10] : (k4_tarski(X9,X10) != X8 | ~r2_hidden(X10,X1) | ~r2_hidden(X9,X0))) & (? [X11,X12] : (k4_tarski(X11,X12) = X8 & r2_hidden(X12,X1) & r2_hidden(X11,X0)) | ~r2_hidden(X8,X2))) | k2_zfmisc_1(X0,X1) != X2))),
% 3.46/1.00    inference(rectify,[],[f21])).
% 3.46/1.00  
% 3.46/1.00  fof(f25,plain,(
% 3.46/1.00    ! [X8,X1,X0] : (? [X11,X12] : (k4_tarski(X11,X12) = X8 & r2_hidden(X12,X1) & r2_hidden(X11,X0)) => (k4_tarski(sK5(X0,X1,X8),sK6(X0,X1,X8)) = X8 & r2_hidden(sK6(X0,X1,X8),X1) & r2_hidden(sK5(X0,X1,X8),X0)))),
% 3.46/1.00    introduced(choice_axiom,[])).
% 3.46/1.00  
% 3.46/1.00  fof(f24,plain,(
% 3.46/1.00    ( ! [X3] : (! [X2,X1,X0] : (? [X6,X7] : (k4_tarski(X6,X7) = X3 & r2_hidden(X7,X1) & r2_hidden(X6,X0)) => (k4_tarski(sK3(X0,X1,X2),sK4(X0,X1,X2)) = X3 & r2_hidden(sK4(X0,X1,X2),X1) & r2_hidden(sK3(X0,X1,X2),X0)))) )),
% 3.46/1.00    introduced(choice_axiom,[])).
% 3.46/1.00  
% 3.46/1.00  fof(f23,plain,(
% 3.46/1.00    ! [X2,X1,X0] : (? [X3] : ((! [X4,X5] : (k4_tarski(X4,X5) != X3 | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X0)) | ~r2_hidden(X3,X2)) & (? [X6,X7] : (k4_tarski(X6,X7) = X3 & r2_hidden(X7,X1) & r2_hidden(X6,X0)) | r2_hidden(X3,X2))) => ((! [X5,X4] : (k4_tarski(X4,X5) != sK2(X0,X1,X2) | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X0)) | ~r2_hidden(sK2(X0,X1,X2),X2)) & (? [X7,X6] : (k4_tarski(X6,X7) = sK2(X0,X1,X2) & r2_hidden(X7,X1) & r2_hidden(X6,X0)) | r2_hidden(sK2(X0,X1,X2),X2))))),
% 3.46/1.00    introduced(choice_axiom,[])).
% 3.46/1.00  
% 3.46/1.00  fof(f26,plain,(
% 3.46/1.00    ! [X0,X1,X2] : ((k2_zfmisc_1(X0,X1) = X2 | ((! [X4,X5] : (k4_tarski(X4,X5) != sK2(X0,X1,X2) | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X0)) | ~r2_hidden(sK2(X0,X1,X2),X2)) & ((k4_tarski(sK3(X0,X1,X2),sK4(X0,X1,X2)) = sK2(X0,X1,X2) & r2_hidden(sK4(X0,X1,X2),X1) & r2_hidden(sK3(X0,X1,X2),X0)) | r2_hidden(sK2(X0,X1,X2),X2)))) & (! [X8] : ((r2_hidden(X8,X2) | ! [X9,X10] : (k4_tarski(X9,X10) != X8 | ~r2_hidden(X10,X1) | ~r2_hidden(X9,X0))) & ((k4_tarski(sK5(X0,X1,X8),sK6(X0,X1,X8)) = X8 & r2_hidden(sK6(X0,X1,X8),X1) & r2_hidden(sK5(X0,X1,X8),X0)) | ~r2_hidden(X8,X2))) | k2_zfmisc_1(X0,X1) != X2))),
% 3.46/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5,sK6])],[f22,f25,f24,f23])).
% 3.46/1.00  
% 3.46/1.00  fof(f38,plain,(
% 3.46/1.00    ( ! [X2,X0,X8,X1] : (r2_hidden(sK6(X0,X1,X8),X1) | ~r2_hidden(X8,X2) | k2_zfmisc_1(X0,X1) != X2) )),
% 3.46/1.00    inference(cnf_transformation,[],[f26])).
% 3.46/1.00  
% 3.46/1.00  fof(f55,plain,(
% 3.46/1.00    ( ! [X0,X8,X1] : (r2_hidden(sK6(X0,X1,X8),X1) | ~r2_hidden(X8,k2_zfmisc_1(X0,X1))) )),
% 3.46/1.00    inference(equality_resolution,[],[f38])).
% 3.46/1.00  
% 3.46/1.00  fof(f2,axiom,(
% 3.46/1.00    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) <=> r2_hidden(X2,X1)) => X0 = X1)),
% 3.46/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.46/1.00  
% 3.46/1.00  fof(f10,plain,(
% 3.46/1.00    ! [X0,X1] : (X0 = X1 | ? [X2] : (r2_hidden(X2,X0) <~> r2_hidden(X2,X1)))),
% 3.46/1.00    inference(ennf_transformation,[],[f2])).
% 3.46/1.00  
% 3.46/1.00  fof(f18,plain,(
% 3.46/1.00    ! [X0,X1] : (X0 = X1 | ? [X2] : ((~r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) & (r2_hidden(X2,X1) | r2_hidden(X2,X0))))),
% 3.46/1.00    inference(nnf_transformation,[],[f10])).
% 3.46/1.00  
% 3.46/1.00  fof(f19,plain,(
% 3.46/1.00    ! [X1,X0] : (? [X2] : ((~r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) & (r2_hidden(X2,X1) | r2_hidden(X2,X0))) => ((~r2_hidden(sK1(X0,X1),X1) | ~r2_hidden(sK1(X0,X1),X0)) & (r2_hidden(sK1(X0,X1),X1) | r2_hidden(sK1(X0,X1),X0))))),
% 3.46/1.00    introduced(choice_axiom,[])).
% 3.46/1.00  
% 3.46/1.00  fof(f20,plain,(
% 3.46/1.00    ! [X0,X1] : (X0 = X1 | ((~r2_hidden(sK1(X0,X1),X1) | ~r2_hidden(sK1(X0,X1),X0)) & (r2_hidden(sK1(X0,X1),X1) | r2_hidden(sK1(X0,X1),X0))))),
% 3.46/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f18,f19])).
% 3.46/1.00  
% 3.46/1.00  fof(f34,plain,(
% 3.46/1.00    ( ! [X0,X1] : (X0 = X1 | r2_hidden(sK1(X0,X1),X1) | r2_hidden(sK1(X0,X1),X0)) )),
% 3.46/1.00    inference(cnf_transformation,[],[f20])).
% 3.46/1.00  
% 3.46/1.00  fof(f3,axiom,(
% 3.46/1.00    ! [X0] : r1_xboole_0(X0,k1_xboole_0)),
% 3.46/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.46/1.00  
% 3.46/1.00  fof(f36,plain,(
% 3.46/1.00    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) )),
% 3.46/1.00    inference(cnf_transformation,[],[f3])).
% 3.46/1.00  
% 3.46/1.00  fof(f6,axiom,(
% 3.46/1.00    ! [X0,X1,X2] : ~(r2_hidden(X0,X2) & r1_xboole_0(k2_tarski(X0,X1),X2))),
% 3.46/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.46/1.00  
% 3.46/1.00  fof(f11,plain,(
% 3.46/1.00    ! [X0,X1,X2] : (~r2_hidden(X0,X2) | ~r1_xboole_0(k2_tarski(X0,X1),X2))),
% 3.46/1.00    inference(ennf_transformation,[],[f6])).
% 3.46/1.00  
% 3.46/1.00  fof(f48,plain,(
% 3.46/1.00    ( ! [X2,X0,X1] : (~r2_hidden(X0,X2) | ~r1_xboole_0(k2_tarski(X0,X1),X2)) )),
% 3.46/1.00    inference(cnf_transformation,[],[f11])).
% 3.46/1.00  
% 3.46/1.00  fof(f33,plain,(
% 3.46/1.00    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r2_hidden(sK0(X0,X1),X1)) )),
% 3.46/1.00    inference(cnf_transformation,[],[f17])).
% 3.46/1.00  
% 3.46/1.00  fof(f42,plain,(
% 3.46/1.00    ( ! [X2,X0,X1] : (k2_zfmisc_1(X0,X1) = X2 | r2_hidden(sK4(X0,X1,X2),X1) | r2_hidden(sK2(X0,X1,X2),X2)) )),
% 3.46/1.00    inference(cnf_transformation,[],[f26])).
% 3.46/1.00  
% 3.46/1.00  fof(f46,plain,(
% 3.46/1.00    ( ! [X2,X0,X3,X1] : (r2_hidden(X1,X3) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))) )),
% 3.46/1.00    inference(cnf_transformation,[],[f28])).
% 3.46/1.00  
% 3.46/1.00  fof(f50,plain,(
% 3.46/1.00    k1_xboole_0 != k2_zfmisc_1(sK7,sK8)),
% 3.46/1.00    inference(cnf_transformation,[],[f30])).
% 3.46/1.00  
% 3.46/1.00  fof(f37,plain,(
% 3.46/1.00    ( ! [X2,X0,X8,X1] : (r2_hidden(sK5(X0,X1,X8),X0) | ~r2_hidden(X8,X2) | k2_zfmisc_1(X0,X1) != X2) )),
% 3.46/1.00    inference(cnf_transformation,[],[f26])).
% 3.46/1.00  
% 3.46/1.00  fof(f56,plain,(
% 3.46/1.00    ( ! [X0,X8,X1] : (r2_hidden(sK5(X0,X1,X8),X0) | ~r2_hidden(X8,k2_zfmisc_1(X0,X1))) )),
% 3.46/1.00    inference(equality_resolution,[],[f37])).
% 3.46/1.00  
% 3.46/1.00  fof(f32,plain,(
% 3.46/1.00    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK0(X0,X1),X0)) )),
% 3.46/1.00    inference(cnf_transformation,[],[f17])).
% 3.46/1.00  
% 3.46/1.00  fof(f51,plain,(
% 3.46/1.00    ~r1_tarski(sK8,sK10) | ~r1_tarski(sK7,sK9)),
% 3.46/1.00    inference(cnf_transformation,[],[f30])).
% 3.46/1.00  
% 3.46/1.00  cnf(c_16,plain,
% 3.46/1.00      ( r2_hidden(X0,X1)
% 3.46/1.00      | ~ r2_hidden(k4_tarski(X0,X2),k2_zfmisc_1(X1,X3)) ),
% 3.46/1.00      inference(cnf_transformation,[],[f45]) ).
% 3.46/1.00  
% 3.46/1.00  cnf(c_2,plain,
% 3.46/1.00      ( ~ r2_hidden(X0,X1) | r2_hidden(X0,X2) | ~ r1_tarski(X1,X2) ),
% 3.46/1.00      inference(cnf_transformation,[],[f31]) ).
% 3.46/1.00  
% 3.46/1.00  cnf(c_20,negated_conjecture,
% 3.46/1.00      ( r1_tarski(k2_zfmisc_1(sK7,sK8),k2_zfmisc_1(sK9,sK10)) ),
% 3.46/1.00      inference(cnf_transformation,[],[f49]) ).
% 3.46/1.00  
% 3.46/1.00  cnf(c_1061,plain,
% 3.46/1.00      ( r2_hidden(X0,k2_zfmisc_1(sK9,sK10))
% 3.46/1.00      | ~ r2_hidden(X0,k2_zfmisc_1(sK7,sK8)) ),
% 3.46/1.00      inference(resolution,[status(thm)],[c_2,c_20]) ).
% 3.46/1.00  
% 3.46/1.00  cnf(c_1180,plain,
% 3.46/1.00      ( r2_hidden(X0,sK9)
% 3.46/1.00      | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(sK7,sK8)) ),
% 3.46/1.00      inference(resolution,[status(thm)],[c_16,c_1061]) ).
% 3.46/1.00  
% 3.46/1.00  cnf(c_14,plain,
% 3.46/1.00      ( ~ r2_hidden(X0,X1)
% 3.46/1.00      | ~ r2_hidden(X2,X3)
% 3.46/1.00      | r2_hidden(k4_tarski(X2,X0),k2_zfmisc_1(X3,X1)) ),
% 3.46/1.00      inference(cnf_transformation,[],[f47]) ).
% 3.46/1.00  
% 3.46/1.00  cnf(c_2950,plain,
% 3.46/1.00      ( r2_hidden(X0,sK9) | ~ r2_hidden(X0,sK7) | ~ r2_hidden(X1,sK8) ),
% 3.46/1.00      inference(resolution,[status(thm)],[c_1180,c_14]) ).
% 3.46/1.00  
% 3.46/1.00  cnf(c_12,plain,
% 3.46/1.00      ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
% 3.46/1.00      | r2_hidden(sK6(X1,X2,X0),X2) ),
% 3.46/1.00      inference(cnf_transformation,[],[f55]) ).
% 3.46/1.00  
% 3.46/1.00  cnf(c_3208,plain,
% 3.46/1.00      ( ~ r2_hidden(X0,k2_zfmisc_1(X1,sK8))
% 3.46/1.00      | r2_hidden(X2,sK9)
% 3.46/1.00      | ~ r2_hidden(X2,sK7) ),
% 3.46/1.00      inference(resolution,[status(thm)],[c_2950,c_12]) ).
% 3.46/1.00  
% 3.46/1.00  cnf(c_4,plain,
% 3.46/1.00      ( r2_hidden(sK1(X0,X1),X1) | r2_hidden(sK1(X0,X1),X0) | X1 = X0 ),
% 3.46/1.00      inference(cnf_transformation,[],[f34]) ).
% 3.46/1.00  
% 3.46/1.00  cnf(c_5,plain,
% 3.46/1.00      ( r1_xboole_0(X0,k1_xboole_0) ),
% 3.46/1.00      inference(cnf_transformation,[],[f36]) ).
% 3.46/1.00  
% 3.46/1.00  cnf(c_17,plain,
% 3.46/1.00      ( ~ r1_xboole_0(k2_tarski(X0,X1),X2) | ~ r2_hidden(X0,X2) ),
% 3.46/1.00      inference(cnf_transformation,[],[f48]) ).
% 3.46/1.00  
% 3.46/1.00  cnf(c_224,plain,
% 3.46/1.00      ( ~ r2_hidden(X0,X1) | k2_tarski(X0,X2) != X3 | k1_xboole_0 != X1 ),
% 3.46/1.00      inference(resolution_lifted,[status(thm)],[c_5,c_17]) ).
% 3.46/1.00  
% 3.46/1.00  cnf(c_225,plain,
% 3.46/1.00      ( ~ r2_hidden(X0,k1_xboole_0) ),
% 3.46/1.00      inference(unflattening,[status(thm)],[c_224]) ).
% 3.46/1.00  
% 3.46/1.00  cnf(c_1337,plain,
% 3.46/1.00      ( r2_hidden(sK1(k1_xboole_0,X0),X0) | X0 = k1_xboole_0 ),
% 3.46/1.00      inference(resolution,[status(thm)],[c_4,c_225]) ).
% 3.46/1.00  
% 3.46/1.00  cnf(c_4147,plain,
% 3.46/1.00      ( r2_hidden(X0,sK9)
% 3.46/1.00      | ~ r2_hidden(X0,sK7)
% 3.46/1.00      | k2_zfmisc_1(X1,sK8) = k1_xboole_0 ),
% 3.46/1.00      inference(resolution,[status(thm)],[c_3208,c_1337]) ).
% 3.46/1.00  
% 3.46/1.00  cnf(c_0,plain,
% 3.46/1.00      ( ~ r2_hidden(sK0(X0,X1),X1) | r1_tarski(X0,X1) ),
% 3.46/1.00      inference(cnf_transformation,[],[f33]) ).
% 3.46/1.00  
% 3.46/1.00  cnf(c_7767,plain,
% 3.46/1.00      ( ~ r2_hidden(sK0(X0,sK9),sK7)
% 3.46/1.00      | r1_tarski(X0,sK9)
% 3.46/1.00      | k2_zfmisc_1(X1,sK8) = k1_xboole_0 ),
% 3.46/1.00      inference(resolution,[status(thm)],[c_4147,c_0]) ).
% 3.46/1.00  
% 3.46/1.00  cnf(c_7769,plain,
% 3.46/1.00      ( ~ r2_hidden(sK0(sK7,sK9),sK7)
% 3.46/1.00      | r1_tarski(sK7,sK9)
% 3.46/1.00      | k2_zfmisc_1(sK7,sK8) = k1_xboole_0 ),
% 3.46/1.00      inference(instantiation,[status(thm)],[c_7767]) ).
% 3.46/1.00  
% 3.46/1.00  cnf(c_8,plain,
% 3.46/1.00      ( r2_hidden(sK4(X0,X1,X2),X1)
% 3.46/1.00      | r2_hidden(sK2(X0,X1,X2),X2)
% 3.46/1.00      | k2_zfmisc_1(X0,X1) = X2 ),
% 3.46/1.00      inference(cnf_transformation,[],[f42]) ).
% 3.46/1.00  
% 3.46/1.00  cnf(c_15,plain,
% 3.46/1.00      ( r2_hidden(X0,X1)
% 3.46/1.00      | ~ r2_hidden(k4_tarski(X2,X0),k2_zfmisc_1(X3,X1)) ),
% 3.46/1.00      inference(cnf_transformation,[],[f46]) ).
% 3.46/1.00  
% 3.46/1.00  cnf(c_1170,plain,
% 3.46/1.00      ( r2_hidden(X0,sK10)
% 3.46/1.00      | ~ r2_hidden(k4_tarski(X1,X0),k2_zfmisc_1(sK7,sK8)) ),
% 3.46/1.00      inference(resolution,[status(thm)],[c_15,c_1061]) ).
% 3.46/1.00  
% 3.46/1.00  cnf(c_2941,plain,
% 3.46/1.00      ( ~ r2_hidden(X0,sK7) | r2_hidden(X1,sK10) | ~ r2_hidden(X1,sK8) ),
% 3.46/1.00      inference(resolution,[status(thm)],[c_1170,c_14]) ).
% 3.46/1.00  
% 3.46/1.00  cnf(c_4284,plain,
% 3.46/1.00      ( r2_hidden(X0,sK10)
% 3.46/1.00      | ~ r2_hidden(X0,sK8)
% 3.46/1.00      | r2_hidden(sK4(X1,X2,sK7),X2)
% 3.46/1.00      | k2_zfmisc_1(X1,X2) = sK7 ),
% 3.46/1.00      inference(resolution,[status(thm)],[c_8,c_2941]) ).
% 3.46/1.00  
% 3.46/1.00  cnf(c_19,negated_conjecture,
% 3.46/1.00      ( k1_xboole_0 != k2_zfmisc_1(sK7,sK8) ),
% 3.46/1.00      inference(cnf_transformation,[],[f50]) ).
% 3.46/1.00  
% 3.46/1.00  cnf(c_359,plain,( X0 = X0 ),theory(equality) ).
% 3.46/1.00  
% 3.46/1.00  cnf(c_370,plain,
% 3.46/1.00      ( sK7 = sK7 ),
% 3.46/1.00      inference(instantiation,[status(thm)],[c_359]) ).
% 3.46/1.00  
% 3.46/1.00  cnf(c_859,plain,
% 3.46/1.00      ( r2_hidden(sK1(k2_zfmisc_1(sK7,sK8),k1_xboole_0),k2_zfmisc_1(sK7,sK8))
% 3.46/1.00      | r2_hidden(sK1(k2_zfmisc_1(sK7,sK8),k1_xboole_0),k1_xboole_0)
% 3.46/1.00      | k1_xboole_0 = k2_zfmisc_1(sK7,sK8) ),
% 3.46/1.00      inference(instantiation,[status(thm)],[c_4]) ).
% 3.46/1.00  
% 3.46/1.00  cnf(c_13,plain,
% 3.46/1.00      ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
% 3.46/1.00      | r2_hidden(sK5(X1,X2,X0),X1) ),
% 3.46/1.00      inference(cnf_transformation,[],[f56]) ).
% 3.46/1.00  
% 3.46/1.00  cnf(c_941,plain,
% 3.46/1.00      ( r2_hidden(sK5(sK7,sK8,sK1(k2_zfmisc_1(sK7,sK8),k1_xboole_0)),sK7)
% 3.46/1.00      | ~ r2_hidden(sK1(k2_zfmisc_1(sK7,sK8),k1_xboole_0),k2_zfmisc_1(sK7,sK8)) ),
% 3.46/1.00      inference(instantiation,[status(thm)],[c_13]) ).
% 3.46/1.00  
% 3.46/1.00  cnf(c_1,plain,
% 3.46/1.00      ( r2_hidden(sK0(X0,X1),X0) | r1_tarski(X0,X1) ),
% 3.46/1.00      inference(cnf_transformation,[],[f32]) ).
% 3.46/1.00  
% 3.46/1.00  cnf(c_961,plain,
% 3.46/1.00      ( r1_tarski(X0,X0) ),
% 3.46/1.00      inference(resolution,[status(thm)],[c_0,c_1]) ).
% 3.46/1.00  
% 3.46/1.00  cnf(c_963,plain,
% 3.46/1.00      ( r1_tarski(sK7,sK7) ),
% 3.46/1.00      inference(instantiation,[status(thm)],[c_961]) ).
% 3.46/1.00  
% 3.46/1.00  cnf(c_980,plain,
% 3.46/1.00      ( k1_xboole_0 = k1_xboole_0 ),
% 3.46/1.00      inference(instantiation,[status(thm)],[c_359]) ).
% 3.46/1.00  
% 3.46/1.00  cnf(c_1040,plain,
% 3.46/1.00      ( ~ r2_hidden(sK1(k2_zfmisc_1(sK7,sK8),k1_xboole_0),k1_xboole_0) ),
% 3.46/1.00      inference(instantiation,[status(thm)],[c_225]) ).
% 3.46/1.00  
% 3.46/1.00  cnf(c_3184,plain,
% 3.46/1.00      ( r2_hidden(X0,sK10) | ~ r2_hidden(X0,sK8) | sK7 = k1_xboole_0 ),
% 3.46/1.00      inference(resolution,[status(thm)],[c_2941,c_1337]) ).
% 3.46/1.00  
% 3.46/1.00  cnf(c_360,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 3.46/1.00  
% 3.46/1.00  cnf(c_981,plain,
% 3.46/1.00      ( X0 != X1 | k1_xboole_0 != X1 | k1_xboole_0 = X0 ),
% 3.46/1.00      inference(instantiation,[status(thm)],[c_360]) ).
% 3.46/1.00  
% 3.46/1.00  cnf(c_3419,plain,
% 3.46/1.00      ( X0 != k1_xboole_0
% 3.46/1.00      | k1_xboole_0 = X0
% 3.46/1.00      | k1_xboole_0 != k1_xboole_0 ),
% 3.46/1.00      inference(instantiation,[status(thm)],[c_981]) ).
% 3.46/1.00  
% 3.46/1.00  cnf(c_3420,plain,
% 3.46/1.00      ( sK7 != k1_xboole_0
% 3.46/1.00      | k1_xboole_0 = sK7
% 3.46/1.00      | k1_xboole_0 != k1_xboole_0 ),
% 3.46/1.00      inference(instantiation,[status(thm)],[c_3419]) ).
% 3.46/1.00  
% 3.46/1.00  cnf(c_361,plain,
% 3.46/1.00      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,X3) | X2 != X0 | X3 != X1 ),
% 3.46/1.00      theory(equality) ).
% 3.46/1.00  
% 3.46/1.00  cnf(c_4157,plain,
% 3.46/1.00      ( ~ r1_tarski(X0,X1)
% 3.46/1.00      | r1_tarski(sK7,k1_xboole_0)
% 3.46/1.00      | sK7 != X0
% 3.46/1.00      | k1_xboole_0 != X1 ),
% 3.46/1.00      inference(instantiation,[status(thm)],[c_361]) ).
% 3.46/1.00  
% 3.46/1.00  cnf(c_4159,plain,
% 3.46/1.00      ( ~ r1_tarski(sK7,sK7)
% 3.46/1.00      | r1_tarski(sK7,k1_xboole_0)
% 3.46/1.00      | sK7 != sK7
% 3.46/1.00      | k1_xboole_0 != sK7 ),
% 3.46/1.00      inference(instantiation,[status(thm)],[c_4157]) ).
% 3.46/1.00  
% 3.46/1.00  cnf(c_1365,plain,
% 3.46/1.00      ( r2_hidden(sK5(sK7,sK8,sK1(k2_zfmisc_1(sK7,sK8),k1_xboole_0)),X0)
% 3.46/1.00      | ~ r2_hidden(sK5(sK7,sK8,sK1(k2_zfmisc_1(sK7,sK8),k1_xboole_0)),sK7)
% 3.46/1.00      | ~ r1_tarski(sK7,X0) ),
% 3.46/1.00      inference(instantiation,[status(thm)],[c_2]) ).
% 3.46/1.00  
% 3.46/1.00  cnf(c_5097,plain,
% 3.46/1.00      ( ~ r2_hidden(sK5(sK7,sK8,sK1(k2_zfmisc_1(sK7,sK8),k1_xboole_0)),sK7)
% 3.46/1.00      | r2_hidden(sK5(sK7,sK8,sK1(k2_zfmisc_1(sK7,sK8),k1_xboole_0)),k1_xboole_0)
% 3.46/1.00      | ~ r1_tarski(sK7,k1_xboole_0) ),
% 3.46/1.00      inference(instantiation,[status(thm)],[c_1365]) ).
% 3.46/1.00  
% 3.46/1.00  cnf(c_5098,plain,
% 3.46/1.00      ( ~ r2_hidden(sK5(sK7,sK8,sK1(k2_zfmisc_1(sK7,sK8),k1_xboole_0)),k1_xboole_0) ),
% 3.46/1.00      inference(instantiation,[status(thm)],[c_225]) ).
% 3.46/1.00  
% 3.46/1.00  cnf(c_5653,plain,
% 3.46/1.00      ( r2_hidden(X0,sK10) | ~ r2_hidden(X0,sK8) ),
% 3.46/1.00      inference(global_propositional_subsumption,
% 3.46/1.00                [status(thm)],
% 3.46/1.00                [c_4284,c_19,c_370,c_859,c_941,c_963,c_980,c_1040,c_3184,
% 3.46/1.00                 c_3420,c_4159,c_5097,c_5098]) ).
% 3.46/1.00  
% 3.46/1.00  cnf(c_5671,plain,
% 3.46/1.00      ( ~ r2_hidden(sK0(X0,sK10),sK8) | r1_tarski(X0,sK10) ),
% 3.46/1.00      inference(resolution,[status(thm)],[c_5653,c_0]) ).
% 3.46/1.00  
% 3.46/1.00  cnf(c_6803,plain,
% 3.46/1.00      ( r1_tarski(sK8,sK10) ),
% 3.46/1.00      inference(resolution,[status(thm)],[c_5671,c_1]) ).
% 3.46/1.00  
% 3.46/1.00  cnf(c_857,plain,
% 3.46/1.00      ( k2_zfmisc_1(sK7,sK8) != X0
% 3.46/1.00      | k1_xboole_0 != X0
% 3.46/1.00      | k1_xboole_0 = k2_zfmisc_1(sK7,sK8) ),
% 3.46/1.00      inference(instantiation,[status(thm)],[c_360]) ).
% 3.46/1.00  
% 3.46/1.00  cnf(c_979,plain,
% 3.46/1.00      ( k2_zfmisc_1(sK7,sK8) != k1_xboole_0
% 3.46/1.00      | k1_xboole_0 = k2_zfmisc_1(sK7,sK8)
% 3.46/1.00      | k1_xboole_0 != k1_xboole_0 ),
% 3.46/1.00      inference(instantiation,[status(thm)],[c_857]) ).
% 3.46/1.00  
% 3.46/1.00  cnf(c_909,plain,
% 3.46/1.00      ( r2_hidden(sK0(sK7,sK9),sK7) | r1_tarski(sK7,sK9) ),
% 3.46/1.00      inference(instantiation,[status(thm)],[c_1]) ).
% 3.46/1.00  
% 3.46/1.00  cnf(c_18,negated_conjecture,
% 3.46/1.00      ( ~ r1_tarski(sK7,sK9) | ~ r1_tarski(sK8,sK10) ),
% 3.46/1.00      inference(cnf_transformation,[],[f51]) ).
% 3.46/1.00  
% 3.46/1.00  cnf(contradiction,plain,
% 3.46/1.00      ( $false ),
% 3.46/1.00      inference(minisat,
% 3.46/1.00                [status(thm)],
% 3.46/1.00                [c_7769,c_6803,c_980,c_979,c_909,c_18,c_19]) ).
% 3.46/1.00  
% 3.46/1.00  
% 3.46/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 3.46/1.00  
% 3.46/1.00  ------                               Statistics
% 3.46/1.00  
% 3.46/1.00  ------ Selected
% 3.46/1.00  
% 3.46/1.00  total_time:                             0.339
% 3.46/1.00  
%------------------------------------------------------------------------------
