%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:37:51 EST 2020

% Result     : Theorem 3.57s
% Output     : CNFRefutation 3.57s
% Verified   : 
% Statistics : Number of formulae       :  139 (1063 expanded)
%              Number of clauses        :   85 ( 376 expanded)
%              Number of leaves         :   16 ( 226 expanded)
%              Depth                    :   21
%              Number of atoms          :  406 (3587 expanded)
%              Number of equality atoms :  177 (1167 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal clause size      :   18 (   2 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f9,conjecture,(
    ! [X0,X1,X2,X3] :
      ( r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3))
     => ( ( r1_tarski(X1,X3)
          & r1_tarski(X0,X2) )
        | k1_xboole_0 = k2_zfmisc_1(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

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
   => ( ( ~ r1_tarski(sK8,sK10)
        | ~ r1_tarski(sK7,sK9) )
      & k1_xboole_0 != k2_zfmisc_1(sK7,sK8)
      & r1_tarski(k2_zfmisc_1(sK7,sK8),k2_zfmisc_1(sK9,sK10)) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,
    ( ( ~ r1_tarski(sK8,sK10)
      | ~ r1_tarski(sK7,sK9) )
    & k1_xboole_0 != k2_zfmisc_1(sK7,sK8)
    & r1_tarski(k2_zfmisc_1(sK7,sK8),k2_zfmisc_1(sK9,sK10)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7,sK8,sK9,sK10])],[f16,f33])).

fof(f57,plain,(
    r1_tarski(k2_zfmisc_1(sK7,sK8),k2_zfmisc_1(sK9,sK10)) ),
    inference(cnf_transformation,[],[f34])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f40,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f2])).

fof(f13,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f21,plain,(
    ! [X1,X0] :
      ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
     => r2_hidden(sK1(X0,X1),k3_xboole_0(X0,X1)) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( r2_hidden(sK1(X0,X1),k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f13,f21])).

fof(f38,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK1(X0,X1),k3_xboole_0(X0,X1))
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( k2_zfmisc_1(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ? [X4,X5] :
              ( k4_tarski(X4,X5) = X3
              & r2_hidden(X5,X1)
              & r2_hidden(X4,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
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

fof(f24,plain,(
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
    inference(rectify,[],[f23])).

fof(f27,plain,(
    ! [X8,X1,X0] :
      ( ? [X11,X12] :
          ( k4_tarski(X11,X12) = X8
          & r2_hidden(X12,X1)
          & r2_hidden(X11,X0) )
     => ( k4_tarski(sK5(X0,X1,X8),sK6(X0,X1,X8)) = X8
        & r2_hidden(sK6(X0,X1,X8),X1)
        & r2_hidden(sK5(X0,X1,X8),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X6,X7] :
          ( k4_tarski(X6,X7) = X3
          & r2_hidden(X7,X1)
          & r2_hidden(X6,X0) )
     => ( k4_tarski(sK3(X0,X1,X2),sK4(X0,X1,X2)) = X3
        & r2_hidden(sK4(X0,X1,X2),X1)
        & r2_hidden(sK3(X0,X1,X2),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
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

fof(f28,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5,sK6])],[f24,f27,f26,f25])).

fof(f45,plain,(
    ! [X2,X0,X8,X1] :
      ( k4_tarski(sK5(X0,X1,X8),sK6(X0,X1,X8)) = X8
      | ~ r2_hidden(X8,X2)
      | k2_zfmisc_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f28])).

fof(f62,plain,(
    ! [X0,X8,X1] :
      ( k4_tarski(sK5(X0,X1,X8),sK6(X0,X1,X8)) = X8
      | ~ r2_hidden(X8,k2_zfmisc_1(X0,X1)) ) ),
    inference(equality_resolution,[],[f45])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

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

fof(f36,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK0(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,k3_xboole_0(X0,X1)) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f58,plain,(
    k1_xboole_0 != k2_zfmisc_1(sK7,sK8) ),
    inference(cnf_transformation,[],[f34])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f8])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f31])).

fof(f54,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f55,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f32])).

fof(f66,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f55])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( k2_zfmisc_1(X0,X1) = X2
      | r2_hidden(sK3(X0,X1,X2),X0)
      | r2_hidden(sK2(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f5,axiom,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f5])).

fof(f4,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
    <=> ( r2_hidden(X1,X3)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
        | ~ r2_hidden(X1,X3)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X3)
          & r2_hidden(X0,X2) )
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ) ),
    inference(nnf_transformation,[],[f7])).

fof(f30,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
        | ~ r2_hidden(X1,X3)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X3)
          & r2_hidden(X0,X2) )
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ) ),
    inference(flattening,[],[f29])).

fof(f51,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X0,X2)
      | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f35,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f59,plain,
    ( ~ r1_tarski(sK8,sK10)
    | ~ r1_tarski(sK7,sK9) ),
    inference(cnf_transformation,[],[f34])).

fof(f52,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X1,X3)
      | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f53,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
      | ~ r2_hidden(X1,X3)
      | ~ r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f37,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK0(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f20])).

cnf(c_24,negated_conjecture,
    ( r1_tarski(k2_zfmisc_1(sK7,sK8),k2_zfmisc_1(sK9,sK10)) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_619,plain,
    ( r1_tarski(k2_zfmisc_1(sK7,sK8),k2_zfmisc_1(sK9,sK10)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_5,plain,
    ( ~ r1_tarski(X0,X1)
    | k3_xboole_0(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f40])).

cnf(c_633,plain,
    ( k3_xboole_0(X0,X1) = X0
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_937,plain,
    ( k3_xboole_0(k2_zfmisc_1(sK7,sK8),k2_zfmisc_1(sK9,sK10)) = k2_zfmisc_1(sK7,sK8) ),
    inference(superposition,[status(thm)],[c_619,c_633])).

cnf(c_4,plain,
    ( r1_xboole_0(X0,X1)
    | r2_hidden(sK1(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_634,plain,
    ( r1_xboole_0(X0,X1) = iProver_top
    | r2_hidden(sK1(X0,X1),k3_xboole_0(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_1786,plain,
    ( r1_xboole_0(k2_zfmisc_1(sK7,sK8),k2_zfmisc_1(sK9,sK10)) = iProver_top
    | r2_hidden(sK1(k2_zfmisc_1(sK7,sK8),k2_zfmisc_1(sK9,sK10)),k2_zfmisc_1(sK7,sK8)) = iProver_top ),
    inference(superposition,[status(thm)],[c_937,c_634])).

cnf(c_13,plain,
    ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
    | k4_tarski(sK5(X1,X2,X0),sK6(X1,X2,X0)) = X0 ),
    inference(cnf_transformation,[],[f62])).

cnf(c_625,plain,
    ( k4_tarski(sK5(X0,X1,X2),sK6(X0,X1,X2)) = X2
    | r2_hidden(X2,k2_zfmisc_1(X0,X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_2477,plain,
    ( k4_tarski(sK5(sK7,sK8,sK1(k2_zfmisc_1(sK7,sK8),k2_zfmisc_1(sK9,sK10))),sK6(sK7,sK8,sK1(k2_zfmisc_1(sK7,sK8),k2_zfmisc_1(sK9,sK10)))) = sK1(k2_zfmisc_1(sK7,sK8),k2_zfmisc_1(sK9,sK10))
    | r1_xboole_0(k2_zfmisc_1(sK7,sK8),k2_zfmisc_1(sK9,sK10)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1786,c_625])).

cnf(c_1,plain,
    ( r2_hidden(sK0(X0,X1),X0)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_637,plain,
    ( r2_hidden(sK0(X0,X1),X0) = iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_3,plain,
    ( ~ r1_xboole_0(X0,X1)
    | ~ r2_hidden(X2,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_635,plain,
    ( r1_xboole_0(X0,X1) != iProver_top
    | r2_hidden(X2,k3_xboole_0(X0,X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_1496,plain,
    ( r1_xboole_0(X0,X1) != iProver_top
    | r1_tarski(k3_xboole_0(X0,X1),X2) = iProver_top ),
    inference(superposition,[status(thm)],[c_637,c_635])).

cnf(c_2165,plain,
    ( k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,X1)
    | r1_xboole_0(X0,X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1496,c_633])).

cnf(c_3246,plain,
    ( k4_tarski(sK5(sK7,sK8,sK1(k2_zfmisc_1(sK7,sK8),k2_zfmisc_1(sK9,sK10))),sK6(sK7,sK8,sK1(k2_zfmisc_1(sK7,sK8),k2_zfmisc_1(sK9,sK10)))) = sK1(k2_zfmisc_1(sK7,sK8),k2_zfmisc_1(sK9,sK10))
    | k3_xboole_0(k3_xboole_0(k2_zfmisc_1(sK7,sK8),k2_zfmisc_1(sK9,sK10)),X0) = k3_xboole_0(k2_zfmisc_1(sK7,sK8),k2_zfmisc_1(sK9,sK10)) ),
    inference(superposition,[status(thm)],[c_2477,c_2165])).

cnf(c_3259,plain,
    ( k4_tarski(sK5(sK7,sK8,sK1(k2_zfmisc_1(sK7,sK8),k2_zfmisc_1(sK9,sK10))),sK6(sK7,sK8,sK1(k2_zfmisc_1(sK7,sK8),k2_zfmisc_1(sK9,sK10)))) = sK1(k2_zfmisc_1(sK7,sK8),k2_zfmisc_1(sK9,sK10))
    | k3_xboole_0(k2_zfmisc_1(sK7,sK8),X0) = k2_zfmisc_1(sK7,sK8) ),
    inference(light_normalisation,[status(thm)],[c_3246,c_937])).

cnf(c_3548,plain,
    ( k4_tarski(sK5(sK7,sK8,sK1(k2_zfmisc_1(sK7,sK8),k2_zfmisc_1(sK9,sK10))),sK6(sK7,sK8,sK1(k2_zfmisc_1(sK7,sK8),k2_zfmisc_1(sK9,sK10)))) = sK1(k2_zfmisc_1(sK7,sK8),k2_zfmisc_1(sK9,sK10))
    | r1_xboole_0(k2_zfmisc_1(sK7,sK8),X0) != iProver_top
    | r2_hidden(X1,k2_zfmisc_1(sK7,sK8)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3259,c_635])).

cnf(c_23,negated_conjecture,
    ( k1_xboole_0 != k2_zfmisc_1(sK7,sK8) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_21,plain,
    ( k2_zfmisc_1(X0,X1) != k1_xboole_0
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f54])).

cnf(c_27,plain,
    ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) != k1_xboole_0
    | k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_21])).

cnf(c_20,plain,
    ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f66])).

cnf(c_28,plain,
    ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_20])).

cnf(c_288,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_813,plain,
    ( k2_zfmisc_1(sK7,sK8) != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = k2_zfmisc_1(sK7,sK8) ),
    inference(instantiation,[status(thm)],[c_288])).

cnf(c_814,plain,
    ( k2_zfmisc_1(sK7,sK8) != k1_xboole_0
    | k1_xboole_0 = k2_zfmisc_1(sK7,sK8)
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_813])).

cnf(c_11,plain,
    ( r2_hidden(sK3(X0,X1,X2),X0)
    | r2_hidden(sK2(X0,X1,X2),X2)
    | k2_zfmisc_1(X0,X1) = X2 ),
    inference(cnf_transformation,[],[f47])).

cnf(c_627,plain,
    ( k2_zfmisc_1(X0,X1) = X2
    | r2_hidden(sK3(X0,X1,X2),X0) = iProver_top
    | r2_hidden(sK2(X0,X1,X2),X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_7,plain,
    ( r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_631,plain,
    ( r1_xboole_0(X0,k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_6,plain,
    ( r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_632,plain,
    ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_936,plain,
    ( k3_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_632,c_633])).

cnf(c_1497,plain,
    ( r1_xboole_0(k1_xboole_0,X0) != iProver_top
    | r2_hidden(X1,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_936,c_635])).

cnf(c_1641,plain,
    ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_631,c_1497])).

cnf(c_2942,plain,
    ( k2_zfmisc_1(k1_xboole_0,X0) = X1
    | r2_hidden(sK2(k1_xboole_0,X0,X1),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_627,c_1641])).

cnf(c_2945,plain,
    ( k1_xboole_0 = X0
    | r2_hidden(sK2(k1_xboole_0,X1,X0),X0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_2942,c_20])).

cnf(c_1498,plain,
    ( r1_xboole_0(k2_zfmisc_1(sK7,sK8),k2_zfmisc_1(sK9,sK10)) != iProver_top
    | r2_hidden(X0,k2_zfmisc_1(sK7,sK8)) != iProver_top ),
    inference(superposition,[status(thm)],[c_937,c_635])).

cnf(c_3248,plain,
    ( k4_tarski(sK5(sK7,sK8,sK1(k2_zfmisc_1(sK7,sK8),k2_zfmisc_1(sK9,sK10))),sK6(sK7,sK8,sK1(k2_zfmisc_1(sK7,sK8),k2_zfmisc_1(sK9,sK10)))) = sK1(k2_zfmisc_1(sK7,sK8),k2_zfmisc_1(sK9,sK10))
    | r2_hidden(X0,k2_zfmisc_1(sK7,sK8)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2477,c_1498])).

cnf(c_3629,plain,
    ( k4_tarski(sK5(sK7,sK8,sK1(k2_zfmisc_1(sK7,sK8),k2_zfmisc_1(sK9,sK10))),sK6(sK7,sK8,sK1(k2_zfmisc_1(sK7,sK8),k2_zfmisc_1(sK9,sK10)))) = sK1(k2_zfmisc_1(sK7,sK8),k2_zfmisc_1(sK9,sK10))
    | k2_zfmisc_1(sK7,sK8) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2945,c_3248])).

cnf(c_3899,plain,
    ( k4_tarski(sK5(sK7,sK8,sK1(k2_zfmisc_1(sK7,sK8),k2_zfmisc_1(sK9,sK10))),sK6(sK7,sK8,sK1(k2_zfmisc_1(sK7,sK8),k2_zfmisc_1(sK9,sK10)))) = sK1(k2_zfmisc_1(sK7,sK8),k2_zfmisc_1(sK9,sK10)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3548,c_23,c_27,c_28,c_814,c_3629])).

cnf(c_18,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(k4_tarski(X0,X2),k2_zfmisc_1(X1,X3)) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_621,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r2_hidden(k4_tarski(X0,X2),k2_zfmisc_1(X1,X3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_3906,plain,
    ( r2_hidden(sK5(sK7,sK8,sK1(k2_zfmisc_1(sK7,sK8),k2_zfmisc_1(sK9,sK10))),X0) = iProver_top
    | r2_hidden(sK1(k2_zfmisc_1(sK7,sK8),k2_zfmisc_1(sK9,sK10)),k2_zfmisc_1(X0,X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3899,c_621])).

cnf(c_7935,plain,
    ( r1_xboole_0(k2_zfmisc_1(sK7,sK8),k2_zfmisc_1(sK9,sK10)) = iProver_top
    | r2_hidden(sK5(sK7,sK8,sK1(k2_zfmisc_1(sK7,sK8),k2_zfmisc_1(sK9,sK10))),sK7) = iProver_top ),
    inference(superposition,[status(thm)],[c_1786,c_3906])).

cnf(c_2163,plain,
    ( r1_xboole_0(k2_zfmisc_1(sK7,sK8),k2_zfmisc_1(sK9,sK10)) != iProver_top
    | r1_tarski(k2_zfmisc_1(sK7,sK8),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_937,c_1496])).

cnf(c_2181,plain,
    ( r1_xboole_0(k2_zfmisc_1(sK7,sK8),k2_zfmisc_1(sK9,sK10)) != iProver_top
    | r1_tarski(k2_zfmisc_1(sK7,sK8),k1_xboole_0) = iProver_top ),
    inference(instantiation,[status(thm)],[c_2163])).

cnf(c_2,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | ~ r1_tarski(X1,X2) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_636,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,X2) = iProver_top
    | r1_tarski(X1,X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_2634,plain,
    ( r1_xboole_0(k2_zfmisc_1(sK7,sK8),k2_zfmisc_1(sK9,sK10)) = iProver_top
    | r2_hidden(sK1(k2_zfmisc_1(sK7,sK8),k2_zfmisc_1(sK9,sK10)),X0) = iProver_top
    | r1_tarski(k2_zfmisc_1(sK7,sK8),X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1786,c_636])).

cnf(c_3210,plain,
    ( r1_xboole_0(k2_zfmisc_1(sK7,sK8),k2_zfmisc_1(sK9,sK10)) = iProver_top
    | r1_tarski(k2_zfmisc_1(sK7,sK8),k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2634,c_1641])).

cnf(c_3008,plain,
    ( k3_xboole_0(X0,X1) = k1_xboole_0
    | r1_xboole_0(X0,X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_2945,c_635])).

cnf(c_5052,plain,
    ( k3_xboole_0(k2_zfmisc_1(sK7,sK8),k2_zfmisc_1(sK9,sK10)) = k1_xboole_0
    | r1_tarski(k2_zfmisc_1(sK7,sK8),k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_3210,c_3008])).

cnf(c_5071,plain,
    ( k2_zfmisc_1(sK7,sK8) = k1_xboole_0
    | r1_tarski(k2_zfmisc_1(sK7,sK8),k1_xboole_0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_5052,c_937])).

cnf(c_7956,plain,
    ( r2_hidden(sK5(sK7,sK8,sK1(k2_zfmisc_1(sK7,sK8),k2_zfmisc_1(sK9,sK10))),sK7) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_7935,c_23,c_27,c_28,c_814,c_2181,c_5071])).

cnf(c_7961,plain,
    ( r2_hidden(sK5(sK7,sK8,sK1(k2_zfmisc_1(sK7,sK8),k2_zfmisc_1(sK9,sK10))),X0) = iProver_top
    | r1_tarski(sK7,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_7956,c_636])).

cnf(c_22,negated_conjecture,
    ( ~ r1_tarski(sK7,sK9)
    | ~ r1_tarski(sK8,sK10) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_26,plain,
    ( r1_tarski(sK7,sK9) != iProver_top
    | r1_tarski(sK8,sK10) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_17,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(k4_tarski(X2,X0),k2_zfmisc_1(X3,X1)) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_964,plain,
    ( r2_hidden(X0,k2_zfmisc_1(sK9,sK10))
    | ~ r2_hidden(X0,k2_zfmisc_1(sK7,sK8)) ),
    inference(resolution,[status(thm)],[c_2,c_24])).

cnf(c_1451,plain,
    ( r2_hidden(X0,sK10)
    | ~ r2_hidden(k4_tarski(X1,X0),k2_zfmisc_1(sK7,sK8)) ),
    inference(resolution,[status(thm)],[c_17,c_964])).

cnf(c_16,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X2,X3)
    | r2_hidden(k4_tarski(X2,X0),k2_zfmisc_1(X3,X1)) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_1949,plain,
    ( ~ r2_hidden(X0,sK7)
    | r2_hidden(X1,sK10)
    | ~ r2_hidden(X1,sK8) ),
    inference(resolution,[status(thm)],[c_1451,c_16])).

cnf(c_2056,plain,
    ( r2_hidden(X0,sK10)
    | ~ r2_hidden(X0,sK8)
    | r1_tarski(sK7,X1) ),
    inference(resolution,[status(thm)],[c_1949,c_1])).

cnf(c_0,plain,
    ( ~ r2_hidden(sK0(X0,X1),X1)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_2102,plain,
    ( ~ r2_hidden(sK0(X0,sK10),sK8)
    | r1_tarski(X0,sK10)
    | r1_tarski(sK7,X1) ),
    inference(resolution,[status(thm)],[c_2056,c_0])).

cnf(c_2518,plain,
    ( r1_tarski(sK7,X0)
    | r1_tarski(sK8,sK10) ),
    inference(resolution,[status(thm)],[c_2102,c_1])).

cnf(c_2519,plain,
    ( r1_tarski(sK7,X0) = iProver_top
    | r1_tarski(sK8,sK10) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2518])).

cnf(c_1466,plain,
    ( r2_hidden(X0,sK9)
    | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(sK7,sK8)) ),
    inference(resolution,[status(thm)],[c_18,c_964])).

cnf(c_1958,plain,
    ( r2_hidden(X0,sK9)
    | ~ r2_hidden(X0,sK7)
    | ~ r2_hidden(X1,sK8) ),
    inference(resolution,[status(thm)],[c_1466,c_16])).

cnf(c_2076,plain,
    ( r2_hidden(X0,sK9)
    | ~ r2_hidden(X0,sK7)
    | r1_tarski(sK8,X1) ),
    inference(resolution,[status(thm)],[c_1958,c_1])).

cnf(c_2201,plain,
    ( ~ r2_hidden(sK0(X0,sK9),sK7)
    | r1_tarski(X0,sK9)
    | r1_tarski(sK8,X1) ),
    inference(resolution,[status(thm)],[c_2076,c_0])).

cnf(c_2530,plain,
    ( r1_tarski(sK7,sK9)
    | r1_tarski(sK8,X0) ),
    inference(resolution,[status(thm)],[c_2201,c_1])).

cnf(c_2531,plain,
    ( r1_tarski(sK7,sK9) = iProver_top
    | r1_tarski(sK8,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2530])).

cnf(c_2533,plain,
    ( r1_tarski(sK7,sK9) = iProver_top
    | r1_tarski(sK8,k1_xboole_0) = iProver_top ),
    inference(instantiation,[status(thm)],[c_2531])).

cnf(c_622,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r2_hidden(k4_tarski(X2,X0),k2_zfmisc_1(X3,X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_3904,plain,
    ( r2_hidden(sK6(sK7,sK8,sK1(k2_zfmisc_1(sK7,sK8),k2_zfmisc_1(sK9,sK10))),X0) = iProver_top
    | r2_hidden(sK1(k2_zfmisc_1(sK7,sK8),k2_zfmisc_1(sK9,sK10)),k2_zfmisc_1(X1,X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3899,c_622])).

cnf(c_6656,plain,
    ( r1_xboole_0(k2_zfmisc_1(sK7,sK8),k2_zfmisc_1(sK9,sK10)) = iProver_top
    | r2_hidden(sK6(sK7,sK8,sK1(k2_zfmisc_1(sK7,sK8),k2_zfmisc_1(sK9,sK10))),sK8) = iProver_top ),
    inference(superposition,[status(thm)],[c_1786,c_3904])).

cnf(c_6677,plain,
    ( r2_hidden(sK6(sK7,sK8,sK1(k2_zfmisc_1(sK7,sK8),k2_zfmisc_1(sK9,sK10))),sK8) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6656,c_23,c_27,c_28,c_814,c_2181,c_5071])).

cnf(c_6682,plain,
    ( r2_hidden(sK6(sK7,sK8,sK1(k2_zfmisc_1(sK7,sK8),k2_zfmisc_1(sK9,sK10))),X0) = iProver_top
    | r1_tarski(sK8,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_6677,c_636])).

cnf(c_6995,plain,
    ( r1_tarski(sK8,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_6682,c_1641])).

cnf(c_8105,plain,
    ( r2_hidden(sK5(sK7,sK8,sK1(k2_zfmisc_1(sK7,sK8),k2_zfmisc_1(sK9,sK10))),X0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_7961,c_26,c_2519,c_2533,c_6995])).

cnf(c_8115,plain,
    ( $false ),
    inference(superposition,[status(thm)],[c_8105,c_1641])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : iproveropt_run.sh %d %s
% 0.11/0.33  % Computer   : n002.cluster.edu
% 0.11/0.33  % Model      : x86_64 x86_64
% 0.11/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.33  % Memory     : 8042.1875MB
% 0.11/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.33  % CPULimit   : 60
% 0.11/0.33  % WCLimit    : 600
% 0.11/0.33  % DateTime   : Tue Dec  1 13:24:07 EST 2020
% 0.11/0.33  % CPUTime    : 
% 0.11/0.33  % Running in FOF mode
% 3.57/0.98  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.57/0.98  
% 3.57/0.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.57/0.98  
% 3.57/0.98  ------  iProver source info
% 3.57/0.98  
% 3.57/0.98  git: date: 2020-06-30 10:37:57 +0100
% 3.57/0.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.57/0.98  git: non_committed_changes: false
% 3.57/0.98  git: last_make_outside_of_git: false
% 3.57/0.98  
% 3.57/0.98  ------ 
% 3.57/0.98  ------ Parsing...
% 3.57/0.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.57/0.98  
% 3.57/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 1 0s  sf_e 
% 3.57/0.98  
% 3.57/0.98  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.57/0.98  
% 3.57/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.57/0.98  ------ Proving...
% 3.57/0.98  ------ Problem Properties 
% 3.57/0.98  
% 3.57/0.98  
% 3.57/0.98  clauses                                 24
% 3.57/0.98  conjectures                             3
% 3.57/0.98  EPR                                     4
% 3.57/0.98  Horn                                    18
% 3.57/0.98  unary                                   6
% 3.57/0.98  binary                                  11
% 3.57/0.98  lits                                    51
% 3.57/0.98  lits eq                                 14
% 3.57/0.98  fd_pure                                 0
% 3.57/0.98  fd_pseudo                               0
% 3.57/0.98  fd_cond                                 1
% 3.57/0.98  fd_pseudo_cond                          4
% 3.57/0.98  AC symbols                              0
% 3.57/0.98  
% 3.57/0.98  ------ Input Options Time Limit: Unbounded
% 3.57/0.98  
% 3.57/0.98  
% 3.57/0.98  ------ 
% 3.57/0.98  Current options:
% 3.57/0.98  ------ 
% 3.57/0.98  
% 3.57/0.98  
% 3.57/0.98  
% 3.57/0.98  
% 3.57/0.98  ------ Proving...
% 3.57/0.98  
% 3.57/0.98  
% 3.57/0.98  % SZS status Theorem for theBenchmark.p
% 3.57/0.98  
% 3.57/0.98   Resolution empty clause
% 3.57/0.98  
% 3.57/0.98  % SZS output start CNFRefutation for theBenchmark.p
% 3.57/0.98  
% 3.57/0.98  fof(f9,conjecture,(
% 3.57/0.98    ! [X0,X1,X2,X3] : (r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)) => ((r1_tarski(X1,X3) & r1_tarski(X0,X2)) | k1_xboole_0 = k2_zfmisc_1(X0,X1)))),
% 3.57/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.57/0.98  
% 3.57/0.98  fof(f10,negated_conjecture,(
% 3.57/0.98    ~! [X0,X1,X2,X3] : (r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)) => ((r1_tarski(X1,X3) & r1_tarski(X0,X2)) | k1_xboole_0 = k2_zfmisc_1(X0,X1)))),
% 3.57/0.98    inference(negated_conjecture,[],[f9])).
% 3.57/0.98  
% 3.57/0.98  fof(f15,plain,(
% 3.57/0.98    ? [X0,X1,X2,X3] : (((~r1_tarski(X1,X3) | ~r1_tarski(X0,X2)) & k1_xboole_0 != k2_zfmisc_1(X0,X1)) & r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)))),
% 3.57/0.98    inference(ennf_transformation,[],[f10])).
% 3.57/0.98  
% 3.57/0.98  fof(f16,plain,(
% 3.57/0.98    ? [X0,X1,X2,X3] : ((~r1_tarski(X1,X3) | ~r1_tarski(X0,X2)) & k1_xboole_0 != k2_zfmisc_1(X0,X1) & r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)))),
% 3.57/0.98    inference(flattening,[],[f15])).
% 3.57/0.98  
% 3.57/0.98  fof(f33,plain,(
% 3.57/0.98    ? [X0,X1,X2,X3] : ((~r1_tarski(X1,X3) | ~r1_tarski(X0,X2)) & k1_xboole_0 != k2_zfmisc_1(X0,X1) & r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3))) => ((~r1_tarski(sK8,sK10) | ~r1_tarski(sK7,sK9)) & k1_xboole_0 != k2_zfmisc_1(sK7,sK8) & r1_tarski(k2_zfmisc_1(sK7,sK8),k2_zfmisc_1(sK9,sK10)))),
% 3.57/0.98    introduced(choice_axiom,[])).
% 3.57/0.98  
% 3.57/0.98  fof(f34,plain,(
% 3.57/0.98    (~r1_tarski(sK8,sK10) | ~r1_tarski(sK7,sK9)) & k1_xboole_0 != k2_zfmisc_1(sK7,sK8) & r1_tarski(k2_zfmisc_1(sK7,sK8),k2_zfmisc_1(sK9,sK10))),
% 3.57/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7,sK8,sK9,sK10])],[f16,f33])).
% 3.57/0.98  
% 3.57/0.98  fof(f57,plain,(
% 3.57/0.98    r1_tarski(k2_zfmisc_1(sK7,sK8),k2_zfmisc_1(sK9,sK10))),
% 3.57/0.98    inference(cnf_transformation,[],[f34])).
% 3.57/0.98  
% 3.57/0.98  fof(f3,axiom,(
% 3.57/0.98    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 3.57/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.57/0.98  
% 3.57/0.98  fof(f14,plain,(
% 3.57/0.98    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 3.57/0.98    inference(ennf_transformation,[],[f3])).
% 3.57/0.98  
% 3.57/0.98  fof(f40,plain,(
% 3.57/0.98    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 3.57/0.98    inference(cnf_transformation,[],[f14])).
% 3.57/0.98  
% 3.57/0.98  fof(f2,axiom,(
% 3.57/0.98    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 3.57/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.57/0.98  
% 3.57/0.98  fof(f11,plain,(
% 3.57/0.98    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X3] : ~r2_hidden(X3,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 3.57/0.98    inference(rectify,[],[f2])).
% 3.57/0.98  
% 3.57/0.98  fof(f13,plain,(
% 3.57/0.98    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 3.57/0.98    inference(ennf_transformation,[],[f11])).
% 3.57/0.98  
% 3.57/0.98  fof(f21,plain,(
% 3.57/0.98    ! [X1,X0] : (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) => r2_hidden(sK1(X0,X1),k3_xboole_0(X0,X1)))),
% 3.57/0.98    introduced(choice_axiom,[])).
% 3.57/0.98  
% 3.57/0.98  fof(f22,plain,(
% 3.57/0.98    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (r2_hidden(sK1(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 3.57/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f13,f21])).
% 3.57/0.98  
% 3.57/0.98  fof(f38,plain,(
% 3.57/0.98    ( ! [X0,X1] : (r2_hidden(sK1(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)) )),
% 3.57/0.98    inference(cnf_transformation,[],[f22])).
% 3.57/0.98  
% 3.57/0.98  fof(f6,axiom,(
% 3.57/0.98    ! [X0,X1,X2] : (k2_zfmisc_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4,X5] : (k4_tarski(X4,X5) = X3 & r2_hidden(X5,X1) & r2_hidden(X4,X0))))),
% 3.57/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.57/0.98  
% 3.57/0.98  fof(f23,plain,(
% 3.57/0.98    ! [X0,X1,X2] : ((k2_zfmisc_1(X0,X1) = X2 | ? [X3] : ((! [X4,X5] : (k4_tarski(X4,X5) != X3 | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X0)) | ~r2_hidden(X3,X2)) & (? [X4,X5] : (k4_tarski(X4,X5) = X3 & r2_hidden(X5,X1) & r2_hidden(X4,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ! [X4,X5] : (k4_tarski(X4,X5) != X3 | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X0))) & (? [X4,X5] : (k4_tarski(X4,X5) = X3 & r2_hidden(X5,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X3,X2))) | k2_zfmisc_1(X0,X1) != X2))),
% 3.57/0.98    inference(nnf_transformation,[],[f6])).
% 3.57/0.98  
% 3.57/0.98  fof(f24,plain,(
% 3.57/0.98    ! [X0,X1,X2] : ((k2_zfmisc_1(X0,X1) = X2 | ? [X3] : ((! [X4,X5] : (k4_tarski(X4,X5) != X3 | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X0)) | ~r2_hidden(X3,X2)) & (? [X6,X7] : (k4_tarski(X6,X7) = X3 & r2_hidden(X7,X1) & r2_hidden(X6,X0)) | r2_hidden(X3,X2)))) & (! [X8] : ((r2_hidden(X8,X2) | ! [X9,X10] : (k4_tarski(X9,X10) != X8 | ~r2_hidden(X10,X1) | ~r2_hidden(X9,X0))) & (? [X11,X12] : (k4_tarski(X11,X12) = X8 & r2_hidden(X12,X1) & r2_hidden(X11,X0)) | ~r2_hidden(X8,X2))) | k2_zfmisc_1(X0,X1) != X2))),
% 3.57/0.98    inference(rectify,[],[f23])).
% 3.57/0.98  
% 3.57/0.98  fof(f27,plain,(
% 3.57/0.98    ! [X8,X1,X0] : (? [X11,X12] : (k4_tarski(X11,X12) = X8 & r2_hidden(X12,X1) & r2_hidden(X11,X0)) => (k4_tarski(sK5(X0,X1,X8),sK6(X0,X1,X8)) = X8 & r2_hidden(sK6(X0,X1,X8),X1) & r2_hidden(sK5(X0,X1,X8),X0)))),
% 3.57/0.98    introduced(choice_axiom,[])).
% 3.57/0.98  
% 3.57/0.98  fof(f26,plain,(
% 3.57/0.98    ( ! [X3] : (! [X2,X1,X0] : (? [X6,X7] : (k4_tarski(X6,X7) = X3 & r2_hidden(X7,X1) & r2_hidden(X6,X0)) => (k4_tarski(sK3(X0,X1,X2),sK4(X0,X1,X2)) = X3 & r2_hidden(sK4(X0,X1,X2),X1) & r2_hidden(sK3(X0,X1,X2),X0)))) )),
% 3.57/0.98    introduced(choice_axiom,[])).
% 3.57/0.98  
% 3.57/0.98  fof(f25,plain,(
% 3.57/0.98    ! [X2,X1,X0] : (? [X3] : ((! [X4,X5] : (k4_tarski(X4,X5) != X3 | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X0)) | ~r2_hidden(X3,X2)) & (? [X6,X7] : (k4_tarski(X6,X7) = X3 & r2_hidden(X7,X1) & r2_hidden(X6,X0)) | r2_hidden(X3,X2))) => ((! [X5,X4] : (k4_tarski(X4,X5) != sK2(X0,X1,X2) | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X0)) | ~r2_hidden(sK2(X0,X1,X2),X2)) & (? [X7,X6] : (k4_tarski(X6,X7) = sK2(X0,X1,X2) & r2_hidden(X7,X1) & r2_hidden(X6,X0)) | r2_hidden(sK2(X0,X1,X2),X2))))),
% 3.57/0.98    introduced(choice_axiom,[])).
% 3.57/0.98  
% 3.57/0.98  fof(f28,plain,(
% 3.57/0.98    ! [X0,X1,X2] : ((k2_zfmisc_1(X0,X1) = X2 | ((! [X4,X5] : (k4_tarski(X4,X5) != sK2(X0,X1,X2) | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X0)) | ~r2_hidden(sK2(X0,X1,X2),X2)) & ((k4_tarski(sK3(X0,X1,X2),sK4(X0,X1,X2)) = sK2(X0,X1,X2) & r2_hidden(sK4(X0,X1,X2),X1) & r2_hidden(sK3(X0,X1,X2),X0)) | r2_hidden(sK2(X0,X1,X2),X2)))) & (! [X8] : ((r2_hidden(X8,X2) | ! [X9,X10] : (k4_tarski(X9,X10) != X8 | ~r2_hidden(X10,X1) | ~r2_hidden(X9,X0))) & ((k4_tarski(sK5(X0,X1,X8),sK6(X0,X1,X8)) = X8 & r2_hidden(sK6(X0,X1,X8),X1) & r2_hidden(sK5(X0,X1,X8),X0)) | ~r2_hidden(X8,X2))) | k2_zfmisc_1(X0,X1) != X2))),
% 3.57/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5,sK6])],[f24,f27,f26,f25])).
% 3.57/0.98  
% 3.57/0.98  fof(f45,plain,(
% 3.57/0.98    ( ! [X2,X0,X8,X1] : (k4_tarski(sK5(X0,X1,X8),sK6(X0,X1,X8)) = X8 | ~r2_hidden(X8,X2) | k2_zfmisc_1(X0,X1) != X2) )),
% 3.57/0.98    inference(cnf_transformation,[],[f28])).
% 3.57/0.98  
% 3.57/0.98  fof(f62,plain,(
% 3.57/0.98    ( ! [X0,X8,X1] : (k4_tarski(sK5(X0,X1,X8),sK6(X0,X1,X8)) = X8 | ~r2_hidden(X8,k2_zfmisc_1(X0,X1))) )),
% 3.57/0.98    inference(equality_resolution,[],[f45])).
% 3.57/0.98  
% 3.57/0.98  fof(f1,axiom,(
% 3.57/0.98    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 3.57/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.57/0.98  
% 3.57/0.98  fof(f12,plain,(
% 3.57/0.98    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 3.57/0.98    inference(ennf_transformation,[],[f1])).
% 3.57/0.98  
% 3.57/0.98  fof(f17,plain,(
% 3.57/0.98    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 3.57/0.98    inference(nnf_transformation,[],[f12])).
% 3.57/0.98  
% 3.57/0.98  fof(f18,plain,(
% 3.57/0.98    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 3.57/0.98    inference(rectify,[],[f17])).
% 3.57/0.98  
% 3.57/0.98  fof(f19,plain,(
% 3.57/0.98    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 3.57/0.98    introduced(choice_axiom,[])).
% 3.57/0.98  
% 3.57/0.98  fof(f20,plain,(
% 3.57/0.98    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 3.57/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f18,f19])).
% 3.57/0.98  
% 3.57/0.98  fof(f36,plain,(
% 3.57/0.98    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK0(X0,X1),X0)) )),
% 3.57/0.98    inference(cnf_transformation,[],[f20])).
% 3.57/0.98  
% 3.57/0.98  fof(f39,plain,(
% 3.57/0.98    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,k3_xboole_0(X0,X1))) )),
% 3.57/0.98    inference(cnf_transformation,[],[f22])).
% 3.57/0.98  
% 3.57/0.98  fof(f58,plain,(
% 3.57/0.98    k1_xboole_0 != k2_zfmisc_1(sK7,sK8)),
% 3.57/0.98    inference(cnf_transformation,[],[f34])).
% 3.57/0.98  
% 3.57/0.98  fof(f8,axiom,(
% 3.57/0.98    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 3.57/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.57/0.98  
% 3.57/0.98  fof(f31,plain,(
% 3.57/0.98    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 3.57/0.98    inference(nnf_transformation,[],[f8])).
% 3.57/0.98  
% 3.57/0.98  fof(f32,plain,(
% 3.57/0.98    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 3.57/0.98    inference(flattening,[],[f31])).
% 3.57/0.98  
% 3.57/0.98  fof(f54,plain,(
% 3.57/0.98    ( ! [X0,X1] : (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)) )),
% 3.57/0.98    inference(cnf_transformation,[],[f32])).
% 3.57/0.98  
% 3.57/0.98  fof(f55,plain,(
% 3.57/0.98    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X0) )),
% 3.57/0.98    inference(cnf_transformation,[],[f32])).
% 3.57/0.98  
% 3.57/0.98  fof(f66,plain,(
% 3.57/0.98    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 3.57/0.98    inference(equality_resolution,[],[f55])).
% 3.57/0.98  
% 3.57/0.98  fof(f47,plain,(
% 3.57/0.98    ( ! [X2,X0,X1] : (k2_zfmisc_1(X0,X1) = X2 | r2_hidden(sK3(X0,X1,X2),X0) | r2_hidden(sK2(X0,X1,X2),X2)) )),
% 3.57/0.98    inference(cnf_transformation,[],[f28])).
% 3.57/0.98  
% 3.57/0.98  fof(f5,axiom,(
% 3.57/0.98    ! [X0] : r1_xboole_0(X0,k1_xboole_0)),
% 3.57/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.57/0.98  
% 3.57/0.98  fof(f42,plain,(
% 3.57/0.98    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) )),
% 3.57/0.98    inference(cnf_transformation,[],[f5])).
% 3.57/0.98  
% 3.57/0.98  fof(f4,axiom,(
% 3.57/0.98    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 3.57/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.57/0.98  
% 3.57/0.98  fof(f41,plain,(
% 3.57/0.98    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 3.57/0.98    inference(cnf_transformation,[],[f4])).
% 3.57/0.98  
% 3.57/0.98  fof(f7,axiom,(
% 3.57/0.98    ! [X0,X1,X2,X3] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) <=> (r2_hidden(X1,X3) & r2_hidden(X0,X2)))),
% 3.57/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.57/0.98  
% 3.57/0.98  fof(f29,plain,(
% 3.57/0.98    ! [X0,X1,X2,X3] : ((r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | (~r2_hidden(X1,X3) | ~r2_hidden(X0,X2))) & ((r2_hidden(X1,X3) & r2_hidden(X0,X2)) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))))),
% 3.57/0.98    inference(nnf_transformation,[],[f7])).
% 3.57/0.98  
% 3.57/0.98  fof(f30,plain,(
% 3.57/0.98    ! [X0,X1,X2,X3] : ((r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | ~r2_hidden(X1,X3) | ~r2_hidden(X0,X2)) & ((r2_hidden(X1,X3) & r2_hidden(X0,X2)) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))))),
% 3.57/0.98    inference(flattening,[],[f29])).
% 3.57/0.98  
% 3.57/0.98  fof(f51,plain,(
% 3.57/0.98    ( ! [X2,X0,X3,X1] : (r2_hidden(X0,X2) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))) )),
% 3.57/0.98    inference(cnf_transformation,[],[f30])).
% 3.57/0.98  
% 3.57/0.98  fof(f35,plain,(
% 3.57/0.98    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,X1)) )),
% 3.57/0.98    inference(cnf_transformation,[],[f20])).
% 3.57/0.98  
% 3.57/0.98  fof(f59,plain,(
% 3.57/0.98    ~r1_tarski(sK8,sK10) | ~r1_tarski(sK7,sK9)),
% 3.57/0.98    inference(cnf_transformation,[],[f34])).
% 3.57/0.98  
% 3.57/0.98  fof(f52,plain,(
% 3.57/0.98    ( ! [X2,X0,X3,X1] : (r2_hidden(X1,X3) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))) )),
% 3.57/0.98    inference(cnf_transformation,[],[f30])).
% 3.57/0.98  
% 3.57/0.98  fof(f53,plain,(
% 3.57/0.98    ( ! [X2,X0,X3,X1] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | ~r2_hidden(X1,X3) | ~r2_hidden(X0,X2)) )),
% 3.57/0.98    inference(cnf_transformation,[],[f30])).
% 3.57/0.98  
% 3.57/0.98  fof(f37,plain,(
% 3.57/0.98    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r2_hidden(sK0(X0,X1),X1)) )),
% 3.57/0.98    inference(cnf_transformation,[],[f20])).
% 3.57/0.98  
% 3.57/0.98  cnf(c_24,negated_conjecture,
% 3.57/0.98      ( r1_tarski(k2_zfmisc_1(sK7,sK8),k2_zfmisc_1(sK9,sK10)) ),
% 3.57/0.98      inference(cnf_transformation,[],[f57]) ).
% 3.57/0.98  
% 3.57/0.98  cnf(c_619,plain,
% 3.57/0.98      ( r1_tarski(k2_zfmisc_1(sK7,sK8),k2_zfmisc_1(sK9,sK10)) = iProver_top ),
% 3.57/0.98      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 3.57/0.98  
% 3.57/0.98  cnf(c_5,plain,
% 3.57/0.98      ( ~ r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0 ),
% 3.57/0.98      inference(cnf_transformation,[],[f40]) ).
% 3.57/0.98  
% 3.57/0.98  cnf(c_633,plain,
% 3.57/0.98      ( k3_xboole_0(X0,X1) = X0 | r1_tarski(X0,X1) != iProver_top ),
% 3.57/0.98      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 3.57/0.98  
% 3.57/0.98  cnf(c_937,plain,
% 3.57/0.98      ( k3_xboole_0(k2_zfmisc_1(sK7,sK8),k2_zfmisc_1(sK9,sK10)) = k2_zfmisc_1(sK7,sK8) ),
% 3.57/0.98      inference(superposition,[status(thm)],[c_619,c_633]) ).
% 3.57/0.98  
% 3.57/0.98  cnf(c_4,plain,
% 3.57/0.98      ( r1_xboole_0(X0,X1) | r2_hidden(sK1(X0,X1),k3_xboole_0(X0,X1)) ),
% 3.57/0.98      inference(cnf_transformation,[],[f38]) ).
% 3.57/0.98  
% 3.57/0.98  cnf(c_634,plain,
% 3.57/0.98      ( r1_xboole_0(X0,X1) = iProver_top
% 3.57/0.98      | r2_hidden(sK1(X0,X1),k3_xboole_0(X0,X1)) = iProver_top ),
% 3.57/0.98      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 3.57/0.98  
% 3.57/0.98  cnf(c_1786,plain,
% 3.57/0.98      ( r1_xboole_0(k2_zfmisc_1(sK7,sK8),k2_zfmisc_1(sK9,sK10)) = iProver_top
% 3.57/0.98      | r2_hidden(sK1(k2_zfmisc_1(sK7,sK8),k2_zfmisc_1(sK9,sK10)),k2_zfmisc_1(sK7,sK8)) = iProver_top ),
% 3.57/0.98      inference(superposition,[status(thm)],[c_937,c_634]) ).
% 3.57/0.98  
% 3.57/0.98  cnf(c_13,plain,
% 3.57/0.98      ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
% 3.57/0.98      | k4_tarski(sK5(X1,X2,X0),sK6(X1,X2,X0)) = X0 ),
% 3.57/0.98      inference(cnf_transformation,[],[f62]) ).
% 3.57/0.98  
% 3.57/0.98  cnf(c_625,plain,
% 3.57/0.98      ( k4_tarski(sK5(X0,X1,X2),sK6(X0,X1,X2)) = X2
% 3.57/0.98      | r2_hidden(X2,k2_zfmisc_1(X0,X1)) != iProver_top ),
% 3.57/0.98      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 3.57/0.98  
% 3.57/0.98  cnf(c_2477,plain,
% 3.57/0.98      ( k4_tarski(sK5(sK7,sK8,sK1(k2_zfmisc_1(sK7,sK8),k2_zfmisc_1(sK9,sK10))),sK6(sK7,sK8,sK1(k2_zfmisc_1(sK7,sK8),k2_zfmisc_1(sK9,sK10)))) = sK1(k2_zfmisc_1(sK7,sK8),k2_zfmisc_1(sK9,sK10))
% 3.57/0.98      | r1_xboole_0(k2_zfmisc_1(sK7,sK8),k2_zfmisc_1(sK9,sK10)) = iProver_top ),
% 3.57/0.98      inference(superposition,[status(thm)],[c_1786,c_625]) ).
% 3.57/0.98  
% 3.57/0.98  cnf(c_1,plain,
% 3.57/0.98      ( r2_hidden(sK0(X0,X1),X0) | r1_tarski(X0,X1) ),
% 3.57/0.98      inference(cnf_transformation,[],[f36]) ).
% 3.57/0.98  
% 3.57/0.98  cnf(c_637,plain,
% 3.57/0.98      ( r2_hidden(sK0(X0,X1),X0) = iProver_top
% 3.57/0.98      | r1_tarski(X0,X1) = iProver_top ),
% 3.57/0.98      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 3.57/0.98  
% 3.57/0.98  cnf(c_3,plain,
% 3.57/0.98      ( ~ r1_xboole_0(X0,X1) | ~ r2_hidden(X2,k3_xboole_0(X0,X1)) ),
% 3.57/0.98      inference(cnf_transformation,[],[f39]) ).
% 3.57/0.98  
% 3.57/0.98  cnf(c_635,plain,
% 3.57/0.98      ( r1_xboole_0(X0,X1) != iProver_top
% 3.57/0.98      | r2_hidden(X2,k3_xboole_0(X0,X1)) != iProver_top ),
% 3.57/0.98      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 3.57/0.98  
% 3.57/0.98  cnf(c_1496,plain,
% 3.57/0.98      ( r1_xboole_0(X0,X1) != iProver_top
% 3.57/0.98      | r1_tarski(k3_xboole_0(X0,X1),X2) = iProver_top ),
% 3.57/0.98      inference(superposition,[status(thm)],[c_637,c_635]) ).
% 3.57/0.98  
% 3.57/0.98  cnf(c_2165,plain,
% 3.57/0.98      ( k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,X1)
% 3.57/0.98      | r1_xboole_0(X0,X1) != iProver_top ),
% 3.57/0.98      inference(superposition,[status(thm)],[c_1496,c_633]) ).
% 3.57/0.98  
% 3.57/0.98  cnf(c_3246,plain,
% 3.57/0.98      ( k4_tarski(sK5(sK7,sK8,sK1(k2_zfmisc_1(sK7,sK8),k2_zfmisc_1(sK9,sK10))),sK6(sK7,sK8,sK1(k2_zfmisc_1(sK7,sK8),k2_zfmisc_1(sK9,sK10)))) = sK1(k2_zfmisc_1(sK7,sK8),k2_zfmisc_1(sK9,sK10))
% 3.57/0.98      | k3_xboole_0(k3_xboole_0(k2_zfmisc_1(sK7,sK8),k2_zfmisc_1(sK9,sK10)),X0) = k3_xboole_0(k2_zfmisc_1(sK7,sK8),k2_zfmisc_1(sK9,sK10)) ),
% 3.57/0.98      inference(superposition,[status(thm)],[c_2477,c_2165]) ).
% 3.57/0.98  
% 3.57/0.98  cnf(c_3259,plain,
% 3.57/0.98      ( k4_tarski(sK5(sK7,sK8,sK1(k2_zfmisc_1(sK7,sK8),k2_zfmisc_1(sK9,sK10))),sK6(sK7,sK8,sK1(k2_zfmisc_1(sK7,sK8),k2_zfmisc_1(sK9,sK10)))) = sK1(k2_zfmisc_1(sK7,sK8),k2_zfmisc_1(sK9,sK10))
% 3.57/0.98      | k3_xboole_0(k2_zfmisc_1(sK7,sK8),X0) = k2_zfmisc_1(sK7,sK8) ),
% 3.57/0.98      inference(light_normalisation,[status(thm)],[c_3246,c_937]) ).
% 3.57/0.98  
% 3.57/0.98  cnf(c_3548,plain,
% 3.57/0.98      ( k4_tarski(sK5(sK7,sK8,sK1(k2_zfmisc_1(sK7,sK8),k2_zfmisc_1(sK9,sK10))),sK6(sK7,sK8,sK1(k2_zfmisc_1(sK7,sK8),k2_zfmisc_1(sK9,sK10)))) = sK1(k2_zfmisc_1(sK7,sK8),k2_zfmisc_1(sK9,sK10))
% 3.57/0.98      | r1_xboole_0(k2_zfmisc_1(sK7,sK8),X0) != iProver_top
% 3.57/0.98      | r2_hidden(X1,k2_zfmisc_1(sK7,sK8)) != iProver_top ),
% 3.57/0.98      inference(superposition,[status(thm)],[c_3259,c_635]) ).
% 3.57/0.98  
% 3.57/0.98  cnf(c_23,negated_conjecture,
% 3.57/0.98      ( k1_xboole_0 != k2_zfmisc_1(sK7,sK8) ),
% 3.57/0.98      inference(cnf_transformation,[],[f58]) ).
% 3.57/0.98  
% 3.57/0.98  cnf(c_21,plain,
% 3.57/0.98      ( k2_zfmisc_1(X0,X1) != k1_xboole_0
% 3.57/0.98      | k1_xboole_0 = X1
% 3.57/0.98      | k1_xboole_0 = X0 ),
% 3.57/0.98      inference(cnf_transformation,[],[f54]) ).
% 3.57/0.98  
% 3.57/0.98  cnf(c_27,plain,
% 3.57/0.98      ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) != k1_xboole_0
% 3.57/0.98      | k1_xboole_0 = k1_xboole_0 ),
% 3.57/0.98      inference(instantiation,[status(thm)],[c_21]) ).
% 3.57/0.98  
% 3.57/0.98  cnf(c_20,plain,
% 3.57/0.98      ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
% 3.57/0.98      inference(cnf_transformation,[],[f66]) ).
% 3.57/0.98  
% 3.57/0.98  cnf(c_28,plain,
% 3.57/0.98      ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
% 3.57/0.98      inference(instantiation,[status(thm)],[c_20]) ).
% 3.57/0.98  
% 3.57/0.98  cnf(c_288,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 3.57/0.98  
% 3.57/0.98  cnf(c_813,plain,
% 3.57/0.98      ( k2_zfmisc_1(sK7,sK8) != X0
% 3.57/0.98      | k1_xboole_0 != X0
% 3.57/0.98      | k1_xboole_0 = k2_zfmisc_1(sK7,sK8) ),
% 3.57/0.98      inference(instantiation,[status(thm)],[c_288]) ).
% 3.57/0.98  
% 3.57/0.98  cnf(c_814,plain,
% 3.57/0.98      ( k2_zfmisc_1(sK7,sK8) != k1_xboole_0
% 3.57/0.98      | k1_xboole_0 = k2_zfmisc_1(sK7,sK8)
% 3.57/0.98      | k1_xboole_0 != k1_xboole_0 ),
% 3.57/0.98      inference(instantiation,[status(thm)],[c_813]) ).
% 3.57/0.98  
% 3.57/0.98  cnf(c_11,plain,
% 3.57/0.98      ( r2_hidden(sK3(X0,X1,X2),X0)
% 3.57/0.98      | r2_hidden(sK2(X0,X1,X2),X2)
% 3.57/0.98      | k2_zfmisc_1(X0,X1) = X2 ),
% 3.57/0.98      inference(cnf_transformation,[],[f47]) ).
% 3.57/0.98  
% 3.57/0.98  cnf(c_627,plain,
% 3.57/0.98      ( k2_zfmisc_1(X0,X1) = X2
% 3.57/0.98      | r2_hidden(sK3(X0,X1,X2),X0) = iProver_top
% 3.57/0.98      | r2_hidden(sK2(X0,X1,X2),X2) = iProver_top ),
% 3.57/0.98      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 3.57/0.98  
% 3.57/0.98  cnf(c_7,plain,
% 3.57/0.98      ( r1_xboole_0(X0,k1_xboole_0) ),
% 3.57/0.98      inference(cnf_transformation,[],[f42]) ).
% 3.57/0.98  
% 3.57/0.98  cnf(c_631,plain,
% 3.57/0.98      ( r1_xboole_0(X0,k1_xboole_0) = iProver_top ),
% 3.57/0.98      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 3.57/0.98  
% 3.57/0.98  cnf(c_6,plain,
% 3.57/0.98      ( r1_tarski(k1_xboole_0,X0) ),
% 3.57/0.98      inference(cnf_transformation,[],[f41]) ).
% 3.57/0.98  
% 3.57/0.98  cnf(c_632,plain,
% 3.57/0.98      ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
% 3.57/0.98      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 3.57/0.98  
% 3.57/0.98  cnf(c_936,plain,
% 3.57/0.98      ( k3_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
% 3.57/0.98      inference(superposition,[status(thm)],[c_632,c_633]) ).
% 3.57/0.98  
% 3.57/0.98  cnf(c_1497,plain,
% 3.57/0.98      ( r1_xboole_0(k1_xboole_0,X0) != iProver_top
% 3.57/0.98      | r2_hidden(X1,k1_xboole_0) != iProver_top ),
% 3.57/0.98      inference(superposition,[status(thm)],[c_936,c_635]) ).
% 3.57/0.98  
% 3.57/0.98  cnf(c_1641,plain,
% 3.57/0.98      ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
% 3.57/0.98      inference(superposition,[status(thm)],[c_631,c_1497]) ).
% 3.57/0.98  
% 3.57/0.98  cnf(c_2942,plain,
% 3.57/0.98      ( k2_zfmisc_1(k1_xboole_0,X0) = X1
% 3.57/0.98      | r2_hidden(sK2(k1_xboole_0,X0,X1),X1) = iProver_top ),
% 3.57/0.98      inference(superposition,[status(thm)],[c_627,c_1641]) ).
% 3.57/0.98  
% 3.57/0.98  cnf(c_2945,plain,
% 3.57/0.98      ( k1_xboole_0 = X0 | r2_hidden(sK2(k1_xboole_0,X1,X0),X0) = iProver_top ),
% 3.57/0.98      inference(demodulation,[status(thm)],[c_2942,c_20]) ).
% 3.57/0.98  
% 3.57/0.98  cnf(c_1498,plain,
% 3.57/0.98      ( r1_xboole_0(k2_zfmisc_1(sK7,sK8),k2_zfmisc_1(sK9,sK10)) != iProver_top
% 3.57/0.98      | r2_hidden(X0,k2_zfmisc_1(sK7,sK8)) != iProver_top ),
% 3.57/0.98      inference(superposition,[status(thm)],[c_937,c_635]) ).
% 3.57/0.98  
% 3.57/0.98  cnf(c_3248,plain,
% 3.57/0.98      ( k4_tarski(sK5(sK7,sK8,sK1(k2_zfmisc_1(sK7,sK8),k2_zfmisc_1(sK9,sK10))),sK6(sK7,sK8,sK1(k2_zfmisc_1(sK7,sK8),k2_zfmisc_1(sK9,sK10)))) = sK1(k2_zfmisc_1(sK7,sK8),k2_zfmisc_1(sK9,sK10))
% 3.57/0.98      | r2_hidden(X0,k2_zfmisc_1(sK7,sK8)) != iProver_top ),
% 3.57/0.98      inference(superposition,[status(thm)],[c_2477,c_1498]) ).
% 3.57/0.98  
% 3.57/0.98  cnf(c_3629,plain,
% 3.57/0.98      ( k4_tarski(sK5(sK7,sK8,sK1(k2_zfmisc_1(sK7,sK8),k2_zfmisc_1(sK9,sK10))),sK6(sK7,sK8,sK1(k2_zfmisc_1(sK7,sK8),k2_zfmisc_1(sK9,sK10)))) = sK1(k2_zfmisc_1(sK7,sK8),k2_zfmisc_1(sK9,sK10))
% 3.57/0.98      | k2_zfmisc_1(sK7,sK8) = k1_xboole_0 ),
% 3.57/0.98      inference(superposition,[status(thm)],[c_2945,c_3248]) ).
% 3.57/0.98  
% 3.57/0.98  cnf(c_3899,plain,
% 3.57/0.98      ( k4_tarski(sK5(sK7,sK8,sK1(k2_zfmisc_1(sK7,sK8),k2_zfmisc_1(sK9,sK10))),sK6(sK7,sK8,sK1(k2_zfmisc_1(sK7,sK8),k2_zfmisc_1(sK9,sK10)))) = sK1(k2_zfmisc_1(sK7,sK8),k2_zfmisc_1(sK9,sK10)) ),
% 3.57/0.98      inference(global_propositional_subsumption,
% 3.57/0.98                [status(thm)],
% 3.57/0.98                [c_3548,c_23,c_27,c_28,c_814,c_3629]) ).
% 3.57/0.98  
% 3.57/0.98  cnf(c_18,plain,
% 3.57/0.98      ( r2_hidden(X0,X1) | ~ r2_hidden(k4_tarski(X0,X2),k2_zfmisc_1(X1,X3)) ),
% 3.57/0.98      inference(cnf_transformation,[],[f51]) ).
% 3.57/0.98  
% 3.57/0.98  cnf(c_621,plain,
% 3.57/0.98      ( r2_hidden(X0,X1) = iProver_top
% 3.57/0.98      | r2_hidden(k4_tarski(X0,X2),k2_zfmisc_1(X1,X3)) != iProver_top ),
% 3.57/0.98      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 3.57/0.98  
% 3.57/0.98  cnf(c_3906,plain,
% 3.57/0.98      ( r2_hidden(sK5(sK7,sK8,sK1(k2_zfmisc_1(sK7,sK8),k2_zfmisc_1(sK9,sK10))),X0) = iProver_top
% 3.57/0.98      | r2_hidden(sK1(k2_zfmisc_1(sK7,sK8),k2_zfmisc_1(sK9,sK10)),k2_zfmisc_1(X0,X1)) != iProver_top ),
% 3.57/0.98      inference(superposition,[status(thm)],[c_3899,c_621]) ).
% 3.57/0.98  
% 3.57/0.98  cnf(c_7935,plain,
% 3.57/0.98      ( r1_xboole_0(k2_zfmisc_1(sK7,sK8),k2_zfmisc_1(sK9,sK10)) = iProver_top
% 3.57/0.98      | r2_hidden(sK5(sK7,sK8,sK1(k2_zfmisc_1(sK7,sK8),k2_zfmisc_1(sK9,sK10))),sK7) = iProver_top ),
% 3.57/0.98      inference(superposition,[status(thm)],[c_1786,c_3906]) ).
% 3.57/0.98  
% 3.57/0.98  cnf(c_2163,plain,
% 3.57/0.98      ( r1_xboole_0(k2_zfmisc_1(sK7,sK8),k2_zfmisc_1(sK9,sK10)) != iProver_top
% 3.57/0.98      | r1_tarski(k2_zfmisc_1(sK7,sK8),X0) = iProver_top ),
% 3.57/0.98      inference(superposition,[status(thm)],[c_937,c_1496]) ).
% 3.57/0.98  
% 3.57/0.98  cnf(c_2181,plain,
% 3.57/0.98      ( r1_xboole_0(k2_zfmisc_1(sK7,sK8),k2_zfmisc_1(sK9,sK10)) != iProver_top
% 3.57/0.98      | r1_tarski(k2_zfmisc_1(sK7,sK8),k1_xboole_0) = iProver_top ),
% 3.57/0.98      inference(instantiation,[status(thm)],[c_2163]) ).
% 3.57/0.98  
% 3.57/0.98  cnf(c_2,plain,
% 3.57/0.98      ( ~ r2_hidden(X0,X1) | r2_hidden(X0,X2) | ~ r1_tarski(X1,X2) ),
% 3.57/0.98      inference(cnf_transformation,[],[f35]) ).
% 3.57/0.98  
% 3.57/0.98  cnf(c_636,plain,
% 3.57/0.98      ( r2_hidden(X0,X1) != iProver_top
% 3.57/0.98      | r2_hidden(X0,X2) = iProver_top
% 3.57/0.98      | r1_tarski(X1,X2) != iProver_top ),
% 3.57/0.98      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 3.57/0.98  
% 3.57/0.98  cnf(c_2634,plain,
% 3.57/0.98      ( r1_xboole_0(k2_zfmisc_1(sK7,sK8),k2_zfmisc_1(sK9,sK10)) = iProver_top
% 3.57/0.98      | r2_hidden(sK1(k2_zfmisc_1(sK7,sK8),k2_zfmisc_1(sK9,sK10)),X0) = iProver_top
% 3.57/0.98      | r1_tarski(k2_zfmisc_1(sK7,sK8),X0) != iProver_top ),
% 3.57/0.98      inference(superposition,[status(thm)],[c_1786,c_636]) ).
% 3.57/0.98  
% 3.57/0.98  cnf(c_3210,plain,
% 3.57/0.98      ( r1_xboole_0(k2_zfmisc_1(sK7,sK8),k2_zfmisc_1(sK9,sK10)) = iProver_top
% 3.57/0.98      | r1_tarski(k2_zfmisc_1(sK7,sK8),k1_xboole_0) != iProver_top ),
% 3.57/0.98      inference(superposition,[status(thm)],[c_2634,c_1641]) ).
% 3.57/0.98  
% 3.57/0.98  cnf(c_3008,plain,
% 3.57/0.98      ( k3_xboole_0(X0,X1) = k1_xboole_0 | r1_xboole_0(X0,X1) != iProver_top ),
% 3.57/0.98      inference(superposition,[status(thm)],[c_2945,c_635]) ).
% 3.57/0.98  
% 3.57/0.98  cnf(c_5052,plain,
% 3.57/0.98      ( k3_xboole_0(k2_zfmisc_1(sK7,sK8),k2_zfmisc_1(sK9,sK10)) = k1_xboole_0
% 3.57/0.98      | r1_tarski(k2_zfmisc_1(sK7,sK8),k1_xboole_0) != iProver_top ),
% 3.57/0.98      inference(superposition,[status(thm)],[c_3210,c_3008]) ).
% 3.57/0.98  
% 3.57/0.98  cnf(c_5071,plain,
% 3.57/0.98      ( k2_zfmisc_1(sK7,sK8) = k1_xboole_0
% 3.57/0.98      | r1_tarski(k2_zfmisc_1(sK7,sK8),k1_xboole_0) != iProver_top ),
% 3.57/0.98      inference(demodulation,[status(thm)],[c_5052,c_937]) ).
% 3.57/0.98  
% 3.57/0.98  cnf(c_7956,plain,
% 3.57/0.98      ( r2_hidden(sK5(sK7,sK8,sK1(k2_zfmisc_1(sK7,sK8),k2_zfmisc_1(sK9,sK10))),sK7) = iProver_top ),
% 3.57/0.98      inference(global_propositional_subsumption,
% 3.57/0.98                [status(thm)],
% 3.57/0.98                [c_7935,c_23,c_27,c_28,c_814,c_2181,c_5071]) ).
% 3.57/0.98  
% 3.57/0.98  cnf(c_7961,plain,
% 3.57/0.98      ( r2_hidden(sK5(sK7,sK8,sK1(k2_zfmisc_1(sK7,sK8),k2_zfmisc_1(sK9,sK10))),X0) = iProver_top
% 3.57/0.98      | r1_tarski(sK7,X0) != iProver_top ),
% 3.57/0.98      inference(superposition,[status(thm)],[c_7956,c_636]) ).
% 3.57/0.98  
% 3.57/0.98  cnf(c_22,negated_conjecture,
% 3.57/0.98      ( ~ r1_tarski(sK7,sK9) | ~ r1_tarski(sK8,sK10) ),
% 3.57/0.98      inference(cnf_transformation,[],[f59]) ).
% 3.57/0.98  
% 3.57/0.98  cnf(c_26,plain,
% 3.57/0.98      ( r1_tarski(sK7,sK9) != iProver_top
% 3.57/0.98      | r1_tarski(sK8,sK10) != iProver_top ),
% 3.57/0.98      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 3.57/0.98  
% 3.57/0.98  cnf(c_17,plain,
% 3.57/0.98      ( r2_hidden(X0,X1) | ~ r2_hidden(k4_tarski(X2,X0),k2_zfmisc_1(X3,X1)) ),
% 3.57/0.98      inference(cnf_transformation,[],[f52]) ).
% 3.57/0.98  
% 3.57/0.98  cnf(c_964,plain,
% 3.57/0.98      ( r2_hidden(X0,k2_zfmisc_1(sK9,sK10))
% 3.57/0.98      | ~ r2_hidden(X0,k2_zfmisc_1(sK7,sK8)) ),
% 3.57/0.98      inference(resolution,[status(thm)],[c_2,c_24]) ).
% 3.57/0.98  
% 3.57/0.98  cnf(c_1451,plain,
% 3.57/0.98      ( r2_hidden(X0,sK10)
% 3.57/0.98      | ~ r2_hidden(k4_tarski(X1,X0),k2_zfmisc_1(sK7,sK8)) ),
% 3.57/0.98      inference(resolution,[status(thm)],[c_17,c_964]) ).
% 3.57/0.98  
% 3.57/0.98  cnf(c_16,plain,
% 3.57/0.98      ( ~ r2_hidden(X0,X1)
% 3.57/0.98      | ~ r2_hidden(X2,X3)
% 3.57/0.98      | r2_hidden(k4_tarski(X2,X0),k2_zfmisc_1(X3,X1)) ),
% 3.57/0.98      inference(cnf_transformation,[],[f53]) ).
% 3.57/0.98  
% 3.57/0.98  cnf(c_1949,plain,
% 3.57/0.98      ( ~ r2_hidden(X0,sK7) | r2_hidden(X1,sK10) | ~ r2_hidden(X1,sK8) ),
% 3.57/0.98      inference(resolution,[status(thm)],[c_1451,c_16]) ).
% 3.57/0.98  
% 3.57/0.98  cnf(c_2056,plain,
% 3.57/0.98      ( r2_hidden(X0,sK10) | ~ r2_hidden(X0,sK8) | r1_tarski(sK7,X1) ),
% 3.57/0.98      inference(resolution,[status(thm)],[c_1949,c_1]) ).
% 3.57/0.98  
% 3.57/0.98  cnf(c_0,plain,
% 3.57/0.98      ( ~ r2_hidden(sK0(X0,X1),X1) | r1_tarski(X0,X1) ),
% 3.57/0.98      inference(cnf_transformation,[],[f37]) ).
% 3.57/0.98  
% 3.57/0.98  cnf(c_2102,plain,
% 3.57/0.98      ( ~ r2_hidden(sK0(X0,sK10),sK8)
% 3.57/0.98      | r1_tarski(X0,sK10)
% 3.57/0.98      | r1_tarski(sK7,X1) ),
% 3.57/0.98      inference(resolution,[status(thm)],[c_2056,c_0]) ).
% 3.57/0.98  
% 3.57/0.98  cnf(c_2518,plain,
% 3.57/0.98      ( r1_tarski(sK7,X0) | r1_tarski(sK8,sK10) ),
% 3.57/0.98      inference(resolution,[status(thm)],[c_2102,c_1]) ).
% 3.57/0.98  
% 3.57/0.98  cnf(c_2519,plain,
% 3.57/0.98      ( r1_tarski(sK7,X0) = iProver_top | r1_tarski(sK8,sK10) = iProver_top ),
% 3.57/0.98      inference(predicate_to_equality,[status(thm)],[c_2518]) ).
% 3.57/0.98  
% 3.57/0.98  cnf(c_1466,plain,
% 3.57/0.98      ( r2_hidden(X0,sK9)
% 3.57/0.98      | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(sK7,sK8)) ),
% 3.57/0.98      inference(resolution,[status(thm)],[c_18,c_964]) ).
% 3.57/0.98  
% 3.57/0.98  cnf(c_1958,plain,
% 3.57/0.98      ( r2_hidden(X0,sK9) | ~ r2_hidden(X0,sK7) | ~ r2_hidden(X1,sK8) ),
% 3.57/0.98      inference(resolution,[status(thm)],[c_1466,c_16]) ).
% 3.57/0.98  
% 3.57/0.98  cnf(c_2076,plain,
% 3.57/0.98      ( r2_hidden(X0,sK9) | ~ r2_hidden(X0,sK7) | r1_tarski(sK8,X1) ),
% 3.57/0.98      inference(resolution,[status(thm)],[c_1958,c_1]) ).
% 3.57/0.98  
% 3.57/0.98  cnf(c_2201,plain,
% 3.57/0.98      ( ~ r2_hidden(sK0(X0,sK9),sK7) | r1_tarski(X0,sK9) | r1_tarski(sK8,X1) ),
% 3.57/0.98      inference(resolution,[status(thm)],[c_2076,c_0]) ).
% 3.57/0.98  
% 3.57/0.98  cnf(c_2530,plain,
% 3.57/0.98      ( r1_tarski(sK7,sK9) | r1_tarski(sK8,X0) ),
% 3.57/0.98      inference(resolution,[status(thm)],[c_2201,c_1]) ).
% 3.57/0.98  
% 3.57/0.98  cnf(c_2531,plain,
% 3.57/0.98      ( r1_tarski(sK7,sK9) = iProver_top | r1_tarski(sK8,X0) = iProver_top ),
% 3.57/0.98      inference(predicate_to_equality,[status(thm)],[c_2530]) ).
% 3.57/0.98  
% 3.57/0.98  cnf(c_2533,plain,
% 3.57/0.98      ( r1_tarski(sK7,sK9) = iProver_top
% 3.57/0.98      | r1_tarski(sK8,k1_xboole_0) = iProver_top ),
% 3.57/0.98      inference(instantiation,[status(thm)],[c_2531]) ).
% 3.57/0.98  
% 3.57/0.98  cnf(c_622,plain,
% 3.57/0.98      ( r2_hidden(X0,X1) = iProver_top
% 3.57/0.98      | r2_hidden(k4_tarski(X2,X0),k2_zfmisc_1(X3,X1)) != iProver_top ),
% 3.57/0.98      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 3.57/0.98  
% 3.57/0.98  cnf(c_3904,plain,
% 3.57/0.98      ( r2_hidden(sK6(sK7,sK8,sK1(k2_zfmisc_1(sK7,sK8),k2_zfmisc_1(sK9,sK10))),X0) = iProver_top
% 3.57/0.98      | r2_hidden(sK1(k2_zfmisc_1(sK7,sK8),k2_zfmisc_1(sK9,sK10)),k2_zfmisc_1(X1,X0)) != iProver_top ),
% 3.57/0.98      inference(superposition,[status(thm)],[c_3899,c_622]) ).
% 3.57/0.98  
% 3.57/0.98  cnf(c_6656,plain,
% 3.57/0.98      ( r1_xboole_0(k2_zfmisc_1(sK7,sK8),k2_zfmisc_1(sK9,sK10)) = iProver_top
% 3.57/0.98      | r2_hidden(sK6(sK7,sK8,sK1(k2_zfmisc_1(sK7,sK8),k2_zfmisc_1(sK9,sK10))),sK8) = iProver_top ),
% 3.57/0.98      inference(superposition,[status(thm)],[c_1786,c_3904]) ).
% 3.57/0.98  
% 3.57/0.98  cnf(c_6677,plain,
% 3.57/0.98      ( r2_hidden(sK6(sK7,sK8,sK1(k2_zfmisc_1(sK7,sK8),k2_zfmisc_1(sK9,sK10))),sK8) = iProver_top ),
% 3.57/0.98      inference(global_propositional_subsumption,
% 3.57/0.98                [status(thm)],
% 3.57/0.98                [c_6656,c_23,c_27,c_28,c_814,c_2181,c_5071]) ).
% 3.57/0.98  
% 3.57/0.98  cnf(c_6682,plain,
% 3.57/0.98      ( r2_hidden(sK6(sK7,sK8,sK1(k2_zfmisc_1(sK7,sK8),k2_zfmisc_1(sK9,sK10))),X0) = iProver_top
% 3.57/0.98      | r1_tarski(sK8,X0) != iProver_top ),
% 3.57/0.98      inference(superposition,[status(thm)],[c_6677,c_636]) ).
% 3.57/0.98  
% 3.57/0.98  cnf(c_6995,plain,
% 3.57/0.98      ( r1_tarski(sK8,k1_xboole_0) != iProver_top ),
% 3.57/0.98      inference(superposition,[status(thm)],[c_6682,c_1641]) ).
% 3.57/0.98  
% 3.57/0.98  cnf(c_8105,plain,
% 3.57/0.98      ( r2_hidden(sK5(sK7,sK8,sK1(k2_zfmisc_1(sK7,sK8),k2_zfmisc_1(sK9,sK10))),X0) = iProver_top ),
% 3.57/0.98      inference(global_propositional_subsumption,
% 3.57/0.98                [status(thm)],
% 3.57/0.98                [c_7961,c_26,c_2519,c_2533,c_6995]) ).
% 3.57/0.98  
% 3.57/0.98  cnf(c_8115,plain,
% 3.57/0.98      ( $false ),
% 3.57/0.98      inference(superposition,[status(thm)],[c_8105,c_1641]) ).
% 3.57/0.98  
% 3.57/0.98  
% 3.57/0.98  % SZS output end CNFRefutation for theBenchmark.p
% 3.57/0.98  
% 3.57/0.98  ------                               Statistics
% 3.57/0.98  
% 3.57/0.98  ------ Selected
% 3.57/0.98  
% 3.57/0.98  total_time:                             0.271
% 3.57/0.98  
%------------------------------------------------------------------------------
