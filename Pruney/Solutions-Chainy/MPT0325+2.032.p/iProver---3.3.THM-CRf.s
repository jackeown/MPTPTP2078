%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:37:50 EST 2020

% Result     : Theorem 7.15s
% Output     : CNFRefutation 7.15s
% Verified   : 
% Statistics : Number of formulae       :  120 ( 278 expanded)
%              Number of clauses        :   65 (  86 expanded)
%              Number of leaves         :   19 (  67 expanded)
%              Depth                    :   16
%              Number of atoms          :  379 (1083 expanded)
%              Number of equality atoms :  115 ( 252 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal clause size      :   18 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( k2_zfmisc_1(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ? [X4,X5] :
              ( k4_tarski(X4,X5) = X3
              & r2_hidden(X5,X1)
              & r2_hidden(X4,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
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

fof(f25,plain,(
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
    inference(rectify,[],[f24])).

fof(f28,plain,(
    ! [X8,X1,X0] :
      ( ? [X11,X12] :
          ( k4_tarski(X11,X12) = X8
          & r2_hidden(X12,X1)
          & r2_hidden(X11,X0) )
     => ( k4_tarski(sK5(X0,X1,X8),sK6(X0,X1,X8)) = X8
        & r2_hidden(sK6(X0,X1,X8),X1)
        & r2_hidden(sK5(X0,X1,X8),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X6,X7] :
          ( k4_tarski(X6,X7) = X3
          & r2_hidden(X7,X1)
          & r2_hidden(X6,X0) )
     => ( k4_tarski(sK3(X0,X1,X2),sK4(X0,X1,X2)) = X3
        & r2_hidden(sK4(X0,X1,X2),X1)
        & r2_hidden(sK3(X0,X1,X2),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,(
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

fof(f29,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5,sK6])],[f25,f28,f27,f26])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( k2_zfmisc_1(X0,X1) = X2
      | r2_hidden(sK3(X0,X1,X2),X0)
      | r2_hidden(sK2(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
    <=> ( r2_hidden(X1,X3)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
        | ~ r2_hidden(X1,X3)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X3)
          & r2_hidden(X0,X2) )
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ) ),
    inference(nnf_transformation,[],[f8])).

fof(f31,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
        | ~ r2_hidden(X1,X3)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X3)
          & r2_hidden(X0,X2) )
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ) ),
    inference(flattening,[],[f30])).

fof(f54,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X1,X3)
      | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

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

fof(f36,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

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

fof(f34,plain,
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

fof(f35,plain,
    ( ( ~ r1_tarski(sK8,sK10)
      | ~ r1_tarski(sK7,sK9) )
    & k1_xboole_0 != k2_zfmisc_1(sK7,sK8)
    & r1_tarski(k2_zfmisc_1(sK7,sK8),k2_zfmisc_1(sK9,sK10)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7,sK8,sK9,sK10])],[f17,f34])).

fof(f59,plain,(
    r1_tarski(k2_zfmisc_1(sK7,sK8),k2_zfmisc_1(sK9,sK10)) ),
    inference(cnf_transformation,[],[f35])).

fof(f55,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
      | ~ r2_hidden(X1,X3)
      | ~ r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f60,plain,(
    k1_xboole_0 != k2_zfmisc_1(sK7,sK8) ),
    inference(cnf_transformation,[],[f35])).

fof(f38,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK0(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f37,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK0(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f61,plain,
    ( ~ r1_tarski(sK8,sK10)
    | ~ r1_tarski(sK7,sK9) ),
    inference(cnf_transformation,[],[f35])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( k2_zfmisc_1(X0,X1) = X2
      | r2_hidden(sK4(X0,X1,X2),X1)
      | r2_hidden(sK2(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f53,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X0,X2)
      | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f3])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f22,plain,(
    ! [X1,X0] :
      ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
     => r2_hidden(sK1(X0,X1),k3_xboole_0(X0,X1)) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( r2_hidden(sK1(X0,X1),k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f15,f22])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,k3_xboole_0(X0,X1)) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f4,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ) ),
    inference(definition_unfolding,[],[f41,f42])).

fof(f5,axiom,(
    ! [X0] : k4_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X0] : k4_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f5])).

fof(f6,axiom,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f6])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f39,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f9])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f32])).

fof(f57,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f33])).

fof(f70,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f57])).

fof(f56,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_282,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_21828,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k1_xboole_0,k4_xboole_0(X2,k4_xboole_0(X2,X3)))
    | k4_xboole_0(X2,k4_xboole_0(X2,X3)) != X1
    | k1_xboole_0 != X0 ),
    inference(instantiation,[status(thm)],[c_282])).

cnf(c_21830,plain,
    ( r1_tarski(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k1_xboole_0)))
    | ~ r1_tarski(k1_xboole_0,k1_xboole_0)
    | k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k1_xboole_0)) != k1_xboole_0
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_21828])).

cnf(c_281,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_280,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_1889,plain,
    ( X0 != X1
    | X1 = X0 ),
    inference(resolution,[status(thm)],[c_281,c_280])).

cnf(c_11,plain,
    ( r2_hidden(sK3(X0,X1,X2),X0)
    | r2_hidden(sK2(X0,X1,X2),X2)
    | k2_zfmisc_1(X0,X1) = X2 ),
    inference(cnf_transformation,[],[f49])).

cnf(c_17,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(k4_tarski(X2,X0),k2_zfmisc_1(X3,X1)) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_2,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | ~ r1_tarski(X1,X2) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_24,negated_conjecture,
    ( r1_tarski(k2_zfmisc_1(sK7,sK8),k2_zfmisc_1(sK9,sK10)) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_914,plain,
    ( r2_hidden(X0,k2_zfmisc_1(sK9,sK10))
    | ~ r2_hidden(X0,k2_zfmisc_1(sK7,sK8)) ),
    inference(resolution,[status(thm)],[c_2,c_24])).

cnf(c_1056,plain,
    ( r2_hidden(X0,sK10)
    | ~ r2_hidden(k4_tarski(X1,X0),k2_zfmisc_1(sK7,sK8)) ),
    inference(resolution,[status(thm)],[c_17,c_914])).

cnf(c_16,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X2,X3)
    | r2_hidden(k4_tarski(X2,X0),k2_zfmisc_1(X3,X1)) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_2344,plain,
    ( ~ r2_hidden(X0,sK7)
    | r2_hidden(X1,sK10)
    | ~ r2_hidden(X1,sK8) ),
    inference(resolution,[status(thm)],[c_1056,c_16])).

cnf(c_3488,plain,
    ( r2_hidden(X0,sK10)
    | ~ r2_hidden(X0,sK8)
    | r2_hidden(sK2(sK7,X1,X2),X2)
    | k2_zfmisc_1(sK7,X1) = X2 ),
    inference(resolution,[status(thm)],[c_11,c_2344])).

cnf(c_5512,plain,
    ( r2_hidden(X0,sK10)
    | ~ r2_hidden(X0,sK8)
    | r2_hidden(sK2(sK7,X1,X2),X2)
    | X2 = k2_zfmisc_1(sK7,X1) ),
    inference(resolution,[status(thm)],[c_1889,c_3488])).

cnf(c_23,negated_conjecture,
    ( k1_xboole_0 != k2_zfmisc_1(sK7,sK8) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_11988,plain,
    ( r2_hidden(X0,sK10)
    | ~ r2_hidden(X0,sK8)
    | r2_hidden(sK2(sK7,sK8,k1_xboole_0),k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_5512,c_23])).

cnf(c_0,plain,
    ( ~ r2_hidden(sK0(X0,X1),X1)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_12068,plain,
    ( r2_hidden(sK2(sK7,sK8,k1_xboole_0),k1_xboole_0)
    | ~ r2_hidden(sK0(X0,sK10),sK8)
    | r1_tarski(X0,sK10) ),
    inference(resolution,[status(thm)],[c_11988,c_0])).

cnf(c_1,plain,
    ( r2_hidden(sK0(X0,X1),X0)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_12080,plain,
    ( r2_hidden(sK2(sK7,sK8,k1_xboole_0),k1_xboole_0)
    | r1_tarski(sK8,sK10) ),
    inference(resolution,[status(thm)],[c_12068,c_1])).

cnf(c_22,negated_conjecture,
    ( ~ r1_tarski(sK7,sK9)
    | ~ r1_tarski(sK8,sK10) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_10,plain,
    ( r2_hidden(sK4(X0,X1,X2),X1)
    | r2_hidden(sK2(X0,X1,X2),X2)
    | k2_zfmisc_1(X0,X1) = X2 ),
    inference(cnf_transformation,[],[f50])).

cnf(c_18,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(k4_tarski(X0,X2),k2_zfmisc_1(X1,X3)) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_1066,plain,
    ( r2_hidden(X0,sK9)
    | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(sK7,sK8)) ),
    inference(resolution,[status(thm)],[c_18,c_914])).

cnf(c_2353,plain,
    ( r2_hidden(X0,sK9)
    | ~ r2_hidden(X0,sK7)
    | ~ r2_hidden(X1,sK8) ),
    inference(resolution,[status(thm)],[c_1066,c_16])).

cnf(c_3418,plain,
    ( r2_hidden(X0,sK9)
    | ~ r2_hidden(X0,sK7)
    | r2_hidden(sK2(X1,sK8,X2),X2)
    | k2_zfmisc_1(X1,sK8) = X2 ),
    inference(resolution,[status(thm)],[c_10,c_2353])).

cnf(c_5508,plain,
    ( r2_hidden(X0,sK9)
    | ~ r2_hidden(X0,sK7)
    | r2_hidden(sK2(X1,sK8,X2),X2)
    | X2 = k2_zfmisc_1(X1,sK8) ),
    inference(resolution,[status(thm)],[c_1889,c_3418])).

cnf(c_10152,plain,
    ( r2_hidden(X0,sK9)
    | ~ r2_hidden(X0,sK7)
    | r2_hidden(sK2(sK7,sK8,k1_xboole_0),k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_5508,c_23])).

cnf(c_11692,plain,
    ( r2_hidden(sK2(sK7,sK8,k1_xboole_0),k1_xboole_0)
    | ~ r2_hidden(sK0(X0,sK9),sK7)
    | r1_tarski(X0,sK9) ),
    inference(resolution,[status(thm)],[c_10152,c_0])).

cnf(c_11704,plain,
    ( r2_hidden(sK2(sK7,sK8,k1_xboole_0),k1_xboole_0)
    | r1_tarski(sK7,sK9) ),
    inference(resolution,[status(thm)],[c_11692,c_1])).

cnf(c_12368,plain,
    ( r2_hidden(sK2(sK7,sK8,k1_xboole_0),k1_xboole_0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_12080,c_22,c_11704])).

cnf(c_4,plain,
    ( ~ r1_xboole_0(X0,X1)
    | ~ r2_hidden(X2,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_2387,plain,
    ( ~ r1_xboole_0(X0,X1)
    | ~ r2_hidden(sK2(sK7,sK8,X2),k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_2393,plain,
    ( ~ r1_xboole_0(k1_xboole_0,k1_xboole_0)
    | ~ r2_hidden(sK2(sK7,sK8,k1_xboole_0),k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k1_xboole_0))) ),
    inference(instantiation,[status(thm)],[c_2387])).

cnf(c_1122,plain,
    ( ~ r2_hidden(sK2(sK7,sK8,X0),X0)
    | r2_hidden(sK2(sK7,sK8,X0),X1)
    | ~ r1_tarski(X0,X1) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_2386,plain,
    ( ~ r2_hidden(sK2(sK7,sK8,X0),X0)
    | r2_hidden(sK2(sK7,sK8,X0),k4_xboole_0(X1,k4_xboole_0(X1,X2)))
    | ~ r1_tarski(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2))) ),
    inference(instantiation,[status(thm)],[c_1122])).

cnf(c_2389,plain,
    ( r2_hidden(sK2(sK7,sK8,k1_xboole_0),k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k1_xboole_0)))
    | ~ r2_hidden(sK2(sK7,sK8,k1_xboole_0),k1_xboole_0)
    | ~ r1_tarski(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k1_xboole_0))) ),
    inference(instantiation,[status(thm)],[c_2386])).

cnf(c_609,plain,
    ( k2_zfmisc_1(X0,X1) = X2
    | r2_hidden(sK3(X0,X1,X2),X0) = iProver_top
    | r2_hidden(sK2(X0,X1,X2),X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_6,plain,
    ( k4_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f43])).

cnf(c_615,plain,
    ( r1_xboole_0(X0,X1) != iProver_top
    | r2_hidden(X2,k4_xboole_0(X0,k4_xboole_0(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_1616,plain,
    ( r1_xboole_0(k1_xboole_0,X0) != iProver_top
    | r2_hidden(X1,k4_xboole_0(k1_xboole_0,k1_xboole_0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_6,c_615])).

cnf(c_1619,plain,
    ( r1_xboole_0(k1_xboole_0,X0) != iProver_top
    | r2_hidden(X1,k1_xboole_0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1616,c_6])).

cnf(c_7,plain,
    ( r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_613,plain,
    ( r1_xboole_0(X0,k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_3,plain,
    ( ~ r1_xboole_0(X0,X1)
    | r1_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_616,plain,
    ( r1_xboole_0(X0,X1) != iProver_top
    | r1_xboole_0(X1,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_1024,plain,
    ( r1_xboole_0(k1_xboole_0,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_613,c_616])).

cnf(c_1803,plain,
    ( r2_hidden(X1,k1_xboole_0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1619,c_1024])).

cnf(c_1804,plain,
    ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
    inference(renaming,[status(thm)],[c_1803])).

cnf(c_2057,plain,
    ( k2_zfmisc_1(k1_xboole_0,X0) = X1
    | r2_hidden(sK2(k1_xboole_0,X0,X1),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_609,c_1804])).

cnf(c_20,plain,
    ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f70])).

cnf(c_2060,plain,
    ( k1_xboole_0 = X0
    | r2_hidden(sK2(k1_xboole_0,X1,X0),X0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_2057,c_20])).

cnf(c_2223,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_xboole_0
    | r1_xboole_0(X0,X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_2060,c_615])).

cnf(c_2242,plain,
    ( k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k1_xboole_0)) = k1_xboole_0
    | r1_xboole_0(k1_xboole_0,k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_2223])).

cnf(c_821,plain,
    ( r1_tarski(X0,X0) ),
    inference(resolution,[status(thm)],[c_0,c_1])).

cnf(c_823,plain,
    ( r1_tarski(k1_xboole_0,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_821])).

cnf(c_50,plain,
    ( r1_xboole_0(X0,k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_52,plain,
    ( r1_xboole_0(k1_xboole_0,k1_xboole_0) = iProver_top ),
    inference(instantiation,[status(thm)],[c_50])).

cnf(c_51,plain,
    ( r1_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_28,plain,
    ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_20])).

cnf(c_21,plain,
    ( k2_zfmisc_1(X0,X1) != k1_xboole_0
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f56])).

cnf(c_27,plain,
    ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) != k1_xboole_0
    | k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_21])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_21830,c_12368,c_2393,c_2389,c_2242,c_823,c_52,c_51,c_28,c_27])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.11  % Command    : iproveropt_run.sh %d %s
% 0.11/0.32  % Computer   : n003.cluster.edu
% 0.11/0.32  % Model      : x86_64 x86_64
% 0.11/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.32  % Memory     : 8042.1875MB
% 0.11/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.32  % CPULimit   : 60
% 0.11/0.32  % WCLimit    : 600
% 0.11/0.32  % DateTime   : Tue Dec  1 16:14:57 EST 2020
% 0.11/0.33  % CPUTime    : 
% 0.11/0.33  % Running in FOF mode
% 7.15/1.42  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.15/1.42  
% 7.15/1.42  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.15/1.42  
% 7.15/1.42  ------  iProver source info
% 7.15/1.42  
% 7.15/1.42  git: date: 2020-06-30 10:37:57 +0100
% 7.15/1.42  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.15/1.42  git: non_committed_changes: false
% 7.15/1.42  git: last_make_outside_of_git: false
% 7.15/1.42  
% 7.15/1.42  ------ 
% 7.15/1.42  
% 7.15/1.42  ------ Input Options
% 7.15/1.42  
% 7.15/1.42  --out_options                           all
% 7.15/1.42  --tptp_safe_out                         true
% 7.15/1.42  --problem_path                          ""
% 7.15/1.42  --include_path                          ""
% 7.15/1.42  --clausifier                            res/vclausify_rel
% 7.15/1.42  --clausifier_options                    --mode clausify
% 7.15/1.42  --stdin                                 false
% 7.15/1.42  --stats_out                             sel
% 7.15/1.42  
% 7.15/1.42  ------ General Options
% 7.15/1.42  
% 7.15/1.42  --fof                                   false
% 7.15/1.42  --time_out_real                         604.99
% 7.15/1.42  --time_out_virtual                      -1.
% 7.15/1.42  --symbol_type_check                     false
% 7.15/1.42  --clausify_out                          false
% 7.15/1.42  --sig_cnt_out                           false
% 7.15/1.42  --trig_cnt_out                          false
% 7.15/1.42  --trig_cnt_out_tolerance                1.
% 7.15/1.42  --trig_cnt_out_sk_spl                   false
% 7.15/1.42  --abstr_cl_out                          false
% 7.15/1.42  
% 7.15/1.42  ------ Global Options
% 7.15/1.42  
% 7.15/1.42  --schedule                              none
% 7.15/1.42  --add_important_lit                     false
% 7.15/1.42  --prop_solver_per_cl                    1000
% 7.15/1.42  --min_unsat_core                        false
% 7.15/1.42  --soft_assumptions                      false
% 7.15/1.42  --soft_lemma_size                       3
% 7.15/1.42  --prop_impl_unit_size                   0
% 7.15/1.42  --prop_impl_unit                        []
% 7.15/1.42  --share_sel_clauses                     true
% 7.15/1.42  --reset_solvers                         false
% 7.15/1.42  --bc_imp_inh                            [conj_cone]
% 7.15/1.42  --conj_cone_tolerance                   3.
% 7.15/1.42  --extra_neg_conj                        none
% 7.15/1.42  --large_theory_mode                     true
% 7.15/1.42  --prolific_symb_bound                   200
% 7.15/1.42  --lt_threshold                          2000
% 7.15/1.42  --clause_weak_htbl                      true
% 7.15/1.42  --gc_record_bc_elim                     false
% 7.15/1.42  
% 7.15/1.42  ------ Preprocessing Options
% 7.15/1.42  
% 7.15/1.42  --preprocessing_flag                    true
% 7.15/1.42  --time_out_prep_mult                    0.1
% 7.15/1.42  --splitting_mode                        input
% 7.15/1.42  --splitting_grd                         true
% 7.15/1.42  --splitting_cvd                         false
% 7.15/1.42  --splitting_cvd_svl                     false
% 7.15/1.42  --splitting_nvd                         32
% 7.15/1.42  --sub_typing                            true
% 7.15/1.42  --prep_gs_sim                           false
% 7.15/1.42  --prep_unflatten                        true
% 7.15/1.42  --prep_res_sim                          true
% 7.15/1.42  --prep_upred                            true
% 7.15/1.42  --prep_sem_filter                       exhaustive
% 7.15/1.42  --prep_sem_filter_out                   false
% 7.15/1.42  --pred_elim                             false
% 7.15/1.42  --res_sim_input                         true
% 7.15/1.42  --eq_ax_congr_red                       true
% 7.15/1.42  --pure_diseq_elim                       true
% 7.15/1.42  --brand_transform                       false
% 7.15/1.42  --non_eq_to_eq                          false
% 7.15/1.42  --prep_def_merge                        true
% 7.15/1.42  --prep_def_merge_prop_impl              false
% 7.15/1.42  --prep_def_merge_mbd                    true
% 7.15/1.42  --prep_def_merge_tr_red                 false
% 7.15/1.42  --prep_def_merge_tr_cl                  false
% 7.15/1.42  --smt_preprocessing                     true
% 7.15/1.42  --smt_ac_axioms                         fast
% 7.15/1.42  --preprocessed_out                      false
% 7.15/1.42  --preprocessed_stats                    false
% 7.15/1.42  
% 7.15/1.42  ------ Abstraction refinement Options
% 7.15/1.42  
% 7.15/1.42  --abstr_ref                             []
% 7.15/1.42  --abstr_ref_prep                        false
% 7.15/1.42  --abstr_ref_until_sat                   false
% 7.15/1.42  --abstr_ref_sig_restrict                funpre
% 7.15/1.42  --abstr_ref_af_restrict_to_split_sk     false
% 7.15/1.42  --abstr_ref_under                       []
% 7.15/1.42  
% 7.15/1.42  ------ SAT Options
% 7.15/1.42  
% 7.15/1.42  --sat_mode                              false
% 7.15/1.42  --sat_fm_restart_options                ""
% 7.15/1.42  --sat_gr_def                            false
% 7.15/1.42  --sat_epr_types                         true
% 7.15/1.42  --sat_non_cyclic_types                  false
% 7.15/1.42  --sat_finite_models                     false
% 7.15/1.42  --sat_fm_lemmas                         false
% 7.15/1.42  --sat_fm_prep                           false
% 7.15/1.42  --sat_fm_uc_incr                        true
% 7.15/1.42  --sat_out_model                         small
% 7.15/1.42  --sat_out_clauses                       false
% 7.15/1.42  
% 7.15/1.42  ------ QBF Options
% 7.15/1.42  
% 7.15/1.42  --qbf_mode                              false
% 7.15/1.42  --qbf_elim_univ                         false
% 7.15/1.42  --qbf_dom_inst                          none
% 7.15/1.42  --qbf_dom_pre_inst                      false
% 7.15/1.42  --qbf_sk_in                             false
% 7.15/1.42  --qbf_pred_elim                         true
% 7.15/1.42  --qbf_split                             512
% 7.15/1.42  
% 7.15/1.42  ------ BMC1 Options
% 7.15/1.42  
% 7.15/1.42  --bmc1_incremental                      false
% 7.15/1.42  --bmc1_axioms                           reachable_all
% 7.15/1.42  --bmc1_min_bound                        0
% 7.15/1.42  --bmc1_max_bound                        -1
% 7.15/1.42  --bmc1_max_bound_default                -1
% 7.15/1.42  --bmc1_symbol_reachability              true
% 7.15/1.42  --bmc1_property_lemmas                  false
% 7.15/1.42  --bmc1_k_induction                      false
% 7.15/1.42  --bmc1_non_equiv_states                 false
% 7.15/1.42  --bmc1_deadlock                         false
% 7.15/1.42  --bmc1_ucm                              false
% 7.15/1.42  --bmc1_add_unsat_core                   none
% 7.15/1.42  --bmc1_unsat_core_children              false
% 7.15/1.42  --bmc1_unsat_core_extrapolate_axioms    false
% 7.15/1.42  --bmc1_out_stat                         full
% 7.15/1.42  --bmc1_ground_init                      false
% 7.15/1.42  --bmc1_pre_inst_next_state              false
% 7.15/1.42  --bmc1_pre_inst_state                   false
% 7.15/1.42  --bmc1_pre_inst_reach_state             false
% 7.15/1.42  --bmc1_out_unsat_core                   false
% 7.15/1.42  --bmc1_aig_witness_out                  false
% 7.15/1.42  --bmc1_verbose                          false
% 7.15/1.42  --bmc1_dump_clauses_tptp                false
% 7.15/1.42  --bmc1_dump_unsat_core_tptp             false
% 7.15/1.42  --bmc1_dump_file                        -
% 7.15/1.42  --bmc1_ucm_expand_uc_limit              128
% 7.15/1.42  --bmc1_ucm_n_expand_iterations          6
% 7.15/1.42  --bmc1_ucm_extend_mode                  1
% 7.15/1.42  --bmc1_ucm_init_mode                    2
% 7.15/1.42  --bmc1_ucm_cone_mode                    none
% 7.15/1.42  --bmc1_ucm_reduced_relation_type        0
% 7.15/1.42  --bmc1_ucm_relax_model                  4
% 7.15/1.42  --bmc1_ucm_full_tr_after_sat            true
% 7.15/1.42  --bmc1_ucm_expand_neg_assumptions       false
% 7.15/1.42  --bmc1_ucm_layered_model                none
% 7.15/1.42  --bmc1_ucm_max_lemma_size               10
% 7.15/1.42  
% 7.15/1.42  ------ AIG Options
% 7.15/1.42  
% 7.15/1.42  --aig_mode                              false
% 7.15/1.42  
% 7.15/1.42  ------ Instantiation Options
% 7.15/1.42  
% 7.15/1.42  --instantiation_flag                    true
% 7.15/1.42  --inst_sos_flag                         false
% 7.15/1.42  --inst_sos_phase                        true
% 7.15/1.42  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.15/1.42  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.15/1.42  --inst_lit_sel_side                     num_symb
% 7.15/1.42  --inst_solver_per_active                1400
% 7.15/1.42  --inst_solver_calls_frac                1.
% 7.15/1.42  --inst_passive_queue_type               priority_queues
% 7.15/1.42  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.15/1.42  --inst_passive_queues_freq              [25;2]
% 7.15/1.42  --inst_dismatching                      true
% 7.15/1.42  --inst_eager_unprocessed_to_passive     true
% 7.15/1.42  --inst_prop_sim_given                   true
% 7.15/1.42  --inst_prop_sim_new                     false
% 7.15/1.42  --inst_subs_new                         false
% 7.15/1.42  --inst_eq_res_simp                      false
% 7.15/1.42  --inst_subs_given                       false
% 7.15/1.42  --inst_orphan_elimination               true
% 7.15/1.42  --inst_learning_loop_flag               true
% 7.15/1.42  --inst_learning_start                   3000
% 7.15/1.42  --inst_learning_factor                  2
% 7.15/1.42  --inst_start_prop_sim_after_learn       3
% 7.15/1.42  --inst_sel_renew                        solver
% 7.15/1.42  --inst_lit_activity_flag                true
% 7.15/1.42  --inst_restr_to_given                   false
% 7.15/1.42  --inst_activity_threshold               500
% 7.15/1.42  --inst_out_proof                        true
% 7.15/1.42  
% 7.15/1.42  ------ Resolution Options
% 7.15/1.42  
% 7.15/1.42  --resolution_flag                       true
% 7.15/1.42  --res_lit_sel                           adaptive
% 7.15/1.42  --res_lit_sel_side                      none
% 7.15/1.42  --res_ordering                          kbo
% 7.15/1.42  --res_to_prop_solver                    active
% 7.15/1.42  --res_prop_simpl_new                    false
% 7.15/1.42  --res_prop_simpl_given                  true
% 7.15/1.42  --res_passive_queue_type                priority_queues
% 7.15/1.42  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.15/1.42  --res_passive_queues_freq               [15;5]
% 7.15/1.42  --res_forward_subs                      full
% 7.15/1.42  --res_backward_subs                     full
% 7.15/1.42  --res_forward_subs_resolution           true
% 7.15/1.42  --res_backward_subs_resolution          true
% 7.15/1.42  --res_orphan_elimination                true
% 7.15/1.42  --res_time_limit                        2.
% 7.15/1.42  --res_out_proof                         true
% 7.15/1.42  
% 7.15/1.42  ------ Superposition Options
% 7.15/1.42  
% 7.15/1.42  --superposition_flag                    true
% 7.15/1.42  --sup_passive_queue_type                priority_queues
% 7.15/1.42  --sup_passive_queues                    [[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.15/1.42  --sup_passive_queues_freq               [1;4]
% 7.15/1.42  --demod_completeness_check              fast
% 7.15/1.42  --demod_use_ground                      true
% 7.15/1.42  --sup_to_prop_solver                    passive
% 7.15/1.42  --sup_prop_simpl_new                    true
% 7.15/1.42  --sup_prop_simpl_given                  true
% 7.15/1.42  --sup_fun_splitting                     false
% 7.15/1.42  --sup_smt_interval                      50000
% 7.15/1.42  
% 7.15/1.42  ------ Superposition Simplification Setup
% 7.15/1.42  
% 7.15/1.42  --sup_indices_passive                   []
% 7.15/1.42  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.15/1.42  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.15/1.42  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.15/1.42  --sup_full_triv                         [TrivRules;PropSubs]
% 7.15/1.42  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.15/1.42  --sup_full_bw                           [BwDemod]
% 7.15/1.42  --sup_immed_triv                        [TrivRules]
% 7.15/1.42  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.15/1.42  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.15/1.42  --sup_immed_bw_main                     []
% 7.15/1.42  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.15/1.42  --sup_input_triv                        [Unflattening;TrivRules]
% 7.15/1.42  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.15/1.42  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.15/1.42  
% 7.15/1.42  ------ Combination Options
% 7.15/1.42  
% 7.15/1.42  --comb_res_mult                         3
% 7.15/1.42  --comb_sup_mult                         2
% 7.15/1.42  --comb_inst_mult                        10
% 7.15/1.42  
% 7.15/1.42  ------ Debug Options
% 7.15/1.42  
% 7.15/1.42  --dbg_backtrace                         false
% 7.15/1.42  --dbg_dump_prop_clauses                 false
% 7.15/1.42  --dbg_dump_prop_clauses_file            -
% 7.15/1.42  --dbg_out_stat                          false
% 7.15/1.42  ------ Parsing...
% 7.15/1.42  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.15/1.42  
% 7.15/1.42  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 1 0s  sf_e 
% 7.15/1.42  
% 7.15/1.42  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.15/1.42  
% 7.15/1.42  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.15/1.42  ------ Proving...
% 7.15/1.42  ------ Problem Properties 
% 7.15/1.42  
% 7.15/1.42  
% 7.15/1.42  clauses                                 24
% 7.15/1.42  conjectures                             3
% 7.15/1.42  EPR                                     4
% 7.15/1.42  Horn                                    18
% 7.15/1.42  unary                                   6
% 7.15/1.42  binary                                  11
% 7.15/1.42  lits                                    51
% 7.15/1.42  lits eq                                 14
% 7.15/1.42  fd_pure                                 0
% 7.15/1.42  fd_pseudo                               0
% 7.15/1.42  fd_cond                                 1
% 7.15/1.42  fd_pseudo_cond                          4
% 7.15/1.42  AC symbols                              0
% 7.15/1.42  
% 7.15/1.42  ------ Input Options Time Limit: Unbounded
% 7.15/1.42  
% 7.15/1.42  
% 7.15/1.42  ------ 
% 7.15/1.42  Current options:
% 7.15/1.42  ------ 
% 7.15/1.42  
% 7.15/1.42  ------ Input Options
% 7.15/1.42  
% 7.15/1.42  --out_options                           all
% 7.15/1.42  --tptp_safe_out                         true
% 7.15/1.42  --problem_path                          ""
% 7.15/1.42  --include_path                          ""
% 7.15/1.42  --clausifier                            res/vclausify_rel
% 7.15/1.42  --clausifier_options                    --mode clausify
% 7.15/1.42  --stdin                                 false
% 7.15/1.42  --stats_out                             sel
% 7.15/1.42  
% 7.15/1.42  ------ General Options
% 7.15/1.42  
% 7.15/1.42  --fof                                   false
% 7.15/1.42  --time_out_real                         604.99
% 7.15/1.42  --time_out_virtual                      -1.
% 7.15/1.42  --symbol_type_check                     false
% 7.15/1.42  --clausify_out                          false
% 7.15/1.42  --sig_cnt_out                           false
% 7.15/1.42  --trig_cnt_out                          false
% 7.15/1.42  --trig_cnt_out_tolerance                1.
% 7.15/1.42  --trig_cnt_out_sk_spl                   false
% 7.15/1.42  --abstr_cl_out                          false
% 7.15/1.42  
% 7.15/1.42  ------ Global Options
% 7.15/1.42  
% 7.15/1.42  --schedule                              none
% 7.15/1.42  --add_important_lit                     false
% 7.15/1.42  --prop_solver_per_cl                    1000
% 7.15/1.42  --min_unsat_core                        false
% 7.15/1.42  --soft_assumptions                      false
% 7.15/1.42  --soft_lemma_size                       3
% 7.15/1.42  --prop_impl_unit_size                   0
% 7.15/1.42  --prop_impl_unit                        []
% 7.15/1.42  --share_sel_clauses                     true
% 7.15/1.42  --reset_solvers                         false
% 7.15/1.42  --bc_imp_inh                            [conj_cone]
% 7.15/1.42  --conj_cone_tolerance                   3.
% 7.15/1.42  --extra_neg_conj                        none
% 7.15/1.42  --large_theory_mode                     true
% 7.15/1.42  --prolific_symb_bound                   200
% 7.15/1.42  --lt_threshold                          2000
% 7.15/1.42  --clause_weak_htbl                      true
% 7.15/1.42  --gc_record_bc_elim                     false
% 7.15/1.42  
% 7.15/1.42  ------ Preprocessing Options
% 7.15/1.42  
% 7.15/1.42  --preprocessing_flag                    true
% 7.15/1.42  --time_out_prep_mult                    0.1
% 7.15/1.42  --splitting_mode                        input
% 7.15/1.42  --splitting_grd                         true
% 7.15/1.42  --splitting_cvd                         false
% 7.15/1.42  --splitting_cvd_svl                     false
% 7.15/1.42  --splitting_nvd                         32
% 7.15/1.42  --sub_typing                            true
% 7.15/1.42  --prep_gs_sim                           false
% 7.15/1.42  --prep_unflatten                        true
% 7.15/1.42  --prep_res_sim                          true
% 7.15/1.42  --prep_upred                            true
% 7.15/1.42  --prep_sem_filter                       exhaustive
% 7.15/1.42  --prep_sem_filter_out                   false
% 7.15/1.42  --pred_elim                             false
% 7.15/1.42  --res_sim_input                         true
% 7.15/1.42  --eq_ax_congr_red                       true
% 7.15/1.42  --pure_diseq_elim                       true
% 7.15/1.42  --brand_transform                       false
% 7.15/1.42  --non_eq_to_eq                          false
% 7.15/1.42  --prep_def_merge                        true
% 7.15/1.42  --prep_def_merge_prop_impl              false
% 7.15/1.42  --prep_def_merge_mbd                    true
% 7.15/1.42  --prep_def_merge_tr_red                 false
% 7.15/1.42  --prep_def_merge_tr_cl                  false
% 7.15/1.42  --smt_preprocessing                     true
% 7.15/1.42  --smt_ac_axioms                         fast
% 7.15/1.42  --preprocessed_out                      false
% 7.15/1.42  --preprocessed_stats                    false
% 7.15/1.42  
% 7.15/1.42  ------ Abstraction refinement Options
% 7.15/1.42  
% 7.15/1.42  --abstr_ref                             []
% 7.15/1.42  --abstr_ref_prep                        false
% 7.15/1.42  --abstr_ref_until_sat                   false
% 7.15/1.42  --abstr_ref_sig_restrict                funpre
% 7.15/1.42  --abstr_ref_af_restrict_to_split_sk     false
% 7.15/1.42  --abstr_ref_under                       []
% 7.15/1.42  
% 7.15/1.42  ------ SAT Options
% 7.15/1.42  
% 7.15/1.42  --sat_mode                              false
% 7.15/1.42  --sat_fm_restart_options                ""
% 7.15/1.42  --sat_gr_def                            false
% 7.15/1.42  --sat_epr_types                         true
% 7.15/1.42  --sat_non_cyclic_types                  false
% 7.15/1.42  --sat_finite_models                     false
% 7.15/1.42  --sat_fm_lemmas                         false
% 7.15/1.42  --sat_fm_prep                           false
% 7.15/1.42  --sat_fm_uc_incr                        true
% 7.15/1.42  --sat_out_model                         small
% 7.15/1.42  --sat_out_clauses                       false
% 7.15/1.42  
% 7.15/1.42  ------ QBF Options
% 7.15/1.42  
% 7.15/1.42  --qbf_mode                              false
% 7.15/1.42  --qbf_elim_univ                         false
% 7.15/1.42  --qbf_dom_inst                          none
% 7.15/1.42  --qbf_dom_pre_inst                      false
% 7.15/1.42  --qbf_sk_in                             false
% 7.15/1.42  --qbf_pred_elim                         true
% 7.15/1.42  --qbf_split                             512
% 7.15/1.42  
% 7.15/1.42  ------ BMC1 Options
% 7.15/1.42  
% 7.15/1.42  --bmc1_incremental                      false
% 7.15/1.42  --bmc1_axioms                           reachable_all
% 7.15/1.42  --bmc1_min_bound                        0
% 7.15/1.42  --bmc1_max_bound                        -1
% 7.15/1.42  --bmc1_max_bound_default                -1
% 7.15/1.42  --bmc1_symbol_reachability              true
% 7.15/1.42  --bmc1_property_lemmas                  false
% 7.15/1.42  --bmc1_k_induction                      false
% 7.15/1.42  --bmc1_non_equiv_states                 false
% 7.15/1.42  --bmc1_deadlock                         false
% 7.15/1.42  --bmc1_ucm                              false
% 7.15/1.42  --bmc1_add_unsat_core                   none
% 7.15/1.42  --bmc1_unsat_core_children              false
% 7.15/1.42  --bmc1_unsat_core_extrapolate_axioms    false
% 7.15/1.42  --bmc1_out_stat                         full
% 7.15/1.42  --bmc1_ground_init                      false
% 7.15/1.42  --bmc1_pre_inst_next_state              false
% 7.15/1.42  --bmc1_pre_inst_state                   false
% 7.15/1.42  --bmc1_pre_inst_reach_state             false
% 7.15/1.42  --bmc1_out_unsat_core                   false
% 7.15/1.42  --bmc1_aig_witness_out                  false
% 7.15/1.42  --bmc1_verbose                          false
% 7.15/1.42  --bmc1_dump_clauses_tptp                false
% 7.15/1.42  --bmc1_dump_unsat_core_tptp             false
% 7.15/1.42  --bmc1_dump_file                        -
% 7.15/1.42  --bmc1_ucm_expand_uc_limit              128
% 7.15/1.42  --bmc1_ucm_n_expand_iterations          6
% 7.15/1.42  --bmc1_ucm_extend_mode                  1
% 7.15/1.42  --bmc1_ucm_init_mode                    2
% 7.15/1.42  --bmc1_ucm_cone_mode                    none
% 7.15/1.42  --bmc1_ucm_reduced_relation_type        0
% 7.15/1.42  --bmc1_ucm_relax_model                  4
% 7.15/1.42  --bmc1_ucm_full_tr_after_sat            true
% 7.15/1.42  --bmc1_ucm_expand_neg_assumptions       false
% 7.15/1.42  --bmc1_ucm_layered_model                none
% 7.15/1.42  --bmc1_ucm_max_lemma_size               10
% 7.15/1.42  
% 7.15/1.42  ------ AIG Options
% 7.15/1.42  
% 7.15/1.42  --aig_mode                              false
% 7.15/1.42  
% 7.15/1.42  ------ Instantiation Options
% 7.15/1.42  
% 7.15/1.42  --instantiation_flag                    true
% 7.15/1.42  --inst_sos_flag                         false
% 7.15/1.42  --inst_sos_phase                        true
% 7.15/1.42  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.15/1.42  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.15/1.42  --inst_lit_sel_side                     num_symb
% 7.15/1.42  --inst_solver_per_active                1400
% 7.15/1.42  --inst_solver_calls_frac                1.
% 7.15/1.42  --inst_passive_queue_type               priority_queues
% 7.15/1.42  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.15/1.42  --inst_passive_queues_freq              [25;2]
% 7.15/1.42  --inst_dismatching                      true
% 7.15/1.42  --inst_eager_unprocessed_to_passive     true
% 7.15/1.42  --inst_prop_sim_given                   true
% 7.15/1.42  --inst_prop_sim_new                     false
% 7.15/1.42  --inst_subs_new                         false
% 7.15/1.42  --inst_eq_res_simp                      false
% 7.15/1.42  --inst_subs_given                       false
% 7.15/1.42  --inst_orphan_elimination               true
% 7.15/1.42  --inst_learning_loop_flag               true
% 7.15/1.42  --inst_learning_start                   3000
% 7.15/1.42  --inst_learning_factor                  2
% 7.15/1.42  --inst_start_prop_sim_after_learn       3
% 7.15/1.42  --inst_sel_renew                        solver
% 7.15/1.42  --inst_lit_activity_flag                true
% 7.15/1.42  --inst_restr_to_given                   false
% 7.15/1.42  --inst_activity_threshold               500
% 7.15/1.42  --inst_out_proof                        true
% 7.15/1.42  
% 7.15/1.42  ------ Resolution Options
% 7.15/1.42  
% 7.15/1.42  --resolution_flag                       true
% 7.15/1.42  --res_lit_sel                           adaptive
% 7.15/1.42  --res_lit_sel_side                      none
% 7.15/1.42  --res_ordering                          kbo
% 7.15/1.42  --res_to_prop_solver                    active
% 7.15/1.42  --res_prop_simpl_new                    false
% 7.15/1.42  --res_prop_simpl_given                  true
% 7.15/1.42  --res_passive_queue_type                priority_queues
% 7.15/1.42  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.15/1.42  --res_passive_queues_freq               [15;5]
% 7.15/1.42  --res_forward_subs                      full
% 7.15/1.42  --res_backward_subs                     full
% 7.15/1.42  --res_forward_subs_resolution           true
% 7.15/1.42  --res_backward_subs_resolution          true
% 7.15/1.42  --res_orphan_elimination                true
% 7.15/1.42  --res_time_limit                        2.
% 7.15/1.42  --res_out_proof                         true
% 7.15/1.42  
% 7.15/1.42  ------ Superposition Options
% 7.15/1.42  
% 7.15/1.42  --superposition_flag                    true
% 7.15/1.42  --sup_passive_queue_type                priority_queues
% 7.15/1.42  --sup_passive_queues                    [[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.15/1.42  --sup_passive_queues_freq               [1;4]
% 7.15/1.42  --demod_completeness_check              fast
% 7.15/1.42  --demod_use_ground                      true
% 7.15/1.42  --sup_to_prop_solver                    passive
% 7.15/1.42  --sup_prop_simpl_new                    true
% 7.15/1.42  --sup_prop_simpl_given                  true
% 7.15/1.42  --sup_fun_splitting                     false
% 7.15/1.42  --sup_smt_interval                      50000
% 7.15/1.42  
% 7.15/1.42  ------ Superposition Simplification Setup
% 7.15/1.42  
% 7.15/1.42  --sup_indices_passive                   []
% 7.15/1.42  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.15/1.42  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.15/1.42  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.15/1.42  --sup_full_triv                         [TrivRules;PropSubs]
% 7.15/1.42  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.15/1.42  --sup_full_bw                           [BwDemod]
% 7.15/1.42  --sup_immed_triv                        [TrivRules]
% 7.15/1.42  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.15/1.42  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.15/1.42  --sup_immed_bw_main                     []
% 7.15/1.42  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.15/1.42  --sup_input_triv                        [Unflattening;TrivRules]
% 7.15/1.42  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.15/1.42  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.15/1.42  
% 7.15/1.42  ------ Combination Options
% 7.15/1.42  
% 7.15/1.42  --comb_res_mult                         3
% 7.15/1.42  --comb_sup_mult                         2
% 7.15/1.42  --comb_inst_mult                        10
% 7.15/1.42  
% 7.15/1.42  ------ Debug Options
% 7.15/1.42  
% 7.15/1.42  --dbg_backtrace                         false
% 7.15/1.42  --dbg_dump_prop_clauses                 false
% 7.15/1.42  --dbg_dump_prop_clauses_file            -
% 7.15/1.42  --dbg_out_stat                          false
% 7.15/1.42  
% 7.15/1.42  
% 7.15/1.42  
% 7.15/1.42  
% 7.15/1.42  ------ Proving...
% 7.15/1.42  
% 7.15/1.42  
% 7.15/1.42  % SZS status Theorem for theBenchmark.p
% 7.15/1.42  
% 7.15/1.42  % SZS output start CNFRefutation for theBenchmark.p
% 7.15/1.42  
% 7.15/1.42  fof(f7,axiom,(
% 7.15/1.42    ! [X0,X1,X2] : (k2_zfmisc_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4,X5] : (k4_tarski(X4,X5) = X3 & r2_hidden(X5,X1) & r2_hidden(X4,X0))))),
% 7.15/1.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.15/1.42  
% 7.15/1.42  fof(f24,plain,(
% 7.15/1.42    ! [X0,X1,X2] : ((k2_zfmisc_1(X0,X1) = X2 | ? [X3] : ((! [X4,X5] : (k4_tarski(X4,X5) != X3 | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X0)) | ~r2_hidden(X3,X2)) & (? [X4,X5] : (k4_tarski(X4,X5) = X3 & r2_hidden(X5,X1) & r2_hidden(X4,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ! [X4,X5] : (k4_tarski(X4,X5) != X3 | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X0))) & (? [X4,X5] : (k4_tarski(X4,X5) = X3 & r2_hidden(X5,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X3,X2))) | k2_zfmisc_1(X0,X1) != X2))),
% 7.15/1.42    inference(nnf_transformation,[],[f7])).
% 7.15/1.42  
% 7.15/1.42  fof(f25,plain,(
% 7.15/1.42    ! [X0,X1,X2] : ((k2_zfmisc_1(X0,X1) = X2 | ? [X3] : ((! [X4,X5] : (k4_tarski(X4,X5) != X3 | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X0)) | ~r2_hidden(X3,X2)) & (? [X6,X7] : (k4_tarski(X6,X7) = X3 & r2_hidden(X7,X1) & r2_hidden(X6,X0)) | r2_hidden(X3,X2)))) & (! [X8] : ((r2_hidden(X8,X2) | ! [X9,X10] : (k4_tarski(X9,X10) != X8 | ~r2_hidden(X10,X1) | ~r2_hidden(X9,X0))) & (? [X11,X12] : (k4_tarski(X11,X12) = X8 & r2_hidden(X12,X1) & r2_hidden(X11,X0)) | ~r2_hidden(X8,X2))) | k2_zfmisc_1(X0,X1) != X2))),
% 7.15/1.42    inference(rectify,[],[f24])).
% 7.15/1.42  
% 7.15/1.42  fof(f28,plain,(
% 7.15/1.42    ! [X8,X1,X0] : (? [X11,X12] : (k4_tarski(X11,X12) = X8 & r2_hidden(X12,X1) & r2_hidden(X11,X0)) => (k4_tarski(sK5(X0,X1,X8),sK6(X0,X1,X8)) = X8 & r2_hidden(sK6(X0,X1,X8),X1) & r2_hidden(sK5(X0,X1,X8),X0)))),
% 7.15/1.42    introduced(choice_axiom,[])).
% 7.15/1.42  
% 7.15/1.42  fof(f27,plain,(
% 7.15/1.42    ( ! [X3] : (! [X2,X1,X0] : (? [X6,X7] : (k4_tarski(X6,X7) = X3 & r2_hidden(X7,X1) & r2_hidden(X6,X0)) => (k4_tarski(sK3(X0,X1,X2),sK4(X0,X1,X2)) = X3 & r2_hidden(sK4(X0,X1,X2),X1) & r2_hidden(sK3(X0,X1,X2),X0)))) )),
% 7.15/1.42    introduced(choice_axiom,[])).
% 7.15/1.42  
% 7.15/1.42  fof(f26,plain,(
% 7.15/1.42    ! [X2,X1,X0] : (? [X3] : ((! [X4,X5] : (k4_tarski(X4,X5) != X3 | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X0)) | ~r2_hidden(X3,X2)) & (? [X6,X7] : (k4_tarski(X6,X7) = X3 & r2_hidden(X7,X1) & r2_hidden(X6,X0)) | r2_hidden(X3,X2))) => ((! [X5,X4] : (k4_tarski(X4,X5) != sK2(X0,X1,X2) | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X0)) | ~r2_hidden(sK2(X0,X1,X2),X2)) & (? [X7,X6] : (k4_tarski(X6,X7) = sK2(X0,X1,X2) & r2_hidden(X7,X1) & r2_hidden(X6,X0)) | r2_hidden(sK2(X0,X1,X2),X2))))),
% 7.15/1.42    introduced(choice_axiom,[])).
% 7.15/1.42  
% 7.15/1.42  fof(f29,plain,(
% 7.15/1.42    ! [X0,X1,X2] : ((k2_zfmisc_1(X0,X1) = X2 | ((! [X4,X5] : (k4_tarski(X4,X5) != sK2(X0,X1,X2) | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X0)) | ~r2_hidden(sK2(X0,X1,X2),X2)) & ((k4_tarski(sK3(X0,X1,X2),sK4(X0,X1,X2)) = sK2(X0,X1,X2) & r2_hidden(sK4(X0,X1,X2),X1) & r2_hidden(sK3(X0,X1,X2),X0)) | r2_hidden(sK2(X0,X1,X2),X2)))) & (! [X8] : ((r2_hidden(X8,X2) | ! [X9,X10] : (k4_tarski(X9,X10) != X8 | ~r2_hidden(X10,X1) | ~r2_hidden(X9,X0))) & ((k4_tarski(sK5(X0,X1,X8),sK6(X0,X1,X8)) = X8 & r2_hidden(sK6(X0,X1,X8),X1) & r2_hidden(sK5(X0,X1,X8),X0)) | ~r2_hidden(X8,X2))) | k2_zfmisc_1(X0,X1) != X2))),
% 7.15/1.42    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5,sK6])],[f25,f28,f27,f26])).
% 7.15/1.42  
% 7.15/1.42  fof(f49,plain,(
% 7.15/1.42    ( ! [X2,X0,X1] : (k2_zfmisc_1(X0,X1) = X2 | r2_hidden(sK3(X0,X1,X2),X0) | r2_hidden(sK2(X0,X1,X2),X2)) )),
% 7.15/1.42    inference(cnf_transformation,[],[f29])).
% 7.15/1.42  
% 7.15/1.42  fof(f8,axiom,(
% 7.15/1.42    ! [X0,X1,X2,X3] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) <=> (r2_hidden(X1,X3) & r2_hidden(X0,X2)))),
% 7.15/1.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.15/1.42  
% 7.15/1.42  fof(f30,plain,(
% 7.15/1.42    ! [X0,X1,X2,X3] : ((r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | (~r2_hidden(X1,X3) | ~r2_hidden(X0,X2))) & ((r2_hidden(X1,X3) & r2_hidden(X0,X2)) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))))),
% 7.15/1.42    inference(nnf_transformation,[],[f8])).
% 7.15/1.42  
% 7.15/1.42  fof(f31,plain,(
% 7.15/1.42    ! [X0,X1,X2,X3] : ((r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | ~r2_hidden(X1,X3) | ~r2_hidden(X0,X2)) & ((r2_hidden(X1,X3) & r2_hidden(X0,X2)) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))))),
% 7.15/1.42    inference(flattening,[],[f30])).
% 7.15/1.42  
% 7.15/1.42  fof(f54,plain,(
% 7.15/1.42    ( ! [X2,X0,X3,X1] : (r2_hidden(X1,X3) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))) )),
% 7.15/1.42    inference(cnf_transformation,[],[f31])).
% 7.15/1.42  
% 7.15/1.42  fof(f1,axiom,(
% 7.15/1.42    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 7.15/1.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.15/1.42  
% 7.15/1.42  fof(f13,plain,(
% 7.15/1.42    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 7.15/1.42    inference(ennf_transformation,[],[f1])).
% 7.15/1.42  
% 7.15/1.42  fof(f18,plain,(
% 7.15/1.42    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 7.15/1.42    inference(nnf_transformation,[],[f13])).
% 7.15/1.42  
% 7.15/1.42  fof(f19,plain,(
% 7.15/1.42    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 7.15/1.42    inference(rectify,[],[f18])).
% 7.15/1.42  
% 7.15/1.42  fof(f20,plain,(
% 7.15/1.42    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 7.15/1.42    introduced(choice_axiom,[])).
% 7.15/1.42  
% 7.15/1.42  fof(f21,plain,(
% 7.15/1.42    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 7.15/1.42    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f19,f20])).
% 7.15/1.42  
% 7.15/1.42  fof(f36,plain,(
% 7.15/1.42    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,X1)) )),
% 7.15/1.42    inference(cnf_transformation,[],[f21])).
% 7.15/1.42  
% 7.15/1.42  fof(f10,conjecture,(
% 7.15/1.42    ! [X0,X1,X2,X3] : (r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)) => ((r1_tarski(X1,X3) & r1_tarski(X0,X2)) | k1_xboole_0 = k2_zfmisc_1(X0,X1)))),
% 7.15/1.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.15/1.42  
% 7.15/1.42  fof(f11,negated_conjecture,(
% 7.15/1.42    ~! [X0,X1,X2,X3] : (r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)) => ((r1_tarski(X1,X3) & r1_tarski(X0,X2)) | k1_xboole_0 = k2_zfmisc_1(X0,X1)))),
% 7.15/1.42    inference(negated_conjecture,[],[f10])).
% 7.15/1.42  
% 7.15/1.42  fof(f16,plain,(
% 7.15/1.42    ? [X0,X1,X2,X3] : (((~r1_tarski(X1,X3) | ~r1_tarski(X0,X2)) & k1_xboole_0 != k2_zfmisc_1(X0,X1)) & r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)))),
% 7.15/1.42    inference(ennf_transformation,[],[f11])).
% 7.15/1.42  
% 7.15/1.42  fof(f17,plain,(
% 7.15/1.42    ? [X0,X1,X2,X3] : ((~r1_tarski(X1,X3) | ~r1_tarski(X0,X2)) & k1_xboole_0 != k2_zfmisc_1(X0,X1) & r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)))),
% 7.15/1.42    inference(flattening,[],[f16])).
% 7.15/1.42  
% 7.15/1.42  fof(f34,plain,(
% 7.15/1.42    ? [X0,X1,X2,X3] : ((~r1_tarski(X1,X3) | ~r1_tarski(X0,X2)) & k1_xboole_0 != k2_zfmisc_1(X0,X1) & r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3))) => ((~r1_tarski(sK8,sK10) | ~r1_tarski(sK7,sK9)) & k1_xboole_0 != k2_zfmisc_1(sK7,sK8) & r1_tarski(k2_zfmisc_1(sK7,sK8),k2_zfmisc_1(sK9,sK10)))),
% 7.15/1.42    introduced(choice_axiom,[])).
% 7.15/1.42  
% 7.15/1.42  fof(f35,plain,(
% 7.15/1.42    (~r1_tarski(sK8,sK10) | ~r1_tarski(sK7,sK9)) & k1_xboole_0 != k2_zfmisc_1(sK7,sK8) & r1_tarski(k2_zfmisc_1(sK7,sK8),k2_zfmisc_1(sK9,sK10))),
% 7.15/1.42    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7,sK8,sK9,sK10])],[f17,f34])).
% 7.15/1.42  
% 7.15/1.42  fof(f59,plain,(
% 7.15/1.42    r1_tarski(k2_zfmisc_1(sK7,sK8),k2_zfmisc_1(sK9,sK10))),
% 7.15/1.42    inference(cnf_transformation,[],[f35])).
% 7.15/1.42  
% 7.15/1.42  fof(f55,plain,(
% 7.15/1.42    ( ! [X2,X0,X3,X1] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | ~r2_hidden(X1,X3) | ~r2_hidden(X0,X2)) )),
% 7.15/1.42    inference(cnf_transformation,[],[f31])).
% 7.15/1.42  
% 7.15/1.42  fof(f60,plain,(
% 7.15/1.42    k1_xboole_0 != k2_zfmisc_1(sK7,sK8)),
% 7.15/1.42    inference(cnf_transformation,[],[f35])).
% 7.15/1.42  
% 7.15/1.42  fof(f38,plain,(
% 7.15/1.42    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r2_hidden(sK0(X0,X1),X1)) )),
% 7.15/1.42    inference(cnf_transformation,[],[f21])).
% 7.15/1.42  
% 7.15/1.42  fof(f37,plain,(
% 7.15/1.42    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK0(X0,X1),X0)) )),
% 7.15/1.42    inference(cnf_transformation,[],[f21])).
% 7.15/1.42  
% 7.15/1.42  fof(f61,plain,(
% 7.15/1.42    ~r1_tarski(sK8,sK10) | ~r1_tarski(sK7,sK9)),
% 7.15/1.42    inference(cnf_transformation,[],[f35])).
% 7.15/1.42  
% 7.15/1.42  fof(f50,plain,(
% 7.15/1.42    ( ! [X2,X0,X1] : (k2_zfmisc_1(X0,X1) = X2 | r2_hidden(sK4(X0,X1,X2),X1) | r2_hidden(sK2(X0,X1,X2),X2)) )),
% 7.15/1.42    inference(cnf_transformation,[],[f29])).
% 7.15/1.42  
% 7.15/1.42  fof(f53,plain,(
% 7.15/1.42    ( ! [X2,X0,X3,X1] : (r2_hidden(X0,X2) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))) )),
% 7.15/1.42    inference(cnf_transformation,[],[f31])).
% 7.15/1.42  
% 7.15/1.42  fof(f3,axiom,(
% 7.15/1.42    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 7.15/1.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.15/1.42  
% 7.15/1.42  fof(f12,plain,(
% 7.15/1.42    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X3] : ~r2_hidden(X3,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 7.15/1.42    inference(rectify,[],[f3])).
% 7.15/1.42  
% 7.15/1.42  fof(f15,plain,(
% 7.15/1.42    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 7.15/1.42    inference(ennf_transformation,[],[f12])).
% 7.15/1.42  
% 7.15/1.42  fof(f22,plain,(
% 7.15/1.42    ! [X1,X0] : (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) => r2_hidden(sK1(X0,X1),k3_xboole_0(X0,X1)))),
% 7.15/1.42    introduced(choice_axiom,[])).
% 7.15/1.42  
% 7.15/1.42  fof(f23,plain,(
% 7.15/1.42    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (r2_hidden(sK1(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 7.15/1.42    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f15,f22])).
% 7.15/1.42  
% 7.15/1.42  fof(f41,plain,(
% 7.15/1.42    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,k3_xboole_0(X0,X1))) )),
% 7.15/1.42    inference(cnf_transformation,[],[f23])).
% 7.15/1.42  
% 7.15/1.42  fof(f4,axiom,(
% 7.15/1.42    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 7.15/1.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.15/1.42  
% 7.15/1.42  fof(f42,plain,(
% 7.15/1.42    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 7.15/1.42    inference(cnf_transformation,[],[f4])).
% 7.15/1.42  
% 7.15/1.42  fof(f62,plain,(
% 7.15/1.42    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 7.15/1.42    inference(definition_unfolding,[],[f41,f42])).
% 7.15/1.42  
% 7.15/1.42  fof(f5,axiom,(
% 7.15/1.42    ! [X0] : k4_xboole_0(k1_xboole_0,X0) = k1_xboole_0),
% 7.15/1.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.15/1.42  
% 7.15/1.42  fof(f43,plain,(
% 7.15/1.42    ( ! [X0] : (k4_xboole_0(k1_xboole_0,X0) = k1_xboole_0) )),
% 7.15/1.42    inference(cnf_transformation,[],[f5])).
% 7.15/1.42  
% 7.15/1.42  fof(f6,axiom,(
% 7.15/1.42    ! [X0] : r1_xboole_0(X0,k1_xboole_0)),
% 7.15/1.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.15/1.42  
% 7.15/1.42  fof(f44,plain,(
% 7.15/1.42    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) )),
% 7.15/1.42    inference(cnf_transformation,[],[f6])).
% 7.15/1.42  
% 7.15/1.42  fof(f2,axiom,(
% 7.15/1.42    ! [X0,X1] : (r1_xboole_0(X0,X1) => r1_xboole_0(X1,X0))),
% 7.15/1.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.15/1.42  
% 7.15/1.42  fof(f14,plain,(
% 7.15/1.42    ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1))),
% 7.15/1.42    inference(ennf_transformation,[],[f2])).
% 7.15/1.42  
% 7.15/1.42  fof(f39,plain,(
% 7.15/1.42    ( ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1)) )),
% 7.15/1.42    inference(cnf_transformation,[],[f14])).
% 7.15/1.42  
% 7.15/1.42  fof(f9,axiom,(
% 7.15/1.42    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 7.15/1.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.15/1.42  
% 7.15/1.42  fof(f32,plain,(
% 7.15/1.42    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 7.15/1.42    inference(nnf_transformation,[],[f9])).
% 7.15/1.42  
% 7.15/1.42  fof(f33,plain,(
% 7.15/1.42    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 7.15/1.42    inference(flattening,[],[f32])).
% 7.15/1.42  
% 7.15/1.42  fof(f57,plain,(
% 7.15/1.42    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X0) )),
% 7.15/1.42    inference(cnf_transformation,[],[f33])).
% 7.15/1.42  
% 7.15/1.42  fof(f70,plain,(
% 7.15/1.42    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 7.15/1.42    inference(equality_resolution,[],[f57])).
% 7.15/1.42  
% 7.15/1.42  fof(f56,plain,(
% 7.15/1.42    ( ! [X0,X1] : (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)) )),
% 7.15/1.42    inference(cnf_transformation,[],[f33])).
% 7.15/1.42  
% 7.15/1.42  cnf(c_282,plain,
% 7.15/1.42      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,X3) | X2 != X0 | X3 != X1 ),
% 7.15/1.42      theory(equality) ).
% 7.15/1.42  
% 7.15/1.42  cnf(c_21828,plain,
% 7.15/1.42      ( ~ r1_tarski(X0,X1)
% 7.15/1.42      | r1_tarski(k1_xboole_0,k4_xboole_0(X2,k4_xboole_0(X2,X3)))
% 7.15/1.42      | k4_xboole_0(X2,k4_xboole_0(X2,X3)) != X1
% 7.15/1.42      | k1_xboole_0 != X0 ),
% 7.15/1.42      inference(instantiation,[status(thm)],[c_282]) ).
% 7.15/1.42  
% 7.15/1.42  cnf(c_21830,plain,
% 7.15/1.42      ( r1_tarski(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k1_xboole_0)))
% 7.15/1.42      | ~ r1_tarski(k1_xboole_0,k1_xboole_0)
% 7.15/1.42      | k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k1_xboole_0)) != k1_xboole_0
% 7.15/1.42      | k1_xboole_0 != k1_xboole_0 ),
% 7.15/1.42      inference(instantiation,[status(thm)],[c_21828]) ).
% 7.15/1.42  
% 7.15/1.42  cnf(c_281,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 7.15/1.42  
% 7.15/1.42  cnf(c_280,plain,( X0 = X0 ),theory(equality) ).
% 7.15/1.42  
% 7.15/1.42  cnf(c_1889,plain,
% 7.15/1.42      ( X0 != X1 | X1 = X0 ),
% 7.15/1.42      inference(resolution,[status(thm)],[c_281,c_280]) ).
% 7.15/1.42  
% 7.15/1.42  cnf(c_11,plain,
% 7.15/1.42      ( r2_hidden(sK3(X0,X1,X2),X0)
% 7.15/1.42      | r2_hidden(sK2(X0,X1,X2),X2)
% 7.15/1.42      | k2_zfmisc_1(X0,X1) = X2 ),
% 7.15/1.42      inference(cnf_transformation,[],[f49]) ).
% 7.15/1.42  
% 7.15/1.42  cnf(c_17,plain,
% 7.15/1.42      ( r2_hidden(X0,X1)
% 7.15/1.42      | ~ r2_hidden(k4_tarski(X2,X0),k2_zfmisc_1(X3,X1)) ),
% 7.15/1.42      inference(cnf_transformation,[],[f54]) ).
% 7.15/1.42  
% 7.15/1.42  cnf(c_2,plain,
% 7.15/1.42      ( ~ r2_hidden(X0,X1) | r2_hidden(X0,X2) | ~ r1_tarski(X1,X2) ),
% 7.15/1.42      inference(cnf_transformation,[],[f36]) ).
% 7.15/1.42  
% 7.15/1.42  cnf(c_24,negated_conjecture,
% 7.15/1.42      ( r1_tarski(k2_zfmisc_1(sK7,sK8),k2_zfmisc_1(sK9,sK10)) ),
% 7.15/1.42      inference(cnf_transformation,[],[f59]) ).
% 7.15/1.42  
% 7.15/1.42  cnf(c_914,plain,
% 7.15/1.42      ( r2_hidden(X0,k2_zfmisc_1(sK9,sK10))
% 7.15/1.42      | ~ r2_hidden(X0,k2_zfmisc_1(sK7,sK8)) ),
% 7.15/1.42      inference(resolution,[status(thm)],[c_2,c_24]) ).
% 7.15/1.42  
% 7.15/1.42  cnf(c_1056,plain,
% 7.15/1.42      ( r2_hidden(X0,sK10)
% 7.15/1.42      | ~ r2_hidden(k4_tarski(X1,X0),k2_zfmisc_1(sK7,sK8)) ),
% 7.15/1.42      inference(resolution,[status(thm)],[c_17,c_914]) ).
% 7.15/1.42  
% 7.15/1.42  cnf(c_16,plain,
% 7.15/1.42      ( ~ r2_hidden(X0,X1)
% 7.15/1.42      | ~ r2_hidden(X2,X3)
% 7.15/1.42      | r2_hidden(k4_tarski(X2,X0),k2_zfmisc_1(X3,X1)) ),
% 7.15/1.42      inference(cnf_transformation,[],[f55]) ).
% 7.15/1.42  
% 7.15/1.42  cnf(c_2344,plain,
% 7.15/1.42      ( ~ r2_hidden(X0,sK7) | r2_hidden(X1,sK10) | ~ r2_hidden(X1,sK8) ),
% 7.15/1.42      inference(resolution,[status(thm)],[c_1056,c_16]) ).
% 7.15/1.42  
% 7.15/1.42  cnf(c_3488,plain,
% 7.15/1.42      ( r2_hidden(X0,sK10)
% 7.15/1.42      | ~ r2_hidden(X0,sK8)
% 7.15/1.42      | r2_hidden(sK2(sK7,X1,X2),X2)
% 7.15/1.42      | k2_zfmisc_1(sK7,X1) = X2 ),
% 7.15/1.42      inference(resolution,[status(thm)],[c_11,c_2344]) ).
% 7.15/1.42  
% 7.15/1.42  cnf(c_5512,plain,
% 7.15/1.42      ( r2_hidden(X0,sK10)
% 7.15/1.42      | ~ r2_hidden(X0,sK8)
% 7.15/1.42      | r2_hidden(sK2(sK7,X1,X2),X2)
% 7.15/1.42      | X2 = k2_zfmisc_1(sK7,X1) ),
% 7.15/1.42      inference(resolution,[status(thm)],[c_1889,c_3488]) ).
% 7.15/1.42  
% 7.15/1.42  cnf(c_23,negated_conjecture,
% 7.15/1.42      ( k1_xboole_0 != k2_zfmisc_1(sK7,sK8) ),
% 7.15/1.42      inference(cnf_transformation,[],[f60]) ).
% 7.15/1.42  
% 7.15/1.42  cnf(c_11988,plain,
% 7.15/1.42      ( r2_hidden(X0,sK10)
% 7.15/1.42      | ~ r2_hidden(X0,sK8)
% 7.15/1.42      | r2_hidden(sK2(sK7,sK8,k1_xboole_0),k1_xboole_0) ),
% 7.15/1.42      inference(resolution,[status(thm)],[c_5512,c_23]) ).
% 7.15/1.42  
% 7.15/1.42  cnf(c_0,plain,
% 7.15/1.42      ( ~ r2_hidden(sK0(X0,X1),X1) | r1_tarski(X0,X1) ),
% 7.15/1.42      inference(cnf_transformation,[],[f38]) ).
% 7.15/1.42  
% 7.15/1.42  cnf(c_12068,plain,
% 7.15/1.42      ( r2_hidden(sK2(sK7,sK8,k1_xboole_0),k1_xboole_0)
% 7.15/1.42      | ~ r2_hidden(sK0(X0,sK10),sK8)
% 7.15/1.42      | r1_tarski(X0,sK10) ),
% 7.15/1.42      inference(resolution,[status(thm)],[c_11988,c_0]) ).
% 7.15/1.42  
% 7.15/1.42  cnf(c_1,plain,
% 7.15/1.42      ( r2_hidden(sK0(X0,X1),X0) | r1_tarski(X0,X1) ),
% 7.15/1.42      inference(cnf_transformation,[],[f37]) ).
% 7.15/1.42  
% 7.15/1.42  cnf(c_12080,plain,
% 7.15/1.42      ( r2_hidden(sK2(sK7,sK8,k1_xboole_0),k1_xboole_0)
% 7.15/1.42      | r1_tarski(sK8,sK10) ),
% 7.15/1.42      inference(resolution,[status(thm)],[c_12068,c_1]) ).
% 7.15/1.42  
% 7.15/1.42  cnf(c_22,negated_conjecture,
% 7.15/1.42      ( ~ r1_tarski(sK7,sK9) | ~ r1_tarski(sK8,sK10) ),
% 7.15/1.42      inference(cnf_transformation,[],[f61]) ).
% 7.15/1.42  
% 7.15/1.42  cnf(c_10,plain,
% 7.15/1.42      ( r2_hidden(sK4(X0,X1,X2),X1)
% 7.15/1.42      | r2_hidden(sK2(X0,X1,X2),X2)
% 7.15/1.42      | k2_zfmisc_1(X0,X1) = X2 ),
% 7.15/1.42      inference(cnf_transformation,[],[f50]) ).
% 7.15/1.42  
% 7.15/1.42  cnf(c_18,plain,
% 7.15/1.42      ( r2_hidden(X0,X1)
% 7.15/1.42      | ~ r2_hidden(k4_tarski(X0,X2),k2_zfmisc_1(X1,X3)) ),
% 7.15/1.42      inference(cnf_transformation,[],[f53]) ).
% 7.15/1.42  
% 7.15/1.42  cnf(c_1066,plain,
% 7.15/1.42      ( r2_hidden(X0,sK9)
% 7.15/1.42      | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(sK7,sK8)) ),
% 7.15/1.42      inference(resolution,[status(thm)],[c_18,c_914]) ).
% 7.15/1.42  
% 7.15/1.42  cnf(c_2353,plain,
% 7.15/1.42      ( r2_hidden(X0,sK9) | ~ r2_hidden(X0,sK7) | ~ r2_hidden(X1,sK8) ),
% 7.15/1.42      inference(resolution,[status(thm)],[c_1066,c_16]) ).
% 7.15/1.42  
% 7.15/1.42  cnf(c_3418,plain,
% 7.15/1.42      ( r2_hidden(X0,sK9)
% 7.15/1.42      | ~ r2_hidden(X0,sK7)
% 7.15/1.42      | r2_hidden(sK2(X1,sK8,X2),X2)
% 7.15/1.42      | k2_zfmisc_1(X1,sK8) = X2 ),
% 7.15/1.42      inference(resolution,[status(thm)],[c_10,c_2353]) ).
% 7.15/1.42  
% 7.15/1.42  cnf(c_5508,plain,
% 7.15/1.42      ( r2_hidden(X0,sK9)
% 7.15/1.42      | ~ r2_hidden(X0,sK7)
% 7.15/1.42      | r2_hidden(sK2(X1,sK8,X2),X2)
% 7.15/1.42      | X2 = k2_zfmisc_1(X1,sK8) ),
% 7.15/1.42      inference(resolution,[status(thm)],[c_1889,c_3418]) ).
% 7.15/1.42  
% 7.15/1.42  cnf(c_10152,plain,
% 7.15/1.42      ( r2_hidden(X0,sK9)
% 7.15/1.42      | ~ r2_hidden(X0,sK7)
% 7.15/1.42      | r2_hidden(sK2(sK7,sK8,k1_xboole_0),k1_xboole_0) ),
% 7.15/1.42      inference(resolution,[status(thm)],[c_5508,c_23]) ).
% 7.15/1.42  
% 7.15/1.42  cnf(c_11692,plain,
% 7.15/1.42      ( r2_hidden(sK2(sK7,sK8,k1_xboole_0),k1_xboole_0)
% 7.15/1.42      | ~ r2_hidden(sK0(X0,sK9),sK7)
% 7.15/1.42      | r1_tarski(X0,sK9) ),
% 7.15/1.42      inference(resolution,[status(thm)],[c_10152,c_0]) ).
% 7.15/1.42  
% 7.15/1.42  cnf(c_11704,plain,
% 7.15/1.42      ( r2_hidden(sK2(sK7,sK8,k1_xboole_0),k1_xboole_0)
% 7.15/1.42      | r1_tarski(sK7,sK9) ),
% 7.15/1.42      inference(resolution,[status(thm)],[c_11692,c_1]) ).
% 7.15/1.42  
% 7.15/1.42  cnf(c_12368,plain,
% 7.15/1.42      ( r2_hidden(sK2(sK7,sK8,k1_xboole_0),k1_xboole_0) ),
% 7.15/1.42      inference(global_propositional_subsumption,
% 7.15/1.42                [status(thm)],
% 7.15/1.42                [c_12080,c_22,c_11704]) ).
% 7.15/1.42  
% 7.15/1.42  cnf(c_4,plain,
% 7.15/1.42      ( ~ r1_xboole_0(X0,X1)
% 7.15/1.42      | ~ r2_hidden(X2,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
% 7.15/1.42      inference(cnf_transformation,[],[f62]) ).
% 7.15/1.42  
% 7.15/1.42  cnf(c_2387,plain,
% 7.15/1.42      ( ~ r1_xboole_0(X0,X1)
% 7.15/1.42      | ~ r2_hidden(sK2(sK7,sK8,X2),k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
% 7.15/1.42      inference(instantiation,[status(thm)],[c_4]) ).
% 7.15/1.42  
% 7.15/1.42  cnf(c_2393,plain,
% 7.15/1.42      ( ~ r1_xboole_0(k1_xboole_0,k1_xboole_0)
% 7.15/1.42      | ~ r2_hidden(sK2(sK7,sK8,k1_xboole_0),k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k1_xboole_0))) ),
% 7.15/1.42      inference(instantiation,[status(thm)],[c_2387]) ).
% 7.15/1.42  
% 7.15/1.42  cnf(c_1122,plain,
% 7.15/1.42      ( ~ r2_hidden(sK2(sK7,sK8,X0),X0)
% 7.15/1.42      | r2_hidden(sK2(sK7,sK8,X0),X1)
% 7.15/1.42      | ~ r1_tarski(X0,X1) ),
% 7.15/1.42      inference(instantiation,[status(thm)],[c_2]) ).
% 7.15/1.42  
% 7.15/1.42  cnf(c_2386,plain,
% 7.15/1.42      ( ~ r2_hidden(sK2(sK7,sK8,X0),X0)
% 7.15/1.42      | r2_hidden(sK2(sK7,sK8,X0),k4_xboole_0(X1,k4_xboole_0(X1,X2)))
% 7.15/1.42      | ~ r1_tarski(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2))) ),
% 7.15/1.42      inference(instantiation,[status(thm)],[c_1122]) ).
% 7.15/1.42  
% 7.15/1.42  cnf(c_2389,plain,
% 7.15/1.42      ( r2_hidden(sK2(sK7,sK8,k1_xboole_0),k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k1_xboole_0)))
% 7.15/1.42      | ~ r2_hidden(sK2(sK7,sK8,k1_xboole_0),k1_xboole_0)
% 7.15/1.42      | ~ r1_tarski(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k1_xboole_0))) ),
% 7.15/1.42      inference(instantiation,[status(thm)],[c_2386]) ).
% 7.15/1.42  
% 7.15/1.42  cnf(c_609,plain,
% 7.15/1.42      ( k2_zfmisc_1(X0,X1) = X2
% 7.15/1.42      | r2_hidden(sK3(X0,X1,X2),X0) = iProver_top
% 7.15/1.42      | r2_hidden(sK2(X0,X1,X2),X2) = iProver_top ),
% 7.15/1.42      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 7.15/1.42  
% 7.15/1.42  cnf(c_6,plain,
% 7.15/1.42      ( k4_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
% 7.15/1.42      inference(cnf_transformation,[],[f43]) ).
% 7.15/1.42  
% 7.15/1.42  cnf(c_615,plain,
% 7.15/1.42      ( r1_xboole_0(X0,X1) != iProver_top
% 7.15/1.42      | r2_hidden(X2,k4_xboole_0(X0,k4_xboole_0(X0,X1))) != iProver_top ),
% 7.15/1.42      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 7.15/1.42  
% 7.15/1.42  cnf(c_1616,plain,
% 7.15/1.42      ( r1_xboole_0(k1_xboole_0,X0) != iProver_top
% 7.15/1.42      | r2_hidden(X1,k4_xboole_0(k1_xboole_0,k1_xboole_0)) != iProver_top ),
% 7.15/1.42      inference(superposition,[status(thm)],[c_6,c_615]) ).
% 7.15/1.42  
% 7.15/1.42  cnf(c_1619,plain,
% 7.15/1.42      ( r1_xboole_0(k1_xboole_0,X0) != iProver_top
% 7.15/1.42      | r2_hidden(X1,k1_xboole_0) != iProver_top ),
% 7.15/1.42      inference(demodulation,[status(thm)],[c_1616,c_6]) ).
% 7.15/1.42  
% 7.15/1.42  cnf(c_7,plain,
% 7.15/1.42      ( r1_xboole_0(X0,k1_xboole_0) ),
% 7.15/1.42      inference(cnf_transformation,[],[f44]) ).
% 7.15/1.42  
% 7.15/1.42  cnf(c_613,plain,
% 7.15/1.42      ( r1_xboole_0(X0,k1_xboole_0) = iProver_top ),
% 7.15/1.42      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 7.15/1.42  
% 7.15/1.42  cnf(c_3,plain,
% 7.15/1.42      ( ~ r1_xboole_0(X0,X1) | r1_xboole_0(X1,X0) ),
% 7.15/1.42      inference(cnf_transformation,[],[f39]) ).
% 7.15/1.42  
% 7.15/1.42  cnf(c_616,plain,
% 7.15/1.42      ( r1_xboole_0(X0,X1) != iProver_top
% 7.15/1.42      | r1_xboole_0(X1,X0) = iProver_top ),
% 7.15/1.42      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 7.15/1.42  
% 7.15/1.42  cnf(c_1024,plain,
% 7.15/1.42      ( r1_xboole_0(k1_xboole_0,X0) = iProver_top ),
% 7.15/1.42      inference(superposition,[status(thm)],[c_613,c_616]) ).
% 7.15/1.42  
% 7.15/1.42  cnf(c_1803,plain,
% 7.15/1.42      ( r2_hidden(X1,k1_xboole_0) != iProver_top ),
% 7.15/1.42      inference(global_propositional_subsumption,
% 7.15/1.42                [status(thm)],
% 7.15/1.42                [c_1619,c_1024]) ).
% 7.15/1.42  
% 7.15/1.42  cnf(c_1804,plain,
% 7.15/1.42      ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
% 7.15/1.42      inference(renaming,[status(thm)],[c_1803]) ).
% 7.15/1.42  
% 7.15/1.42  cnf(c_2057,plain,
% 7.15/1.42      ( k2_zfmisc_1(k1_xboole_0,X0) = X1
% 7.15/1.42      | r2_hidden(sK2(k1_xboole_0,X0,X1),X1) = iProver_top ),
% 7.15/1.42      inference(superposition,[status(thm)],[c_609,c_1804]) ).
% 7.15/1.42  
% 7.15/1.42  cnf(c_20,plain,
% 7.15/1.42      ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
% 7.15/1.42      inference(cnf_transformation,[],[f70]) ).
% 7.15/1.42  
% 7.15/1.42  cnf(c_2060,plain,
% 7.15/1.42      ( k1_xboole_0 = X0
% 7.15/1.42      | r2_hidden(sK2(k1_xboole_0,X1,X0),X0) = iProver_top ),
% 7.15/1.42      inference(demodulation,[status(thm)],[c_2057,c_20]) ).
% 7.15/1.42  
% 7.15/1.42  cnf(c_2223,plain,
% 7.15/1.42      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_xboole_0
% 7.15/1.42      | r1_xboole_0(X0,X1) != iProver_top ),
% 7.15/1.42      inference(superposition,[status(thm)],[c_2060,c_615]) ).
% 7.15/1.42  
% 7.15/1.42  cnf(c_2242,plain,
% 7.15/1.42      ( k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k1_xboole_0)) = k1_xboole_0
% 7.15/1.42      | r1_xboole_0(k1_xboole_0,k1_xboole_0) != iProver_top ),
% 7.15/1.42      inference(instantiation,[status(thm)],[c_2223]) ).
% 7.15/1.42  
% 7.15/1.42  cnf(c_821,plain,
% 7.15/1.42      ( r1_tarski(X0,X0) ),
% 7.15/1.42      inference(resolution,[status(thm)],[c_0,c_1]) ).
% 7.15/1.42  
% 7.15/1.42  cnf(c_823,plain,
% 7.15/1.42      ( r1_tarski(k1_xboole_0,k1_xboole_0) ),
% 7.15/1.42      inference(instantiation,[status(thm)],[c_821]) ).
% 7.15/1.42  
% 7.15/1.42  cnf(c_50,plain,
% 7.15/1.42      ( r1_xboole_0(X0,k1_xboole_0) = iProver_top ),
% 7.15/1.42      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 7.15/1.42  
% 7.15/1.42  cnf(c_52,plain,
% 7.15/1.42      ( r1_xboole_0(k1_xboole_0,k1_xboole_0) = iProver_top ),
% 7.15/1.42      inference(instantiation,[status(thm)],[c_50]) ).
% 7.15/1.42  
% 7.15/1.42  cnf(c_51,plain,
% 7.15/1.42      ( r1_xboole_0(k1_xboole_0,k1_xboole_0) ),
% 7.15/1.42      inference(instantiation,[status(thm)],[c_7]) ).
% 7.15/1.42  
% 7.15/1.42  cnf(c_28,plain,
% 7.15/1.42      ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
% 7.15/1.42      inference(instantiation,[status(thm)],[c_20]) ).
% 7.15/1.42  
% 7.15/1.42  cnf(c_21,plain,
% 7.15/1.42      ( k2_zfmisc_1(X0,X1) != k1_xboole_0
% 7.15/1.42      | k1_xboole_0 = X1
% 7.15/1.42      | k1_xboole_0 = X0 ),
% 7.15/1.42      inference(cnf_transformation,[],[f56]) ).
% 7.15/1.42  
% 7.15/1.42  cnf(c_27,plain,
% 7.15/1.42      ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) != k1_xboole_0
% 7.15/1.42      | k1_xboole_0 = k1_xboole_0 ),
% 7.15/1.42      inference(instantiation,[status(thm)],[c_21]) ).
% 7.15/1.42  
% 7.15/1.42  cnf(contradiction,plain,
% 7.15/1.42      ( $false ),
% 7.15/1.42      inference(minisat,
% 7.15/1.42                [status(thm)],
% 7.15/1.42                [c_21830,c_12368,c_2393,c_2389,c_2242,c_823,c_52,c_51,
% 7.15/1.42                 c_28,c_27]) ).
% 7.15/1.42  
% 7.15/1.42  
% 7.15/1.42  % SZS output end CNFRefutation for theBenchmark.p
% 7.15/1.42  
% 7.15/1.42  ------                               Statistics
% 7.15/1.42  
% 7.15/1.42  ------ Selected
% 7.15/1.42  
% 7.15/1.42  total_time:                             0.607
% 7.15/1.42  
%------------------------------------------------------------------------------
