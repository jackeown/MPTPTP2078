%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:47:30 EST 2020

% Result     : Theorem 3.78s
% Output     : CNFRefutation 3.78s
% Verified   : 
% Statistics : Number of formulae       :  113 ( 297 expanded)
%              Number of clauses        :   55 (  94 expanded)
%              Number of leaves         :   18 (  65 expanded)
%              Depth                    :   20
%              Number of atoms          :  410 (1208 expanded)
%              Number of equality atoms :  141 ( 359 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal clause size      :   15 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1,axiom,(
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

fof(f10,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X3] :
              ~ ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f1])).

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
    inference(ennf_transformation,[],[f10])).

fof(f15,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
     => ( r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ( r2_hidden(sK0(X0,X1),X1)
          & r2_hidden(sK0(X0,X1),X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f11,f15])).

fof(f39,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK0(X0,X1),X0)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f40,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK0(X0,X1),X1)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f8,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( k1_xboole_0 = k10_relat_1(X1,X0)
      <=> r1_xboole_0(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f9,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => ( k1_xboole_0 = k10_relat_1(X1,X0)
        <=> r1_xboole_0(k2_relat_1(X1),X0) ) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f14,plain,(
    ? [X0,X1] :
      ( ( k1_xboole_0 = k10_relat_1(X1,X0)
      <~> r1_xboole_0(k2_relat_1(X1),X0) )
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f35,plain,(
    ? [X0,X1] :
      ( ( ~ r1_xboole_0(k2_relat_1(X1),X0)
        | k1_xboole_0 != k10_relat_1(X1,X0) )
      & ( r1_xboole_0(k2_relat_1(X1),X0)
        | k1_xboole_0 = k10_relat_1(X1,X0) )
      & v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f14])).

fof(f36,plain,(
    ? [X0,X1] :
      ( ( ~ r1_xboole_0(k2_relat_1(X1),X0)
        | k1_xboole_0 != k10_relat_1(X1,X0) )
      & ( r1_xboole_0(k2_relat_1(X1),X0)
        | k1_xboole_0 = k10_relat_1(X1,X0) )
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f35])).

fof(f37,plain,
    ( ? [X0,X1] :
        ( ( ~ r1_xboole_0(k2_relat_1(X1),X0)
          | k1_xboole_0 != k10_relat_1(X1,X0) )
        & ( r1_xboole_0(k2_relat_1(X1),X0)
          | k1_xboole_0 = k10_relat_1(X1,X0) )
        & v1_relat_1(X1) )
   => ( ( ~ r1_xboole_0(k2_relat_1(sK9),sK8)
        | k1_xboole_0 != k10_relat_1(sK9,sK8) )
      & ( r1_xboole_0(k2_relat_1(sK9),sK8)
        | k1_xboole_0 = k10_relat_1(sK9,sK8) )
      & v1_relat_1(sK9) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,
    ( ( ~ r1_xboole_0(k2_relat_1(sK9),sK8)
      | k1_xboole_0 != k10_relat_1(sK9,sK8) )
    & ( r1_xboole_0(k2_relat_1(sK9),sK8)
      | k1_xboole_0 = k10_relat_1(sK9,sK8) )
    & v1_relat_1(sK9) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8,sK9])],[f36,f37])).

fof(f63,plain,
    ( r1_xboole_0(k2_relat_1(sK9),sK8)
    | k1_xboole_0 = k10_relat_1(sK9,sK8) ),
    inference(cnf_transformation,[],[f38])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( k2_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X3,X2),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( k2_relat_1(X0) = X1
        | ? [X2] :
            ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,X2),X0)
              | ~ r2_hidden(X2,X1) )
            & ( ? [X3] : r2_hidden(k4_tarski(X3,X2),X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | ! [X3] : ~ r2_hidden(k4_tarski(X3,X2),X0) )
            & ( ? [X3] : r2_hidden(k4_tarski(X3,X2),X0)
              | ~ r2_hidden(X2,X1) ) )
        | k2_relat_1(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( k2_relat_1(X0) = X1
        | ? [X2] :
            ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,X2),X0)
              | ~ r2_hidden(X2,X1) )
            & ( ? [X4] : r2_hidden(k4_tarski(X4,X2),X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] : ~ r2_hidden(k4_tarski(X6,X5),X0) )
            & ( ? [X7] : r2_hidden(k4_tarski(X7,X5),X0)
              | ~ r2_hidden(X5,X1) ) )
        | k2_relat_1(X0) != X1 ) ) ),
    inference(rectify,[],[f25])).

fof(f29,plain,(
    ! [X5,X0] :
      ( ? [X7] : r2_hidden(k4_tarski(X7,X5),X0)
     => r2_hidden(k4_tarski(sK6(X0,X5),X5),X0) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] : r2_hidden(k4_tarski(X4,X2),X0)
     => r2_hidden(k4_tarski(sK5(X0,X1),X2),X0) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,X2),X0)
            | ~ r2_hidden(X2,X1) )
          & ( ? [X4] : r2_hidden(k4_tarski(X4,X2),X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,sK4(X0,X1)),X0)
          | ~ r2_hidden(sK4(X0,X1),X1) )
        & ( ? [X4] : r2_hidden(k4_tarski(X4,sK4(X0,X1)),X0)
          | r2_hidden(sK4(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( k2_relat_1(X0) = X1
        | ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,sK4(X0,X1)),X0)
            | ~ r2_hidden(sK4(X0,X1),X1) )
          & ( r2_hidden(k4_tarski(sK5(X0,X1),sK4(X0,X1)),X0)
            | r2_hidden(sK4(X0,X1),X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] : ~ r2_hidden(k4_tarski(X6,X5),X0) )
            & ( r2_hidden(k4_tarski(sK6(X0,X5),X5),X0)
              | ~ r2_hidden(X5,X1) ) )
        | k2_relat_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6])],[f26,f29,f28,f27])).

fof(f54,plain,(
    ! [X0,X1] :
      ( k2_relat_1(X0) = X1
      | r2_hidden(k4_tarski(sK5(X0,X1),sK4(X0,X1)),X0)
      | r2_hidden(sK4(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) = k1_xboole_0
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1] :
      ( ( k2_zfmisc_1(X0,X1) = k1_xboole_0
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k2_zfmisc_1(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ( k2_zfmisc_1(X0,X1) = k1_xboole_0
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k2_zfmisc_1(X0,X1) != k1_xboole_0 ) ) ),
    inference(flattening,[],[f17])).

fof(f44,plain,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) = k1_xboole_0
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f18])).

fof(f65,plain,(
    ! [X0] : k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(equality_resolution,[],[f44])).

fof(f3,axiom,(
    ! [X0,X1] : ~ r2_hidden(X0,k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X0,X1] : ~ r2_hidden(X0,k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f7,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f61,plain,(
    k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f7])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(X0,k10_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X0,X3),X2)
            & r2_hidden(X3,k2_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k10_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X0,X3),X2)
            & r2_hidden(X3,k2_relat_1(X2)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k10_relat_1(X2,X1))
          | ! [X3] :
              ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(k4_tarski(X0,X3),X2)
              | ~ r2_hidden(X3,k2_relat_1(X2)) ) )
        & ( ? [X3] :
              ( r2_hidden(X3,X1)
              & r2_hidden(k4_tarski(X0,X3),X2)
              & r2_hidden(X3,k2_relat_1(X2)) )
          | ~ r2_hidden(X0,k10_relat_1(X2,X1)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(nnf_transformation,[],[f13])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k10_relat_1(X2,X1))
          | ! [X3] :
              ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(k4_tarski(X0,X3),X2)
              | ~ r2_hidden(X3,k2_relat_1(X2)) ) )
        & ( ? [X4] :
              ( r2_hidden(X4,X1)
              & r2_hidden(k4_tarski(X0,X4),X2)
              & r2_hidden(X4,k2_relat_1(X2)) )
          | ~ r2_hidden(X0,k10_relat_1(X2,X1)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(rectify,[],[f31])).

fof(f33,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( r2_hidden(X4,X1)
          & r2_hidden(k4_tarski(X0,X4),X2)
          & r2_hidden(X4,k2_relat_1(X2)) )
     => ( r2_hidden(sK7(X0,X1,X2),X1)
        & r2_hidden(k4_tarski(X0,sK7(X0,X1,X2)),X2)
        & r2_hidden(sK7(X0,X1,X2),k2_relat_1(X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k10_relat_1(X2,X1))
          | ! [X3] :
              ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(k4_tarski(X0,X3),X2)
              | ~ r2_hidden(X3,k2_relat_1(X2)) ) )
        & ( ( r2_hidden(sK7(X0,X1,X2),X1)
            & r2_hidden(k4_tarski(X0,sK7(X0,X1,X2)),X2)
            & r2_hidden(sK7(X0,X1,X2),k2_relat_1(X2)) )
          | ~ r2_hidden(X0,k10_relat_1(X2,X1)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f32,f33])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK7(X0,X1,X2),k2_relat_1(X2))
      | ~ r2_hidden(X0,k10_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f62,plain,(
    v1_relat_1(sK9) ),
    inference(cnf_transformation,[],[f38])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK7(X0,X1,X2),X1)
      | ~ r2_hidden(X0,k10_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f52,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(k4_tarski(sK6(X0,X5),X5),X0)
      | ~ r2_hidden(X5,X1)
      | k2_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f30])).

fof(f71,plain,(
    ! [X0,X5] :
      ( r2_hidden(k4_tarski(sK6(X0,X5),X5),X0)
      | ~ r2_hidden(X5,k2_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f52])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1,X2] :
          ( k10_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ? [X4] :
                  ( r2_hidden(X4,X1)
                  & r2_hidden(k4_tarski(X3,X4),X0) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k10_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ? [X4] :
                  ( r2_hidden(X4,X1)
                  & r2_hidden(k4_tarski(X3,X4),X0) ) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k10_relat_1(X0,X1) = X2
            | ? [X3] :
                ( ( ! [X4] :
                      ( ~ r2_hidden(X4,X1)
                      | ~ r2_hidden(k4_tarski(X3,X4),X0) )
                  | ~ r2_hidden(X3,X2) )
                & ( ? [X4] :
                      ( r2_hidden(X4,X1)
                      & r2_hidden(k4_tarski(X3,X4),X0) )
                  | r2_hidden(X3,X2) ) ) )
          & ( ! [X3] :
                ( ( r2_hidden(X3,X2)
                  | ! [X4] :
                      ( ~ r2_hidden(X4,X1)
                      | ~ r2_hidden(k4_tarski(X3,X4),X0) ) )
                & ( ? [X4] :
                      ( r2_hidden(X4,X1)
                      & r2_hidden(k4_tarski(X3,X4),X0) )
                  | ~ r2_hidden(X3,X2) ) )
            | k10_relat_1(X0,X1) != X2 ) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f12])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k10_relat_1(X0,X1) = X2
            | ? [X3] :
                ( ( ! [X4] :
                      ( ~ r2_hidden(X4,X1)
                      | ~ r2_hidden(k4_tarski(X3,X4),X0) )
                  | ~ r2_hidden(X3,X2) )
                & ( ? [X5] :
                      ( r2_hidden(X5,X1)
                      & r2_hidden(k4_tarski(X3,X5),X0) )
                  | r2_hidden(X3,X2) ) ) )
          & ( ! [X6] :
                ( ( r2_hidden(X6,X2)
                  | ! [X7] :
                      ( ~ r2_hidden(X7,X1)
                      | ~ r2_hidden(k4_tarski(X6,X7),X0) ) )
                & ( ? [X8] :
                      ( r2_hidden(X8,X1)
                      & r2_hidden(k4_tarski(X6,X8),X0) )
                  | ~ r2_hidden(X6,X2) ) )
            | k10_relat_1(X0,X1) != X2 ) )
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f19])).

fof(f23,plain,(
    ! [X6,X1,X0] :
      ( ? [X8] :
          ( r2_hidden(X8,X1)
          & r2_hidden(k4_tarski(X6,X8),X0) )
     => ( r2_hidden(sK3(X0,X1,X6),X1)
        & r2_hidden(k4_tarski(X6,sK3(X0,X1,X6)),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X5] :
          ( r2_hidden(X5,X1)
          & r2_hidden(k4_tarski(X3,X5),X0) )
     => ( r2_hidden(sK2(X0,X1,X2),X1)
        & r2_hidden(k4_tarski(X3,sK2(X0,X1,X2)),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ! [X4] :
                ( ~ r2_hidden(X4,X1)
                | ~ r2_hidden(k4_tarski(X3,X4),X0) )
            | ~ r2_hidden(X3,X2) )
          & ( ? [X5] :
                ( r2_hidden(X5,X1)
                & r2_hidden(k4_tarski(X3,X5),X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( ! [X4] :
              ( ~ r2_hidden(X4,X1)
              | ~ r2_hidden(k4_tarski(sK1(X0,X1,X2),X4),X0) )
          | ~ r2_hidden(sK1(X0,X1,X2),X2) )
        & ( ? [X5] :
              ( r2_hidden(X5,X1)
              & r2_hidden(k4_tarski(sK1(X0,X1,X2),X5),X0) )
          | r2_hidden(sK1(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k10_relat_1(X0,X1) = X2
            | ( ( ! [X4] :
                    ( ~ r2_hidden(X4,X1)
                    | ~ r2_hidden(k4_tarski(sK1(X0,X1,X2),X4),X0) )
                | ~ r2_hidden(sK1(X0,X1,X2),X2) )
              & ( ( r2_hidden(sK2(X0,X1,X2),X1)
                  & r2_hidden(k4_tarski(sK1(X0,X1,X2),sK2(X0,X1,X2)),X0) )
                | r2_hidden(sK1(X0,X1,X2),X2) ) ) )
          & ( ! [X6] :
                ( ( r2_hidden(X6,X2)
                  | ! [X7] :
                      ( ~ r2_hidden(X7,X1)
                      | ~ r2_hidden(k4_tarski(X6,X7),X0) ) )
                & ( ( r2_hidden(sK3(X0,X1,X6),X1)
                    & r2_hidden(k4_tarski(X6,sK3(X0,X1,X6)),X0) )
                  | ~ r2_hidden(X6,X2) ) )
            | k10_relat_1(X0,X1) != X2 ) )
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f20,f23,f22,f21])).

fof(f48,plain,(
    ! [X6,X2,X0,X7,X1] :
      ( r2_hidden(X6,X2)
      | ~ r2_hidden(X7,X1)
      | ~ r2_hidden(k4_tarski(X6,X7),X0)
      | k10_relat_1(X0,X1) != X2
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f67,plain,(
    ! [X6,X0,X7,X1] :
      ( r2_hidden(X6,k10_relat_1(X0,X1))
      | ~ r2_hidden(X7,X1)
      | ~ r2_hidden(k4_tarski(X6,X7),X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f48])).

fof(f43,plain,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) = k1_xboole_0
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f18])).

fof(f66,plain,(
    ! [X1] : k2_zfmisc_1(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(equality_resolution,[],[f43])).

fof(f42,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | k2_zfmisc_1(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f18])).

fof(f64,plain,
    ( ~ r1_xboole_0(k2_relat_1(sK9),sK8)
    | k1_xboole_0 != k10_relat_1(sK9,sK8) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_2,plain,
    ( r2_hidden(sK0(X0,X1),X0)
    | r1_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_2386,plain,
    ( r2_hidden(sK0(X0,X1),X0) = iProver_top
    | r1_xboole_0(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_1,plain,
    ( r2_hidden(sK0(X0,X1),X1)
    | r1_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_2387,plain,
    ( r2_hidden(sK0(X0,X1),X1) = iProver_top
    | r1_xboole_0(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_24,negated_conjecture,
    ( r1_xboole_0(k2_relat_1(sK9),sK8)
    | k1_xboole_0 = k10_relat_1(sK9,sK8) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_2379,plain,
    ( k1_xboole_0 = k10_relat_1(sK9,sK8)
    | r1_xboole_0(k2_relat_1(sK9),sK8) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_14,plain,
    ( r2_hidden(sK4(X0,X1),X1)
    | r2_hidden(k4_tarski(sK5(X0,X1),sK4(X0,X1)),X0)
    | k2_relat_1(X0) = X1 ),
    inference(cnf_transformation,[],[f54])).

cnf(c_2383,plain,
    ( k2_relat_1(X0) = X1
    | r2_hidden(sK4(X0,X1),X1) = iProver_top
    | r2_hidden(k4_tarski(sK5(X0,X1),sK4(X0,X1)),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_3,plain,
    ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f65])).

cnf(c_6,negated_conjecture,
    ( ~ r2_hidden(X0,k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_2385,plain,
    ( r2_hidden(X0,k2_zfmisc_1(X0,X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_2780,plain,
    ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_3,c_2385])).

cnf(c_3161,plain,
    ( k2_relat_1(k1_xboole_0) = X0
    | r2_hidden(sK4(k1_xboole_0,X0),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_2383,c_2780])).

cnf(c_21,plain,
    ( k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f61])).

cnf(c_3164,plain,
    ( k1_xboole_0 = X0
    | r2_hidden(sK4(k1_xboole_0,X0),X0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_3161,c_21])).

cnf(c_20,plain,
    ( ~ r2_hidden(X0,k10_relat_1(X1,X2))
    | r2_hidden(sK7(X0,X2,X1),k2_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_25,negated_conjecture,
    ( v1_relat_1(sK9) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_436,plain,
    ( ~ r2_hidden(X0,k10_relat_1(X1,X2))
    | r2_hidden(sK7(X0,X2,X1),k2_relat_1(X1))
    | sK9 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_20,c_25])).

cnf(c_437,plain,
    ( ~ r2_hidden(X0,k10_relat_1(sK9,X1))
    | r2_hidden(sK7(X0,X1,sK9),k2_relat_1(sK9)) ),
    inference(unflattening,[status(thm)],[c_436])).

cnf(c_2372,plain,
    ( r2_hidden(X0,k10_relat_1(sK9,X1)) != iProver_top
    | r2_hidden(sK7(X0,X1,sK9),k2_relat_1(sK9)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_437])).

cnf(c_18,plain,
    ( ~ r2_hidden(X0,k10_relat_1(X1,X2))
    | r2_hidden(sK7(X0,X2,X1),X2)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_460,plain,
    ( ~ r2_hidden(X0,k10_relat_1(X1,X2))
    | r2_hidden(sK7(X0,X2,X1),X2)
    | sK9 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_18,c_25])).

cnf(c_461,plain,
    ( ~ r2_hidden(X0,k10_relat_1(sK9,X1))
    | r2_hidden(sK7(X0,X1,sK9),X1) ),
    inference(unflattening,[status(thm)],[c_460])).

cnf(c_2370,plain,
    ( r2_hidden(X0,k10_relat_1(sK9,X1)) != iProver_top
    | r2_hidden(sK7(X0,X1,sK9),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_461])).

cnf(c_0,negated_conjecture,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X0,X2)
    | ~ r1_xboole_0(X2,X1) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_2388,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,X2) != iProver_top
    | r1_xboole_0(X2,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_2617,plain,
    ( r2_hidden(X0,k10_relat_1(sK9,X1)) != iProver_top
    | r2_hidden(sK7(X0,X1,sK9),X2) != iProver_top
    | r1_xboole_0(X2,X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_2370,c_2388])).

cnf(c_2873,plain,
    ( r2_hidden(X0,k10_relat_1(sK9,X1)) != iProver_top
    | r1_xboole_0(k2_relat_1(sK9),X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_2372,c_2617])).

cnf(c_3742,plain,
    ( k10_relat_1(sK9,X0) = k1_xboole_0
    | r1_xboole_0(k2_relat_1(sK9),X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_3164,c_2873])).

cnf(c_4865,plain,
    ( k10_relat_1(sK9,sK8) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2379,c_3742])).

cnf(c_16,plain,
    ( ~ r2_hidden(X0,k2_relat_1(X1))
    | r2_hidden(k4_tarski(sK6(X1,X0),X0),X1) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_2381,plain,
    ( r2_hidden(X0,k2_relat_1(X1)) != iProver_top
    | r2_hidden(k4_tarski(sK6(X1,X0),X0),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_10,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,k10_relat_1(X3,X1))
    | ~ r2_hidden(k4_tarski(X2,X0),X3)
    | ~ v1_relat_1(X3) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_421,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,k10_relat_1(X3,X1))
    | ~ r2_hidden(k4_tarski(X2,X0),X3)
    | sK9 != X3 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_25])).

cnf(c_422,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,k10_relat_1(sK9,X1))
    | ~ r2_hidden(k4_tarski(X2,X0),sK9) ),
    inference(unflattening,[status(thm)],[c_421])).

cnf(c_2373,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X2,k10_relat_1(sK9,X1)) = iProver_top
    | r2_hidden(k4_tarski(X2,X0),sK9) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_422])).

cnf(c_3111,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,k2_relat_1(sK9)) != iProver_top
    | r2_hidden(sK6(sK9,X0),k10_relat_1(sK9,X1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2381,c_2373])).

cnf(c_5367,plain,
    ( r2_hidden(X0,k2_relat_1(sK9)) != iProver_top
    | r2_hidden(X0,sK8) != iProver_top
    | r2_hidden(sK6(sK9,X0),k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_4865,c_3111])).

cnf(c_5510,plain,
    ( r2_hidden(X0,k2_relat_1(sK9)) != iProver_top
    | r2_hidden(X0,sK8) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_5367,c_2780])).

cnf(c_5514,plain,
    ( r2_hidden(sK0(X0,k2_relat_1(sK9)),sK8) != iProver_top
    | r1_xboole_0(X0,k2_relat_1(sK9)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2387,c_5510])).

cnf(c_15669,plain,
    ( r1_xboole_0(sK8,k2_relat_1(sK9)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2386,c_5514])).

cnf(c_2958,plain,
    ( r2_hidden(sK0(X0,X1),X2) != iProver_top
    | r1_xboole_0(X2,X0) != iProver_top
    | r1_xboole_0(X0,X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_2386,c_2388])).

cnf(c_2991,plain,
    ( r1_xboole_0(X0,X1) != iProver_top
    | r1_xboole_0(X1,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_2387,c_2958])).

cnf(c_15675,plain,
    ( r1_xboole_0(k2_relat_1(sK9),sK8) = iProver_top ),
    inference(superposition,[status(thm)],[c_15669,c_2991])).

cnf(c_790,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_2596,plain,
    ( X0 != X1
    | X0 = k10_relat_1(sK9,X2)
    | k10_relat_1(sK9,X2) != X1 ),
    inference(instantiation,[status(thm)],[c_790])).

cnf(c_3286,plain,
    ( k10_relat_1(sK9,sK8) != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = k10_relat_1(sK9,sK8) ),
    inference(instantiation,[status(thm)],[c_2596])).

cnf(c_3287,plain,
    ( k10_relat_1(sK9,sK8) != k1_xboole_0
    | k1_xboole_0 = k10_relat_1(sK9,sK8)
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_3286])).

cnf(c_4,plain,
    ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f66])).

cnf(c_74,plain,
    ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_5,plain,
    ( k2_zfmisc_1(X0,X1) != k1_xboole_0
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f42])).

cnf(c_73,plain,
    ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) != k1_xboole_0
    | k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_23,negated_conjecture,
    ( ~ r1_xboole_0(k2_relat_1(sK9),sK8)
    | k1_xboole_0 != k10_relat_1(sK9,sK8) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_28,plain,
    ( k1_xboole_0 != k10_relat_1(sK9,sK8)
    | r1_xboole_0(k2_relat_1(sK9),sK8) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_15675,c_4865,c_3287,c_74,c_73,c_28])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n006.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 20:44:07 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 3.78/0.98  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.78/0.98  
% 3.78/0.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.78/0.98  
% 3.78/0.98  ------  iProver source info
% 3.78/0.98  
% 3.78/0.98  git: date: 2020-06-30 10:37:57 +0100
% 3.78/0.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.78/0.98  git: non_committed_changes: false
% 3.78/0.98  git: last_make_outside_of_git: false
% 3.78/0.98  
% 3.78/0.98  ------ 
% 3.78/0.98  ------ Parsing...
% 3.78/0.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.78/0.98  
% 3.78/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 3.78/0.98  
% 3.78/0.98  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.78/0.98  
% 3.78/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.78/0.98  ------ Proving...
% 3.78/0.98  ------ Problem Properties 
% 3.78/0.98  
% 3.78/0.98  
% 3.78/0.98  clauses                                 24
% 3.78/0.98  conjectures                             4
% 3.78/0.98  EPR                                     1
% 3.78/0.98  Horn                                    17
% 3.78/0.98  unary                                   5
% 3.78/0.98  binary                                  11
% 3.78/0.98  lits                                    52
% 3.78/0.98  lits eq                                 14
% 3.78/0.98  fd_pure                                 0
% 3.78/0.98  fd_pseudo                               0
% 3.78/0.98  fd_cond                                 1
% 3.78/0.98  fd_pseudo_cond                          5
% 3.78/0.98  AC symbols                              0
% 3.78/0.98  
% 3.78/0.98  ------ Input Options Time Limit: Unbounded
% 3.78/0.98  
% 3.78/0.98  
% 3.78/0.98  
% 3.78/0.98  
% 3.78/0.98  ------ Preprocessing... sf_s  rm: 12 0s  sf_e  sf_s  rm: 0 0s  sf_e ------ 
% 3.78/0.98  Current options:
% 3.78/0.98  ------ 
% 3.78/0.98  
% 3.78/0.98  
% 3.78/0.98  
% 3.78/0.98  
% 3.78/0.98  ------ Proving...
% 3.78/0.98  
% 3.78/0.98  
% 3.78/0.98  ------ Preprocessing... sf_s  rm: 13 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.78/0.98  
% 3.78/0.98  ------ Proving...
% 3.78/0.98  
% 3.78/0.98  
% 3.78/0.98  ------ Preprocessing... sf_s  rm: 15 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.78/0.98  
% 3.78/0.98  ------ Proving...
% 3.78/0.98  
% 3.78/0.98  
% 3.78/0.98  ------ Preprocessing... sf_s  rm: 17 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.78/0.98  
% 3.78/0.98  ------ Proving...
% 3.78/0.98  
% 3.78/0.98  
% 3.78/0.98  ------ Preprocessing... sf_s  rm: 18 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.78/0.98  
% 3.78/0.98  ------ Proving...
% 3.78/0.98  
% 3.78/0.98  
% 3.78/0.98  ------ Preprocessing... sf_s  rm: 18 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.78/0.98  
% 3.78/0.98  ------ Proving...
% 3.78/0.98  
% 3.78/0.98  
% 3.78/0.98  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 3.78/0.98  
% 3.78/0.98  ------ Proving...
% 3.78/0.98  
% 3.78/0.98  
% 3.78/0.98  % SZS status Theorem for theBenchmark.p
% 3.78/0.98  
% 3.78/0.98  % SZS output start CNFRefutation for theBenchmark.p
% 3.78/0.98  
% 3.78/0.98  fof(f1,axiom,(
% 3.78/0.98    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 3.78/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.78/0.98  
% 3.78/0.98  fof(f10,plain,(
% 3.78/0.98    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 3.78/0.98    inference(rectify,[],[f1])).
% 3.78/0.98  
% 3.78/0.98  fof(f11,plain,(
% 3.78/0.98    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 3.78/0.98    inference(ennf_transformation,[],[f10])).
% 3.78/0.98  
% 3.78/0.98  fof(f15,plain,(
% 3.78/0.98    ! [X1,X0] : (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) => (r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 3.78/0.98    introduced(choice_axiom,[])).
% 3.78/0.98  
% 3.78/0.98  fof(f16,plain,(
% 3.78/0.98    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & ((r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)) | r1_xboole_0(X0,X1)))),
% 3.78/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f11,f15])).
% 3.78/0.98  
% 3.78/0.98  fof(f39,plain,(
% 3.78/0.98    ( ! [X0,X1] : (r2_hidden(sK0(X0,X1),X0) | r1_xboole_0(X0,X1)) )),
% 3.78/0.98    inference(cnf_transformation,[],[f16])).
% 3.78/0.98  
% 3.78/0.98  fof(f40,plain,(
% 3.78/0.98    ( ! [X0,X1] : (r2_hidden(sK0(X0,X1),X1) | r1_xboole_0(X0,X1)) )),
% 3.78/0.98    inference(cnf_transformation,[],[f16])).
% 3.78/0.98  
% 3.78/0.98  fof(f8,conjecture,(
% 3.78/0.98    ! [X0,X1] : (v1_relat_1(X1) => (k1_xboole_0 = k10_relat_1(X1,X0) <=> r1_xboole_0(k2_relat_1(X1),X0)))),
% 3.78/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.78/0.98  
% 3.78/0.98  fof(f9,negated_conjecture,(
% 3.78/0.98    ~! [X0,X1] : (v1_relat_1(X1) => (k1_xboole_0 = k10_relat_1(X1,X0) <=> r1_xboole_0(k2_relat_1(X1),X0)))),
% 3.78/0.98    inference(negated_conjecture,[],[f8])).
% 3.78/0.98  
% 3.78/0.98  fof(f14,plain,(
% 3.78/0.98    ? [X0,X1] : ((k1_xboole_0 = k10_relat_1(X1,X0) <~> r1_xboole_0(k2_relat_1(X1),X0)) & v1_relat_1(X1))),
% 3.78/0.98    inference(ennf_transformation,[],[f9])).
% 3.78/0.98  
% 3.78/0.98  fof(f35,plain,(
% 3.78/0.98    ? [X0,X1] : (((~r1_xboole_0(k2_relat_1(X1),X0) | k1_xboole_0 != k10_relat_1(X1,X0)) & (r1_xboole_0(k2_relat_1(X1),X0) | k1_xboole_0 = k10_relat_1(X1,X0))) & v1_relat_1(X1))),
% 3.78/0.98    inference(nnf_transformation,[],[f14])).
% 3.78/0.98  
% 3.78/0.98  fof(f36,plain,(
% 3.78/0.98    ? [X0,X1] : ((~r1_xboole_0(k2_relat_1(X1),X0) | k1_xboole_0 != k10_relat_1(X1,X0)) & (r1_xboole_0(k2_relat_1(X1),X0) | k1_xboole_0 = k10_relat_1(X1,X0)) & v1_relat_1(X1))),
% 3.78/0.98    inference(flattening,[],[f35])).
% 3.78/0.98  
% 3.78/0.98  fof(f37,plain,(
% 3.78/0.98    ? [X0,X1] : ((~r1_xboole_0(k2_relat_1(X1),X0) | k1_xboole_0 != k10_relat_1(X1,X0)) & (r1_xboole_0(k2_relat_1(X1),X0) | k1_xboole_0 = k10_relat_1(X1,X0)) & v1_relat_1(X1)) => ((~r1_xboole_0(k2_relat_1(sK9),sK8) | k1_xboole_0 != k10_relat_1(sK9,sK8)) & (r1_xboole_0(k2_relat_1(sK9),sK8) | k1_xboole_0 = k10_relat_1(sK9,sK8)) & v1_relat_1(sK9))),
% 3.78/0.98    introduced(choice_axiom,[])).
% 3.78/0.98  
% 3.78/0.98  fof(f38,plain,(
% 3.78/0.98    (~r1_xboole_0(k2_relat_1(sK9),sK8) | k1_xboole_0 != k10_relat_1(sK9,sK8)) & (r1_xboole_0(k2_relat_1(sK9),sK8) | k1_xboole_0 = k10_relat_1(sK9,sK8)) & v1_relat_1(sK9)),
% 3.78/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8,sK9])],[f36,f37])).
% 3.78/0.98  
% 3.78/0.98  fof(f63,plain,(
% 3.78/0.98    r1_xboole_0(k2_relat_1(sK9),sK8) | k1_xboole_0 = k10_relat_1(sK9,sK8)),
% 3.78/0.98    inference(cnf_transformation,[],[f38])).
% 3.78/0.98  
% 3.78/0.98  fof(f5,axiom,(
% 3.78/0.98    ! [X0,X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : r2_hidden(k4_tarski(X3,X2),X0)))),
% 3.78/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.78/0.98  
% 3.78/0.98  fof(f25,plain,(
% 3.78/0.98    ! [X0,X1] : ((k2_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1)) & (? [X3] : r2_hidden(k4_tarski(X3,X2),X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0)) & (? [X3] : r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1))) | k2_relat_1(X0) != X1))),
% 3.78/0.98    inference(nnf_transformation,[],[f5])).
% 3.78/0.98  
% 3.78/0.98  fof(f26,plain,(
% 3.78/0.98    ! [X0,X1] : ((k2_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X4,X2),X0) | r2_hidden(X2,X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X6,X5),X0)) & (? [X7] : r2_hidden(k4_tarski(X7,X5),X0) | ~r2_hidden(X5,X1))) | k2_relat_1(X0) != X1))),
% 3.78/0.98    inference(rectify,[],[f25])).
% 3.78/0.98  
% 3.78/0.98  fof(f29,plain,(
% 3.78/0.98    ! [X5,X0] : (? [X7] : r2_hidden(k4_tarski(X7,X5),X0) => r2_hidden(k4_tarski(sK6(X0,X5),X5),X0))),
% 3.78/0.98    introduced(choice_axiom,[])).
% 3.78/0.98  
% 3.78/0.98  fof(f28,plain,(
% 3.78/0.98    ( ! [X2] : (! [X1,X0] : (? [X4] : r2_hidden(k4_tarski(X4,X2),X0) => r2_hidden(k4_tarski(sK5(X0,X1),X2),X0))) )),
% 3.78/0.98    introduced(choice_axiom,[])).
% 3.78/0.98  
% 3.78/0.98  fof(f27,plain,(
% 3.78/0.98    ! [X1,X0] : (? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X4,X2),X0) | r2_hidden(X2,X1))) => ((! [X3] : ~r2_hidden(k4_tarski(X3,sK4(X0,X1)),X0) | ~r2_hidden(sK4(X0,X1),X1)) & (? [X4] : r2_hidden(k4_tarski(X4,sK4(X0,X1)),X0) | r2_hidden(sK4(X0,X1),X1))))),
% 3.78/0.98    introduced(choice_axiom,[])).
% 3.78/0.98  
% 3.78/0.98  fof(f30,plain,(
% 3.78/0.98    ! [X0,X1] : ((k2_relat_1(X0) = X1 | ((! [X3] : ~r2_hidden(k4_tarski(X3,sK4(X0,X1)),X0) | ~r2_hidden(sK4(X0,X1),X1)) & (r2_hidden(k4_tarski(sK5(X0,X1),sK4(X0,X1)),X0) | r2_hidden(sK4(X0,X1),X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X6,X5),X0)) & (r2_hidden(k4_tarski(sK6(X0,X5),X5),X0) | ~r2_hidden(X5,X1))) | k2_relat_1(X0) != X1))),
% 3.78/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6])],[f26,f29,f28,f27])).
% 3.78/0.98  
% 3.78/0.98  fof(f54,plain,(
% 3.78/0.98    ( ! [X0,X1] : (k2_relat_1(X0) = X1 | r2_hidden(k4_tarski(sK5(X0,X1),sK4(X0,X1)),X0) | r2_hidden(sK4(X0,X1),X1)) )),
% 3.78/0.98    inference(cnf_transformation,[],[f30])).
% 3.78/0.98  
% 3.78/0.98  fof(f2,axiom,(
% 3.78/0.98    ! [X0,X1] : (k2_zfmisc_1(X0,X1) = k1_xboole_0 <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 3.78/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.78/0.98  
% 3.78/0.98  fof(f17,plain,(
% 3.78/0.98    ! [X0,X1] : ((k2_zfmisc_1(X0,X1) = k1_xboole_0 | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k2_zfmisc_1(X0,X1) != k1_xboole_0))),
% 3.78/0.98    inference(nnf_transformation,[],[f2])).
% 3.78/0.98  
% 3.78/0.98  fof(f18,plain,(
% 3.78/0.98    ! [X0,X1] : ((k2_zfmisc_1(X0,X1) = k1_xboole_0 | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k2_zfmisc_1(X0,X1) != k1_xboole_0))),
% 3.78/0.98    inference(flattening,[],[f17])).
% 3.78/0.98  
% 3.78/0.98  fof(f44,plain,(
% 3.78/0.98    ( ! [X0,X1] : (k2_zfmisc_1(X0,X1) = k1_xboole_0 | k1_xboole_0 != X1) )),
% 3.78/0.98    inference(cnf_transformation,[],[f18])).
% 3.78/0.98  
% 3.78/0.98  fof(f65,plain,(
% 3.78/0.98    ( ! [X0] : (k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0) )),
% 3.78/0.98    inference(equality_resolution,[],[f44])).
% 3.78/0.98  
% 3.78/0.98  fof(f3,axiom,(
% 3.78/0.98    ! [X0,X1] : ~r2_hidden(X0,k2_zfmisc_1(X0,X1))),
% 3.78/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.78/0.98  
% 3.78/0.98  fof(f45,plain,(
% 3.78/0.98    ( ! [X0,X1] : (~r2_hidden(X0,k2_zfmisc_1(X0,X1))) )),
% 3.78/0.98    inference(cnf_transformation,[],[f3])).
% 3.78/0.98  
% 3.78/0.98  fof(f7,axiom,(
% 3.78/0.98    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 3.78/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.78/0.98  
% 3.78/0.98  fof(f61,plain,(
% 3.78/0.98    k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 3.78/0.98    inference(cnf_transformation,[],[f7])).
% 3.78/0.98  
% 3.78/0.98  fof(f6,axiom,(
% 3.78/0.98    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(X0,k10_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X0,X3),X2) & r2_hidden(X3,k2_relat_1(X2)))))),
% 3.78/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.78/0.98  
% 3.78/0.98  fof(f13,plain,(
% 3.78/0.98    ! [X0,X1,X2] : ((r2_hidden(X0,k10_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X0,X3),X2) & r2_hidden(X3,k2_relat_1(X2)))) | ~v1_relat_1(X2))),
% 3.78/0.98    inference(ennf_transformation,[],[f6])).
% 3.78/0.98  
% 3.78/0.98  fof(f31,plain,(
% 3.78/0.98    ! [X0,X1,X2] : (((r2_hidden(X0,k10_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X0,X3),X2) | ~r2_hidden(X3,k2_relat_1(X2)))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X0,X3),X2) & r2_hidden(X3,k2_relat_1(X2))) | ~r2_hidden(X0,k10_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 3.78/0.98    inference(nnf_transformation,[],[f13])).
% 3.78/0.98  
% 3.78/0.98  fof(f32,plain,(
% 3.78/0.98    ! [X0,X1,X2] : (((r2_hidden(X0,k10_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X0,X3),X2) | ~r2_hidden(X3,k2_relat_1(X2)))) & (? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X0,X4),X2) & r2_hidden(X4,k2_relat_1(X2))) | ~r2_hidden(X0,k10_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 3.78/0.98    inference(rectify,[],[f31])).
% 3.78/0.98  
% 3.78/0.98  fof(f33,plain,(
% 3.78/0.98    ! [X2,X1,X0] : (? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X0,X4),X2) & r2_hidden(X4,k2_relat_1(X2))) => (r2_hidden(sK7(X0,X1,X2),X1) & r2_hidden(k4_tarski(X0,sK7(X0,X1,X2)),X2) & r2_hidden(sK7(X0,X1,X2),k2_relat_1(X2))))),
% 3.78/0.98    introduced(choice_axiom,[])).
% 3.78/0.98  
% 3.78/0.98  fof(f34,plain,(
% 3.78/0.98    ! [X0,X1,X2] : (((r2_hidden(X0,k10_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X0,X3),X2) | ~r2_hidden(X3,k2_relat_1(X2)))) & ((r2_hidden(sK7(X0,X1,X2),X1) & r2_hidden(k4_tarski(X0,sK7(X0,X1,X2)),X2) & r2_hidden(sK7(X0,X1,X2),k2_relat_1(X2))) | ~r2_hidden(X0,k10_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 3.78/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f32,f33])).
% 3.78/0.98  
% 3.78/0.98  fof(f56,plain,(
% 3.78/0.98    ( ! [X2,X0,X1] : (r2_hidden(sK7(X0,X1,X2),k2_relat_1(X2)) | ~r2_hidden(X0,k10_relat_1(X2,X1)) | ~v1_relat_1(X2)) )),
% 3.78/0.98    inference(cnf_transformation,[],[f34])).
% 3.78/0.98  
% 3.78/0.98  fof(f62,plain,(
% 3.78/0.98    v1_relat_1(sK9)),
% 3.78/0.98    inference(cnf_transformation,[],[f38])).
% 3.78/0.98  
% 3.78/0.98  fof(f58,plain,(
% 3.78/0.98    ( ! [X2,X0,X1] : (r2_hidden(sK7(X0,X1,X2),X1) | ~r2_hidden(X0,k10_relat_1(X2,X1)) | ~v1_relat_1(X2)) )),
% 3.78/0.98    inference(cnf_transformation,[],[f34])).
% 3.78/0.98  
% 3.78/0.98  fof(f41,plain,(
% 3.78/0.98    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) )),
% 3.78/0.98    inference(cnf_transformation,[],[f16])).
% 3.78/0.98  
% 3.78/0.98  fof(f52,plain,(
% 3.78/0.98    ( ! [X0,X5,X1] : (r2_hidden(k4_tarski(sK6(X0,X5),X5),X0) | ~r2_hidden(X5,X1) | k2_relat_1(X0) != X1) )),
% 3.78/0.98    inference(cnf_transformation,[],[f30])).
% 3.78/0.98  
% 3.78/0.98  fof(f71,plain,(
% 3.78/0.98    ( ! [X0,X5] : (r2_hidden(k4_tarski(sK6(X0,X5),X5),X0) | ~r2_hidden(X5,k2_relat_1(X0))) )),
% 3.78/0.98    inference(equality_resolution,[],[f52])).
% 3.78/0.98  
% 3.78/0.98  fof(f4,axiom,(
% 3.78/0.98    ! [X0] : (v1_relat_1(X0) => ! [X1,X2] : (k10_relat_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X3,X4),X0)))))),
% 3.78/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.78/0.98  
% 3.78/0.98  fof(f12,plain,(
% 3.78/0.98    ! [X0] : (! [X1,X2] : (k10_relat_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X3,X4),X0)))) | ~v1_relat_1(X0))),
% 3.78/0.98    inference(ennf_transformation,[],[f4])).
% 3.78/0.98  
% 3.78/0.98  fof(f19,plain,(
% 3.78/0.98    ! [X0] : (! [X1,X2] : ((k10_relat_1(X0,X1) = X2 | ? [X3] : ((! [X4] : (~r2_hidden(X4,X1) | ~r2_hidden(k4_tarski(X3,X4),X0)) | ~r2_hidden(X3,X2)) & (? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X3,X4),X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ! [X4] : (~r2_hidden(X4,X1) | ~r2_hidden(k4_tarski(X3,X4),X0))) & (? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X3,X4),X0)) | ~r2_hidden(X3,X2))) | k10_relat_1(X0,X1) != X2)) | ~v1_relat_1(X0))),
% 3.78/0.98    inference(nnf_transformation,[],[f12])).
% 3.78/0.98  
% 3.78/0.98  fof(f20,plain,(
% 3.78/0.98    ! [X0] : (! [X1,X2] : ((k10_relat_1(X0,X1) = X2 | ? [X3] : ((! [X4] : (~r2_hidden(X4,X1) | ~r2_hidden(k4_tarski(X3,X4),X0)) | ~r2_hidden(X3,X2)) & (? [X5] : (r2_hidden(X5,X1) & r2_hidden(k4_tarski(X3,X5),X0)) | r2_hidden(X3,X2)))) & (! [X6] : ((r2_hidden(X6,X2) | ! [X7] : (~r2_hidden(X7,X1) | ~r2_hidden(k4_tarski(X6,X7),X0))) & (? [X8] : (r2_hidden(X8,X1) & r2_hidden(k4_tarski(X6,X8),X0)) | ~r2_hidden(X6,X2))) | k10_relat_1(X0,X1) != X2)) | ~v1_relat_1(X0))),
% 3.78/0.98    inference(rectify,[],[f19])).
% 3.78/0.98  
% 3.78/0.98  fof(f23,plain,(
% 3.78/0.98    ! [X6,X1,X0] : (? [X8] : (r2_hidden(X8,X1) & r2_hidden(k4_tarski(X6,X8),X0)) => (r2_hidden(sK3(X0,X1,X6),X1) & r2_hidden(k4_tarski(X6,sK3(X0,X1,X6)),X0)))),
% 3.78/0.98    introduced(choice_axiom,[])).
% 3.78/0.98  
% 3.78/0.98  fof(f22,plain,(
% 3.78/0.98    ( ! [X3] : (! [X2,X1,X0] : (? [X5] : (r2_hidden(X5,X1) & r2_hidden(k4_tarski(X3,X5),X0)) => (r2_hidden(sK2(X0,X1,X2),X1) & r2_hidden(k4_tarski(X3,sK2(X0,X1,X2)),X0)))) )),
% 3.78/0.98    introduced(choice_axiom,[])).
% 3.78/0.98  
% 3.78/0.98  fof(f21,plain,(
% 3.78/0.98    ! [X2,X1,X0] : (? [X3] : ((! [X4] : (~r2_hidden(X4,X1) | ~r2_hidden(k4_tarski(X3,X4),X0)) | ~r2_hidden(X3,X2)) & (? [X5] : (r2_hidden(X5,X1) & r2_hidden(k4_tarski(X3,X5),X0)) | r2_hidden(X3,X2))) => ((! [X4] : (~r2_hidden(X4,X1) | ~r2_hidden(k4_tarski(sK1(X0,X1,X2),X4),X0)) | ~r2_hidden(sK1(X0,X1,X2),X2)) & (? [X5] : (r2_hidden(X5,X1) & r2_hidden(k4_tarski(sK1(X0,X1,X2),X5),X0)) | r2_hidden(sK1(X0,X1,X2),X2))))),
% 3.78/0.98    introduced(choice_axiom,[])).
% 3.78/0.98  
% 3.78/0.98  fof(f24,plain,(
% 3.78/0.98    ! [X0] : (! [X1,X2] : ((k10_relat_1(X0,X1) = X2 | ((! [X4] : (~r2_hidden(X4,X1) | ~r2_hidden(k4_tarski(sK1(X0,X1,X2),X4),X0)) | ~r2_hidden(sK1(X0,X1,X2),X2)) & ((r2_hidden(sK2(X0,X1,X2),X1) & r2_hidden(k4_tarski(sK1(X0,X1,X2),sK2(X0,X1,X2)),X0)) | r2_hidden(sK1(X0,X1,X2),X2)))) & (! [X6] : ((r2_hidden(X6,X2) | ! [X7] : (~r2_hidden(X7,X1) | ~r2_hidden(k4_tarski(X6,X7),X0))) & ((r2_hidden(sK3(X0,X1,X6),X1) & r2_hidden(k4_tarski(X6,sK3(X0,X1,X6)),X0)) | ~r2_hidden(X6,X2))) | k10_relat_1(X0,X1) != X2)) | ~v1_relat_1(X0))),
% 3.78/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f20,f23,f22,f21])).
% 3.78/0.98  
% 3.78/0.98  fof(f48,plain,(
% 3.78/0.98    ( ! [X6,X2,X0,X7,X1] : (r2_hidden(X6,X2) | ~r2_hidden(X7,X1) | ~r2_hidden(k4_tarski(X6,X7),X0) | k10_relat_1(X0,X1) != X2 | ~v1_relat_1(X0)) )),
% 3.78/0.98    inference(cnf_transformation,[],[f24])).
% 3.78/0.98  
% 3.78/0.98  fof(f67,plain,(
% 3.78/0.98    ( ! [X6,X0,X7,X1] : (r2_hidden(X6,k10_relat_1(X0,X1)) | ~r2_hidden(X7,X1) | ~r2_hidden(k4_tarski(X6,X7),X0) | ~v1_relat_1(X0)) )),
% 3.78/0.98    inference(equality_resolution,[],[f48])).
% 3.78/0.98  
% 3.78/0.98  fof(f43,plain,(
% 3.78/0.98    ( ! [X0,X1] : (k2_zfmisc_1(X0,X1) = k1_xboole_0 | k1_xboole_0 != X0) )),
% 3.78/0.98    inference(cnf_transformation,[],[f18])).
% 3.78/0.98  
% 3.78/0.98  fof(f66,plain,(
% 3.78/0.98    ( ! [X1] : (k2_zfmisc_1(k1_xboole_0,X1) = k1_xboole_0) )),
% 3.78/0.98    inference(equality_resolution,[],[f43])).
% 3.78/0.98  
% 3.78/0.98  fof(f42,plain,(
% 3.78/0.98    ( ! [X0,X1] : (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k2_zfmisc_1(X0,X1) != k1_xboole_0) )),
% 3.78/0.98    inference(cnf_transformation,[],[f18])).
% 3.78/0.98  
% 3.78/0.98  fof(f64,plain,(
% 3.78/0.98    ~r1_xboole_0(k2_relat_1(sK9),sK8) | k1_xboole_0 != k10_relat_1(sK9,sK8)),
% 3.78/0.98    inference(cnf_transformation,[],[f38])).
% 3.78/0.98  
% 3.78/0.98  cnf(c_2,plain,
% 3.78/0.98      ( r2_hidden(sK0(X0,X1),X0) | r1_xboole_0(X0,X1) ),
% 3.78/0.98      inference(cnf_transformation,[],[f39]) ).
% 3.78/0.98  
% 3.78/0.98  cnf(c_2386,plain,
% 3.78/0.98      ( r2_hidden(sK0(X0,X1),X0) = iProver_top
% 3.78/0.98      | r1_xboole_0(X0,X1) = iProver_top ),
% 3.78/0.98      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 3.78/0.98  
% 3.78/0.98  cnf(c_1,plain,
% 3.78/0.98      ( r2_hidden(sK0(X0,X1),X1) | r1_xboole_0(X0,X1) ),
% 3.78/0.98      inference(cnf_transformation,[],[f40]) ).
% 3.78/0.98  
% 3.78/0.98  cnf(c_2387,plain,
% 3.78/0.98      ( r2_hidden(sK0(X0,X1),X1) = iProver_top
% 3.78/0.98      | r1_xboole_0(X0,X1) = iProver_top ),
% 3.78/0.98      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 3.78/0.98  
% 3.78/0.98  cnf(c_24,negated_conjecture,
% 3.78/0.98      ( r1_xboole_0(k2_relat_1(sK9),sK8)
% 3.78/0.98      | k1_xboole_0 = k10_relat_1(sK9,sK8) ),
% 3.78/0.98      inference(cnf_transformation,[],[f63]) ).
% 3.78/0.98  
% 3.78/0.98  cnf(c_2379,plain,
% 3.78/0.98      ( k1_xboole_0 = k10_relat_1(sK9,sK8)
% 3.78/0.98      | r1_xboole_0(k2_relat_1(sK9),sK8) = iProver_top ),
% 3.78/0.98      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 3.78/0.98  
% 3.78/0.98  cnf(c_14,plain,
% 3.78/0.98      ( r2_hidden(sK4(X0,X1),X1)
% 3.78/0.98      | r2_hidden(k4_tarski(sK5(X0,X1),sK4(X0,X1)),X0)
% 3.78/0.98      | k2_relat_1(X0) = X1 ),
% 3.78/0.98      inference(cnf_transformation,[],[f54]) ).
% 3.78/0.98  
% 3.78/0.98  cnf(c_2383,plain,
% 3.78/0.98      ( k2_relat_1(X0) = X1
% 3.78/0.98      | r2_hidden(sK4(X0,X1),X1) = iProver_top
% 3.78/0.98      | r2_hidden(k4_tarski(sK5(X0,X1),sK4(X0,X1)),X0) = iProver_top ),
% 3.78/0.98      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 3.78/0.98  
% 3.78/0.98  cnf(c_3,plain,
% 3.78/0.98      ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
% 3.78/0.98      inference(cnf_transformation,[],[f65]) ).
% 3.78/0.98  
% 3.78/0.98  cnf(c_6,negated_conjecture,
% 3.78/0.98      ( ~ r2_hidden(X0,k2_zfmisc_1(X0,X1)) ),
% 3.78/0.98      inference(cnf_transformation,[],[f45]) ).
% 3.78/0.98  
% 3.78/0.98  cnf(c_2385,plain,
% 3.78/0.98      ( r2_hidden(X0,k2_zfmisc_1(X0,X1)) != iProver_top ),
% 3.78/0.98      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 3.78/0.98  
% 3.78/0.98  cnf(c_2780,plain,
% 3.78/0.98      ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
% 3.78/0.98      inference(superposition,[status(thm)],[c_3,c_2385]) ).
% 3.78/0.98  
% 3.78/0.98  cnf(c_3161,plain,
% 3.78/0.98      ( k2_relat_1(k1_xboole_0) = X0
% 3.78/0.98      | r2_hidden(sK4(k1_xboole_0,X0),X0) = iProver_top ),
% 3.78/0.98      inference(superposition,[status(thm)],[c_2383,c_2780]) ).
% 3.78/0.98  
% 3.78/0.98  cnf(c_21,plain,
% 3.78/0.98      ( k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
% 3.78/0.98      inference(cnf_transformation,[],[f61]) ).
% 3.78/0.98  
% 3.78/0.98  cnf(c_3164,plain,
% 3.78/0.98      ( k1_xboole_0 = X0
% 3.78/0.98      | r2_hidden(sK4(k1_xboole_0,X0),X0) = iProver_top ),
% 3.78/0.98      inference(demodulation,[status(thm)],[c_3161,c_21]) ).
% 3.78/0.98  
% 3.78/0.98  cnf(c_20,plain,
% 3.78/0.98      ( ~ r2_hidden(X0,k10_relat_1(X1,X2))
% 3.78/0.98      | r2_hidden(sK7(X0,X2,X1),k2_relat_1(X1))
% 3.78/0.98      | ~ v1_relat_1(X1) ),
% 3.78/0.98      inference(cnf_transformation,[],[f56]) ).
% 3.78/0.98  
% 3.78/0.98  cnf(c_25,negated_conjecture,
% 3.78/0.98      ( v1_relat_1(sK9) ),
% 3.78/0.98      inference(cnf_transformation,[],[f62]) ).
% 3.78/0.98  
% 3.78/0.98  cnf(c_436,plain,
% 3.78/0.98      ( ~ r2_hidden(X0,k10_relat_1(X1,X2))
% 3.78/0.98      | r2_hidden(sK7(X0,X2,X1),k2_relat_1(X1))
% 3.78/0.98      | sK9 != X1 ),
% 3.78/0.98      inference(resolution_lifted,[status(thm)],[c_20,c_25]) ).
% 3.78/0.98  
% 3.78/0.98  cnf(c_437,plain,
% 3.78/0.98      ( ~ r2_hidden(X0,k10_relat_1(sK9,X1))
% 3.78/0.98      | r2_hidden(sK7(X0,X1,sK9),k2_relat_1(sK9)) ),
% 3.78/0.98      inference(unflattening,[status(thm)],[c_436]) ).
% 3.78/0.98  
% 3.78/0.98  cnf(c_2372,plain,
% 3.78/0.98      ( r2_hidden(X0,k10_relat_1(sK9,X1)) != iProver_top
% 3.78/0.98      | r2_hidden(sK7(X0,X1,sK9),k2_relat_1(sK9)) = iProver_top ),
% 3.78/0.98      inference(predicate_to_equality,[status(thm)],[c_437]) ).
% 3.78/0.98  
% 3.78/0.98  cnf(c_18,plain,
% 3.78/0.98      ( ~ r2_hidden(X0,k10_relat_1(X1,X2))
% 3.78/0.98      | r2_hidden(sK7(X0,X2,X1),X2)
% 3.78/0.98      | ~ v1_relat_1(X1) ),
% 3.78/0.98      inference(cnf_transformation,[],[f58]) ).
% 3.78/0.98  
% 3.78/0.98  cnf(c_460,plain,
% 3.78/0.98      ( ~ r2_hidden(X0,k10_relat_1(X1,X2))
% 3.78/0.98      | r2_hidden(sK7(X0,X2,X1),X2)
% 3.78/0.98      | sK9 != X1 ),
% 3.78/0.98      inference(resolution_lifted,[status(thm)],[c_18,c_25]) ).
% 3.78/0.98  
% 3.78/0.98  cnf(c_461,plain,
% 3.78/0.98      ( ~ r2_hidden(X0,k10_relat_1(sK9,X1))
% 3.78/0.98      | r2_hidden(sK7(X0,X1,sK9),X1) ),
% 3.78/0.98      inference(unflattening,[status(thm)],[c_460]) ).
% 3.78/0.98  
% 3.78/0.98  cnf(c_2370,plain,
% 3.78/0.98      ( r2_hidden(X0,k10_relat_1(sK9,X1)) != iProver_top
% 3.78/0.98      | r2_hidden(sK7(X0,X1,sK9),X1) = iProver_top ),
% 3.78/0.98      inference(predicate_to_equality,[status(thm)],[c_461]) ).
% 3.78/0.98  
% 3.78/0.98  cnf(c_0,negated_conjecture,
% 3.78/0.98      ( ~ r2_hidden(X0,X1) | ~ r2_hidden(X0,X2) | ~ r1_xboole_0(X2,X1) ),
% 3.78/0.98      inference(cnf_transformation,[],[f41]) ).
% 3.78/0.98  
% 3.78/0.98  cnf(c_2388,plain,
% 3.78/0.98      ( r2_hidden(X0,X1) != iProver_top
% 3.78/0.98      | r2_hidden(X0,X2) != iProver_top
% 3.78/0.98      | r1_xboole_0(X2,X1) != iProver_top ),
% 3.78/0.98      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 3.78/0.98  
% 3.78/0.98  cnf(c_2617,plain,
% 3.78/0.98      ( r2_hidden(X0,k10_relat_1(sK9,X1)) != iProver_top
% 3.78/0.98      | r2_hidden(sK7(X0,X1,sK9),X2) != iProver_top
% 3.78/0.98      | r1_xboole_0(X2,X1) != iProver_top ),
% 3.78/0.98      inference(superposition,[status(thm)],[c_2370,c_2388]) ).
% 3.78/0.98  
% 3.78/0.98  cnf(c_2873,plain,
% 3.78/0.98      ( r2_hidden(X0,k10_relat_1(sK9,X1)) != iProver_top
% 3.78/0.98      | r1_xboole_0(k2_relat_1(sK9),X1) != iProver_top ),
% 3.78/0.98      inference(superposition,[status(thm)],[c_2372,c_2617]) ).
% 3.78/0.98  
% 3.78/0.98  cnf(c_3742,plain,
% 3.78/0.98      ( k10_relat_1(sK9,X0) = k1_xboole_0
% 3.78/0.98      | r1_xboole_0(k2_relat_1(sK9),X0) != iProver_top ),
% 3.78/0.98      inference(superposition,[status(thm)],[c_3164,c_2873]) ).
% 3.78/0.98  
% 3.78/0.98  cnf(c_4865,plain,
% 3.78/0.98      ( k10_relat_1(sK9,sK8) = k1_xboole_0 ),
% 3.78/0.98      inference(superposition,[status(thm)],[c_2379,c_3742]) ).
% 3.78/0.98  
% 3.78/0.98  cnf(c_16,plain,
% 3.78/0.98      ( ~ r2_hidden(X0,k2_relat_1(X1))
% 3.78/0.98      | r2_hidden(k4_tarski(sK6(X1,X0),X0),X1) ),
% 3.78/0.98      inference(cnf_transformation,[],[f71]) ).
% 3.78/0.98  
% 3.78/0.98  cnf(c_2381,plain,
% 3.78/0.98      ( r2_hidden(X0,k2_relat_1(X1)) != iProver_top
% 3.78/0.98      | r2_hidden(k4_tarski(sK6(X1,X0),X0),X1) = iProver_top ),
% 3.78/0.98      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 3.78/0.98  
% 3.78/0.98  cnf(c_10,plain,
% 3.78/0.98      ( ~ r2_hidden(X0,X1)
% 3.78/0.98      | r2_hidden(X2,k10_relat_1(X3,X1))
% 3.78/0.98      | ~ r2_hidden(k4_tarski(X2,X0),X3)
% 3.78/0.98      | ~ v1_relat_1(X3) ),
% 3.78/0.98      inference(cnf_transformation,[],[f67]) ).
% 3.78/0.98  
% 3.78/0.98  cnf(c_421,plain,
% 3.78/0.98      ( ~ r2_hidden(X0,X1)
% 3.78/0.98      | r2_hidden(X2,k10_relat_1(X3,X1))
% 3.78/0.98      | ~ r2_hidden(k4_tarski(X2,X0),X3)
% 3.78/0.98      | sK9 != X3 ),
% 3.78/0.98      inference(resolution_lifted,[status(thm)],[c_10,c_25]) ).
% 3.78/0.98  
% 3.78/0.98  cnf(c_422,plain,
% 3.78/0.98      ( ~ r2_hidden(X0,X1)
% 3.78/0.98      | r2_hidden(X2,k10_relat_1(sK9,X1))
% 3.78/0.98      | ~ r2_hidden(k4_tarski(X2,X0),sK9) ),
% 3.78/0.98      inference(unflattening,[status(thm)],[c_421]) ).
% 3.78/0.98  
% 3.78/0.98  cnf(c_2373,plain,
% 3.78/0.98      ( r2_hidden(X0,X1) != iProver_top
% 3.78/0.98      | r2_hidden(X2,k10_relat_1(sK9,X1)) = iProver_top
% 3.78/0.98      | r2_hidden(k4_tarski(X2,X0),sK9) != iProver_top ),
% 3.78/0.98      inference(predicate_to_equality,[status(thm)],[c_422]) ).
% 3.78/0.98  
% 3.78/0.98  cnf(c_3111,plain,
% 3.78/0.98      ( r2_hidden(X0,X1) != iProver_top
% 3.78/0.98      | r2_hidden(X0,k2_relat_1(sK9)) != iProver_top
% 3.78/0.98      | r2_hidden(sK6(sK9,X0),k10_relat_1(sK9,X1)) = iProver_top ),
% 3.78/0.98      inference(superposition,[status(thm)],[c_2381,c_2373]) ).
% 3.78/0.98  
% 3.78/0.98  cnf(c_5367,plain,
% 3.78/0.98      ( r2_hidden(X0,k2_relat_1(sK9)) != iProver_top
% 3.78/0.98      | r2_hidden(X0,sK8) != iProver_top
% 3.78/0.98      | r2_hidden(sK6(sK9,X0),k1_xboole_0) = iProver_top ),
% 3.78/0.98      inference(superposition,[status(thm)],[c_4865,c_3111]) ).
% 3.78/0.98  
% 3.78/0.98  cnf(c_5510,plain,
% 3.78/0.98      ( r2_hidden(X0,k2_relat_1(sK9)) != iProver_top
% 3.78/0.98      | r2_hidden(X0,sK8) != iProver_top ),
% 3.78/0.98      inference(forward_subsumption_resolution,
% 3.78/0.98                [status(thm)],
% 3.78/0.98                [c_5367,c_2780]) ).
% 3.78/0.98  
% 3.78/0.98  cnf(c_5514,plain,
% 3.78/0.98      ( r2_hidden(sK0(X0,k2_relat_1(sK9)),sK8) != iProver_top
% 3.78/0.98      | r1_xboole_0(X0,k2_relat_1(sK9)) = iProver_top ),
% 3.78/0.98      inference(superposition,[status(thm)],[c_2387,c_5510]) ).
% 3.78/0.98  
% 3.78/0.98  cnf(c_15669,plain,
% 3.78/0.98      ( r1_xboole_0(sK8,k2_relat_1(sK9)) = iProver_top ),
% 3.78/0.98      inference(superposition,[status(thm)],[c_2386,c_5514]) ).
% 3.78/0.98  
% 3.78/0.98  cnf(c_2958,plain,
% 3.78/0.98      ( r2_hidden(sK0(X0,X1),X2) != iProver_top
% 3.78/0.98      | r1_xboole_0(X2,X0) != iProver_top
% 3.78/0.98      | r1_xboole_0(X0,X1) = iProver_top ),
% 3.78/0.98      inference(superposition,[status(thm)],[c_2386,c_2388]) ).
% 3.78/0.98  
% 3.78/0.98  cnf(c_2991,plain,
% 3.78/0.98      ( r1_xboole_0(X0,X1) != iProver_top
% 3.78/0.98      | r1_xboole_0(X1,X0) = iProver_top ),
% 3.78/0.98      inference(superposition,[status(thm)],[c_2387,c_2958]) ).
% 3.78/0.98  
% 3.78/0.98  cnf(c_15675,plain,
% 3.78/0.98      ( r1_xboole_0(k2_relat_1(sK9),sK8) = iProver_top ),
% 3.78/0.98      inference(superposition,[status(thm)],[c_15669,c_2991]) ).
% 3.78/0.98  
% 3.78/0.98  cnf(c_790,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 3.78/0.98  
% 3.78/0.98  cnf(c_2596,plain,
% 3.78/0.98      ( X0 != X1 | X0 = k10_relat_1(sK9,X2) | k10_relat_1(sK9,X2) != X1 ),
% 3.78/0.98      inference(instantiation,[status(thm)],[c_790]) ).
% 3.78/0.98  
% 3.78/0.98  cnf(c_3286,plain,
% 3.78/0.98      ( k10_relat_1(sK9,sK8) != X0
% 3.78/0.98      | k1_xboole_0 != X0
% 3.78/0.98      | k1_xboole_0 = k10_relat_1(sK9,sK8) ),
% 3.78/0.98      inference(instantiation,[status(thm)],[c_2596]) ).
% 3.78/0.98  
% 3.78/0.98  cnf(c_3287,plain,
% 3.78/0.98      ( k10_relat_1(sK9,sK8) != k1_xboole_0
% 3.78/0.98      | k1_xboole_0 = k10_relat_1(sK9,sK8)
% 3.78/0.98      | k1_xboole_0 != k1_xboole_0 ),
% 3.78/0.98      inference(instantiation,[status(thm)],[c_3286]) ).
% 3.78/0.98  
% 3.78/0.98  cnf(c_4,plain,
% 3.78/0.98      ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
% 3.78/0.98      inference(cnf_transformation,[],[f66]) ).
% 3.78/0.98  
% 3.78/0.98  cnf(c_74,plain,
% 3.78/0.98      ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
% 3.78/0.98      inference(instantiation,[status(thm)],[c_4]) ).
% 3.78/0.98  
% 3.78/0.98  cnf(c_5,plain,
% 3.78/0.98      ( k2_zfmisc_1(X0,X1) != k1_xboole_0
% 3.78/0.98      | k1_xboole_0 = X1
% 3.78/0.98      | k1_xboole_0 = X0 ),
% 3.78/0.98      inference(cnf_transformation,[],[f42]) ).
% 3.78/0.98  
% 3.78/0.98  cnf(c_73,plain,
% 3.78/0.98      ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) != k1_xboole_0
% 3.78/0.98      | k1_xboole_0 = k1_xboole_0 ),
% 3.78/0.98      inference(instantiation,[status(thm)],[c_5]) ).
% 3.78/0.98  
% 3.78/0.98  cnf(c_23,negated_conjecture,
% 3.78/0.98      ( ~ r1_xboole_0(k2_relat_1(sK9),sK8)
% 3.78/0.98      | k1_xboole_0 != k10_relat_1(sK9,sK8) ),
% 3.78/0.98      inference(cnf_transformation,[],[f64]) ).
% 3.78/0.98  
% 3.78/0.98  cnf(c_28,plain,
% 3.78/0.98      ( k1_xboole_0 != k10_relat_1(sK9,sK8)
% 3.78/0.98      | r1_xboole_0(k2_relat_1(sK9),sK8) != iProver_top ),
% 3.78/0.98      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 3.78/0.98  
% 3.78/0.98  cnf(contradiction,plain,
% 3.78/0.98      ( $false ),
% 3.78/0.98      inference(minisat,
% 3.78/0.98                [status(thm)],
% 3.78/0.98                [c_15675,c_4865,c_3287,c_74,c_73,c_28]) ).
% 3.78/0.98  
% 3.78/0.98  
% 3.78/0.98  % SZS output end CNFRefutation for theBenchmark.p
% 3.78/0.98  
% 3.78/0.98  ------                               Statistics
% 3.78/0.98  
% 3.78/0.98  ------ Selected
% 3.78/0.98  
% 3.78/0.98  total_time:                             0.405
% 3.78/0.98  
%------------------------------------------------------------------------------
