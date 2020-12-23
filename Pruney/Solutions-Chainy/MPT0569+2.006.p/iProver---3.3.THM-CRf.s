%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:47:28 EST 2020

% Result     : Theorem 23.48s
% Output     : CNFRefutation 23.48s
% Verified   : 
% Statistics : Number of formulae       :  142 ( 495 expanded)
%              Number of clauses        :   72 ( 172 expanded)
%              Number of leaves         :   25 ( 108 expanded)
%              Depth                    :   30
%              Number of atoms          :  532 (2047 expanded)
%              Number of equality atoms :  140 ( 574 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal clause size      :   15 (   2 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f3])).

fof(f14,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f27,plain,(
    ! [X1,X0] :
      ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
     => r2_hidden(sK1(X0,X1),k3_xboole_0(X0,X1)) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( r2_hidden(sK1(X0,X1),k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f14,f27])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,k3_xboole_0(X0,X1)) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f21])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f22])).

fof(f24,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ~ r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( ~ r2_hidden(sK0(X0,X1,X2),X1)
          | ~ r2_hidden(sK0(X0,X1,X2),X0)
          | ~ r2_hidden(sK0(X0,X1,X2),X2) )
        & ( ( r2_hidden(sK0(X0,X1,X2),X1)
            & r2_hidden(sK0(X0,X1,X2),X0) )
          | r2_hidden(sK0(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ( ( ~ r2_hidden(sK0(X0,X1,X2),X1)
            | ~ r2_hidden(sK0(X0,X1,X2),X0)
            | ~ r2_hidden(sK0(X0,X1,X2),X2) )
          & ( ( r2_hidden(sK0(X0,X1,X2),X1)
              & r2_hidden(sK0(X0,X1,X2),X0) )
            | r2_hidden(sK0(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f23,f24])).

fof(f53,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f82,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k3_xboole_0(X0,X1))
      | ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f53])).

fof(f7,axiom,(
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

fof(f17,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k10_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ? [X4] :
                  ( r2_hidden(X4,X1)
                  & r2_hidden(k4_tarski(X3,X4),X0) ) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f31,plain,(
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
    inference(nnf_transformation,[],[f17])).

fof(f32,plain,(
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
    inference(rectify,[],[f31])).

fof(f35,plain,(
    ! [X6,X1,X0] :
      ( ? [X8] :
          ( r2_hidden(X8,X1)
          & r2_hidden(k4_tarski(X6,X8),X0) )
     => ( r2_hidden(sK5(X0,X1,X6),X1)
        & r2_hidden(k4_tarski(X6,sK5(X0,X1,X6)),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X5] :
          ( r2_hidden(X5,X1)
          & r2_hidden(k4_tarski(X3,X5),X0) )
     => ( r2_hidden(sK4(X0,X1,X2),X1)
        & r2_hidden(k4_tarski(X3,sK4(X0,X1,X2)),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,(
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
              | ~ r2_hidden(k4_tarski(sK3(X0,X1,X2),X4),X0) )
          | ~ r2_hidden(sK3(X0,X1,X2),X2) )
        & ( ? [X5] :
              ( r2_hidden(X5,X1)
              & r2_hidden(k4_tarski(sK3(X0,X1,X2),X5),X0) )
          | r2_hidden(sK3(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k10_relat_1(X0,X1) = X2
            | ( ( ! [X4] :
                    ( ~ r2_hidden(X4,X1)
                    | ~ r2_hidden(k4_tarski(sK3(X0,X1,X2),X4),X0) )
                | ~ r2_hidden(sK3(X0,X1,X2),X2) )
              & ( ( r2_hidden(sK4(X0,X1,X2),X1)
                  & r2_hidden(k4_tarski(sK3(X0,X1,X2),sK4(X0,X1,X2)),X0) )
                | r2_hidden(sK3(X0,X1,X2),X2) ) ) )
          & ( ! [X6] :
                ( ( r2_hidden(X6,X2)
                  | ! [X7] :
                      ( ~ r2_hidden(X7,X1)
                      | ~ r2_hidden(k4_tarski(X6,X7),X0) ) )
                & ( ( r2_hidden(sK5(X0,X1,X6),X1)
                    & r2_hidden(k4_tarski(X6,sK5(X0,X1,X6)),X0) )
                  | ~ r2_hidden(X6,X2) ) )
            | k10_relat_1(X0,X1) != X2 ) )
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f32,f35,f34,f33])).

fof(f66,plain,(
    ! [X6,X2,X0,X7,X1] :
      ( r2_hidden(X6,X2)
      | ~ r2_hidden(X7,X1)
      | ~ r2_hidden(k4_tarski(X6,X7),X0)
      | k10_relat_1(X0,X1) != X2
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f85,plain,(
    ! [X6,X0,X7,X1] :
      ( r2_hidden(X6,k10_relat_1(X0,X1))
      | ~ r2_hidden(X7,X1)
      | ~ r2_hidden(k4_tarski(X6,X7),X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f66])).

fof(f11,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( k1_xboole_0 = k10_relat_1(X1,X0)
      <=> r1_xboole_0(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f12,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => ( k1_xboole_0 = k10_relat_1(X1,X0)
        <=> r1_xboole_0(k2_relat_1(X1),X0) ) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f20,plain,(
    ? [X0,X1] :
      ( ( k1_xboole_0 = k10_relat_1(X1,X0)
      <~> r1_xboole_0(k2_relat_1(X1),X0) )
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f47,plain,(
    ? [X0,X1] :
      ( ( ~ r1_xboole_0(k2_relat_1(X1),X0)
        | k1_xboole_0 != k10_relat_1(X1,X0) )
      & ( r1_xboole_0(k2_relat_1(X1),X0)
        | k1_xboole_0 = k10_relat_1(X1,X0) )
      & v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f20])).

fof(f48,plain,(
    ? [X0,X1] :
      ( ( ~ r1_xboole_0(k2_relat_1(X1),X0)
        | k1_xboole_0 != k10_relat_1(X1,X0) )
      & ( r1_xboole_0(k2_relat_1(X1),X0)
        | k1_xboole_0 = k10_relat_1(X1,X0) )
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f47])).

fof(f49,plain,
    ( ? [X0,X1] :
        ( ( ~ r1_xboole_0(k2_relat_1(X1),X0)
          | k1_xboole_0 != k10_relat_1(X1,X0) )
        & ( r1_xboole_0(k2_relat_1(X1),X0)
          | k1_xboole_0 = k10_relat_1(X1,X0) )
        & v1_relat_1(X1) )
   => ( ( ~ r1_xboole_0(k2_relat_1(sK11),sK10)
        | k1_xboole_0 != k10_relat_1(sK11,sK10) )
      & ( r1_xboole_0(k2_relat_1(sK11),sK10)
        | k1_xboole_0 = k10_relat_1(sK11,sK10) )
      & v1_relat_1(sK11) ) ),
    introduced(choice_axiom,[])).

fof(f50,plain,
    ( ( ~ r1_xboole_0(k2_relat_1(sK11),sK10)
      | k1_xboole_0 != k10_relat_1(sK11,sK10) )
    & ( r1_xboole_0(k2_relat_1(sK11),sK10)
      | k1_xboole_0 = k10_relat_1(sK11,sK10) )
    & v1_relat_1(sK11) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK10,sK11])],[f48,f49])).

fof(f80,plain,
    ( r1_xboole_0(k2_relat_1(sK11),sK10)
    | k1_xboole_0 = k10_relat_1(sK11,sK10) ),
    inference(cnf_transformation,[],[f50])).

fof(f81,plain,
    ( ~ r1_xboole_0(k2_relat_1(sK11),sK10)
    | k1_xboole_0 != k10_relat_1(sK11,sK10) ),
    inference(cnf_transformation,[],[f50])).

fof(f4,axiom,(
    ! [X0] :
      ~ ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f4])).

fof(f29,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK2(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,(
    ! [X0] :
      ( r2_hidden(sK2(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f15,f29])).

fof(f61,plain,(
    ! [X0] :
      ( r2_hidden(sK2(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f30])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(X0,k10_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X0,X3),X2)
            & r2_hidden(X3,k2_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k10_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X0,X3),X2)
            & r2_hidden(X3,k2_relat_1(X2)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f43,plain,(
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
    inference(nnf_transformation,[],[f18])).

fof(f44,plain,(
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
    inference(rectify,[],[f43])).

fof(f45,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( r2_hidden(X4,X1)
          & r2_hidden(k4_tarski(X0,X4),X2)
          & r2_hidden(X4,k2_relat_1(X2)) )
     => ( r2_hidden(sK9(X0,X1,X2),X1)
        & r2_hidden(k4_tarski(X0,sK9(X0,X1,X2)),X2)
        & r2_hidden(sK9(X0,X1,X2),k2_relat_1(X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f46,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k10_relat_1(X2,X1))
          | ! [X3] :
              ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(k4_tarski(X0,X3),X2)
              | ~ r2_hidden(X3,k2_relat_1(X2)) ) )
        & ( ( r2_hidden(sK9(X0,X1,X2),X1)
            & r2_hidden(k4_tarski(X0,sK9(X0,X1,X2)),X2)
            & r2_hidden(sK9(X0,X1,X2),k2_relat_1(X2)) )
          | ~ r2_hidden(X0,k10_relat_1(X2,X1)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK9])],[f44,f45])).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK9(X0,X1,X2),X1)
      | ~ r2_hidden(X0,k10_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f74,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK9(X0,X1,X2),k2_relat_1(X2))
      | ~ r2_hidden(X0,k10_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k3_xboole_0(X0,X1) != k1_xboole_0 )
      & ( k3_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f57,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f6,axiom,(
    ! [X0,X1] :
      ~ ( r2_hidden(X0,X1)
        & r1_xboole_0(k1_tarski(X0),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ r1_xboole_0(k1_tarski(X0),X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f63,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ r1_xboole_0(k1_tarski(X0),X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f5,axiom,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f62,plain,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f5])).

fof(f79,plain,(
    v1_relat_1(sK11) ),
    inference(cnf_transformation,[],[f50])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k10_relat_1(X1,X0) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1] :
      ( k10_relat_1(X1,X0) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X0))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f78,plain,(
    ! [X0,X1] :
      ( k10_relat_1(X1,X0) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X0))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f51,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f84,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,k3_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f51])).

fof(f59,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK1(X0,X1),k3_xboole_0(X0,X1))
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( k2_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X3,X2),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
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
    inference(nnf_transformation,[],[f8])).

fof(f38,plain,(
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
    inference(rectify,[],[f37])).

fof(f41,plain,(
    ! [X5,X0] :
      ( ? [X7] : r2_hidden(k4_tarski(X7,X5),X0)
     => r2_hidden(k4_tarski(sK8(X0,X5),X5),X0) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] : r2_hidden(k4_tarski(X4,X2),X0)
     => r2_hidden(k4_tarski(sK7(X0,X1),X2),X0) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,X2),X0)
            | ~ r2_hidden(X2,X1) )
          & ( ? [X4] : r2_hidden(k4_tarski(X4,X2),X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,sK6(X0,X1)),X0)
          | ~ r2_hidden(sK6(X0,X1),X1) )
        & ( ? [X4] : r2_hidden(k4_tarski(X4,sK6(X0,X1)),X0)
          | r2_hidden(sK6(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ( k2_relat_1(X0) = X1
        | ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,sK6(X0,X1)),X0)
            | ~ r2_hidden(sK6(X0,X1),X1) )
          & ( r2_hidden(k4_tarski(sK7(X0,X1),sK6(X0,X1)),X0)
            | r2_hidden(sK6(X0,X1),X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] : ~ r2_hidden(k4_tarski(X6,X5),X0) )
            & ( r2_hidden(k4_tarski(sK8(X0,X5),X5),X0)
              | ~ r2_hidden(X5,X1) ) )
        | k2_relat_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7,sK8])],[f38,f41,f40,f39])).

fof(f70,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(k4_tarski(sK8(X0,X5),X5),X0)
      | ~ r2_hidden(X5,X1)
      | k2_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f42])).

fof(f89,plain,(
    ! [X0,X5] :
      ( r2_hidden(k4_tarski(sK8(X0,X5),X5),X0)
      | ~ r2_hidden(X5,k2_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f70])).

cnf(c_8,plain,
    ( ~ r1_xboole_0(X0,X1)
    | ~ r2_hidden(X2,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_75034,plain,
    ( ~ r1_xboole_0(k10_relat_1(sK11,k3_xboole_0(k2_relat_1(sK11),sK10)),X0)
    | ~ r2_hidden(sK8(sK11,sK1(k2_relat_1(sK11),sK10)),k3_xboole_0(k10_relat_1(sK11,k3_xboole_0(k2_relat_1(sK11),sK10)),X0)) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_75036,plain,
    ( ~ r1_xboole_0(k10_relat_1(sK11,k3_xboole_0(k2_relat_1(sK11),sK10)),k1_xboole_0)
    | ~ r2_hidden(sK8(sK11,sK1(k2_relat_1(sK11),sK10)),k3_xboole_0(k10_relat_1(sK11,k3_xboole_0(k2_relat_1(sK11),sK10)),k1_xboole_0)) ),
    inference(instantiation,[status(thm)],[c_75034])).

cnf(c_574,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_51233,plain,
    ( sK8(sK11,sK1(k2_relat_1(sK11),sK10)) = sK8(sK11,sK1(k2_relat_1(sK11),sK10)) ),
    inference(instantiation,[status(thm)],[c_574])).

cnf(c_577,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_18550,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(sK8(sK11,sK1(k2_relat_1(sK11),sK10)),k10_relat_1(sK11,k3_xboole_0(k2_relat_1(sK11),sK10)))
    | X0 != sK8(sK11,sK1(k2_relat_1(sK11),sK10))
    | X1 != k10_relat_1(sK11,k3_xboole_0(k2_relat_1(sK11),sK10)) ),
    inference(instantiation,[status(thm)],[c_577])).

cnf(c_51232,plain,
    ( r2_hidden(sK8(sK11,sK1(k2_relat_1(sK11),sK10)),X0)
    | ~ r2_hidden(sK8(sK11,sK1(k2_relat_1(sK11),sK10)),k10_relat_1(sK11,k3_xboole_0(k2_relat_1(sK11),sK10)))
    | X0 != k10_relat_1(sK11,k3_xboole_0(k2_relat_1(sK11),sK10))
    | sK8(sK11,sK1(k2_relat_1(sK11),sK10)) != sK8(sK11,sK1(k2_relat_1(sK11),sK10)) ),
    inference(instantiation,[status(thm)],[c_18550])).

cnf(c_51235,plain,
    ( ~ r2_hidden(sK8(sK11,sK1(k2_relat_1(sK11),sK10)),k10_relat_1(sK11,k3_xboole_0(k2_relat_1(sK11),sK10)))
    | r2_hidden(sK8(sK11,sK1(k2_relat_1(sK11),sK10)),k1_xboole_0)
    | sK8(sK11,sK1(k2_relat_1(sK11),sK10)) != sK8(sK11,sK1(k2_relat_1(sK11),sK10))
    | k1_xboole_0 != k10_relat_1(sK11,k3_xboole_0(k2_relat_1(sK11),sK10)) ),
    inference(instantiation,[status(thm)],[c_51232])).

cnf(c_3,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X0,X2)
    | r2_hidden(X0,k3_xboole_0(X2,X1)) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_18558,plain,
    ( ~ r2_hidden(sK8(sK11,sK1(k2_relat_1(sK11),sK10)),X0)
    | ~ r2_hidden(sK8(sK11,sK1(k2_relat_1(sK11),sK10)),k10_relat_1(sK11,k3_xboole_0(k2_relat_1(sK11),sK10)))
    | r2_hidden(sK8(sK11,sK1(k2_relat_1(sK11),sK10)),k3_xboole_0(k10_relat_1(sK11,k3_xboole_0(k2_relat_1(sK11),sK10)),X0)) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_18560,plain,
    ( ~ r2_hidden(sK8(sK11,sK1(k2_relat_1(sK11),sK10)),k10_relat_1(sK11,k3_xboole_0(k2_relat_1(sK11),sK10)))
    | r2_hidden(sK8(sK11,sK1(k2_relat_1(sK11),sK10)),k3_xboole_0(k10_relat_1(sK11,k3_xboole_0(k2_relat_1(sK11),sK10)),k1_xboole_0))
    | ~ r2_hidden(sK8(sK11,sK1(k2_relat_1(sK11),sK10)),k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_18558])).

cnf(c_16,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,k10_relat_1(X3,X1))
    | ~ r2_hidden(k4_tarski(X2,X0),X3)
    | ~ v1_relat_1(X3) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_6159,plain,
    ( r2_hidden(sK8(sK11,sK1(k2_relat_1(sK11),sK10)),k10_relat_1(sK11,X0))
    | ~ r2_hidden(k4_tarski(sK8(sK11,sK1(k2_relat_1(sK11),sK10)),sK1(k2_relat_1(sK11),sK10)),sK11)
    | ~ r2_hidden(sK1(k2_relat_1(sK11),sK10),X0)
    | ~ v1_relat_1(sK11) ),
    inference(instantiation,[status(thm)],[c_16])).

cnf(c_17551,plain,
    ( r2_hidden(sK8(sK11,sK1(k2_relat_1(sK11),sK10)),k10_relat_1(sK11,k3_xboole_0(k2_relat_1(sK11),sK10)))
    | ~ r2_hidden(k4_tarski(sK8(sK11,sK1(k2_relat_1(sK11),sK10)),sK1(k2_relat_1(sK11),sK10)),sK11)
    | ~ r2_hidden(sK1(k2_relat_1(sK11),sK10),k3_xboole_0(k2_relat_1(sK11),sK10))
    | ~ v1_relat_1(sK11) ),
    inference(instantiation,[status(thm)],[c_6159])).

cnf(c_29,negated_conjecture,
    ( r1_xboole_0(k2_relat_1(sK11),sK10)
    | k1_xboole_0 = k10_relat_1(sK11,sK10) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_3654,plain,
    ( r1_xboole_0(k2_relat_1(sK11),sK10)
    | ~ r2_hidden(X0,k10_relat_1(sK11,sK10))
    | r2_hidden(X1,k1_xboole_0)
    | X1 != X0 ),
    inference(resolution,[status(thm)],[c_577,c_29])).

cnf(c_28,negated_conjecture,
    ( ~ r1_xboole_0(k2_relat_1(sK11),sK10)
    | k1_xboole_0 != k10_relat_1(sK11,sK10) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_591,plain,
    ( k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_574])).

cnf(c_575,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_1629,plain,
    ( k10_relat_1(sK11,sK10) != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = k10_relat_1(sK11,sK10) ),
    inference(instantiation,[status(thm)],[c_575])).

cnf(c_1630,plain,
    ( k10_relat_1(sK11,sK10) != k1_xboole_0
    | k1_xboole_0 = k10_relat_1(sK11,sK10)
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1629])).

cnf(c_10,plain,
    ( r2_hidden(sK2(X0),X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f61])).

cnf(c_1232,plain,
    ( k1_xboole_0 = X0
    | r2_hidden(sK2(X0),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_24,plain,
    ( ~ r2_hidden(X0,k10_relat_1(X1,X2))
    | r2_hidden(sK9(X0,X2,X1),X2)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_1219,plain,
    ( r2_hidden(X0,k10_relat_1(X1,X2)) != iProver_top
    | r2_hidden(sK9(X0,X2,X1),X2) = iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_26,plain,
    ( ~ r2_hidden(X0,k10_relat_1(X1,X2))
    | r2_hidden(sK9(X0,X2,X1),k2_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_1217,plain,
    ( r2_hidden(X0,k10_relat_1(X1,X2)) != iProver_top
    | r2_hidden(sK9(X0,X2,X1),k2_relat_1(X1)) = iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_1214,plain,
    ( k1_xboole_0 = k10_relat_1(sK11,sK10)
    | r1_xboole_0(k2_relat_1(sK11),sK10) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_7,plain,
    ( ~ r1_xboole_0(X0,X1)
    | k3_xboole_0(X0,X1) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f57])).

cnf(c_1235,plain,
    ( k3_xboole_0(X0,X1) = k1_xboole_0
    | r1_xboole_0(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_1542,plain,
    ( k10_relat_1(sK11,sK10) = k1_xboole_0
    | k3_xboole_0(k2_relat_1(sK11),sK10) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1214,c_1235])).

cnf(c_1239,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,X2) != iProver_top
    | r2_hidden(X0,k3_xboole_0(X2,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_2440,plain,
    ( k10_relat_1(sK11,sK10) = k1_xboole_0
    | r2_hidden(X0,k2_relat_1(sK11)) != iProver_top
    | r2_hidden(X0,sK10) != iProver_top
    | r2_hidden(X0,k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1542,c_1239])).

cnf(c_12,plain,
    ( ~ r1_xboole_0(k1_tarski(X0),X1)
    | ~ r2_hidden(X0,X1) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_11,plain,
    ( r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_1524,plain,
    ( ~ r2_hidden(X0,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_12,c_11])).

cnf(c_1525,plain,
    ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1524])).

cnf(c_2711,plain,
    ( r2_hidden(X0,sK10) != iProver_top
    | r2_hidden(X0,k2_relat_1(sK11)) != iProver_top
    | k10_relat_1(sK11,sK10) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2440,c_1525])).

cnf(c_2712,plain,
    ( k10_relat_1(sK11,sK10) = k1_xboole_0
    | r2_hidden(X0,k2_relat_1(sK11)) != iProver_top
    | r2_hidden(X0,sK10) != iProver_top ),
    inference(renaming,[status(thm)],[c_2711])).

cnf(c_2723,plain,
    ( k10_relat_1(sK11,sK10) = k1_xboole_0
    | r2_hidden(X0,k10_relat_1(sK11,X1)) != iProver_top
    | r2_hidden(sK9(X0,X1,sK11),sK10) != iProver_top
    | v1_relat_1(sK11) != iProver_top ),
    inference(superposition,[status(thm)],[c_1217,c_2712])).

cnf(c_30,negated_conjecture,
    ( v1_relat_1(sK11) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_31,plain,
    ( v1_relat_1(sK11) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_2911,plain,
    ( r2_hidden(sK9(X0,X1,sK11),sK10) != iProver_top
    | r2_hidden(X0,k10_relat_1(sK11,X1)) != iProver_top
    | k10_relat_1(sK11,sK10) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2723,c_31])).

cnf(c_2912,plain,
    ( k10_relat_1(sK11,sK10) = k1_xboole_0
    | r2_hidden(X0,k10_relat_1(sK11,X1)) != iProver_top
    | r2_hidden(sK9(X0,X1,sK11),sK10) != iProver_top ),
    inference(renaming,[status(thm)],[c_2911])).

cnf(c_2920,plain,
    ( k10_relat_1(sK11,sK10) = k1_xboole_0
    | r2_hidden(X0,k10_relat_1(sK11,sK10)) != iProver_top
    | v1_relat_1(sK11) != iProver_top ),
    inference(superposition,[status(thm)],[c_1219,c_2912])).

cnf(c_3123,plain,
    ( r2_hidden(X0,k10_relat_1(sK11,sK10)) != iProver_top
    | k10_relat_1(sK11,sK10) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2920,c_31])).

cnf(c_3124,plain,
    ( k10_relat_1(sK11,sK10) = k1_xboole_0
    | r2_hidden(X0,k10_relat_1(sK11,sK10)) != iProver_top ),
    inference(renaming,[status(thm)],[c_3123])).

cnf(c_3131,plain,
    ( k10_relat_1(sK11,sK10) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1232,c_3124])).

cnf(c_3865,plain,
    ( ~ r2_hidden(X0,k10_relat_1(sK11,sK10))
    | r2_hidden(X1,k1_xboole_0)
    | X1 != X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3654,c_28,c_591,c_1630,c_3131])).

cnf(c_3874,plain,
    ( ~ r2_hidden(X0,k10_relat_1(sK11,sK10))
    | X1 != X0 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_3865,c_1524])).

cnf(c_3887,plain,
    ( X0 != sK2(k10_relat_1(sK11,sK10))
    | k1_xboole_0 = k10_relat_1(sK11,sK10) ),
    inference(resolution,[status(thm)],[c_3874,c_10])).

cnf(c_3917,plain,
    ( k1_xboole_0 = k10_relat_1(sK11,sK10) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3887,c_591,c_1630,c_3131])).

cnf(c_4080,plain,
    ( ~ r1_xboole_0(k2_relat_1(sK11),sK10) ),
    inference(backward_subsumption_resolution,[status(thm)],[c_3917,c_28])).

cnf(c_2501,plain,
    ( r1_xboole_0(k2_relat_1(sK11),sK10)
    | X0 != k10_relat_1(sK11,sK10)
    | k1_xboole_0 = X0 ),
    inference(resolution,[status(thm)],[c_575,c_29])).

cnf(c_27,plain,
    ( ~ v1_relat_1(X0)
    | k10_relat_1(X0,k3_xboole_0(k2_relat_1(X0),X1)) = k10_relat_1(X0,X1) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_2802,plain,
    ( r1_xboole_0(k2_relat_1(sK11),sK10)
    | ~ v1_relat_1(sK11)
    | k1_xboole_0 = k10_relat_1(sK11,k3_xboole_0(k2_relat_1(sK11),sK10)) ),
    inference(resolution,[status(thm)],[c_2501,c_27])).

cnf(c_2928,plain,
    ( r1_xboole_0(k2_relat_1(sK11),sK10)
    | k1_xboole_0 = k10_relat_1(sK11,k3_xboole_0(k2_relat_1(sK11),sK10)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2802,c_30])).

cnf(c_3667,plain,
    ( r1_xboole_0(k2_relat_1(sK11),sK10)
    | ~ r2_hidden(X0,k10_relat_1(sK11,k3_xboole_0(k2_relat_1(sK11),sK10)))
    | r2_hidden(X1,k1_xboole_0)
    | X1 != X0 ),
    inference(resolution,[status(thm)],[c_577,c_2928])).

cnf(c_4096,plain,
    ( ~ r2_hidden(X0,k10_relat_1(sK11,k3_xboole_0(k2_relat_1(sK11),sK10)))
    | r2_hidden(X1,k1_xboole_0)
    | X1 != X0 ),
    inference(backward_subsumption_resolution,[status(thm)],[c_4080,c_3667])).

cnf(c_4314,plain,
    ( ~ r2_hidden(X0,k10_relat_1(sK11,k3_xboole_0(k2_relat_1(sK11),sK10)))
    | X1 != X0 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_4096,c_1524])).

cnf(c_5,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k3_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_9,plain,
    ( r1_xboole_0(X0,X1)
    | r2_hidden(sK1(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_1706,plain,
    ( r1_xboole_0(X0,X1)
    | r2_hidden(sK1(X0,X1),X0) ),
    inference(resolution,[status(thm)],[c_5,c_9])).

cnf(c_4531,plain,
    ( r1_xboole_0(k10_relat_1(sK11,k3_xboole_0(k2_relat_1(sK11),sK10)),X0)
    | X1 != sK1(k10_relat_1(sK11,k3_xboole_0(k2_relat_1(sK11),sK10)),X0) ),
    inference(resolution,[status(thm)],[c_4314,c_1706])).

cnf(c_9031,plain,
    ( r1_xboole_0(k10_relat_1(sK11,k3_xboole_0(k2_relat_1(sK11),sK10)),X0) ),
    inference(resolution,[status(thm)],[c_4531,c_574])).

cnf(c_9033,plain,
    ( r1_xboole_0(k10_relat_1(sK11,k3_xboole_0(k2_relat_1(sK11),sK10)),k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_9031])).

cnf(c_22,plain,
    ( ~ r2_hidden(X0,k2_relat_1(X1))
    | r2_hidden(k4_tarski(sK8(X1,X0),X0),X1) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_2175,plain,
    ( r2_hidden(k4_tarski(sK8(sK11,sK1(k2_relat_1(sK11),sK10)),sK1(k2_relat_1(sK11),sK10)),sK11)
    | ~ r2_hidden(sK1(k2_relat_1(sK11),sK10),k2_relat_1(sK11)) ),
    inference(instantiation,[status(thm)],[c_22])).

cnf(c_1902,plain,
    ( ~ r2_hidden(sK1(k2_relat_1(sK11),sK10),k3_xboole_0(k2_relat_1(sK11),sK10))
    | r2_hidden(sK1(k2_relat_1(sK11),sK10),k2_relat_1(sK11)) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_1505,plain,
    ( r1_xboole_0(k2_relat_1(sK11),sK10)
    | r2_hidden(sK1(k2_relat_1(sK11),sK10),k3_xboole_0(k2_relat_1(sK11),sK10)) ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_75036,c_51233,c_51235,c_18560,c_17551,c_9033,c_3131,c_2802,c_2175,c_1902,c_1630,c_1505,c_591,c_28,c_30])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n007.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 10:19:21 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.34  % Running in FOF mode
% 23.48/3.49  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 23.48/3.49  
% 23.48/3.49  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 23.48/3.49  
% 23.48/3.49  ------  iProver source info
% 23.48/3.49  
% 23.48/3.49  git: date: 2020-06-30 10:37:57 +0100
% 23.48/3.49  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 23.48/3.49  git: non_committed_changes: false
% 23.48/3.49  git: last_make_outside_of_git: false
% 23.48/3.49  
% 23.48/3.49  ------ 
% 23.48/3.49  ------ Parsing...
% 23.48/3.49  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 23.48/3.49  
% 23.48/3.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 1 0s  sf_e 
% 23.48/3.49  
% 23.48/3.49  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 23.48/3.49  
% 23.48/3.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 23.48/3.49  ------ Proving...
% 23.48/3.49  ------ Problem Properties 
% 23.48/3.49  
% 23.48/3.49  
% 23.48/3.49  clauses                                 30
% 23.48/3.49  conjectures                             3
% 23.48/3.49  EPR                                     2
% 23.48/3.49  Horn                                    22
% 23.48/3.49  unary                                   2
% 23.48/3.49  binary                                  13
% 23.48/3.49  lits                                    79
% 23.48/3.49  lits eq                                 14
% 23.48/3.49  fd_pure                                 0
% 23.48/3.49  fd_pseudo                               0
% 23.48/3.49  fd_cond                                 1
% 23.48/3.49  fd_pseudo_cond                          8
% 23.48/3.49  AC symbols                              0
% 23.48/3.49  
% 23.48/3.49  ------ Input Options Time Limit: Unbounded
% 23.48/3.49  
% 23.48/3.49  
% 23.48/3.49  ------ 
% 23.48/3.49  Current options:
% 23.48/3.49  ------ 
% 23.48/3.49  
% 23.48/3.49  
% 23.48/3.49  
% 23.48/3.49  
% 23.48/3.49  ------ Proving...
% 23.48/3.49  
% 23.48/3.49  
% 23.48/3.49  % SZS status Theorem for theBenchmark.p
% 23.48/3.49  
% 23.48/3.49  % SZS output start CNFRefutation for theBenchmark.p
% 23.48/3.49  
% 23.48/3.49  fof(f3,axiom,(
% 23.48/3.49    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 23.48/3.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.48/3.49  
% 23.48/3.49  fof(f13,plain,(
% 23.48/3.49    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X3] : ~r2_hidden(X3,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 23.48/3.49    inference(rectify,[],[f3])).
% 23.48/3.49  
% 23.48/3.49  fof(f14,plain,(
% 23.48/3.49    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 23.48/3.49    inference(ennf_transformation,[],[f13])).
% 23.48/3.49  
% 23.48/3.49  fof(f27,plain,(
% 23.48/3.49    ! [X1,X0] : (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) => r2_hidden(sK1(X0,X1),k3_xboole_0(X0,X1)))),
% 23.48/3.49    introduced(choice_axiom,[])).
% 23.48/3.49  
% 23.48/3.49  fof(f28,plain,(
% 23.48/3.49    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (r2_hidden(sK1(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 23.48/3.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f14,f27])).
% 23.48/3.49  
% 23.48/3.49  fof(f60,plain,(
% 23.48/3.49    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,k3_xboole_0(X0,X1))) )),
% 23.48/3.49    inference(cnf_transformation,[],[f28])).
% 23.48/3.49  
% 23.48/3.49  fof(f1,axiom,(
% 23.48/3.49    ! [X0,X1,X2] : (k3_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 23.48/3.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.48/3.49  
% 23.48/3.49  fof(f21,plain,(
% 23.48/3.49    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k3_xboole_0(X0,X1) != X2))),
% 23.48/3.49    inference(nnf_transformation,[],[f1])).
% 23.48/3.49  
% 23.48/3.49  fof(f22,plain,(
% 23.48/3.49    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ~r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k3_xboole_0(X0,X1) != X2))),
% 23.48/3.49    inference(flattening,[],[f21])).
% 23.48/3.49  
% 23.48/3.49  fof(f23,plain,(
% 23.48/3.49    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k3_xboole_0(X0,X1) != X2))),
% 23.48/3.49    inference(rectify,[],[f22])).
% 23.48/3.49  
% 23.48/3.49  fof(f24,plain,(
% 23.48/3.49    ! [X2,X1,X0] : (? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((~r2_hidden(sK0(X0,X1,X2),X1) | ~r2_hidden(sK0(X0,X1,X2),X0) | ~r2_hidden(sK0(X0,X1,X2),X2)) & ((r2_hidden(sK0(X0,X1,X2),X1) & r2_hidden(sK0(X0,X1,X2),X0)) | r2_hidden(sK0(X0,X1,X2),X2))))),
% 23.48/3.49    introduced(choice_axiom,[])).
% 23.48/3.49  
% 23.48/3.49  fof(f25,plain,(
% 23.48/3.49    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ((~r2_hidden(sK0(X0,X1,X2),X1) | ~r2_hidden(sK0(X0,X1,X2),X0) | ~r2_hidden(sK0(X0,X1,X2),X2)) & ((r2_hidden(sK0(X0,X1,X2),X1) & r2_hidden(sK0(X0,X1,X2),X0)) | r2_hidden(sK0(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k3_xboole_0(X0,X1) != X2))),
% 23.48/3.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f23,f24])).
% 23.48/3.49  
% 23.48/3.49  fof(f53,plain,(
% 23.48/3.49    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0) | k3_xboole_0(X0,X1) != X2) )),
% 23.48/3.49    inference(cnf_transformation,[],[f25])).
% 23.48/3.49  
% 23.48/3.49  fof(f82,plain,(
% 23.48/3.49    ( ! [X4,X0,X1] : (r2_hidden(X4,k3_xboole_0(X0,X1)) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) )),
% 23.48/3.49    inference(equality_resolution,[],[f53])).
% 23.48/3.49  
% 23.48/3.49  fof(f7,axiom,(
% 23.48/3.49    ! [X0] : (v1_relat_1(X0) => ! [X1,X2] : (k10_relat_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X3,X4),X0)))))),
% 23.48/3.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.48/3.49  
% 23.48/3.49  fof(f17,plain,(
% 23.48/3.49    ! [X0] : (! [X1,X2] : (k10_relat_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X3,X4),X0)))) | ~v1_relat_1(X0))),
% 23.48/3.49    inference(ennf_transformation,[],[f7])).
% 23.48/3.49  
% 23.48/3.49  fof(f31,plain,(
% 23.48/3.49    ! [X0] : (! [X1,X2] : ((k10_relat_1(X0,X1) = X2 | ? [X3] : ((! [X4] : (~r2_hidden(X4,X1) | ~r2_hidden(k4_tarski(X3,X4),X0)) | ~r2_hidden(X3,X2)) & (? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X3,X4),X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ! [X4] : (~r2_hidden(X4,X1) | ~r2_hidden(k4_tarski(X3,X4),X0))) & (? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X3,X4),X0)) | ~r2_hidden(X3,X2))) | k10_relat_1(X0,X1) != X2)) | ~v1_relat_1(X0))),
% 23.48/3.49    inference(nnf_transformation,[],[f17])).
% 23.48/3.49  
% 23.48/3.49  fof(f32,plain,(
% 23.48/3.49    ! [X0] : (! [X1,X2] : ((k10_relat_1(X0,X1) = X2 | ? [X3] : ((! [X4] : (~r2_hidden(X4,X1) | ~r2_hidden(k4_tarski(X3,X4),X0)) | ~r2_hidden(X3,X2)) & (? [X5] : (r2_hidden(X5,X1) & r2_hidden(k4_tarski(X3,X5),X0)) | r2_hidden(X3,X2)))) & (! [X6] : ((r2_hidden(X6,X2) | ! [X7] : (~r2_hidden(X7,X1) | ~r2_hidden(k4_tarski(X6,X7),X0))) & (? [X8] : (r2_hidden(X8,X1) & r2_hidden(k4_tarski(X6,X8),X0)) | ~r2_hidden(X6,X2))) | k10_relat_1(X0,X1) != X2)) | ~v1_relat_1(X0))),
% 23.48/3.49    inference(rectify,[],[f31])).
% 23.48/3.49  
% 23.48/3.49  fof(f35,plain,(
% 23.48/3.49    ! [X6,X1,X0] : (? [X8] : (r2_hidden(X8,X1) & r2_hidden(k4_tarski(X6,X8),X0)) => (r2_hidden(sK5(X0,X1,X6),X1) & r2_hidden(k4_tarski(X6,sK5(X0,X1,X6)),X0)))),
% 23.48/3.49    introduced(choice_axiom,[])).
% 23.48/3.49  
% 23.48/3.49  fof(f34,plain,(
% 23.48/3.49    ( ! [X3] : (! [X2,X1,X0] : (? [X5] : (r2_hidden(X5,X1) & r2_hidden(k4_tarski(X3,X5),X0)) => (r2_hidden(sK4(X0,X1,X2),X1) & r2_hidden(k4_tarski(X3,sK4(X0,X1,X2)),X0)))) )),
% 23.48/3.49    introduced(choice_axiom,[])).
% 23.48/3.49  
% 23.48/3.49  fof(f33,plain,(
% 23.48/3.49    ! [X2,X1,X0] : (? [X3] : ((! [X4] : (~r2_hidden(X4,X1) | ~r2_hidden(k4_tarski(X3,X4),X0)) | ~r2_hidden(X3,X2)) & (? [X5] : (r2_hidden(X5,X1) & r2_hidden(k4_tarski(X3,X5),X0)) | r2_hidden(X3,X2))) => ((! [X4] : (~r2_hidden(X4,X1) | ~r2_hidden(k4_tarski(sK3(X0,X1,X2),X4),X0)) | ~r2_hidden(sK3(X0,X1,X2),X2)) & (? [X5] : (r2_hidden(X5,X1) & r2_hidden(k4_tarski(sK3(X0,X1,X2),X5),X0)) | r2_hidden(sK3(X0,X1,X2),X2))))),
% 23.48/3.49    introduced(choice_axiom,[])).
% 23.48/3.49  
% 23.48/3.49  fof(f36,plain,(
% 23.48/3.49    ! [X0] : (! [X1,X2] : ((k10_relat_1(X0,X1) = X2 | ((! [X4] : (~r2_hidden(X4,X1) | ~r2_hidden(k4_tarski(sK3(X0,X1,X2),X4),X0)) | ~r2_hidden(sK3(X0,X1,X2),X2)) & ((r2_hidden(sK4(X0,X1,X2),X1) & r2_hidden(k4_tarski(sK3(X0,X1,X2),sK4(X0,X1,X2)),X0)) | r2_hidden(sK3(X0,X1,X2),X2)))) & (! [X6] : ((r2_hidden(X6,X2) | ! [X7] : (~r2_hidden(X7,X1) | ~r2_hidden(k4_tarski(X6,X7),X0))) & ((r2_hidden(sK5(X0,X1,X6),X1) & r2_hidden(k4_tarski(X6,sK5(X0,X1,X6)),X0)) | ~r2_hidden(X6,X2))) | k10_relat_1(X0,X1) != X2)) | ~v1_relat_1(X0))),
% 23.48/3.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f32,f35,f34,f33])).
% 23.48/3.49  
% 23.48/3.49  fof(f66,plain,(
% 23.48/3.49    ( ! [X6,X2,X0,X7,X1] : (r2_hidden(X6,X2) | ~r2_hidden(X7,X1) | ~r2_hidden(k4_tarski(X6,X7),X0) | k10_relat_1(X0,X1) != X2 | ~v1_relat_1(X0)) )),
% 23.48/3.49    inference(cnf_transformation,[],[f36])).
% 23.48/3.49  
% 23.48/3.49  fof(f85,plain,(
% 23.48/3.49    ( ! [X6,X0,X7,X1] : (r2_hidden(X6,k10_relat_1(X0,X1)) | ~r2_hidden(X7,X1) | ~r2_hidden(k4_tarski(X6,X7),X0) | ~v1_relat_1(X0)) )),
% 23.48/3.49    inference(equality_resolution,[],[f66])).
% 23.48/3.49  
% 23.48/3.49  fof(f11,conjecture,(
% 23.48/3.49    ! [X0,X1] : (v1_relat_1(X1) => (k1_xboole_0 = k10_relat_1(X1,X0) <=> r1_xboole_0(k2_relat_1(X1),X0)))),
% 23.48/3.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.48/3.49  
% 23.48/3.49  fof(f12,negated_conjecture,(
% 23.48/3.49    ~! [X0,X1] : (v1_relat_1(X1) => (k1_xboole_0 = k10_relat_1(X1,X0) <=> r1_xboole_0(k2_relat_1(X1),X0)))),
% 23.48/3.49    inference(negated_conjecture,[],[f11])).
% 23.48/3.49  
% 23.48/3.49  fof(f20,plain,(
% 23.48/3.49    ? [X0,X1] : ((k1_xboole_0 = k10_relat_1(X1,X0) <~> r1_xboole_0(k2_relat_1(X1),X0)) & v1_relat_1(X1))),
% 23.48/3.49    inference(ennf_transformation,[],[f12])).
% 23.48/3.49  
% 23.48/3.49  fof(f47,plain,(
% 23.48/3.49    ? [X0,X1] : (((~r1_xboole_0(k2_relat_1(X1),X0) | k1_xboole_0 != k10_relat_1(X1,X0)) & (r1_xboole_0(k2_relat_1(X1),X0) | k1_xboole_0 = k10_relat_1(X1,X0))) & v1_relat_1(X1))),
% 23.48/3.49    inference(nnf_transformation,[],[f20])).
% 23.48/3.49  
% 23.48/3.49  fof(f48,plain,(
% 23.48/3.49    ? [X0,X1] : ((~r1_xboole_0(k2_relat_1(X1),X0) | k1_xboole_0 != k10_relat_1(X1,X0)) & (r1_xboole_0(k2_relat_1(X1),X0) | k1_xboole_0 = k10_relat_1(X1,X0)) & v1_relat_1(X1))),
% 23.48/3.49    inference(flattening,[],[f47])).
% 23.48/3.49  
% 23.48/3.49  fof(f49,plain,(
% 23.48/3.49    ? [X0,X1] : ((~r1_xboole_0(k2_relat_1(X1),X0) | k1_xboole_0 != k10_relat_1(X1,X0)) & (r1_xboole_0(k2_relat_1(X1),X0) | k1_xboole_0 = k10_relat_1(X1,X0)) & v1_relat_1(X1)) => ((~r1_xboole_0(k2_relat_1(sK11),sK10) | k1_xboole_0 != k10_relat_1(sK11,sK10)) & (r1_xboole_0(k2_relat_1(sK11),sK10) | k1_xboole_0 = k10_relat_1(sK11,sK10)) & v1_relat_1(sK11))),
% 23.48/3.49    introduced(choice_axiom,[])).
% 23.48/3.49  
% 23.48/3.49  fof(f50,plain,(
% 23.48/3.49    (~r1_xboole_0(k2_relat_1(sK11),sK10) | k1_xboole_0 != k10_relat_1(sK11,sK10)) & (r1_xboole_0(k2_relat_1(sK11),sK10) | k1_xboole_0 = k10_relat_1(sK11,sK10)) & v1_relat_1(sK11)),
% 23.48/3.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK10,sK11])],[f48,f49])).
% 23.48/3.49  
% 23.48/3.49  fof(f80,plain,(
% 23.48/3.49    r1_xboole_0(k2_relat_1(sK11),sK10) | k1_xboole_0 = k10_relat_1(sK11,sK10)),
% 23.48/3.49    inference(cnf_transformation,[],[f50])).
% 23.48/3.49  
% 23.48/3.49  fof(f81,plain,(
% 23.48/3.49    ~r1_xboole_0(k2_relat_1(sK11),sK10) | k1_xboole_0 != k10_relat_1(sK11,sK10)),
% 23.48/3.49    inference(cnf_transformation,[],[f50])).
% 23.48/3.49  
% 23.48/3.49  fof(f4,axiom,(
% 23.48/3.49    ! [X0] : ~(! [X1] : ~r2_hidden(X1,X0) & k1_xboole_0 != X0)),
% 23.48/3.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.48/3.49  
% 23.48/3.49  fof(f15,plain,(
% 23.48/3.49    ! [X0] : (? [X1] : r2_hidden(X1,X0) | k1_xboole_0 = X0)),
% 23.48/3.49    inference(ennf_transformation,[],[f4])).
% 23.48/3.49  
% 23.48/3.49  fof(f29,plain,(
% 23.48/3.49    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK2(X0),X0))),
% 23.48/3.49    introduced(choice_axiom,[])).
% 23.48/3.49  
% 23.48/3.49  fof(f30,plain,(
% 23.48/3.49    ! [X0] : (r2_hidden(sK2(X0),X0) | k1_xboole_0 = X0)),
% 23.48/3.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f15,f29])).
% 23.48/3.49  
% 23.48/3.49  fof(f61,plain,(
% 23.48/3.49    ( ! [X0] : (r2_hidden(sK2(X0),X0) | k1_xboole_0 = X0) )),
% 23.48/3.49    inference(cnf_transformation,[],[f30])).
% 23.48/3.49  
% 23.48/3.49  fof(f9,axiom,(
% 23.48/3.49    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(X0,k10_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X0,X3),X2) & r2_hidden(X3,k2_relat_1(X2)))))),
% 23.48/3.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.48/3.49  
% 23.48/3.49  fof(f18,plain,(
% 23.48/3.49    ! [X0,X1,X2] : ((r2_hidden(X0,k10_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X0,X3),X2) & r2_hidden(X3,k2_relat_1(X2)))) | ~v1_relat_1(X2))),
% 23.48/3.49    inference(ennf_transformation,[],[f9])).
% 23.48/3.49  
% 23.48/3.49  fof(f43,plain,(
% 23.48/3.49    ! [X0,X1,X2] : (((r2_hidden(X0,k10_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X0,X3),X2) | ~r2_hidden(X3,k2_relat_1(X2)))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X0,X3),X2) & r2_hidden(X3,k2_relat_1(X2))) | ~r2_hidden(X0,k10_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 23.48/3.49    inference(nnf_transformation,[],[f18])).
% 23.48/3.49  
% 23.48/3.49  fof(f44,plain,(
% 23.48/3.49    ! [X0,X1,X2] : (((r2_hidden(X0,k10_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X0,X3),X2) | ~r2_hidden(X3,k2_relat_1(X2)))) & (? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X0,X4),X2) & r2_hidden(X4,k2_relat_1(X2))) | ~r2_hidden(X0,k10_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 23.48/3.49    inference(rectify,[],[f43])).
% 23.48/3.49  
% 23.48/3.49  fof(f45,plain,(
% 23.48/3.49    ! [X2,X1,X0] : (? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X0,X4),X2) & r2_hidden(X4,k2_relat_1(X2))) => (r2_hidden(sK9(X0,X1,X2),X1) & r2_hidden(k4_tarski(X0,sK9(X0,X1,X2)),X2) & r2_hidden(sK9(X0,X1,X2),k2_relat_1(X2))))),
% 23.48/3.49    introduced(choice_axiom,[])).
% 23.48/3.49  
% 23.48/3.49  fof(f46,plain,(
% 23.48/3.49    ! [X0,X1,X2] : (((r2_hidden(X0,k10_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X0,X3),X2) | ~r2_hidden(X3,k2_relat_1(X2)))) & ((r2_hidden(sK9(X0,X1,X2),X1) & r2_hidden(k4_tarski(X0,sK9(X0,X1,X2)),X2) & r2_hidden(sK9(X0,X1,X2),k2_relat_1(X2))) | ~r2_hidden(X0,k10_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 23.48/3.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK9])],[f44,f45])).
% 23.48/3.49  
% 23.48/3.49  fof(f76,plain,(
% 23.48/3.49    ( ! [X2,X0,X1] : (r2_hidden(sK9(X0,X1,X2),X1) | ~r2_hidden(X0,k10_relat_1(X2,X1)) | ~v1_relat_1(X2)) )),
% 23.48/3.49    inference(cnf_transformation,[],[f46])).
% 23.48/3.49  
% 23.48/3.49  fof(f74,plain,(
% 23.48/3.49    ( ! [X2,X0,X1] : (r2_hidden(sK9(X0,X1,X2),k2_relat_1(X2)) | ~r2_hidden(X0,k10_relat_1(X2,X1)) | ~v1_relat_1(X2)) )),
% 23.48/3.49    inference(cnf_transformation,[],[f46])).
% 23.48/3.49  
% 23.48/3.49  fof(f2,axiom,(
% 23.48/3.49    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 23.48/3.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.48/3.49  
% 23.48/3.49  fof(f26,plain,(
% 23.48/3.49    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) & (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)))),
% 23.48/3.49    inference(nnf_transformation,[],[f2])).
% 23.48/3.49  
% 23.48/3.49  fof(f57,plain,(
% 23.48/3.49    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)) )),
% 23.48/3.49    inference(cnf_transformation,[],[f26])).
% 23.48/3.49  
% 23.48/3.49  fof(f6,axiom,(
% 23.48/3.49    ! [X0,X1] : ~(r2_hidden(X0,X1) & r1_xboole_0(k1_tarski(X0),X1))),
% 23.48/3.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.48/3.49  
% 23.48/3.49  fof(f16,plain,(
% 23.48/3.49    ! [X0,X1] : (~r2_hidden(X0,X1) | ~r1_xboole_0(k1_tarski(X0),X1))),
% 23.48/3.49    inference(ennf_transformation,[],[f6])).
% 23.48/3.49  
% 23.48/3.49  fof(f63,plain,(
% 23.48/3.49    ( ! [X0,X1] : (~r2_hidden(X0,X1) | ~r1_xboole_0(k1_tarski(X0),X1)) )),
% 23.48/3.49    inference(cnf_transformation,[],[f16])).
% 23.48/3.49  
% 23.48/3.49  fof(f5,axiom,(
% 23.48/3.49    ! [X0] : r1_xboole_0(X0,k1_xboole_0)),
% 23.48/3.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.48/3.49  
% 23.48/3.49  fof(f62,plain,(
% 23.48/3.49    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) )),
% 23.48/3.49    inference(cnf_transformation,[],[f5])).
% 23.48/3.49  
% 23.48/3.49  fof(f79,plain,(
% 23.48/3.49    v1_relat_1(sK11)),
% 23.48/3.49    inference(cnf_transformation,[],[f50])).
% 23.48/3.49  
% 23.48/3.49  fof(f10,axiom,(
% 23.48/3.49    ! [X0,X1] : (v1_relat_1(X1) => k10_relat_1(X1,X0) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X0)))),
% 23.48/3.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.48/3.49  
% 23.48/3.49  fof(f19,plain,(
% 23.48/3.49    ! [X0,X1] : (k10_relat_1(X1,X0) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 23.48/3.49    inference(ennf_transformation,[],[f10])).
% 23.48/3.49  
% 23.48/3.49  fof(f78,plain,(
% 23.48/3.49    ( ! [X0,X1] : (k10_relat_1(X1,X0) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X0)) | ~v1_relat_1(X1)) )),
% 23.48/3.49    inference(cnf_transformation,[],[f19])).
% 23.48/3.49  
% 23.48/3.49  fof(f51,plain,(
% 23.48/3.49    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,X2) | k3_xboole_0(X0,X1) != X2) )),
% 23.48/3.49    inference(cnf_transformation,[],[f25])).
% 23.48/3.49  
% 23.48/3.49  fof(f84,plain,(
% 23.48/3.49    ( ! [X4,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,k3_xboole_0(X0,X1))) )),
% 23.48/3.49    inference(equality_resolution,[],[f51])).
% 23.48/3.49  
% 23.48/3.49  fof(f59,plain,(
% 23.48/3.49    ( ! [X0,X1] : (r2_hidden(sK1(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)) )),
% 23.48/3.49    inference(cnf_transformation,[],[f28])).
% 23.48/3.49  
% 23.48/3.49  fof(f8,axiom,(
% 23.48/3.49    ! [X0,X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : r2_hidden(k4_tarski(X3,X2),X0)))),
% 23.48/3.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.48/3.49  
% 23.48/3.49  fof(f37,plain,(
% 23.48/3.49    ! [X0,X1] : ((k2_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1)) & (? [X3] : r2_hidden(k4_tarski(X3,X2),X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0)) & (? [X3] : r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1))) | k2_relat_1(X0) != X1))),
% 23.48/3.49    inference(nnf_transformation,[],[f8])).
% 23.48/3.49  
% 23.48/3.49  fof(f38,plain,(
% 23.48/3.49    ! [X0,X1] : ((k2_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X4,X2),X0) | r2_hidden(X2,X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X6,X5),X0)) & (? [X7] : r2_hidden(k4_tarski(X7,X5),X0) | ~r2_hidden(X5,X1))) | k2_relat_1(X0) != X1))),
% 23.48/3.49    inference(rectify,[],[f37])).
% 23.48/3.49  
% 23.48/3.49  fof(f41,plain,(
% 23.48/3.49    ! [X5,X0] : (? [X7] : r2_hidden(k4_tarski(X7,X5),X0) => r2_hidden(k4_tarski(sK8(X0,X5),X5),X0))),
% 23.48/3.49    introduced(choice_axiom,[])).
% 23.48/3.49  
% 23.48/3.49  fof(f40,plain,(
% 23.48/3.49    ( ! [X2] : (! [X1,X0] : (? [X4] : r2_hidden(k4_tarski(X4,X2),X0) => r2_hidden(k4_tarski(sK7(X0,X1),X2),X0))) )),
% 23.48/3.49    introduced(choice_axiom,[])).
% 23.48/3.49  
% 23.48/3.49  fof(f39,plain,(
% 23.48/3.49    ! [X1,X0] : (? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X4,X2),X0) | r2_hidden(X2,X1))) => ((! [X3] : ~r2_hidden(k4_tarski(X3,sK6(X0,X1)),X0) | ~r2_hidden(sK6(X0,X1),X1)) & (? [X4] : r2_hidden(k4_tarski(X4,sK6(X0,X1)),X0) | r2_hidden(sK6(X0,X1),X1))))),
% 23.48/3.49    introduced(choice_axiom,[])).
% 23.48/3.49  
% 23.48/3.49  fof(f42,plain,(
% 23.48/3.49    ! [X0,X1] : ((k2_relat_1(X0) = X1 | ((! [X3] : ~r2_hidden(k4_tarski(X3,sK6(X0,X1)),X0) | ~r2_hidden(sK6(X0,X1),X1)) & (r2_hidden(k4_tarski(sK7(X0,X1),sK6(X0,X1)),X0) | r2_hidden(sK6(X0,X1),X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X6,X5),X0)) & (r2_hidden(k4_tarski(sK8(X0,X5),X5),X0) | ~r2_hidden(X5,X1))) | k2_relat_1(X0) != X1))),
% 23.48/3.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7,sK8])],[f38,f41,f40,f39])).
% 23.48/3.49  
% 23.48/3.49  fof(f70,plain,(
% 23.48/3.49    ( ! [X0,X5,X1] : (r2_hidden(k4_tarski(sK8(X0,X5),X5),X0) | ~r2_hidden(X5,X1) | k2_relat_1(X0) != X1) )),
% 23.48/3.49    inference(cnf_transformation,[],[f42])).
% 23.48/3.49  
% 23.48/3.49  fof(f89,plain,(
% 23.48/3.49    ( ! [X0,X5] : (r2_hidden(k4_tarski(sK8(X0,X5),X5),X0) | ~r2_hidden(X5,k2_relat_1(X0))) )),
% 23.48/3.49    inference(equality_resolution,[],[f70])).
% 23.48/3.49  
% 23.48/3.49  cnf(c_8,plain,
% 23.48/3.49      ( ~ r1_xboole_0(X0,X1) | ~ r2_hidden(X2,k3_xboole_0(X0,X1)) ),
% 23.48/3.49      inference(cnf_transformation,[],[f60]) ).
% 23.48/3.49  
% 23.48/3.49  cnf(c_75034,plain,
% 23.48/3.49      ( ~ r1_xboole_0(k10_relat_1(sK11,k3_xboole_0(k2_relat_1(sK11),sK10)),X0)
% 23.48/3.49      | ~ r2_hidden(sK8(sK11,sK1(k2_relat_1(sK11),sK10)),k3_xboole_0(k10_relat_1(sK11,k3_xboole_0(k2_relat_1(sK11),sK10)),X0)) ),
% 23.48/3.49      inference(instantiation,[status(thm)],[c_8]) ).
% 23.48/3.49  
% 23.48/3.49  cnf(c_75036,plain,
% 23.48/3.49      ( ~ r1_xboole_0(k10_relat_1(sK11,k3_xboole_0(k2_relat_1(sK11),sK10)),k1_xboole_0)
% 23.48/3.49      | ~ r2_hidden(sK8(sK11,sK1(k2_relat_1(sK11),sK10)),k3_xboole_0(k10_relat_1(sK11,k3_xboole_0(k2_relat_1(sK11),sK10)),k1_xboole_0)) ),
% 23.48/3.49      inference(instantiation,[status(thm)],[c_75034]) ).
% 23.48/3.49  
% 23.48/3.49  cnf(c_574,plain,( X0 = X0 ),theory(equality) ).
% 23.48/3.49  
% 23.48/3.49  cnf(c_51233,plain,
% 23.48/3.49      ( sK8(sK11,sK1(k2_relat_1(sK11),sK10)) = sK8(sK11,sK1(k2_relat_1(sK11),sK10)) ),
% 23.48/3.49      inference(instantiation,[status(thm)],[c_574]) ).
% 23.48/3.49  
% 23.48/3.49  cnf(c_577,plain,
% 23.48/3.49      ( ~ r2_hidden(X0,X1) | r2_hidden(X2,X3) | X2 != X0 | X3 != X1 ),
% 23.48/3.49      theory(equality) ).
% 23.48/3.49  
% 23.48/3.49  cnf(c_18550,plain,
% 23.48/3.49      ( r2_hidden(X0,X1)
% 23.48/3.49      | ~ r2_hidden(sK8(sK11,sK1(k2_relat_1(sK11),sK10)),k10_relat_1(sK11,k3_xboole_0(k2_relat_1(sK11),sK10)))
% 23.48/3.49      | X0 != sK8(sK11,sK1(k2_relat_1(sK11),sK10))
% 23.48/3.49      | X1 != k10_relat_1(sK11,k3_xboole_0(k2_relat_1(sK11),sK10)) ),
% 23.48/3.49      inference(instantiation,[status(thm)],[c_577]) ).
% 23.48/3.49  
% 23.48/3.49  cnf(c_51232,plain,
% 23.48/3.49      ( r2_hidden(sK8(sK11,sK1(k2_relat_1(sK11),sK10)),X0)
% 23.48/3.49      | ~ r2_hidden(sK8(sK11,sK1(k2_relat_1(sK11),sK10)),k10_relat_1(sK11,k3_xboole_0(k2_relat_1(sK11),sK10)))
% 23.48/3.49      | X0 != k10_relat_1(sK11,k3_xboole_0(k2_relat_1(sK11),sK10))
% 23.48/3.49      | sK8(sK11,sK1(k2_relat_1(sK11),sK10)) != sK8(sK11,sK1(k2_relat_1(sK11),sK10)) ),
% 23.48/3.49      inference(instantiation,[status(thm)],[c_18550]) ).
% 23.48/3.49  
% 23.48/3.49  cnf(c_51235,plain,
% 23.48/3.49      ( ~ r2_hidden(sK8(sK11,sK1(k2_relat_1(sK11),sK10)),k10_relat_1(sK11,k3_xboole_0(k2_relat_1(sK11),sK10)))
% 23.48/3.49      | r2_hidden(sK8(sK11,sK1(k2_relat_1(sK11),sK10)),k1_xboole_0)
% 23.48/3.49      | sK8(sK11,sK1(k2_relat_1(sK11),sK10)) != sK8(sK11,sK1(k2_relat_1(sK11),sK10))
% 23.48/3.49      | k1_xboole_0 != k10_relat_1(sK11,k3_xboole_0(k2_relat_1(sK11),sK10)) ),
% 23.48/3.49      inference(instantiation,[status(thm)],[c_51232]) ).
% 23.48/3.49  
% 23.48/3.49  cnf(c_3,plain,
% 23.48/3.49      ( ~ r2_hidden(X0,X1)
% 23.48/3.49      | ~ r2_hidden(X0,X2)
% 23.48/3.49      | r2_hidden(X0,k3_xboole_0(X2,X1)) ),
% 23.48/3.49      inference(cnf_transformation,[],[f82]) ).
% 23.48/3.49  
% 23.48/3.49  cnf(c_18558,plain,
% 23.48/3.49      ( ~ r2_hidden(sK8(sK11,sK1(k2_relat_1(sK11),sK10)),X0)
% 23.48/3.49      | ~ r2_hidden(sK8(sK11,sK1(k2_relat_1(sK11),sK10)),k10_relat_1(sK11,k3_xboole_0(k2_relat_1(sK11),sK10)))
% 23.48/3.49      | r2_hidden(sK8(sK11,sK1(k2_relat_1(sK11),sK10)),k3_xboole_0(k10_relat_1(sK11,k3_xboole_0(k2_relat_1(sK11),sK10)),X0)) ),
% 23.48/3.49      inference(instantiation,[status(thm)],[c_3]) ).
% 23.48/3.49  
% 23.48/3.49  cnf(c_18560,plain,
% 23.48/3.49      ( ~ r2_hidden(sK8(sK11,sK1(k2_relat_1(sK11),sK10)),k10_relat_1(sK11,k3_xboole_0(k2_relat_1(sK11),sK10)))
% 23.48/3.49      | r2_hidden(sK8(sK11,sK1(k2_relat_1(sK11),sK10)),k3_xboole_0(k10_relat_1(sK11,k3_xboole_0(k2_relat_1(sK11),sK10)),k1_xboole_0))
% 23.48/3.49      | ~ r2_hidden(sK8(sK11,sK1(k2_relat_1(sK11),sK10)),k1_xboole_0) ),
% 23.48/3.49      inference(instantiation,[status(thm)],[c_18558]) ).
% 23.48/3.49  
% 23.48/3.49  cnf(c_16,plain,
% 23.48/3.49      ( ~ r2_hidden(X0,X1)
% 23.48/3.49      | r2_hidden(X2,k10_relat_1(X3,X1))
% 23.48/3.49      | ~ r2_hidden(k4_tarski(X2,X0),X3)
% 23.48/3.49      | ~ v1_relat_1(X3) ),
% 23.48/3.49      inference(cnf_transformation,[],[f85]) ).
% 23.48/3.49  
% 23.48/3.49  cnf(c_6159,plain,
% 23.48/3.49      ( r2_hidden(sK8(sK11,sK1(k2_relat_1(sK11),sK10)),k10_relat_1(sK11,X0))
% 23.48/3.49      | ~ r2_hidden(k4_tarski(sK8(sK11,sK1(k2_relat_1(sK11),sK10)),sK1(k2_relat_1(sK11),sK10)),sK11)
% 23.48/3.49      | ~ r2_hidden(sK1(k2_relat_1(sK11),sK10),X0)
% 23.48/3.49      | ~ v1_relat_1(sK11) ),
% 23.48/3.49      inference(instantiation,[status(thm)],[c_16]) ).
% 23.48/3.49  
% 23.48/3.49  cnf(c_17551,plain,
% 23.48/3.49      ( r2_hidden(sK8(sK11,sK1(k2_relat_1(sK11),sK10)),k10_relat_1(sK11,k3_xboole_0(k2_relat_1(sK11),sK10)))
% 23.48/3.49      | ~ r2_hidden(k4_tarski(sK8(sK11,sK1(k2_relat_1(sK11),sK10)),sK1(k2_relat_1(sK11),sK10)),sK11)
% 23.48/3.49      | ~ r2_hidden(sK1(k2_relat_1(sK11),sK10),k3_xboole_0(k2_relat_1(sK11),sK10))
% 23.48/3.49      | ~ v1_relat_1(sK11) ),
% 23.48/3.49      inference(instantiation,[status(thm)],[c_6159]) ).
% 23.48/3.49  
% 23.48/3.49  cnf(c_29,negated_conjecture,
% 23.48/3.49      ( r1_xboole_0(k2_relat_1(sK11),sK10)
% 23.48/3.49      | k1_xboole_0 = k10_relat_1(sK11,sK10) ),
% 23.48/3.49      inference(cnf_transformation,[],[f80]) ).
% 23.48/3.49  
% 23.48/3.49  cnf(c_3654,plain,
% 23.48/3.49      ( r1_xboole_0(k2_relat_1(sK11),sK10)
% 23.48/3.49      | ~ r2_hidden(X0,k10_relat_1(sK11,sK10))
% 23.48/3.49      | r2_hidden(X1,k1_xboole_0)
% 23.48/3.49      | X1 != X0 ),
% 23.48/3.49      inference(resolution,[status(thm)],[c_577,c_29]) ).
% 23.48/3.49  
% 23.48/3.49  cnf(c_28,negated_conjecture,
% 23.48/3.49      ( ~ r1_xboole_0(k2_relat_1(sK11),sK10)
% 23.48/3.49      | k1_xboole_0 != k10_relat_1(sK11,sK10) ),
% 23.48/3.49      inference(cnf_transformation,[],[f81]) ).
% 23.48/3.49  
% 23.48/3.49  cnf(c_591,plain,
% 23.48/3.49      ( k1_xboole_0 = k1_xboole_0 ),
% 23.48/3.49      inference(instantiation,[status(thm)],[c_574]) ).
% 23.48/3.49  
% 23.48/3.49  cnf(c_575,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 23.48/3.49  
% 23.48/3.49  cnf(c_1629,plain,
% 23.48/3.49      ( k10_relat_1(sK11,sK10) != X0
% 23.48/3.49      | k1_xboole_0 != X0
% 23.48/3.49      | k1_xboole_0 = k10_relat_1(sK11,sK10) ),
% 23.48/3.49      inference(instantiation,[status(thm)],[c_575]) ).
% 23.48/3.49  
% 23.48/3.49  cnf(c_1630,plain,
% 23.48/3.49      ( k10_relat_1(sK11,sK10) != k1_xboole_0
% 23.48/3.49      | k1_xboole_0 = k10_relat_1(sK11,sK10)
% 23.48/3.49      | k1_xboole_0 != k1_xboole_0 ),
% 23.48/3.49      inference(instantiation,[status(thm)],[c_1629]) ).
% 23.48/3.49  
% 23.48/3.49  cnf(c_10,plain,
% 23.48/3.49      ( r2_hidden(sK2(X0),X0) | k1_xboole_0 = X0 ),
% 23.48/3.49      inference(cnf_transformation,[],[f61]) ).
% 23.48/3.49  
% 23.48/3.49  cnf(c_1232,plain,
% 23.48/3.49      ( k1_xboole_0 = X0 | r2_hidden(sK2(X0),X0) = iProver_top ),
% 23.48/3.49      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 23.48/3.49  
% 23.48/3.49  cnf(c_24,plain,
% 23.48/3.49      ( ~ r2_hidden(X0,k10_relat_1(X1,X2))
% 23.48/3.49      | r2_hidden(sK9(X0,X2,X1),X2)
% 23.48/3.49      | ~ v1_relat_1(X1) ),
% 23.48/3.49      inference(cnf_transformation,[],[f76]) ).
% 23.48/3.49  
% 23.48/3.49  cnf(c_1219,plain,
% 23.48/3.49      ( r2_hidden(X0,k10_relat_1(X1,X2)) != iProver_top
% 23.48/3.49      | r2_hidden(sK9(X0,X2,X1),X2) = iProver_top
% 23.48/3.49      | v1_relat_1(X1) != iProver_top ),
% 23.48/3.49      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 23.48/3.49  
% 23.48/3.49  cnf(c_26,plain,
% 23.48/3.49      ( ~ r2_hidden(X0,k10_relat_1(X1,X2))
% 23.48/3.49      | r2_hidden(sK9(X0,X2,X1),k2_relat_1(X1))
% 23.48/3.49      | ~ v1_relat_1(X1) ),
% 23.48/3.49      inference(cnf_transformation,[],[f74]) ).
% 23.48/3.49  
% 23.48/3.49  cnf(c_1217,plain,
% 23.48/3.49      ( r2_hidden(X0,k10_relat_1(X1,X2)) != iProver_top
% 23.48/3.49      | r2_hidden(sK9(X0,X2,X1),k2_relat_1(X1)) = iProver_top
% 23.48/3.49      | v1_relat_1(X1) != iProver_top ),
% 23.48/3.49      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 23.48/3.49  
% 23.48/3.49  cnf(c_1214,plain,
% 23.48/3.49      ( k1_xboole_0 = k10_relat_1(sK11,sK10)
% 23.48/3.49      | r1_xboole_0(k2_relat_1(sK11),sK10) = iProver_top ),
% 23.48/3.49      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 23.48/3.49  
% 23.48/3.49  cnf(c_7,plain,
% 23.48/3.49      ( ~ r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) = k1_xboole_0 ),
% 23.48/3.49      inference(cnf_transformation,[],[f57]) ).
% 23.48/3.49  
% 23.48/3.49  cnf(c_1235,plain,
% 23.48/3.49      ( k3_xboole_0(X0,X1) = k1_xboole_0
% 23.48/3.49      | r1_xboole_0(X0,X1) != iProver_top ),
% 23.48/3.49      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 23.48/3.49  
% 23.48/3.49  cnf(c_1542,plain,
% 23.48/3.49      ( k10_relat_1(sK11,sK10) = k1_xboole_0
% 23.48/3.49      | k3_xboole_0(k2_relat_1(sK11),sK10) = k1_xboole_0 ),
% 23.48/3.49      inference(superposition,[status(thm)],[c_1214,c_1235]) ).
% 23.48/3.49  
% 23.48/3.49  cnf(c_1239,plain,
% 23.48/3.49      ( r2_hidden(X0,X1) != iProver_top
% 23.48/3.49      | r2_hidden(X0,X2) != iProver_top
% 23.48/3.49      | r2_hidden(X0,k3_xboole_0(X2,X1)) = iProver_top ),
% 23.48/3.49      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 23.48/3.49  
% 23.48/3.49  cnf(c_2440,plain,
% 23.48/3.49      ( k10_relat_1(sK11,sK10) = k1_xboole_0
% 23.48/3.49      | r2_hidden(X0,k2_relat_1(sK11)) != iProver_top
% 23.48/3.49      | r2_hidden(X0,sK10) != iProver_top
% 23.48/3.49      | r2_hidden(X0,k1_xboole_0) = iProver_top ),
% 23.48/3.49      inference(superposition,[status(thm)],[c_1542,c_1239]) ).
% 23.48/3.49  
% 23.48/3.49  cnf(c_12,plain,
% 23.48/3.49      ( ~ r1_xboole_0(k1_tarski(X0),X1) | ~ r2_hidden(X0,X1) ),
% 23.48/3.49      inference(cnf_transformation,[],[f63]) ).
% 23.48/3.49  
% 23.48/3.49  cnf(c_11,plain,
% 23.48/3.49      ( r1_xboole_0(X0,k1_xboole_0) ),
% 23.48/3.49      inference(cnf_transformation,[],[f62]) ).
% 23.48/3.49  
% 23.48/3.49  cnf(c_1524,plain,
% 23.48/3.49      ( ~ r2_hidden(X0,k1_xboole_0) ),
% 23.48/3.49      inference(resolution,[status(thm)],[c_12,c_11]) ).
% 23.48/3.49  
% 23.48/3.49  cnf(c_1525,plain,
% 23.48/3.49      ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
% 23.48/3.49      inference(predicate_to_equality,[status(thm)],[c_1524]) ).
% 23.48/3.49  
% 23.48/3.49  cnf(c_2711,plain,
% 23.48/3.49      ( r2_hidden(X0,sK10) != iProver_top
% 23.48/3.49      | r2_hidden(X0,k2_relat_1(sK11)) != iProver_top
% 23.48/3.49      | k10_relat_1(sK11,sK10) = k1_xboole_0 ),
% 23.48/3.49      inference(global_propositional_subsumption,
% 23.48/3.49                [status(thm)],
% 23.48/3.49                [c_2440,c_1525]) ).
% 23.48/3.49  
% 23.48/3.49  cnf(c_2712,plain,
% 23.48/3.49      ( k10_relat_1(sK11,sK10) = k1_xboole_0
% 23.48/3.49      | r2_hidden(X0,k2_relat_1(sK11)) != iProver_top
% 23.48/3.49      | r2_hidden(X0,sK10) != iProver_top ),
% 23.48/3.49      inference(renaming,[status(thm)],[c_2711]) ).
% 23.48/3.49  
% 23.48/3.49  cnf(c_2723,plain,
% 23.48/3.49      ( k10_relat_1(sK11,sK10) = k1_xboole_0
% 23.48/3.49      | r2_hidden(X0,k10_relat_1(sK11,X1)) != iProver_top
% 23.48/3.49      | r2_hidden(sK9(X0,X1,sK11),sK10) != iProver_top
% 23.48/3.49      | v1_relat_1(sK11) != iProver_top ),
% 23.48/3.49      inference(superposition,[status(thm)],[c_1217,c_2712]) ).
% 23.48/3.49  
% 23.48/3.49  cnf(c_30,negated_conjecture,
% 23.48/3.49      ( v1_relat_1(sK11) ),
% 23.48/3.49      inference(cnf_transformation,[],[f79]) ).
% 23.48/3.49  
% 23.48/3.49  cnf(c_31,plain,
% 23.48/3.49      ( v1_relat_1(sK11) = iProver_top ),
% 23.48/3.49      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 23.48/3.49  
% 23.48/3.49  cnf(c_2911,plain,
% 23.48/3.49      ( r2_hidden(sK9(X0,X1,sK11),sK10) != iProver_top
% 23.48/3.49      | r2_hidden(X0,k10_relat_1(sK11,X1)) != iProver_top
% 23.48/3.49      | k10_relat_1(sK11,sK10) = k1_xboole_0 ),
% 23.48/3.49      inference(global_propositional_subsumption,
% 23.48/3.49                [status(thm)],
% 23.48/3.49                [c_2723,c_31]) ).
% 23.48/3.49  
% 23.48/3.49  cnf(c_2912,plain,
% 23.48/3.49      ( k10_relat_1(sK11,sK10) = k1_xboole_0
% 23.48/3.49      | r2_hidden(X0,k10_relat_1(sK11,X1)) != iProver_top
% 23.48/3.49      | r2_hidden(sK9(X0,X1,sK11),sK10) != iProver_top ),
% 23.48/3.49      inference(renaming,[status(thm)],[c_2911]) ).
% 23.48/3.49  
% 23.48/3.49  cnf(c_2920,plain,
% 23.48/3.49      ( k10_relat_1(sK11,sK10) = k1_xboole_0
% 23.48/3.49      | r2_hidden(X0,k10_relat_1(sK11,sK10)) != iProver_top
% 23.48/3.49      | v1_relat_1(sK11) != iProver_top ),
% 23.48/3.49      inference(superposition,[status(thm)],[c_1219,c_2912]) ).
% 23.48/3.49  
% 23.48/3.49  cnf(c_3123,plain,
% 23.48/3.49      ( r2_hidden(X0,k10_relat_1(sK11,sK10)) != iProver_top
% 23.48/3.49      | k10_relat_1(sK11,sK10) = k1_xboole_0 ),
% 23.48/3.49      inference(global_propositional_subsumption,
% 23.48/3.49                [status(thm)],
% 23.48/3.49                [c_2920,c_31]) ).
% 23.48/3.49  
% 23.48/3.49  cnf(c_3124,plain,
% 23.48/3.49      ( k10_relat_1(sK11,sK10) = k1_xboole_0
% 23.48/3.49      | r2_hidden(X0,k10_relat_1(sK11,sK10)) != iProver_top ),
% 23.48/3.49      inference(renaming,[status(thm)],[c_3123]) ).
% 23.48/3.49  
% 23.48/3.49  cnf(c_3131,plain,
% 23.48/3.49      ( k10_relat_1(sK11,sK10) = k1_xboole_0 ),
% 23.48/3.49      inference(superposition,[status(thm)],[c_1232,c_3124]) ).
% 23.48/3.49  
% 23.48/3.49  cnf(c_3865,plain,
% 23.48/3.49      ( ~ r2_hidden(X0,k10_relat_1(sK11,sK10))
% 23.48/3.49      | r2_hidden(X1,k1_xboole_0)
% 23.48/3.49      | X1 != X0 ),
% 23.48/3.49      inference(global_propositional_subsumption,
% 23.48/3.49                [status(thm)],
% 23.48/3.49                [c_3654,c_28,c_591,c_1630,c_3131]) ).
% 23.48/3.49  
% 23.48/3.49  cnf(c_3874,plain,
% 23.48/3.49      ( ~ r2_hidden(X0,k10_relat_1(sK11,sK10)) | X1 != X0 ),
% 23.48/3.49      inference(forward_subsumption_resolution,
% 23.48/3.49                [status(thm)],
% 23.48/3.49                [c_3865,c_1524]) ).
% 23.48/3.49  
% 23.48/3.49  cnf(c_3887,plain,
% 23.48/3.49      ( X0 != sK2(k10_relat_1(sK11,sK10))
% 23.48/3.49      | k1_xboole_0 = k10_relat_1(sK11,sK10) ),
% 23.48/3.49      inference(resolution,[status(thm)],[c_3874,c_10]) ).
% 23.48/3.49  
% 23.48/3.49  cnf(c_3917,plain,
% 23.48/3.49      ( k1_xboole_0 = k10_relat_1(sK11,sK10) ),
% 23.48/3.49      inference(global_propositional_subsumption,
% 23.48/3.49                [status(thm)],
% 23.48/3.49                [c_3887,c_591,c_1630,c_3131]) ).
% 23.48/3.49  
% 23.48/3.49  cnf(c_4080,plain,
% 23.48/3.49      ( ~ r1_xboole_0(k2_relat_1(sK11),sK10) ),
% 23.48/3.49      inference(backward_subsumption_resolution,
% 23.48/3.49                [status(thm)],
% 23.48/3.49                [c_3917,c_28]) ).
% 23.48/3.49  
% 23.48/3.49  cnf(c_2501,plain,
% 23.48/3.49      ( r1_xboole_0(k2_relat_1(sK11),sK10)
% 23.48/3.49      | X0 != k10_relat_1(sK11,sK10)
% 23.48/3.49      | k1_xboole_0 = X0 ),
% 23.48/3.49      inference(resolution,[status(thm)],[c_575,c_29]) ).
% 23.48/3.49  
% 23.48/3.49  cnf(c_27,plain,
% 23.48/3.49      ( ~ v1_relat_1(X0)
% 23.48/3.49      | k10_relat_1(X0,k3_xboole_0(k2_relat_1(X0),X1)) = k10_relat_1(X0,X1) ),
% 23.48/3.49      inference(cnf_transformation,[],[f78]) ).
% 23.48/3.49  
% 23.48/3.49  cnf(c_2802,plain,
% 23.48/3.49      ( r1_xboole_0(k2_relat_1(sK11),sK10)
% 23.48/3.49      | ~ v1_relat_1(sK11)
% 23.48/3.49      | k1_xboole_0 = k10_relat_1(sK11,k3_xboole_0(k2_relat_1(sK11),sK10)) ),
% 23.48/3.49      inference(resolution,[status(thm)],[c_2501,c_27]) ).
% 23.48/3.49  
% 23.48/3.49  cnf(c_2928,plain,
% 23.48/3.49      ( r1_xboole_0(k2_relat_1(sK11),sK10)
% 23.48/3.49      | k1_xboole_0 = k10_relat_1(sK11,k3_xboole_0(k2_relat_1(sK11),sK10)) ),
% 23.48/3.49      inference(global_propositional_subsumption,
% 23.48/3.49                [status(thm)],
% 23.48/3.49                [c_2802,c_30]) ).
% 23.48/3.49  
% 23.48/3.49  cnf(c_3667,plain,
% 23.48/3.49      ( r1_xboole_0(k2_relat_1(sK11),sK10)
% 23.48/3.49      | ~ r2_hidden(X0,k10_relat_1(sK11,k3_xboole_0(k2_relat_1(sK11),sK10)))
% 23.48/3.49      | r2_hidden(X1,k1_xboole_0)
% 23.48/3.49      | X1 != X0 ),
% 23.48/3.49      inference(resolution,[status(thm)],[c_577,c_2928]) ).
% 23.48/3.49  
% 23.48/3.49  cnf(c_4096,plain,
% 23.48/3.49      ( ~ r2_hidden(X0,k10_relat_1(sK11,k3_xboole_0(k2_relat_1(sK11),sK10)))
% 23.48/3.49      | r2_hidden(X1,k1_xboole_0)
% 23.48/3.49      | X1 != X0 ),
% 23.48/3.49      inference(backward_subsumption_resolution,
% 23.48/3.49                [status(thm)],
% 23.48/3.49                [c_4080,c_3667]) ).
% 23.48/3.49  
% 23.48/3.49  cnf(c_4314,plain,
% 23.48/3.49      ( ~ r2_hidden(X0,k10_relat_1(sK11,k3_xboole_0(k2_relat_1(sK11),sK10)))
% 23.48/3.49      | X1 != X0 ),
% 23.48/3.49      inference(forward_subsumption_resolution,
% 23.48/3.49                [status(thm)],
% 23.48/3.49                [c_4096,c_1524]) ).
% 23.48/3.49  
% 23.48/3.49  cnf(c_5,plain,
% 23.48/3.49      ( r2_hidden(X0,X1) | ~ r2_hidden(X0,k3_xboole_0(X1,X2)) ),
% 23.48/3.49      inference(cnf_transformation,[],[f84]) ).
% 23.48/3.49  
% 23.48/3.49  cnf(c_9,plain,
% 23.48/3.49      ( r1_xboole_0(X0,X1) | r2_hidden(sK1(X0,X1),k3_xboole_0(X0,X1)) ),
% 23.48/3.49      inference(cnf_transformation,[],[f59]) ).
% 23.48/3.49  
% 23.48/3.49  cnf(c_1706,plain,
% 23.48/3.49      ( r1_xboole_0(X0,X1) | r2_hidden(sK1(X0,X1),X0) ),
% 23.48/3.49      inference(resolution,[status(thm)],[c_5,c_9]) ).
% 23.48/3.49  
% 23.48/3.49  cnf(c_4531,plain,
% 23.48/3.49      ( r1_xboole_0(k10_relat_1(sK11,k3_xboole_0(k2_relat_1(sK11),sK10)),X0)
% 23.48/3.49      | X1 != sK1(k10_relat_1(sK11,k3_xboole_0(k2_relat_1(sK11),sK10)),X0) ),
% 23.48/3.49      inference(resolution,[status(thm)],[c_4314,c_1706]) ).
% 23.48/3.49  
% 23.48/3.49  cnf(c_9031,plain,
% 23.48/3.49      ( r1_xboole_0(k10_relat_1(sK11,k3_xboole_0(k2_relat_1(sK11),sK10)),X0) ),
% 23.48/3.49      inference(resolution,[status(thm)],[c_4531,c_574]) ).
% 23.48/3.49  
% 23.48/3.49  cnf(c_9033,plain,
% 23.48/3.49      ( r1_xboole_0(k10_relat_1(sK11,k3_xboole_0(k2_relat_1(sK11),sK10)),k1_xboole_0) ),
% 23.48/3.49      inference(instantiation,[status(thm)],[c_9031]) ).
% 23.48/3.49  
% 23.48/3.49  cnf(c_22,plain,
% 23.48/3.49      ( ~ r2_hidden(X0,k2_relat_1(X1))
% 23.48/3.49      | r2_hidden(k4_tarski(sK8(X1,X0),X0),X1) ),
% 23.48/3.49      inference(cnf_transformation,[],[f89]) ).
% 23.48/3.49  
% 23.48/3.49  cnf(c_2175,plain,
% 23.48/3.49      ( r2_hidden(k4_tarski(sK8(sK11,sK1(k2_relat_1(sK11),sK10)),sK1(k2_relat_1(sK11),sK10)),sK11)
% 23.48/3.49      | ~ r2_hidden(sK1(k2_relat_1(sK11),sK10),k2_relat_1(sK11)) ),
% 23.48/3.49      inference(instantiation,[status(thm)],[c_22]) ).
% 23.48/3.49  
% 23.48/3.49  cnf(c_1902,plain,
% 23.48/3.49      ( ~ r2_hidden(sK1(k2_relat_1(sK11),sK10),k3_xboole_0(k2_relat_1(sK11),sK10))
% 23.48/3.49      | r2_hidden(sK1(k2_relat_1(sK11),sK10),k2_relat_1(sK11)) ),
% 23.48/3.49      inference(instantiation,[status(thm)],[c_5]) ).
% 23.48/3.49  
% 23.48/3.49  cnf(c_1505,plain,
% 23.48/3.49      ( r1_xboole_0(k2_relat_1(sK11),sK10)
% 23.48/3.49      | r2_hidden(sK1(k2_relat_1(sK11),sK10),k3_xboole_0(k2_relat_1(sK11),sK10)) ),
% 23.48/3.49      inference(instantiation,[status(thm)],[c_9]) ).
% 23.48/3.49  
% 23.48/3.49  cnf(contradiction,plain,
% 23.48/3.49      ( $false ),
% 23.48/3.49      inference(minisat,
% 23.48/3.49                [status(thm)],
% 23.48/3.49                [c_75036,c_51233,c_51235,c_18560,c_17551,c_9033,c_3131,
% 23.48/3.49                 c_2802,c_2175,c_1902,c_1630,c_1505,c_591,c_28,c_30]) ).
% 23.48/3.49  
% 23.48/3.49  
% 23.48/3.49  % SZS output end CNFRefutation for theBenchmark.p
% 23.48/3.49  
% 23.48/3.49  ------                               Statistics
% 23.48/3.49  
% 23.48/3.49  ------ Selected
% 23.48/3.49  
% 23.48/3.49  total_time:                             2.633
% 23.48/3.49  
%------------------------------------------------------------------------------
