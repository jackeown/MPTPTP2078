%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0687+1.002 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:43:54 EST 2020

% Result     : Theorem 23.37s
% Output     : CNFRefutation 23.37s
% Verified   : 
% Statistics : Number of formulae       :  116 ( 219 expanded)
%              Number of clauses        :   62 (  72 expanded)
%              Number of leaves         :   20 (  54 expanded)
%              Depth                    :   13
%              Number of atoms          :  417 ( 974 expanded)
%              Number of equality atoms :  130 ( 317 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal clause size      :   15 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X1] : ~ r2_hidden(X1,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f23,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f22])).

fof(f24,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK4(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK4(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f23,f24])).

fof(f46,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f5,axiom,(
    v1_xboole_0(o_0_0_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f52,plain,(
    v1_xboole_0(o_0_0_xboole_0) ),
    inference(cnf_transformation,[],[f5])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f10,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f53,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f7,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r2_hidden(X0,k2_relat_1(X1))
      <=> k10_relat_1(X1,k1_tarski(X0)) != k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f8,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => ( r2_hidden(X0,k2_relat_1(X1))
        <=> k10_relat_1(X1,k1_tarski(X0)) != k1_xboole_0 ) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f11,plain,(
    ? [X0,X1] :
      ( ( r2_hidden(X0,k2_relat_1(X1))
      <~> k10_relat_1(X1,k1_tarski(X0)) != k1_xboole_0 )
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f32,plain,(
    ? [X0,X1] :
      ( ( k10_relat_1(X1,k1_tarski(X0)) = k1_xboole_0
        | ~ r2_hidden(X0,k2_relat_1(X1)) )
      & ( k10_relat_1(X1,k1_tarski(X0)) != k1_xboole_0
        | r2_hidden(X0,k2_relat_1(X1)) )
      & v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f11])).

fof(f33,plain,(
    ? [X0,X1] :
      ( ( k10_relat_1(X1,k1_tarski(X0)) = k1_xboole_0
        | ~ r2_hidden(X0,k2_relat_1(X1)) )
      & ( k10_relat_1(X1,k1_tarski(X0)) != k1_xboole_0
        | r2_hidden(X0,k2_relat_1(X1)) )
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f32])).

fof(f34,plain,
    ( ? [X0,X1] :
        ( ( k10_relat_1(X1,k1_tarski(X0)) = k1_xboole_0
          | ~ r2_hidden(X0,k2_relat_1(X1)) )
        & ( k10_relat_1(X1,k1_tarski(X0)) != k1_xboole_0
          | r2_hidden(X0,k2_relat_1(X1)) )
        & v1_relat_1(X1) )
   => ( ( k10_relat_1(sK9,k1_tarski(sK8)) = k1_xboole_0
        | ~ r2_hidden(sK8,k2_relat_1(sK9)) )
      & ( k10_relat_1(sK9,k1_tarski(sK8)) != k1_xboole_0
        | r2_hidden(sK8,k2_relat_1(sK9)) )
      & v1_relat_1(sK9) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,
    ( ( k10_relat_1(sK9,k1_tarski(sK8)) = k1_xboole_0
      | ~ r2_hidden(sK8,k2_relat_1(sK9)) )
    & ( k10_relat_1(sK9,k1_tarski(sK8)) != k1_xboole_0
      | r2_hidden(sK8,k2_relat_1(sK9)) )
    & v1_relat_1(sK9) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8,sK9])],[f33,f34])).

fof(f56,plain,
    ( k10_relat_1(sK9,k1_tarski(sK8)) = k1_xboole_0
    | ~ r2_hidden(sK8,k2_relat_1(sK9)) ),
    inference(cnf_transformation,[],[f35])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( k2_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X3,X2),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
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
    inference(nnf_transformation,[],[f4])).

fof(f27,plain,(
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
    inference(rectify,[],[f26])).

fof(f30,plain,(
    ! [X5,X0] :
      ( ? [X7] : r2_hidden(k4_tarski(X7,X5),X0)
     => r2_hidden(k4_tarski(sK7(X0,X5),X5),X0) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] : r2_hidden(k4_tarski(X4,X2),X0)
     => r2_hidden(k4_tarski(sK6(X0,X1),X2),X0) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,X2),X0)
            | ~ r2_hidden(X2,X1) )
          & ( ? [X4] : r2_hidden(k4_tarski(X4,X2),X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,sK5(X0,X1)),X0)
          | ~ r2_hidden(sK5(X0,X1),X1) )
        & ( ? [X4] : r2_hidden(k4_tarski(X4,sK5(X0,X1)),X0)
          | r2_hidden(sK5(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( k2_relat_1(X0) = X1
        | ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,sK5(X0,X1)),X0)
            | ~ r2_hidden(sK5(X0,X1),X1) )
          & ( r2_hidden(k4_tarski(sK6(X0,X1),sK5(X0,X1)),X0)
            | r2_hidden(sK5(X0,X1),X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] : ~ r2_hidden(k4_tarski(X6,X5),X0) )
            & ( r2_hidden(k4_tarski(sK7(X0,X5),X5),X0)
              | ~ r2_hidden(X5,X1) ) )
        | k2_relat_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6,sK7])],[f27,f30,f29,f28])).

fof(f49,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | ~ r2_hidden(k4_tarski(X6,X5),X0)
      | k2_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f31])).

fof(f63,plain,(
    ! [X6,X0,X5] :
      ( r2_hidden(X5,k2_relat_1(X0))
      | ~ r2_hidden(k4_tarski(X6,X5),X0) ) ),
    inference(equality_resolution,[],[f49])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ? [X2] :
            ( ( X0 != X2
              | ~ r2_hidden(X2,X1) )
            & ( X0 = X2
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | X0 != X2 )
            & ( X0 = X2
              | ~ r2_hidden(X2,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ? [X2] :
            ( ( X0 != X2
              | ~ r2_hidden(X2,X1) )
            & ( X0 = X2
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(rectify,[],[f18])).

fof(f20,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( X0 != X2
            | ~ r2_hidden(X2,X1) )
          & ( X0 = X2
            | r2_hidden(X2,X1) ) )
     => ( ( sK3(X0,X1) != X0
          | ~ r2_hidden(sK3(X0,X1),X1) )
        & ( sK3(X0,X1) = X0
          | r2_hidden(sK3(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ( ( sK3(X0,X1) != X0
            | ~ r2_hidden(sK3(X0,X1),X1) )
          & ( sK3(X0,X1) = X0
            | r2_hidden(sK3(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f19,f20])).

fof(f42,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f21])).

fof(f62,plain,(
    ! [X0,X3] :
      ( X0 = X3
      | ~ r2_hidden(X3,k1_tarski(X0)) ) ),
    inference(equality_resolution,[],[f42])).

fof(f43,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | X0 != X3
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f21])).

fof(f60,plain,(
    ! [X3,X1] :
      ( r2_hidden(X3,X1)
      | k1_tarski(X3) != X1 ) ),
    inference(equality_resolution,[],[f43])).

fof(f61,plain,(
    ! [X3] : r2_hidden(X3,k1_tarski(X3)) ),
    inference(equality_resolution,[],[f60])).

fof(f1,axiom,(
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

fof(f9,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k10_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ? [X4] :
                  ( r2_hidden(X4,X1)
                  & r2_hidden(k4_tarski(X3,X4),X0) ) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f12,plain,(
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
    inference(nnf_transformation,[],[f9])).

fof(f13,plain,(
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
    inference(rectify,[],[f12])).

fof(f16,plain,(
    ! [X6,X1,X0] :
      ( ? [X8] :
          ( r2_hidden(X8,X1)
          & r2_hidden(k4_tarski(X6,X8),X0) )
     => ( r2_hidden(sK2(X0,X1,X6),X1)
        & r2_hidden(k4_tarski(X6,sK2(X0,X1,X6)),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X5] :
          ( r2_hidden(X5,X1)
          & r2_hidden(k4_tarski(X3,X5),X0) )
     => ( r2_hidden(sK1(X0,X1,X2),X1)
        & r2_hidden(k4_tarski(X3,sK1(X0,X1,X2)),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f14,plain,(
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
              | ~ r2_hidden(k4_tarski(sK0(X0,X1,X2),X4),X0) )
          | ~ r2_hidden(sK0(X0,X1,X2),X2) )
        & ( ? [X5] :
              ( r2_hidden(X5,X1)
              & r2_hidden(k4_tarski(sK0(X0,X1,X2),X5),X0) )
          | r2_hidden(sK0(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k10_relat_1(X0,X1) = X2
            | ( ( ! [X4] :
                    ( ~ r2_hidden(X4,X1)
                    | ~ r2_hidden(k4_tarski(sK0(X0,X1,X2),X4),X0) )
                | ~ r2_hidden(sK0(X0,X1,X2),X2) )
              & ( ( r2_hidden(sK1(X0,X1,X2),X1)
                  & r2_hidden(k4_tarski(sK0(X0,X1,X2),sK1(X0,X1,X2)),X0) )
                | r2_hidden(sK0(X0,X1,X2),X2) ) ) )
          & ( ! [X6] :
                ( ( r2_hidden(X6,X2)
                  | ! [X7] :
                      ( ~ r2_hidden(X7,X1)
                      | ~ r2_hidden(k4_tarski(X6,X7),X0) ) )
                & ( ( r2_hidden(sK2(X0,X1,X6),X1)
                    & r2_hidden(k4_tarski(X6,sK2(X0,X1,X6)),X0) )
                  | ~ r2_hidden(X6,X2) ) )
            | k10_relat_1(X0,X1) != X2 ) )
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f13,f16,f15,f14])).

fof(f38,plain,(
    ! [X6,X2,X0,X7,X1] :
      ( r2_hidden(X6,X2)
      | ~ r2_hidden(X7,X1)
      | ~ r2_hidden(k4_tarski(X6,X7),X0)
      | k10_relat_1(X0,X1) != X2
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f57,plain,(
    ! [X6,X0,X7,X1] :
      ( r2_hidden(X6,k10_relat_1(X0,X1))
      | ~ r2_hidden(X7,X1)
      | ~ r2_hidden(k4_tarski(X6,X7),X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f38])).

fof(f54,plain,(
    v1_relat_1(sK9) ),
    inference(cnf_transformation,[],[f35])).

fof(f48,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(k4_tarski(sK7(X0,X5),X5),X0)
      | ~ r2_hidden(X5,X1)
      | k2_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f31])).

fof(f64,plain,(
    ! [X0,X5] :
      ( r2_hidden(k4_tarski(sK7(X0,X5),X5),X0)
      | ~ r2_hidden(X5,k2_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f48])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( k10_relat_1(X0,X1) = X2
      | r2_hidden(k4_tarski(sK0(X0,X1,X2),sK1(X0,X1,X2)),X0)
      | r2_hidden(sK0(X0,X1,X2),X2)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( k10_relat_1(X0,X1) = X2
      | r2_hidden(sK1(X0,X1,X2),X1)
      | r2_hidden(sK0(X0,X1,X2),X2)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f55,plain,
    ( k10_relat_1(sK9,k1_tarski(sK8)) != k1_xboole_0
    | r2_hidden(sK8,k2_relat_1(sK9)) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_672,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_1260,plain,
    ( X0 != X1
    | sK8 != X1
    | sK8 = X0 ),
    inference(instantiation,[status(thm)],[c_672])).

cnf(c_1380,plain,
    ( X0 != sK8
    | sK8 = X0
    | sK8 != sK8 ),
    inference(instantiation,[status(thm)],[c_1260])).

cnf(c_31308,plain,
    ( sK1(sK9,k1_tarski(sK8),k1_xboole_0) != sK8
    | sK8 = sK1(sK9,k1_tarski(sK8),k1_xboole_0)
    | sK8 != sK8 ),
    inference(instantiation,[status(thm)],[c_1380])).

cnf(c_674,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_1185,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(sK8,k2_relat_1(sK9))
    | k2_relat_1(sK9) != X1
    | sK8 != X0 ),
    inference(instantiation,[status(thm)],[c_674])).

cnf(c_13324,plain,
    ( ~ r2_hidden(X0,k2_relat_1(sK9))
    | r2_hidden(sK8,k2_relat_1(sK9))
    | k2_relat_1(sK9) != k2_relat_1(sK9)
    | sK8 != X0 ),
    inference(instantiation,[status(thm)],[c_1185])).

cnf(c_30478,plain,
    ( ~ r2_hidden(sK1(sK9,k1_tarski(sK8),k1_xboole_0),k2_relat_1(sK9))
    | r2_hidden(sK8,k2_relat_1(sK9))
    | k2_relat_1(sK9) != k2_relat_1(sK9)
    | sK8 != sK1(sK9,k1_tarski(sK8),k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_13324])).

cnf(c_11,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_1508,plain,
    ( ~ r2_hidden(X0,k10_relat_1(sK9,X1))
    | ~ v1_xboole_0(k10_relat_1(sK9,X1)) ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_4796,plain,
    ( ~ r2_hidden(sK7(sK9,X0),k10_relat_1(sK9,k1_tarski(X0)))
    | ~ v1_xboole_0(k10_relat_1(sK9,k1_tarski(X0))) ),
    inference(instantiation,[status(thm)],[c_1508])).

cnf(c_21618,plain,
    ( ~ r2_hidden(sK7(sK9,sK8),k10_relat_1(sK9,k1_tarski(sK8)))
    | ~ v1_xboole_0(k10_relat_1(sK9,k1_tarski(sK8))) ),
    inference(instantiation,[status(thm)],[c_4796])).

cnf(c_680,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | X1 != X0 ),
    theory(equality)).

cnf(c_1783,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(k10_relat_1(sK9,X1))
    | k10_relat_1(sK9,X1) != X0 ),
    inference(instantiation,[status(thm)],[c_680])).

cnf(c_10309,plain,
    ( v1_xboole_0(k10_relat_1(sK9,X0))
    | ~ v1_xboole_0(o_0_0_xboole_0)
    | k10_relat_1(sK9,X0) != o_0_0_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1783])).

cnf(c_13524,plain,
    ( v1_xboole_0(k10_relat_1(sK9,k1_tarski(sK8)))
    | ~ v1_xboole_0(o_0_0_xboole_0)
    | k10_relat_1(sK9,k1_tarski(sK8)) != o_0_0_xboole_0 ),
    inference(instantiation,[status(thm)],[c_10309])).

cnf(c_2540,plain,
    ( v1_xboole_0(X0)
    | ~ v1_xboole_0(o_0_0_xboole_0)
    | X0 != o_0_0_xboole_0 ),
    inference(instantiation,[status(thm)],[c_680])).

cnf(c_4041,plain,
    ( v1_xboole_0(k1_xboole_0)
    | ~ v1_xboole_0(o_0_0_xboole_0)
    | k1_xboole_0 != o_0_0_xboole_0 ),
    inference(instantiation,[status(thm)],[c_2540])).

cnf(c_16,plain,
    ( v1_xboole_0(o_0_0_xboole_0) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_1141,plain,
    ( v1_xboole_0(o_0_0_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_17,plain,
    ( ~ v1_xboole_0(X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f53])).

cnf(c_1140,plain,
    ( k1_xboole_0 = X0
    | v1_xboole_0(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_1612,plain,
    ( k1_xboole_0 = o_0_0_xboole_0 ),
    inference(superposition,[status(thm)],[c_1141,c_1140])).

cnf(c_18,negated_conjecture,
    ( ~ r2_hidden(sK8,k2_relat_1(sK9))
    | k10_relat_1(sK9,k1_tarski(sK8)) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f56])).

cnf(c_1139,plain,
    ( k10_relat_1(sK9,k1_tarski(sK8)) = k1_xboole_0
    | r2_hidden(sK8,k2_relat_1(sK9)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_3349,plain,
    ( k10_relat_1(sK9,k1_tarski(sK8)) = o_0_0_xboole_0
    | r2_hidden(sK8,k2_relat_1(sK9)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1612,c_1139])).

cnf(c_3352,plain,
    ( ~ r2_hidden(sK8,k2_relat_1(sK9))
    | k10_relat_1(sK9,k1_tarski(sK8)) = o_0_0_xboole_0 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_3349])).

cnf(c_14,plain,
    ( r2_hidden(X0,k2_relat_1(X1))
    | ~ r2_hidden(k4_tarski(X2,X0),X1) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_2382,plain,
    ( r2_hidden(sK1(sK9,k1_tarski(sK8),k1_xboole_0),k2_relat_1(sK9))
    | ~ r2_hidden(k4_tarski(sK0(sK9,k1_tarski(sK8),k1_xboole_0),sK1(sK9,k1_tarski(sK8),k1_xboole_0)),sK9) ),
    inference(instantiation,[status(thm)],[c_14])).

cnf(c_9,plain,
    ( ~ r2_hidden(X0,k1_tarski(X1))
    | X0 = X1 ),
    inference(cnf_transformation,[],[f62])).

cnf(c_1536,plain,
    ( ~ r2_hidden(X0,k1_tarski(sK8))
    | X0 = sK8 ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_2315,plain,
    ( ~ r2_hidden(sK1(sK9,k1_tarski(sK8),k1_xboole_0),k1_tarski(sK8))
    | sK1(sK9,k1_tarski(sK8),k1_xboole_0) = sK8 ),
    inference(instantiation,[status(thm)],[c_1536])).

cnf(c_8,plain,
    ( r2_hidden(X0,k1_tarski(X0)) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_1708,plain,
    ( r2_hidden(sK8,k1_tarski(sK8)) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_1675,plain,
    ( ~ r2_hidden(sK0(sK9,k1_tarski(sK8),k1_xboole_0),k1_xboole_0)
    | ~ v1_xboole_0(k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_3,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,k10_relat_1(X3,X1))
    | ~ r2_hidden(k4_tarski(X2,X0),X3)
    | ~ v1_relat_1(X3) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_20,negated_conjecture,
    ( v1_relat_1(sK9) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_383,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,k10_relat_1(X3,X1))
    | ~ r2_hidden(k4_tarski(X2,X0),X3)
    | sK9 != X3 ),
    inference(resolution_lifted,[status(thm)],[c_3,c_20])).

cnf(c_384,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,k10_relat_1(sK9,X1))
    | ~ r2_hidden(k4_tarski(X2,X0),sK9) ),
    inference(unflattening,[status(thm)],[c_383])).

cnf(c_1211,plain,
    ( r2_hidden(X0,k10_relat_1(sK9,k1_tarski(X1)))
    | ~ r2_hidden(X1,k1_tarski(X1))
    | ~ r2_hidden(k4_tarski(X0,X1),sK9) ),
    inference(instantiation,[status(thm)],[c_384])).

cnf(c_1289,plain,
    ( ~ r2_hidden(X0,k1_tarski(X0))
    | r2_hidden(sK7(sK9,X0),k10_relat_1(sK9,k1_tarski(X0)))
    | ~ r2_hidden(k4_tarski(sK7(sK9,X0),X0),sK9) ),
    inference(instantiation,[status(thm)],[c_1211])).

cnf(c_1468,plain,
    ( r2_hidden(sK7(sK9,sK8),k10_relat_1(sK9,k1_tarski(sK8)))
    | ~ r2_hidden(k4_tarski(sK7(sK9,sK8),sK8),sK9)
    | ~ r2_hidden(sK8,k1_tarski(sK8)) ),
    inference(instantiation,[status(thm)],[c_1289])).

cnf(c_1250,plain,
    ( ~ r2_hidden(sK8,k1_tarski(X0))
    | sK8 = X0 ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_1363,plain,
    ( ~ r2_hidden(sK8,k1_tarski(sK8))
    | sK8 = sK8 ),
    inference(instantiation,[status(thm)],[c_1250])).

cnf(c_15,plain,
    ( ~ r2_hidden(X0,k2_relat_1(X1))
    | r2_hidden(k4_tarski(sK7(X1,X0),X0),X1) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_1360,plain,
    ( r2_hidden(k4_tarski(sK7(sK9,sK8),sK8),sK9)
    | ~ r2_hidden(sK8,k2_relat_1(sK9)) ),
    inference(instantiation,[status(thm)],[c_15])).

cnf(c_2,plain,
    ( r2_hidden(sK0(X0,X1,X2),X2)
    | r2_hidden(k4_tarski(sK0(X0,X1,X2),sK1(X0,X1,X2)),X0)
    | ~ v1_relat_1(X0)
    | k10_relat_1(X0,X1) = X2 ),
    inference(cnf_transformation,[],[f39])).

cnf(c_335,plain,
    ( r2_hidden(sK0(X0,X1,X2),X2)
    | r2_hidden(k4_tarski(sK0(X0,X1,X2),sK1(X0,X1,X2)),X0)
    | k10_relat_1(X0,X1) = X2
    | sK9 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_2,c_20])).

cnf(c_336,plain,
    ( r2_hidden(sK0(sK9,X0,X1),X1)
    | r2_hidden(k4_tarski(sK0(sK9,X0,X1),sK1(sK9,X0,X1)),sK9)
    | k10_relat_1(sK9,X0) = X1 ),
    inference(unflattening,[status(thm)],[c_335])).

cnf(c_1271,plain,
    ( r2_hidden(sK0(sK9,k1_tarski(sK8),k1_xboole_0),k1_xboole_0)
    | r2_hidden(k4_tarski(sK0(sK9,k1_tarski(sK8),k1_xboole_0),sK1(sK9,k1_tarski(sK8),k1_xboole_0)),sK9)
    | k10_relat_1(sK9,k1_tarski(sK8)) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_336])).

cnf(c_1,plain,
    ( r2_hidden(sK1(X0,X1,X2),X1)
    | r2_hidden(sK0(X0,X1,X2),X2)
    | ~ v1_relat_1(X0)
    | k10_relat_1(X0,X1) = X2 ),
    inference(cnf_transformation,[],[f40])).

cnf(c_350,plain,
    ( r2_hidden(sK1(X0,X1,X2),X1)
    | r2_hidden(sK0(X0,X1,X2),X2)
    | k10_relat_1(X0,X1) = X2
    | sK9 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_1,c_20])).

cnf(c_351,plain,
    ( r2_hidden(sK1(sK9,X0,X1),X0)
    | r2_hidden(sK0(sK9,X0,X1),X1)
    | k10_relat_1(sK9,X0) = X1 ),
    inference(unflattening,[status(thm)],[c_350])).

cnf(c_1261,plain,
    ( r2_hidden(sK1(sK9,k1_tarski(sK8),k1_xboole_0),k1_tarski(sK8))
    | r2_hidden(sK0(sK9,k1_tarski(sK8),k1_xboole_0),k1_xboole_0)
    | k10_relat_1(sK9,k1_tarski(sK8)) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_351])).

cnf(c_681,plain,
    ( X0 != X1
    | k2_relat_1(X0) = k2_relat_1(X1) ),
    theory(equality)).

cnf(c_690,plain,
    ( k2_relat_1(sK9) = k2_relat_1(sK9)
    | sK9 != sK9 ),
    inference(instantiation,[status(thm)],[c_681])).

cnf(c_315,plain,
    ( k1_xboole_0 = X0
    | o_0_0_xboole_0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_17,c_16])).

cnf(c_316,plain,
    ( k1_xboole_0 = o_0_0_xboole_0 ),
    inference(unflattening,[status(thm)],[c_315])).

cnf(c_50,plain,
    ( r2_hidden(sK9,k1_tarski(sK9)) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_47,plain,
    ( ~ r2_hidden(sK9,k1_tarski(sK9))
    | sK9 = sK9 ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_19,negated_conjecture,
    ( r2_hidden(sK8,k2_relat_1(sK9))
    | k10_relat_1(sK9,k1_tarski(sK8)) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f55])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_31308,c_30478,c_21618,c_13524,c_4041,c_3352,c_2382,c_2315,c_1708,c_1675,c_1468,c_1363,c_1360,c_1271,c_1261,c_690,c_316,c_50,c_47,c_16,c_19])).


%------------------------------------------------------------------------------
