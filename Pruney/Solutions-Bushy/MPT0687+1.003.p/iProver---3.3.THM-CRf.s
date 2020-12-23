%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0687+1.003 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n032.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:43:54 EST 2020

% Result     : Theorem 15.71s
% Output     : CNFRefutation 15.71s
% Verified   : 
% Statistics : Number of formulae       :  133 ( 652 expanded)
%              Number of clauses        :   80 ( 257 expanded)
%              Number of leaves         :   19 ( 145 expanded)
%              Depth                    :   25
%              Number of atoms          :  447 (2492 expanded)
%              Number of equality atoms :  174 (1003 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal clause size      :   15 (   2 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f6,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f11])).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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

fof(f13,plain,(
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

fof(f14,plain,(
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
    inference(rectify,[],[f13])).

fof(f17,plain,(
    ! [X6,X1,X0] :
      ( ? [X8] :
          ( r2_hidden(X8,X1)
          & r2_hidden(k4_tarski(X6,X8),X0) )
     => ( r2_hidden(sK2(X0,X1,X6),X1)
        & r2_hidden(k4_tarski(X6,sK2(X0,X1,X6)),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X5] :
          ( r2_hidden(X5,X1)
          & r2_hidden(k4_tarski(X3,X5),X0) )
     => ( r2_hidden(sK1(X0,X1,X2),X1)
        & r2_hidden(k4_tarski(X3,sK1(X0,X1,X2)),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
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

fof(f18,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f14,f17,f16,f15])).

fof(f35,plain,(
    ! [X6,X2,X0,X7,X1] :
      ( r2_hidden(X6,X2)
      | ~ r2_hidden(X7,X1)
      | ~ r2_hidden(k4_tarski(X6,X7),X0)
      | k10_relat_1(X0,X1) != X2
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f53,plain,(
    ! [X6,X0,X7,X1] :
      ( r2_hidden(X6,k10_relat_1(X0,X1))
      | ~ r2_hidden(X7,X1)
      | ~ r2_hidden(k4_tarski(X6,X7),X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f35])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
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

fof(f20,plain,(
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
    inference(rectify,[],[f19])).

fof(f21,plain,(
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

fof(f22,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f20,f21])).

fof(f39,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f22])).

fof(f58,plain,(
    ! [X0,X3] :
      ( X0 = X3
      | ~ r2_hidden(X3,k1_tarski(X0)) ) ),
    inference(equality_resolution,[],[f39])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( k10_relat_1(X0,X1) = X2
      | r2_hidden(sK1(X0,X1,X2),X1)
      | r2_hidden(sK0(X0,X1,X2),X2)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f7,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r2_hidden(X0,k2_relat_1(X1))
      <=> k10_relat_1(X1,k1_tarski(X0)) != k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f8,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => ( r2_hidden(X0,k2_relat_1(X1))
        <=> k10_relat_1(X1,k1_tarski(X0)) != k1_xboole_0 ) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f12,plain,(
    ? [X0,X1] :
      ( ( r2_hidden(X0,k2_relat_1(X1))
      <~> k10_relat_1(X1,k1_tarski(X0)) != k1_xboole_0 )
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f29,plain,(
    ? [X0,X1] :
      ( ( k10_relat_1(X1,k1_tarski(X0)) = k1_xboole_0
        | ~ r2_hidden(X0,k2_relat_1(X1)) )
      & ( k10_relat_1(X1,k1_tarski(X0)) != k1_xboole_0
        | r2_hidden(X0,k2_relat_1(X1)) )
      & v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f12])).

fof(f30,plain,(
    ? [X0,X1] :
      ( ( k10_relat_1(X1,k1_tarski(X0)) = k1_xboole_0
        | ~ r2_hidden(X0,k2_relat_1(X1)) )
      & ( k10_relat_1(X1,k1_tarski(X0)) != k1_xboole_0
        | r2_hidden(X0,k2_relat_1(X1)) )
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f29])).

fof(f31,plain,
    ( ? [X0,X1] :
        ( ( k10_relat_1(X1,k1_tarski(X0)) = k1_xboole_0
          | ~ r2_hidden(X0,k2_relat_1(X1)) )
        & ( k10_relat_1(X1,k1_tarski(X0)) != k1_xboole_0
          | r2_hidden(X0,k2_relat_1(X1)) )
        & v1_relat_1(X1) )
   => ( ( k10_relat_1(sK8,k1_tarski(sK7)) = k1_xboole_0
        | ~ r2_hidden(sK7,k2_relat_1(sK8)) )
      & ( k10_relat_1(sK8,k1_tarski(sK7)) != k1_xboole_0
        | r2_hidden(sK7,k2_relat_1(sK8)) )
      & v1_relat_1(sK8) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,
    ( ( k10_relat_1(sK8,k1_tarski(sK7)) = k1_xboole_0
      | ~ r2_hidden(sK7,k2_relat_1(sK8)) )
    & ( k10_relat_1(sK8,k1_tarski(sK7)) != k1_xboole_0
      | r2_hidden(sK7,k2_relat_1(sK8)) )
    & v1_relat_1(sK8) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7,sK8])],[f30,f31])).

fof(f51,plain,
    ( k10_relat_1(sK8,k1_tarski(sK7)) != k1_xboole_0
    | r2_hidden(sK7,k2_relat_1(sK8)) ),
    inference(cnf_transformation,[],[f32])).

fof(f50,plain,(
    v1_relat_1(sK8) ),
    inference(cnf_transformation,[],[f32])).

fof(f4,axiom,(
    v1_xboole_0(o_0_0_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f47,plain,(
    v1_xboole_0(o_0_0_xboole_0) ),
    inference(cnf_transformation,[],[f4])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f10,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f48,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f41,plain,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
      | sK3(X0,X1) = X0
      | r2_hidden(sK3(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f42,plain,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
      | sK3(X0,X1) != X0
      | ~ r2_hidden(sK3(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( k10_relat_1(X0,X1) = X2
      | r2_hidden(k4_tarski(sK0(X0,X1,X2),sK1(X0,X1,X2)),X0)
      | r2_hidden(sK0(X0,X1,X2),X2)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k2_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X3,X2),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
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
    inference(nnf_transformation,[],[f3])).

fof(f24,plain,(
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
    inference(rectify,[],[f23])).

fof(f27,plain,(
    ! [X5,X0] :
      ( ? [X7] : r2_hidden(k4_tarski(X7,X5),X0)
     => r2_hidden(k4_tarski(sK6(X0,X5),X5),X0) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] : r2_hidden(k4_tarski(X4,X2),X0)
     => r2_hidden(k4_tarski(sK5(X0,X1),X2),X0) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
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

fof(f28,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6])],[f24,f27,f26,f25])).

fof(f44,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | ~ r2_hidden(k4_tarski(X6,X5),X0)
      | k2_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f28])).

fof(f59,plain,(
    ! [X6,X0,X5] :
      ( r2_hidden(X5,k2_relat_1(X0))
      | ~ r2_hidden(k4_tarski(X6,X5),X0) ) ),
    inference(equality_resolution,[],[f44])).

fof(f52,plain,
    ( k10_relat_1(sK8,k1_tarski(sK7)) = k1_xboole_0
    | ~ r2_hidden(sK7,k2_relat_1(sK8)) ),
    inference(cnf_transformation,[],[f32])).

fof(f40,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | X0 != X3
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f22])).

fof(f56,plain,(
    ! [X3,X1] :
      ( r2_hidden(X3,X1)
      | k1_tarski(X3) != X1 ) ),
    inference(equality_resolution,[],[f40])).

fof(f57,plain,(
    ! [X3] : r2_hidden(X3,k1_tarski(X3)) ),
    inference(equality_resolution,[],[f56])).

fof(f43,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(k4_tarski(sK6(X0,X5),X5),X0)
      | ~ r2_hidden(X5,X1)
      | k2_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f28])).

fof(f60,plain,(
    ! [X0,X5] :
      ( r2_hidden(k4_tarski(sK6(X0,X5),X5),X0)
      | ~ r2_hidden(X5,k2_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f43])).

cnf(c_16,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_1330,plain,
    ( ~ r2_hidden(X0,k10_relat_1(X1,X2))
    | ~ v1_xboole_0(k10_relat_1(X1,X2)) ),
    inference(instantiation,[status(thm)],[c_16])).

cnf(c_50048,plain,
    ( ~ r2_hidden(sK6(sK8,sK7),k10_relat_1(sK8,k1_tarski(sK7)))
    | ~ v1_xboole_0(k10_relat_1(sK8,k1_tarski(sK7))) ),
    inference(instantiation,[status(thm)],[c_1330])).

cnf(c_3,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,k10_relat_1(X3,X1))
    | ~ r2_hidden(k4_tarski(X2,X0),X3)
    | ~ v1_relat_1(X3) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_1451,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(sK6(X2,X0),k10_relat_1(X2,X1))
    | ~ r2_hidden(k4_tarski(sK6(X2,X0),X0),X2)
    | ~ v1_relat_1(X2) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_2300,plain,
    ( ~ r2_hidden(X0,k1_tarski(X0))
    | r2_hidden(sK6(X1,X0),k10_relat_1(X1,k1_tarski(X0)))
    | ~ r2_hidden(k4_tarski(sK6(X1,X0),X0),X1)
    | ~ v1_relat_1(X1) ),
    inference(instantiation,[status(thm)],[c_1451])).

cnf(c_40845,plain,
    ( r2_hidden(sK6(sK8,sK7),k10_relat_1(sK8,k1_tarski(sK7)))
    | ~ r2_hidden(k4_tarski(sK6(sK8,sK7),sK7),sK8)
    | ~ r2_hidden(sK7,k1_tarski(sK7))
    | ~ v1_relat_1(sK8) ),
    inference(instantiation,[status(thm)],[c_2300])).

cnf(c_241,plain,
    ( X0 != X1
    | X2 != X3
    | k10_relat_1(X0,X2) = k10_relat_1(X1,X3) ),
    theory(equality)).

cnf(c_242,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_4257,plain,
    ( ~ r2_hidden(X0,k10_relat_1(X1,X2))
    | r2_hidden(X3,k10_relat_1(X4,X5))
    | X3 != X0
    | X4 != X1
    | X5 != X2 ),
    inference(resolution,[status(thm)],[c_241,c_242])).

cnf(c_239,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_2810,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,X1)
    | X2 != X0 ),
    inference(resolution,[status(thm)],[c_242,c_239])).

cnf(c_9,plain,
    ( ~ r2_hidden(X0,k1_tarski(X1))
    | X0 = X1 ),
    inference(cnf_transformation,[],[f58])).

cnf(c_5137,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,X1)
    | ~ r2_hidden(X2,k1_tarski(X0)) ),
    inference(resolution,[status(thm)],[c_2810,c_9])).

cnf(c_1,plain,
    ( r2_hidden(sK1(X0,X1,X2),X1)
    | r2_hidden(sK0(X0,X1,X2),X2)
    | ~ v1_relat_1(X0)
    | k10_relat_1(X0,X1) = X2 ),
    inference(cnf_transformation,[],[f37])).

cnf(c_18,negated_conjecture,
    ( r2_hidden(sK7,k2_relat_1(sK8))
    | k10_relat_1(sK8,k1_tarski(sK7)) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f51])).

cnf(c_5912,plain,
    ( r2_hidden(sK1(sK8,k1_tarski(sK7),k1_xboole_0),k1_tarski(sK7))
    | r2_hidden(sK0(sK8,k1_tarski(sK7),k1_xboole_0),k1_xboole_0)
    | r2_hidden(sK7,k2_relat_1(sK8))
    | ~ v1_relat_1(sK8) ),
    inference(resolution,[status(thm)],[c_1,c_18])).

cnf(c_19,negated_conjecture,
    ( v1_relat_1(sK8) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_14,plain,
    ( v1_xboole_0(o_0_0_xboole_0) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_15,plain,
    ( ~ v1_xboole_0(X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f48])).

cnf(c_943,plain,
    ( ~ v1_xboole_0(o_0_0_xboole_0)
    | k1_xboole_0 = o_0_0_xboole_0 ),
    inference(instantiation,[status(thm)],[c_15])).

cnf(c_247,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | X1 != X0 ),
    theory(equality)).

cnf(c_942,plain,
    ( v1_xboole_0(X0)
    | ~ v1_xboole_0(o_0_0_xboole_0)
    | X0 != o_0_0_xboole_0 ),
    inference(instantiation,[status(thm)],[c_247])).

cnf(c_1047,plain,
    ( v1_xboole_0(k1_xboole_0)
    | ~ v1_xboole_0(o_0_0_xboole_0)
    | k1_xboole_0 != o_0_0_xboole_0 ),
    inference(instantiation,[status(thm)],[c_942])).

cnf(c_1238,plain,
    ( ~ r2_hidden(X0,k1_xboole_0)
    | ~ v1_xboole_0(k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_16])).

cnf(c_1890,plain,
    ( ~ r2_hidden(sK0(sK8,k1_tarski(sK7),k1_xboole_0),k1_xboole_0)
    | ~ v1_xboole_0(k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_1238])).

cnf(c_6396,plain,
    ( r2_hidden(sK7,k2_relat_1(sK8))
    | r2_hidden(sK1(sK8,k1_tarski(sK7),k1_xboole_0),k1_tarski(sK7)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_5912,c_19,c_14,c_943,c_1047,c_1890])).

cnf(c_6397,plain,
    ( r2_hidden(sK1(sK8,k1_tarski(sK7),k1_xboole_0),k1_tarski(sK7))
    | r2_hidden(sK7,k2_relat_1(sK8)) ),
    inference(renaming,[status(thm)],[c_6396])).

cnf(c_18461,plain,
    ( r2_hidden(sK1(sK8,k1_tarski(sK7),k1_xboole_0),X0)
    | ~ r2_hidden(sK7,X0)
    | r2_hidden(sK7,k2_relat_1(sK8)) ),
    inference(resolution,[status(thm)],[c_5137,c_6397])).

cnf(c_20869,plain,
    ( r2_hidden(X0,k10_relat_1(X1,X2))
    | ~ r2_hidden(sK7,k10_relat_1(X3,X4))
    | r2_hidden(sK7,k2_relat_1(sK8))
    | X1 != X3
    | X2 != X4
    | X0 != sK1(sK8,k1_tarski(sK7),k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_4257,c_18461])).

cnf(c_701,plain,
    ( v1_xboole_0(o_0_0_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_700,plain,
    ( k1_xboole_0 = X0
    | v1_xboole_0(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_966,plain,
    ( k1_xboole_0 = o_0_0_xboole_0 ),
    inference(superposition,[status(thm)],[c_701,c_700])).

cnf(c_697,plain,
    ( k10_relat_1(sK8,k1_tarski(sK7)) != k1_xboole_0
    | r2_hidden(sK7,k2_relat_1(sK8)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_1060,plain,
    ( k10_relat_1(sK8,k1_tarski(sK7)) != o_0_0_xboole_0
    | r2_hidden(sK7,k2_relat_1(sK8)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_966,c_697])).

cnf(c_1077,plain,
    ( r2_hidden(sK7,k2_relat_1(sK8))
    | k10_relat_1(sK8,k1_tarski(sK7)) != o_0_0_xboole_0 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_1060])).

cnf(c_696,plain,
    ( v1_relat_1(sK8) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_714,plain,
    ( k10_relat_1(X0,X1) = X2
    | r2_hidden(sK1(X0,X1,X2),X1) = iProver_top
    | r2_hidden(sK0(X0,X1,X2),X2) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_7,plain,
    ( r2_hidden(sK3(X0,X1),X1)
    | sK3(X0,X1) = X0
    | k1_tarski(X0) = X1 ),
    inference(cnf_transformation,[],[f41])).

cnf(c_708,plain,
    ( sK3(X0,X1) = X0
    | k1_tarski(X0) = X1
    | r2_hidden(sK3(X0,X1),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_699,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | v1_xboole_0(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_1738,plain,
    ( sK3(X0,X1) = X0
    | k1_tarski(X0) = X1
    | v1_xboole_0(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_708,c_699])).

cnf(c_4216,plain,
    ( sK3(X0,o_0_0_xboole_0) = X0
    | k1_tarski(X0) = o_0_0_xboole_0 ),
    inference(superposition,[status(thm)],[c_701,c_1738])).

cnf(c_6,plain,
    ( ~ r2_hidden(sK3(X0,X1),X1)
    | sK3(X0,X1) != X0
    | k1_tarski(X0) = X1 ),
    inference(cnf_transformation,[],[f42])).

cnf(c_709,plain,
    ( sK3(X0,X1) != X0
    | k1_tarski(X0) = X1
    | r2_hidden(sK3(X0,X1),X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_5608,plain,
    ( k1_tarski(X0) = o_0_0_xboole_0
    | r2_hidden(sK3(X0,o_0_0_xboole_0),o_0_0_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_4216,c_709])).

cnf(c_29,plain,
    ( v1_xboole_0(o_0_0_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_950,plain,
    ( ~ r2_hidden(X0,o_0_0_xboole_0)
    | ~ v1_xboole_0(o_0_0_xboole_0) ),
    inference(instantiation,[status(thm)],[c_16])).

cnf(c_4120,plain,
    ( ~ r2_hidden(sK3(X0,o_0_0_xboole_0),o_0_0_xboole_0)
    | ~ v1_xboole_0(o_0_0_xboole_0) ),
    inference(instantiation,[status(thm)],[c_950])).

cnf(c_4125,plain,
    ( r2_hidden(sK3(X0,o_0_0_xboole_0),o_0_0_xboole_0) != iProver_top
    | v1_xboole_0(o_0_0_xboole_0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4120])).

cnf(c_5618,plain,
    ( r2_hidden(sK3(X0,o_0_0_xboole_0),o_0_0_xboole_0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5608,c_29,c_4125])).

cnf(c_5626,plain,
    ( k1_tarski(X0) = o_0_0_xboole_0
    | r2_hidden(X0,o_0_0_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_4216,c_5618])).

cnf(c_951,plain,
    ( r2_hidden(X0,o_0_0_xboole_0) != iProver_top
    | v1_xboole_0(o_0_0_xboole_0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_950])).

cnf(c_6598,plain,
    ( r2_hidden(X0,o_0_0_xboole_0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5626,c_29,c_951])).

cnf(c_6605,plain,
    ( k10_relat_1(X0,X1) = o_0_0_xboole_0
    | r2_hidden(sK1(X0,X1,o_0_0_xboole_0),X1) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_714,c_6598])).

cnf(c_706,plain,
    ( X0 = X1
    | r2_hidden(X0,k1_tarski(X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_16839,plain,
    ( sK1(X0,k1_tarski(X1),o_0_0_xboole_0) = X1
    | k10_relat_1(X0,k1_tarski(X1)) = o_0_0_xboole_0
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_6605,c_706])).

cnf(c_20443,plain,
    ( sK1(sK8,k1_tarski(X0),o_0_0_xboole_0) = X0
    | k10_relat_1(sK8,k1_tarski(X0)) = o_0_0_xboole_0 ),
    inference(superposition,[status(thm)],[c_696,c_16839])).

cnf(c_2,plain,
    ( r2_hidden(sK0(X0,X1,X2),X2)
    | r2_hidden(k4_tarski(sK0(X0,X1,X2),sK1(X0,X1,X2)),X0)
    | ~ v1_relat_1(X0)
    | k10_relat_1(X0,X1) = X2 ),
    inference(cnf_transformation,[],[f36])).

cnf(c_713,plain,
    ( k10_relat_1(X0,X1) = X2
    | r2_hidden(sK0(X0,X1,X2),X2) = iProver_top
    | r2_hidden(k4_tarski(sK0(X0,X1,X2),sK1(X0,X1,X2)),X0) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_20598,plain,
    ( k10_relat_1(sK8,k1_tarski(X0)) = o_0_0_xboole_0
    | r2_hidden(sK0(sK8,k1_tarski(X0),o_0_0_xboole_0),o_0_0_xboole_0) = iProver_top
    | r2_hidden(k4_tarski(sK0(sK8,k1_tarski(X0),o_0_0_xboole_0),X0),sK8) = iProver_top
    | v1_relat_1(sK8) != iProver_top ),
    inference(superposition,[status(thm)],[c_20443,c_713])).

cnf(c_20,plain,
    ( v1_relat_1(sK8) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_20613,plain,
    ( r2_hidden(k4_tarski(sK0(sK8,k1_tarski(X0),o_0_0_xboole_0),X0),sK8) = iProver_top
    | r2_hidden(sK0(sK8,k1_tarski(X0),o_0_0_xboole_0),o_0_0_xboole_0) = iProver_top
    | k10_relat_1(sK8,k1_tarski(X0)) = o_0_0_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_20598,c_20])).

cnf(c_20614,plain,
    ( k10_relat_1(sK8,k1_tarski(X0)) = o_0_0_xboole_0
    | r2_hidden(sK0(sK8,k1_tarski(X0),o_0_0_xboole_0),o_0_0_xboole_0) = iProver_top
    | r2_hidden(k4_tarski(sK0(sK8,k1_tarski(X0),o_0_0_xboole_0),X0),sK8) = iProver_top ),
    inference(renaming,[status(thm)],[c_20613])).

cnf(c_20622,plain,
    ( k10_relat_1(sK8,k1_tarski(X0)) = o_0_0_xboole_0
    | r2_hidden(k4_tarski(sK0(sK8,k1_tarski(X0),o_0_0_xboole_0),X0),sK8) = iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_20614,c_6598])).

cnf(c_12,plain,
    ( r2_hidden(X0,k2_relat_1(X1))
    | ~ r2_hidden(k4_tarski(X2,X0),X1) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_703,plain,
    ( r2_hidden(X0,k2_relat_1(X1)) = iProver_top
    | r2_hidden(k4_tarski(X2,X0),X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_20630,plain,
    ( k10_relat_1(sK8,k1_tarski(X0)) = o_0_0_xboole_0
    | r2_hidden(X0,k2_relat_1(sK8)) = iProver_top ),
    inference(superposition,[status(thm)],[c_20622,c_703])).

cnf(c_17,negated_conjecture,
    ( ~ r2_hidden(sK7,k2_relat_1(sK8))
    | k10_relat_1(sK8,k1_tarski(sK7)) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f52])).

cnf(c_698,plain,
    ( k10_relat_1(sK8,k1_tarski(sK7)) = k1_xboole_0
    | r2_hidden(sK7,k2_relat_1(sK8)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_1059,plain,
    ( k10_relat_1(sK8,k1_tarski(sK7)) = o_0_0_xboole_0
    | r2_hidden(sK7,k2_relat_1(sK8)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_966,c_698])).

cnf(c_20958,plain,
    ( k10_relat_1(sK8,k1_tarski(sK7)) = o_0_0_xboole_0 ),
    inference(superposition,[status(thm)],[c_20630,c_1059])).

cnf(c_21166,plain,
    ( r2_hidden(sK7,k2_relat_1(sK8)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_20869,c_1077,c_20958])).

cnf(c_21241,plain,
    ( k10_relat_1(sK8,k1_tarski(sK7)) = k1_xboole_0 ),
    inference(backward_subsumption_resolution,[status(thm)],[c_21166,c_17])).

cnf(c_21283,plain,
    ( v1_xboole_0(k10_relat_1(sK8,k1_tarski(sK7)))
    | ~ v1_xboole_0(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_21241,c_247])).

cnf(c_8,plain,
    ( r2_hidden(X0,k1_tarski(X0)) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_3174,plain,
    ( r2_hidden(sK7,k1_tarski(sK7)) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_13,plain,
    ( ~ r2_hidden(X0,k2_relat_1(X1))
    | r2_hidden(k4_tarski(sK6(X1,X0),X0),X1) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_996,plain,
    ( r2_hidden(k4_tarski(sK6(sK8,sK7),sK7),sK8)
    | ~ r2_hidden(sK7,k2_relat_1(sK8)) ),
    inference(instantiation,[status(thm)],[c_13])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_50048,c_40845,c_21283,c_20958,c_3174,c_1077,c_1047,c_996,c_943,c_14,c_19])).


%------------------------------------------------------------------------------
