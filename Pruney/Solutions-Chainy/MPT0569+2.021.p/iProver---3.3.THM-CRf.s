%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:47:30 EST 2020

% Result     : Theorem 7.56s
% Output     : CNFRefutation 7.56s
% Verified   : 
% Statistics : Number of formulae       :  126 ( 628 expanded)
%              Number of clauses        :   66 ( 224 expanded)
%              Number of leaves         :   23 ( 142 expanded)
%              Depth                    :   20
%              Number of atoms          :  411 (2050 expanded)
%              Number of equality atoms :  138 ( 868 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal clause size      :   15 (   2 average)
%              Maximal term depth       :    5 (   1 average)

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
    inference(rectify,[],[f1])).

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

fof(f19,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
     => ( r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ( r2_hidden(sK0(X0,X1),X1)
          & r2_hidden(sK0(X0,X1),X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f14,f19])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f10,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( k1_xboole_0 = k10_relat_1(X1,X0)
      <=> r1_xboole_0(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f11,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => ( k1_xboole_0 = k10_relat_1(X1,X0)
        <=> r1_xboole_0(k2_relat_1(X1),X0) ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f18,plain,(
    ? [X0,X1] :
      ( ( k1_xboole_0 = k10_relat_1(X1,X0)
      <~> r1_xboole_0(k2_relat_1(X1),X0) )
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f36,plain,(
    ? [X0,X1] :
      ( ( ~ r1_xboole_0(k2_relat_1(X1),X0)
        | k1_xboole_0 != k10_relat_1(X1,X0) )
      & ( r1_xboole_0(k2_relat_1(X1),X0)
        | k1_xboole_0 = k10_relat_1(X1,X0) )
      & v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f18])).

fof(f37,plain,(
    ? [X0,X1] :
      ( ( ~ r1_xboole_0(k2_relat_1(X1),X0)
        | k1_xboole_0 != k10_relat_1(X1,X0) )
      & ( r1_xboole_0(k2_relat_1(X1),X0)
        | k1_xboole_0 = k10_relat_1(X1,X0) )
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f36])).

fof(f38,plain,
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

fof(f39,plain,
    ( ( ~ r1_xboole_0(k2_relat_1(sK9),sK8)
      | k1_xboole_0 != k10_relat_1(sK9,sK8) )
    & ( r1_xboole_0(k2_relat_1(sK9),sK8)
      | k1_xboole_0 = k10_relat_1(sK9,sK8) )
    & v1_relat_1(sK9) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8,sK9])],[f37,f38])).

fof(f62,plain,
    ( r1_xboole_0(k2_relat_1(sK9),sK8)
    | k1_xboole_0 = k10_relat_1(sK9,sK8) ),
    inference(cnf_transformation,[],[f39])).

fof(f61,plain,(
    v1_relat_1(sK9) ),
    inference(cnf_transformation,[],[f39])).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
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

fof(f24,plain,(
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
    inference(nnf_transformation,[],[f16])).

fof(f25,plain,(
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
    inference(rectify,[],[f24])).

fof(f28,plain,(
    ! [X6,X1,X0] :
      ( ? [X8] :
          ( r2_hidden(X8,X1)
          & r2_hidden(k4_tarski(X6,X8),X0) )
     => ( r2_hidden(sK4(X0,X1,X6),X1)
        & r2_hidden(k4_tarski(X6,sK4(X0,X1,X6)),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X5] :
          ( r2_hidden(X5,X1)
          & r2_hidden(k4_tarski(X3,X5),X0) )
     => ( r2_hidden(sK3(X0,X1,X2),X1)
        & r2_hidden(k4_tarski(X3,sK3(X0,X1,X2)),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,(
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
              | ~ r2_hidden(k4_tarski(sK2(X0,X1,X2),X4),X0) )
          | ~ r2_hidden(sK2(X0,X1,X2),X2) )
        & ( ? [X5] :
              ( r2_hidden(X5,X1)
              & r2_hidden(k4_tarski(sK2(X0,X1,X2),X5),X0) )
          | r2_hidden(sK2(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k10_relat_1(X0,X1) = X2
            | ( ( ! [X4] :
                    ( ~ r2_hidden(X4,X1)
                    | ~ r2_hidden(k4_tarski(sK2(X0,X1,X2),X4),X0) )
                | ~ r2_hidden(sK2(X0,X1,X2),X2) )
              & ( ( r2_hidden(sK3(X0,X1,X2),X1)
                  & r2_hidden(k4_tarski(sK2(X0,X1,X2),sK3(X0,X1,X2)),X0) )
                | r2_hidden(sK2(X0,X1,X2),X2) ) ) )
          & ( ! [X6] :
                ( ( r2_hidden(X6,X2)
                  | ! [X7] :
                      ( ~ r2_hidden(X7,X1)
                      | ~ r2_hidden(k4_tarski(X6,X7),X0) ) )
                & ( ( r2_hidden(sK4(X0,X1,X6),X1)
                    & r2_hidden(k4_tarski(X6,sK4(X0,X1,X6)),X0) )
                  | ~ r2_hidden(X6,X2) ) )
            | k10_relat_1(X0,X1) != X2 ) )
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f25,f28,f27,f26])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( k10_relat_1(X0,X1) = X2
      | r2_hidden(sK3(X0,X1,X2),X1)
      | r2_hidden(sK2(X0,X1,X2),X2)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k4_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k4_xboole_0(X0,X1) != X0 )
      & ( k4_xboole_0(X0,X1) = X0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f48,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = X0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f49,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k4_xboole_0(X0,X1) != X0 ) ),
    inference(cnf_transformation,[],[f23])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f2])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f13])).

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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f15,f21])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,k3_xboole_0(X0,X1)) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f5,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f47,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ) ),
    inference(definition_unfolding,[],[f44,f47])).

fof(f3,axiom,(
    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f3])).

fof(f66,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) ),
    inference(definition_unfolding,[],[f45,f47])).

fof(f4,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f4])).

fof(f63,plain,
    ( ~ r1_xboole_0(k2_relat_1(sK9),sK8)
    | k1_xboole_0 != k10_relat_1(sK9,sK8) ),
    inference(cnf_transformation,[],[f39])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k10_relat_1(X1,X0) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1] :
      ( k10_relat_1(X1,X0) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X0))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f60,plain,(
    ! [X0,X1] :
      ( k10_relat_1(X1,X0) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X0))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f67,plain,(
    ! [X0,X1] :
      ( k10_relat_1(X1,X0) = k10_relat_1(X1,k4_xboole_0(k2_relat_1(X1),k4_xboole_0(k2_relat_1(X1),X0)))
      | ~ v1_relat_1(X1) ) ),
    inference(definition_unfolding,[],[f60,f47])).

fof(f52,plain,(
    ! [X6,X2,X0,X7,X1] :
      ( r2_hidden(X6,X2)
      | ~ r2_hidden(X7,X1)
      | ~ r2_hidden(k4_tarski(X6,X7),X0)
      | k10_relat_1(X0,X1) != X2
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f68,plain,(
    ! [X6,X0,X7,X1] :
      ( r2_hidden(X6,k10_relat_1(X0,X1))
      | ~ r2_hidden(X7,X1)
      | ~ r2_hidden(k4_tarski(X6,X7),X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f52])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( k2_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X3,X2),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
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

fof(f31,plain,(
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
    inference(rectify,[],[f30])).

fof(f34,plain,(
    ! [X5,X0] :
      ( ? [X7] : r2_hidden(k4_tarski(X7,X5),X0)
     => r2_hidden(k4_tarski(sK7(X0,X5),X5),X0) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] : r2_hidden(k4_tarski(X4,X2),X0)
     => r2_hidden(k4_tarski(sK6(X0,X1),X2),X0) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,(
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

fof(f35,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6,sK7])],[f31,f34,f33,f32])).

fof(f56,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(k4_tarski(sK7(X0,X5),X5),X0)
      | ~ r2_hidden(X5,X1)
      | k2_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f35])).

fof(f72,plain,(
    ! [X0,X5] :
      ( r2_hidden(k4_tarski(sK7(X0,X5),X5),X0)
      | ~ r2_hidden(X5,k2_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f56])).

fof(f40,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK0(X0,X1),X0)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f41,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK0(X0,X1),X1)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

cnf(c_267,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_7405,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(sK7(sK9,sK0(k2_relat_1(sK9),sK8)),k10_relat_1(sK9,sK8))
    | X0 != sK7(sK9,sK0(k2_relat_1(sK9),sK8))
    | X1 != k10_relat_1(sK9,sK8) ),
    inference(instantiation,[status(thm)],[c_267])).

cnf(c_22214,plain,
    ( r2_hidden(sK7(sK9,sK0(k2_relat_1(sK9),sK8)),X0)
    | ~ r2_hidden(sK7(sK9,sK0(k2_relat_1(sK9),sK8)),k10_relat_1(sK9,sK8))
    | X0 != k10_relat_1(sK9,sK8)
    | sK7(sK9,sK0(k2_relat_1(sK9),sK8)) != sK7(sK9,sK0(k2_relat_1(sK9),sK8)) ),
    inference(instantiation,[status(thm)],[c_7405])).

cnf(c_22216,plain,
    ( ~ r2_hidden(sK7(sK9,sK0(k2_relat_1(sK9),sK8)),k10_relat_1(sK9,sK8))
    | r2_hidden(sK7(sK9,sK0(k2_relat_1(sK9),sK8)),k1_xboole_0)
    | sK7(sK9,sK0(k2_relat_1(sK9),sK8)) != sK7(sK9,sK0(k2_relat_1(sK9),sK8))
    | k1_xboole_0 != k10_relat_1(sK9,sK8) ),
    inference(instantiation,[status(thm)],[c_22214])).

cnf(c_0,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X0,X2)
    | ~ r1_xboole_0(X2,X1) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_7410,plain,
    ( ~ r2_hidden(sK7(sK9,sK0(k2_relat_1(sK9),sK8)),X0)
    | ~ r2_hidden(sK7(sK9,sK0(k2_relat_1(sK9),sK8)),k10_relat_1(sK9,sK8))
    | ~ r1_xboole_0(k10_relat_1(sK9,sK8),X0) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_7412,plain,
    ( ~ r2_hidden(sK7(sK9,sK0(k2_relat_1(sK9),sK8)),k10_relat_1(sK9,sK8))
    | ~ r2_hidden(sK7(sK9,sK0(k2_relat_1(sK9),sK8)),k1_xboole_0)
    | ~ r1_xboole_0(k10_relat_1(sK9,sK8),k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_7410])).

cnf(c_265,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_264,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_2128,plain,
    ( X0 != X1
    | X1 = X0 ),
    inference(resolution,[status(thm)],[c_265,c_264])).

cnf(c_21,negated_conjecture,
    ( r1_xboole_0(k2_relat_1(sK9),sK8)
    | k1_xboole_0 = k10_relat_1(sK9,sK8) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_6676,plain,
    ( r1_xboole_0(k2_relat_1(sK9),sK8)
    | k10_relat_1(sK9,sK8) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_2128,c_21])).

cnf(c_22,negated_conjecture,
    ( v1_relat_1(sK9) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_758,plain,
    ( v1_relat_1(sK9) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_10,plain,
    ( r2_hidden(sK3(X0,X1,X2),X1)
    | r2_hidden(sK2(X0,X1,X2),X2)
    | ~ v1_relat_1(X0)
    | k10_relat_1(X0,X1) = X2 ),
    inference(cnf_transformation,[],[f54])).

cnf(c_770,plain,
    ( k10_relat_1(X0,X1) = X2
    | r2_hidden(sK3(X0,X1,X2),X1) = iProver_top
    | r2_hidden(sK2(X0,X1,X2),X2) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_759,plain,
    ( k1_xboole_0 = k10_relat_1(sK9,sK8)
    | r1_xboole_0(k2_relat_1(sK9),sK8) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_8,plain,
    ( ~ r1_xboole_0(X0,X1)
    | k4_xboole_0(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f48])).

cnf(c_772,plain,
    ( k4_xboole_0(X0,X1) = X0
    | r1_xboole_0(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_1030,plain,
    ( k10_relat_1(sK9,sK8) = k1_xboole_0
    | k4_xboole_0(k2_relat_1(sK9),sK8) = k2_relat_1(sK9) ),
    inference(superposition,[status(thm)],[c_759,c_772])).

cnf(c_7,plain,
    ( r1_xboole_0(X0,X1)
    | k4_xboole_0(X0,X1) != X0 ),
    inference(cnf_transformation,[],[f49])).

cnf(c_773,plain,
    ( k4_xboole_0(X0,X1) != X0
    | r1_xboole_0(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_1129,plain,
    ( k10_relat_1(sK9,sK8) = k1_xboole_0
    | r1_xboole_0(k2_relat_1(sK9),sK8) = iProver_top ),
    inference(superposition,[status(thm)],[c_1030,c_773])).

cnf(c_3,plain,
    ( ~ r2_hidden(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2)))
    | ~ r1_xboole_0(X1,X2) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_775,plain,
    ( r2_hidden(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2))) != iProver_top
    | r1_xboole_0(X1,X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_1906,plain,
    ( k10_relat_1(sK9,sK8) = k1_xboole_0
    | r2_hidden(X0,k4_xboole_0(k2_relat_1(sK9),k2_relat_1(sK9))) != iProver_top
    | r1_xboole_0(k2_relat_1(sK9),sK8) != iProver_top ),
    inference(superposition,[status(thm)],[c_1030,c_775])).

cnf(c_5,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f66])).

cnf(c_6,plain,
    ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f46])).

cnf(c_783,plain,
    ( k4_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_5,c_6])).

cnf(c_1910,plain,
    ( k10_relat_1(sK9,sK8) = k1_xboole_0
    | r2_hidden(X0,k1_xboole_0) != iProver_top
    | r1_xboole_0(k2_relat_1(sK9),sK8) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1906,c_783])).

cnf(c_20,negated_conjecture,
    ( ~ r1_xboole_0(k2_relat_1(sK9),sK8)
    | k1_xboole_0 != k10_relat_1(sK9,sK8) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_25,plain,
    ( k1_xboole_0 != k10_relat_1(sK9,sK8)
    | r1_xboole_0(k2_relat_1(sK9),sK8) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_281,plain,
    ( k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_264])).

cnf(c_1726,plain,
    ( k10_relat_1(sK9,sK8) != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = k10_relat_1(sK9,sK8) ),
    inference(instantiation,[status(thm)],[c_265])).

cnf(c_1727,plain,
    ( k10_relat_1(sK9,sK8) != k1_xboole_0
    | k1_xboole_0 = k10_relat_1(sK9,sK8)
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1726])).

cnf(c_2437,plain,
    ( r2_hidden(X0,k1_xboole_0) != iProver_top
    | r1_xboole_0(k2_relat_1(sK9),sK8) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1910,c_25,c_281,c_1727])).

cnf(c_2443,plain,
    ( k10_relat_1(sK9,sK8) = k1_xboole_0
    | r2_hidden(X0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1129,c_2437])).

cnf(c_3883,plain,
    ( k10_relat_1(X0,X1) = k1_xboole_0
    | k10_relat_1(sK9,sK8) = k1_xboole_0
    | r2_hidden(sK3(X0,X1,k1_xboole_0),X1) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_770,c_2443])).

cnf(c_4463,plain,
    ( k10_relat_1(X0,k1_xboole_0) = k1_xboole_0
    | k10_relat_1(sK9,sK8) = k1_xboole_0
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_3883,c_2443])).

cnf(c_4544,plain,
    ( k10_relat_1(sK9,sK8) = k1_xboole_0
    | k10_relat_1(sK9,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_758,c_4463])).

cnf(c_19,plain,
    ( ~ v1_relat_1(X0)
    | k10_relat_1(X0,k4_xboole_0(k2_relat_1(X0),k4_xboole_0(k2_relat_1(X0),X1))) = k10_relat_1(X0,X1) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_761,plain,
    ( k10_relat_1(X0,k4_xboole_0(k2_relat_1(X0),k4_xboole_0(k2_relat_1(X0),X1))) = k10_relat_1(X0,X1)
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_1255,plain,
    ( k10_relat_1(sK9,k4_xboole_0(k2_relat_1(sK9),k4_xboole_0(k2_relat_1(sK9),X0))) = k10_relat_1(sK9,X0) ),
    inference(superposition,[status(thm)],[c_758,c_761])).

cnf(c_1689,plain,
    ( k10_relat_1(sK9,k4_xboole_0(k2_relat_1(sK9),k2_relat_1(sK9))) = k10_relat_1(sK9,sK8)
    | k10_relat_1(sK9,sK8) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1030,c_1255])).

cnf(c_1692,plain,
    ( k10_relat_1(sK9,sK8) = k1_xboole_0
    | k10_relat_1(sK9,k1_xboole_0) = k10_relat_1(sK9,sK8) ),
    inference(demodulation,[status(thm)],[c_1689,c_783])).

cnf(c_760,plain,
    ( k1_xboole_0 != k10_relat_1(sK9,sK8)
    | r1_xboole_0(k2_relat_1(sK9),sK8) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_1750,plain,
    ( k10_relat_1(sK9,sK8) = k1_xboole_0
    | k10_relat_1(sK9,k1_xboole_0) != k1_xboole_0
    | r1_xboole_0(k2_relat_1(sK9),sK8) != iProver_top ),
    inference(superposition,[status(thm)],[c_1692,c_760])).

cnf(c_4629,plain,
    ( k10_relat_1(sK9,sK8) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_4544,c_1129,c_1750])).

cnf(c_7303,plain,
    ( k10_relat_1(sK9,sK8) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_6676,c_1129,c_1750,c_4544])).

cnf(c_266,plain,
    ( ~ r1_xboole_0(X0,X1)
    | r1_xboole_0(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_2300,plain,
    ( ~ r1_xboole_0(X0,X1)
    | r1_xboole_0(X2,X1)
    | X2 != X0 ),
    inference(resolution,[status(thm)],[c_266,c_264])).

cnf(c_7311,plain,
    ( r1_xboole_0(k10_relat_1(sK9,sK8),X0)
    | ~ r1_xboole_0(k1_xboole_0,X0) ),
    inference(resolution,[status(thm)],[c_7303,c_2300])).

cnf(c_7315,plain,
    ( r1_xboole_0(k10_relat_1(sK9,sK8),k1_xboole_0)
    | ~ r1_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_7311])).

cnf(c_3070,plain,
    ( sK7(sK9,sK0(k2_relat_1(sK9),sK8)) = sK7(sK9,sK0(k2_relat_1(sK9),sK8)) ),
    inference(instantiation,[status(thm)],[c_264])).

cnf(c_12,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,k10_relat_1(X3,X1))
    | ~ r2_hidden(k4_tarski(X2,X0),X3)
    | ~ v1_relat_1(X3) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_1202,plain,
    ( r2_hidden(sK7(sK9,sK0(k2_relat_1(sK9),sK8)),k10_relat_1(sK9,X0))
    | ~ r2_hidden(k4_tarski(sK7(sK9,sK0(k2_relat_1(sK9),sK8)),sK0(k2_relat_1(sK9),sK8)),sK9)
    | ~ r2_hidden(sK0(k2_relat_1(sK9),sK8),X0)
    | ~ v1_relat_1(sK9) ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_1563,plain,
    ( r2_hidden(sK7(sK9,sK0(k2_relat_1(sK9),sK8)),k10_relat_1(sK9,sK8))
    | ~ r2_hidden(k4_tarski(sK7(sK9,sK0(k2_relat_1(sK9),sK8)),sK0(k2_relat_1(sK9),sK8)),sK9)
    | ~ r2_hidden(sK0(k2_relat_1(sK9),sK8),sK8)
    | ~ v1_relat_1(sK9) ),
    inference(instantiation,[status(thm)],[c_1202])).

cnf(c_18,plain,
    ( ~ r2_hidden(X0,k2_relat_1(X1))
    | r2_hidden(k4_tarski(sK7(X1,X0),X0),X1) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_1071,plain,
    ( r2_hidden(k4_tarski(sK7(sK9,sK0(k2_relat_1(sK9),sK8)),sK0(k2_relat_1(sK9),sK8)),sK9)
    | ~ r2_hidden(sK0(k2_relat_1(sK9),sK8),k2_relat_1(sK9)) ),
    inference(instantiation,[status(thm)],[c_18])).

cnf(c_2,plain,
    ( r2_hidden(sK0(X0,X1),X0)
    | r1_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_963,plain,
    ( r2_hidden(sK0(k2_relat_1(sK9),sK8),k2_relat_1(sK9))
    | r1_xboole_0(k2_relat_1(sK9),sK8) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_1,plain,
    ( r2_hidden(sK0(X0,X1),X1)
    | r1_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_960,plain,
    ( r2_hidden(sK0(k2_relat_1(sK9),sK8),sK8)
    | r1_xboole_0(k2_relat_1(sK9),sK8) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_65,plain,
    ( k4_xboole_0(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_63,plain,
    ( r1_xboole_0(k1_xboole_0,k1_xboole_0)
    | k4_xboole_0(k1_xboole_0,k1_xboole_0) != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_22216,c_7412,c_7315,c_4629,c_3070,c_1727,c_1563,c_1071,c_963,c_960,c_281,c_65,c_63,c_20,c_22])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.19/0.34  % CPULimit   : 60
% 0.19/0.34  % WCLimit    : 600
% 0.19/0.34  % DateTime   : Tue Dec  1 14:44:19 EST 2020
% 0.19/0.34  % CPUTime    : 
% 0.19/0.34  % Running in FOF mode
% 7.56/1.49  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.56/1.49  
% 7.56/1.49  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.56/1.49  
% 7.56/1.49  ------  iProver source info
% 7.56/1.49  
% 7.56/1.49  git: date: 2020-06-30 10:37:57 +0100
% 7.56/1.49  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.56/1.49  git: non_committed_changes: false
% 7.56/1.49  git: last_make_outside_of_git: false
% 7.56/1.49  
% 7.56/1.49  ------ 
% 7.56/1.49  ------ Parsing...
% 7.56/1.49  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.56/1.49  
% 7.56/1.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e 
% 7.56/1.49  
% 7.56/1.49  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.56/1.49  
% 7.56/1.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.56/1.49  ------ Proving...
% 7.56/1.49  ------ Problem Properties 
% 7.56/1.49  
% 7.56/1.49  
% 7.56/1.49  clauses                                 23
% 7.56/1.49  conjectures                             3
% 7.56/1.49  EPR                                     2
% 7.56/1.49  Horn                                    16
% 7.56/1.49  unary                                   3
% 7.56/1.49  binary                                  11
% 7.56/1.49  lits                                    57
% 7.56/1.49  lits eq                                 12
% 7.56/1.49  fd_pure                                 0
% 7.56/1.49  fd_pseudo                               0
% 7.56/1.49  fd_cond                                 0
% 7.56/1.49  fd_pseudo_cond                          5
% 7.56/1.49  AC symbols                              0
% 7.56/1.49  
% 7.56/1.49  ------ Input Options Time Limit: Unbounded
% 7.56/1.49  
% 7.56/1.49  
% 7.56/1.49  ------ 
% 7.56/1.49  Current options:
% 7.56/1.49  ------ 
% 7.56/1.49  
% 7.56/1.49  
% 7.56/1.49  
% 7.56/1.49  
% 7.56/1.49  ------ Proving...
% 7.56/1.49  
% 7.56/1.49  
% 7.56/1.49  % SZS status Theorem for theBenchmark.p
% 7.56/1.49  
% 7.56/1.49  % SZS output start CNFRefutation for theBenchmark.p
% 7.56/1.49  
% 7.56/1.49  fof(f1,axiom,(
% 7.56/1.49    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 7.56/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.56/1.49  
% 7.56/1.49  fof(f12,plain,(
% 7.56/1.49    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 7.56/1.49    inference(rectify,[],[f1])).
% 7.56/1.49  
% 7.56/1.49  fof(f14,plain,(
% 7.56/1.49    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 7.56/1.49    inference(ennf_transformation,[],[f12])).
% 7.56/1.49  
% 7.56/1.49  fof(f19,plain,(
% 7.56/1.49    ! [X1,X0] : (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) => (r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 7.56/1.49    introduced(choice_axiom,[])).
% 7.56/1.49  
% 7.56/1.49  fof(f20,plain,(
% 7.56/1.49    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & ((r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)) | r1_xboole_0(X0,X1)))),
% 7.56/1.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f14,f19])).
% 7.56/1.49  
% 7.56/1.49  fof(f42,plain,(
% 7.56/1.49    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) )),
% 7.56/1.49    inference(cnf_transformation,[],[f20])).
% 7.56/1.49  
% 7.56/1.49  fof(f10,conjecture,(
% 7.56/1.49    ! [X0,X1] : (v1_relat_1(X1) => (k1_xboole_0 = k10_relat_1(X1,X0) <=> r1_xboole_0(k2_relat_1(X1),X0)))),
% 7.56/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.56/1.49  
% 7.56/1.49  fof(f11,negated_conjecture,(
% 7.56/1.49    ~! [X0,X1] : (v1_relat_1(X1) => (k1_xboole_0 = k10_relat_1(X1,X0) <=> r1_xboole_0(k2_relat_1(X1),X0)))),
% 7.56/1.49    inference(negated_conjecture,[],[f10])).
% 7.56/1.49  
% 7.56/1.49  fof(f18,plain,(
% 7.56/1.49    ? [X0,X1] : ((k1_xboole_0 = k10_relat_1(X1,X0) <~> r1_xboole_0(k2_relat_1(X1),X0)) & v1_relat_1(X1))),
% 7.56/1.49    inference(ennf_transformation,[],[f11])).
% 7.56/1.49  
% 7.56/1.49  fof(f36,plain,(
% 7.56/1.49    ? [X0,X1] : (((~r1_xboole_0(k2_relat_1(X1),X0) | k1_xboole_0 != k10_relat_1(X1,X0)) & (r1_xboole_0(k2_relat_1(X1),X0) | k1_xboole_0 = k10_relat_1(X1,X0))) & v1_relat_1(X1))),
% 7.56/1.49    inference(nnf_transformation,[],[f18])).
% 7.56/1.49  
% 7.56/1.49  fof(f37,plain,(
% 7.56/1.49    ? [X0,X1] : ((~r1_xboole_0(k2_relat_1(X1),X0) | k1_xboole_0 != k10_relat_1(X1,X0)) & (r1_xboole_0(k2_relat_1(X1),X0) | k1_xboole_0 = k10_relat_1(X1,X0)) & v1_relat_1(X1))),
% 7.56/1.49    inference(flattening,[],[f36])).
% 7.56/1.49  
% 7.56/1.49  fof(f38,plain,(
% 7.56/1.49    ? [X0,X1] : ((~r1_xboole_0(k2_relat_1(X1),X0) | k1_xboole_0 != k10_relat_1(X1,X0)) & (r1_xboole_0(k2_relat_1(X1),X0) | k1_xboole_0 = k10_relat_1(X1,X0)) & v1_relat_1(X1)) => ((~r1_xboole_0(k2_relat_1(sK9),sK8) | k1_xboole_0 != k10_relat_1(sK9,sK8)) & (r1_xboole_0(k2_relat_1(sK9),sK8) | k1_xboole_0 = k10_relat_1(sK9,sK8)) & v1_relat_1(sK9))),
% 7.56/1.49    introduced(choice_axiom,[])).
% 7.56/1.49  
% 7.56/1.49  fof(f39,plain,(
% 7.56/1.49    (~r1_xboole_0(k2_relat_1(sK9),sK8) | k1_xboole_0 != k10_relat_1(sK9,sK8)) & (r1_xboole_0(k2_relat_1(sK9),sK8) | k1_xboole_0 = k10_relat_1(sK9,sK8)) & v1_relat_1(sK9)),
% 7.56/1.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8,sK9])],[f37,f38])).
% 7.56/1.49  
% 7.56/1.49  fof(f62,plain,(
% 7.56/1.49    r1_xboole_0(k2_relat_1(sK9),sK8) | k1_xboole_0 = k10_relat_1(sK9,sK8)),
% 7.56/1.49    inference(cnf_transformation,[],[f39])).
% 7.56/1.49  
% 7.56/1.49  fof(f61,plain,(
% 7.56/1.49    v1_relat_1(sK9)),
% 7.56/1.49    inference(cnf_transformation,[],[f39])).
% 7.56/1.49  
% 7.56/1.49  fof(f7,axiom,(
% 7.56/1.49    ! [X0] : (v1_relat_1(X0) => ! [X1,X2] : (k10_relat_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X3,X4),X0)))))),
% 7.56/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.56/1.49  
% 7.56/1.49  fof(f16,plain,(
% 7.56/1.49    ! [X0] : (! [X1,X2] : (k10_relat_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X3,X4),X0)))) | ~v1_relat_1(X0))),
% 7.56/1.49    inference(ennf_transformation,[],[f7])).
% 7.56/1.49  
% 7.56/1.49  fof(f24,plain,(
% 7.56/1.49    ! [X0] : (! [X1,X2] : ((k10_relat_1(X0,X1) = X2 | ? [X3] : ((! [X4] : (~r2_hidden(X4,X1) | ~r2_hidden(k4_tarski(X3,X4),X0)) | ~r2_hidden(X3,X2)) & (? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X3,X4),X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ! [X4] : (~r2_hidden(X4,X1) | ~r2_hidden(k4_tarski(X3,X4),X0))) & (? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X3,X4),X0)) | ~r2_hidden(X3,X2))) | k10_relat_1(X0,X1) != X2)) | ~v1_relat_1(X0))),
% 7.56/1.49    inference(nnf_transformation,[],[f16])).
% 7.56/1.49  
% 7.56/1.49  fof(f25,plain,(
% 7.56/1.49    ! [X0] : (! [X1,X2] : ((k10_relat_1(X0,X1) = X2 | ? [X3] : ((! [X4] : (~r2_hidden(X4,X1) | ~r2_hidden(k4_tarski(X3,X4),X0)) | ~r2_hidden(X3,X2)) & (? [X5] : (r2_hidden(X5,X1) & r2_hidden(k4_tarski(X3,X5),X0)) | r2_hidden(X3,X2)))) & (! [X6] : ((r2_hidden(X6,X2) | ! [X7] : (~r2_hidden(X7,X1) | ~r2_hidden(k4_tarski(X6,X7),X0))) & (? [X8] : (r2_hidden(X8,X1) & r2_hidden(k4_tarski(X6,X8),X0)) | ~r2_hidden(X6,X2))) | k10_relat_1(X0,X1) != X2)) | ~v1_relat_1(X0))),
% 7.56/1.49    inference(rectify,[],[f24])).
% 7.56/1.49  
% 7.56/1.49  fof(f28,plain,(
% 7.56/1.49    ! [X6,X1,X0] : (? [X8] : (r2_hidden(X8,X1) & r2_hidden(k4_tarski(X6,X8),X0)) => (r2_hidden(sK4(X0,X1,X6),X1) & r2_hidden(k4_tarski(X6,sK4(X0,X1,X6)),X0)))),
% 7.56/1.49    introduced(choice_axiom,[])).
% 7.56/1.49  
% 7.56/1.49  fof(f27,plain,(
% 7.56/1.49    ( ! [X3] : (! [X2,X1,X0] : (? [X5] : (r2_hidden(X5,X1) & r2_hidden(k4_tarski(X3,X5),X0)) => (r2_hidden(sK3(X0,X1,X2),X1) & r2_hidden(k4_tarski(X3,sK3(X0,X1,X2)),X0)))) )),
% 7.56/1.49    introduced(choice_axiom,[])).
% 7.56/1.49  
% 7.56/1.49  fof(f26,plain,(
% 7.56/1.49    ! [X2,X1,X0] : (? [X3] : ((! [X4] : (~r2_hidden(X4,X1) | ~r2_hidden(k4_tarski(X3,X4),X0)) | ~r2_hidden(X3,X2)) & (? [X5] : (r2_hidden(X5,X1) & r2_hidden(k4_tarski(X3,X5),X0)) | r2_hidden(X3,X2))) => ((! [X4] : (~r2_hidden(X4,X1) | ~r2_hidden(k4_tarski(sK2(X0,X1,X2),X4),X0)) | ~r2_hidden(sK2(X0,X1,X2),X2)) & (? [X5] : (r2_hidden(X5,X1) & r2_hidden(k4_tarski(sK2(X0,X1,X2),X5),X0)) | r2_hidden(sK2(X0,X1,X2),X2))))),
% 7.56/1.49    introduced(choice_axiom,[])).
% 7.56/1.49  
% 7.56/1.49  fof(f29,plain,(
% 7.56/1.49    ! [X0] : (! [X1,X2] : ((k10_relat_1(X0,X1) = X2 | ((! [X4] : (~r2_hidden(X4,X1) | ~r2_hidden(k4_tarski(sK2(X0,X1,X2),X4),X0)) | ~r2_hidden(sK2(X0,X1,X2),X2)) & ((r2_hidden(sK3(X0,X1,X2),X1) & r2_hidden(k4_tarski(sK2(X0,X1,X2),sK3(X0,X1,X2)),X0)) | r2_hidden(sK2(X0,X1,X2),X2)))) & (! [X6] : ((r2_hidden(X6,X2) | ! [X7] : (~r2_hidden(X7,X1) | ~r2_hidden(k4_tarski(X6,X7),X0))) & ((r2_hidden(sK4(X0,X1,X6),X1) & r2_hidden(k4_tarski(X6,sK4(X0,X1,X6)),X0)) | ~r2_hidden(X6,X2))) | k10_relat_1(X0,X1) != X2)) | ~v1_relat_1(X0))),
% 7.56/1.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f25,f28,f27,f26])).
% 7.56/1.49  
% 7.56/1.49  fof(f54,plain,(
% 7.56/1.49    ( ! [X2,X0,X1] : (k10_relat_1(X0,X1) = X2 | r2_hidden(sK3(X0,X1,X2),X1) | r2_hidden(sK2(X0,X1,X2),X2) | ~v1_relat_1(X0)) )),
% 7.56/1.49    inference(cnf_transformation,[],[f29])).
% 7.56/1.49  
% 7.56/1.49  fof(f6,axiom,(
% 7.56/1.49    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k4_xboole_0(X0,X1) = X0)),
% 7.56/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.56/1.49  
% 7.56/1.49  fof(f23,plain,(
% 7.56/1.49    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) != X0) & (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)))),
% 7.56/1.49    inference(nnf_transformation,[],[f6])).
% 7.56/1.49  
% 7.56/1.49  fof(f48,plain,(
% 7.56/1.49    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)) )),
% 7.56/1.49    inference(cnf_transformation,[],[f23])).
% 7.56/1.49  
% 7.56/1.49  fof(f49,plain,(
% 7.56/1.49    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) != X0) )),
% 7.56/1.49    inference(cnf_transformation,[],[f23])).
% 7.56/1.49  
% 7.56/1.49  fof(f2,axiom,(
% 7.56/1.49    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 7.56/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.56/1.49  
% 7.56/1.49  fof(f13,plain,(
% 7.56/1.49    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X3] : ~r2_hidden(X3,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 7.56/1.49    inference(rectify,[],[f2])).
% 7.56/1.49  
% 7.56/1.49  fof(f15,plain,(
% 7.56/1.49    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 7.56/1.49    inference(ennf_transformation,[],[f13])).
% 7.56/1.49  
% 7.56/1.49  fof(f21,plain,(
% 7.56/1.49    ! [X1,X0] : (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) => r2_hidden(sK1(X0,X1),k3_xboole_0(X0,X1)))),
% 7.56/1.49    introduced(choice_axiom,[])).
% 7.56/1.49  
% 7.56/1.49  fof(f22,plain,(
% 7.56/1.49    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (r2_hidden(sK1(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 7.56/1.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f15,f21])).
% 7.56/1.49  
% 7.56/1.49  fof(f44,plain,(
% 7.56/1.49    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,k3_xboole_0(X0,X1))) )),
% 7.56/1.49    inference(cnf_transformation,[],[f22])).
% 7.56/1.49  
% 7.56/1.49  fof(f5,axiom,(
% 7.56/1.49    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 7.56/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.56/1.49  
% 7.56/1.49  fof(f47,plain,(
% 7.56/1.49    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 7.56/1.49    inference(cnf_transformation,[],[f5])).
% 7.56/1.49  
% 7.56/1.49  fof(f64,plain,(
% 7.56/1.49    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 7.56/1.49    inference(definition_unfolding,[],[f44,f47])).
% 7.56/1.49  
% 7.56/1.49  fof(f3,axiom,(
% 7.56/1.49    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0),
% 7.56/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.56/1.49  
% 7.56/1.49  fof(f45,plain,(
% 7.56/1.49    ( ! [X0] : (k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0) )),
% 7.56/1.49    inference(cnf_transformation,[],[f3])).
% 7.56/1.49  
% 7.56/1.49  fof(f66,plain,(
% 7.56/1.49    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0))) )),
% 7.56/1.49    inference(definition_unfolding,[],[f45,f47])).
% 7.56/1.49  
% 7.56/1.49  fof(f4,axiom,(
% 7.56/1.49    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 7.56/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.56/1.49  
% 7.56/1.49  fof(f46,plain,(
% 7.56/1.49    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 7.56/1.49    inference(cnf_transformation,[],[f4])).
% 7.56/1.49  
% 7.56/1.49  fof(f63,plain,(
% 7.56/1.49    ~r1_xboole_0(k2_relat_1(sK9),sK8) | k1_xboole_0 != k10_relat_1(sK9,sK8)),
% 7.56/1.49    inference(cnf_transformation,[],[f39])).
% 7.56/1.49  
% 7.56/1.49  fof(f9,axiom,(
% 7.56/1.49    ! [X0,X1] : (v1_relat_1(X1) => k10_relat_1(X1,X0) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X0)))),
% 7.56/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.56/1.49  
% 7.56/1.49  fof(f17,plain,(
% 7.56/1.49    ! [X0,X1] : (k10_relat_1(X1,X0) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 7.56/1.49    inference(ennf_transformation,[],[f9])).
% 7.56/1.49  
% 7.56/1.49  fof(f60,plain,(
% 7.56/1.49    ( ! [X0,X1] : (k10_relat_1(X1,X0) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X0)) | ~v1_relat_1(X1)) )),
% 7.56/1.49    inference(cnf_transformation,[],[f17])).
% 7.56/1.49  
% 7.56/1.49  fof(f67,plain,(
% 7.56/1.49    ( ! [X0,X1] : (k10_relat_1(X1,X0) = k10_relat_1(X1,k4_xboole_0(k2_relat_1(X1),k4_xboole_0(k2_relat_1(X1),X0))) | ~v1_relat_1(X1)) )),
% 7.56/1.49    inference(definition_unfolding,[],[f60,f47])).
% 7.56/1.49  
% 7.56/1.49  fof(f52,plain,(
% 7.56/1.49    ( ! [X6,X2,X0,X7,X1] : (r2_hidden(X6,X2) | ~r2_hidden(X7,X1) | ~r2_hidden(k4_tarski(X6,X7),X0) | k10_relat_1(X0,X1) != X2 | ~v1_relat_1(X0)) )),
% 7.56/1.49    inference(cnf_transformation,[],[f29])).
% 7.56/1.49  
% 7.56/1.49  fof(f68,plain,(
% 7.56/1.49    ( ! [X6,X0,X7,X1] : (r2_hidden(X6,k10_relat_1(X0,X1)) | ~r2_hidden(X7,X1) | ~r2_hidden(k4_tarski(X6,X7),X0) | ~v1_relat_1(X0)) )),
% 7.56/1.49    inference(equality_resolution,[],[f52])).
% 7.56/1.49  
% 7.56/1.49  fof(f8,axiom,(
% 7.56/1.49    ! [X0,X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : r2_hidden(k4_tarski(X3,X2),X0)))),
% 7.56/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.56/1.49  
% 7.56/1.49  fof(f30,plain,(
% 7.56/1.49    ! [X0,X1] : ((k2_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1)) & (? [X3] : r2_hidden(k4_tarski(X3,X2),X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0)) & (? [X3] : r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1))) | k2_relat_1(X0) != X1))),
% 7.56/1.49    inference(nnf_transformation,[],[f8])).
% 7.56/1.49  
% 7.56/1.49  fof(f31,plain,(
% 7.56/1.49    ! [X0,X1] : ((k2_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X4,X2),X0) | r2_hidden(X2,X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X6,X5),X0)) & (? [X7] : r2_hidden(k4_tarski(X7,X5),X0) | ~r2_hidden(X5,X1))) | k2_relat_1(X0) != X1))),
% 7.56/1.49    inference(rectify,[],[f30])).
% 7.56/1.49  
% 7.56/1.49  fof(f34,plain,(
% 7.56/1.49    ! [X5,X0] : (? [X7] : r2_hidden(k4_tarski(X7,X5),X0) => r2_hidden(k4_tarski(sK7(X0,X5),X5),X0))),
% 7.56/1.49    introduced(choice_axiom,[])).
% 7.56/1.49  
% 7.56/1.49  fof(f33,plain,(
% 7.56/1.49    ( ! [X2] : (! [X1,X0] : (? [X4] : r2_hidden(k4_tarski(X4,X2),X0) => r2_hidden(k4_tarski(sK6(X0,X1),X2),X0))) )),
% 7.56/1.49    introduced(choice_axiom,[])).
% 7.56/1.49  
% 7.56/1.49  fof(f32,plain,(
% 7.56/1.49    ! [X1,X0] : (? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X4,X2),X0) | r2_hidden(X2,X1))) => ((! [X3] : ~r2_hidden(k4_tarski(X3,sK5(X0,X1)),X0) | ~r2_hidden(sK5(X0,X1),X1)) & (? [X4] : r2_hidden(k4_tarski(X4,sK5(X0,X1)),X0) | r2_hidden(sK5(X0,X1),X1))))),
% 7.56/1.49    introduced(choice_axiom,[])).
% 7.56/1.49  
% 7.56/1.49  fof(f35,plain,(
% 7.56/1.49    ! [X0,X1] : ((k2_relat_1(X0) = X1 | ((! [X3] : ~r2_hidden(k4_tarski(X3,sK5(X0,X1)),X0) | ~r2_hidden(sK5(X0,X1),X1)) & (r2_hidden(k4_tarski(sK6(X0,X1),sK5(X0,X1)),X0) | r2_hidden(sK5(X0,X1),X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X6,X5),X0)) & (r2_hidden(k4_tarski(sK7(X0,X5),X5),X0) | ~r2_hidden(X5,X1))) | k2_relat_1(X0) != X1))),
% 7.56/1.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6,sK7])],[f31,f34,f33,f32])).
% 7.56/1.49  
% 7.56/1.49  fof(f56,plain,(
% 7.56/1.49    ( ! [X0,X5,X1] : (r2_hidden(k4_tarski(sK7(X0,X5),X5),X0) | ~r2_hidden(X5,X1) | k2_relat_1(X0) != X1) )),
% 7.56/1.49    inference(cnf_transformation,[],[f35])).
% 7.56/1.49  
% 7.56/1.49  fof(f72,plain,(
% 7.56/1.49    ( ! [X0,X5] : (r2_hidden(k4_tarski(sK7(X0,X5),X5),X0) | ~r2_hidden(X5,k2_relat_1(X0))) )),
% 7.56/1.49    inference(equality_resolution,[],[f56])).
% 7.56/1.49  
% 7.56/1.49  fof(f40,plain,(
% 7.56/1.49    ( ! [X0,X1] : (r2_hidden(sK0(X0,X1),X0) | r1_xboole_0(X0,X1)) )),
% 7.56/1.49    inference(cnf_transformation,[],[f20])).
% 7.56/1.49  
% 7.56/1.49  fof(f41,plain,(
% 7.56/1.49    ( ! [X0,X1] : (r2_hidden(sK0(X0,X1),X1) | r1_xboole_0(X0,X1)) )),
% 7.56/1.49    inference(cnf_transformation,[],[f20])).
% 7.56/1.49  
% 7.56/1.49  cnf(c_267,plain,
% 7.56/1.49      ( ~ r2_hidden(X0,X1) | r2_hidden(X2,X3) | X2 != X0 | X3 != X1 ),
% 7.56/1.49      theory(equality) ).
% 7.56/1.49  
% 7.56/1.49  cnf(c_7405,plain,
% 7.56/1.49      ( r2_hidden(X0,X1)
% 7.56/1.49      | ~ r2_hidden(sK7(sK9,sK0(k2_relat_1(sK9),sK8)),k10_relat_1(sK9,sK8))
% 7.56/1.49      | X0 != sK7(sK9,sK0(k2_relat_1(sK9),sK8))
% 7.56/1.49      | X1 != k10_relat_1(sK9,sK8) ),
% 7.56/1.49      inference(instantiation,[status(thm)],[c_267]) ).
% 7.56/1.49  
% 7.56/1.49  cnf(c_22214,plain,
% 7.56/1.49      ( r2_hidden(sK7(sK9,sK0(k2_relat_1(sK9),sK8)),X0)
% 7.56/1.49      | ~ r2_hidden(sK7(sK9,sK0(k2_relat_1(sK9),sK8)),k10_relat_1(sK9,sK8))
% 7.56/1.49      | X0 != k10_relat_1(sK9,sK8)
% 7.56/1.49      | sK7(sK9,sK0(k2_relat_1(sK9),sK8)) != sK7(sK9,sK0(k2_relat_1(sK9),sK8)) ),
% 7.56/1.49      inference(instantiation,[status(thm)],[c_7405]) ).
% 7.56/1.49  
% 7.56/1.49  cnf(c_22216,plain,
% 7.56/1.49      ( ~ r2_hidden(sK7(sK9,sK0(k2_relat_1(sK9),sK8)),k10_relat_1(sK9,sK8))
% 7.56/1.49      | r2_hidden(sK7(sK9,sK0(k2_relat_1(sK9),sK8)),k1_xboole_0)
% 7.56/1.49      | sK7(sK9,sK0(k2_relat_1(sK9),sK8)) != sK7(sK9,sK0(k2_relat_1(sK9),sK8))
% 7.56/1.49      | k1_xboole_0 != k10_relat_1(sK9,sK8) ),
% 7.56/1.49      inference(instantiation,[status(thm)],[c_22214]) ).
% 7.56/1.49  
% 7.56/1.49  cnf(c_0,plain,
% 7.56/1.49      ( ~ r2_hidden(X0,X1) | ~ r2_hidden(X0,X2) | ~ r1_xboole_0(X2,X1) ),
% 7.56/1.49      inference(cnf_transformation,[],[f42]) ).
% 7.56/1.49  
% 7.56/1.49  cnf(c_7410,plain,
% 7.56/1.49      ( ~ r2_hidden(sK7(sK9,sK0(k2_relat_1(sK9),sK8)),X0)
% 7.56/1.49      | ~ r2_hidden(sK7(sK9,sK0(k2_relat_1(sK9),sK8)),k10_relat_1(sK9,sK8))
% 7.56/1.49      | ~ r1_xboole_0(k10_relat_1(sK9,sK8),X0) ),
% 7.56/1.49      inference(instantiation,[status(thm)],[c_0]) ).
% 7.56/1.49  
% 7.56/1.49  cnf(c_7412,plain,
% 7.56/1.49      ( ~ r2_hidden(sK7(sK9,sK0(k2_relat_1(sK9),sK8)),k10_relat_1(sK9,sK8))
% 7.56/1.49      | ~ r2_hidden(sK7(sK9,sK0(k2_relat_1(sK9),sK8)),k1_xboole_0)
% 7.56/1.49      | ~ r1_xboole_0(k10_relat_1(sK9,sK8),k1_xboole_0) ),
% 7.56/1.49      inference(instantiation,[status(thm)],[c_7410]) ).
% 7.56/1.49  
% 7.56/1.49  cnf(c_265,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 7.56/1.49  
% 7.56/1.49  cnf(c_264,plain,( X0 = X0 ),theory(equality) ).
% 7.56/1.49  
% 7.56/1.49  cnf(c_2128,plain,
% 7.56/1.49      ( X0 != X1 | X1 = X0 ),
% 7.56/1.49      inference(resolution,[status(thm)],[c_265,c_264]) ).
% 7.56/1.49  
% 7.56/1.49  cnf(c_21,negated_conjecture,
% 7.56/1.49      ( r1_xboole_0(k2_relat_1(sK9),sK8)
% 7.56/1.49      | k1_xboole_0 = k10_relat_1(sK9,sK8) ),
% 7.56/1.49      inference(cnf_transformation,[],[f62]) ).
% 7.56/1.49  
% 7.56/1.49  cnf(c_6676,plain,
% 7.56/1.49      ( r1_xboole_0(k2_relat_1(sK9),sK8)
% 7.56/1.49      | k10_relat_1(sK9,sK8) = k1_xboole_0 ),
% 7.56/1.49      inference(resolution,[status(thm)],[c_2128,c_21]) ).
% 7.56/1.49  
% 7.56/1.49  cnf(c_22,negated_conjecture,
% 7.56/1.49      ( v1_relat_1(sK9) ),
% 7.56/1.49      inference(cnf_transformation,[],[f61]) ).
% 7.56/1.49  
% 7.56/1.49  cnf(c_758,plain,
% 7.56/1.49      ( v1_relat_1(sK9) = iProver_top ),
% 7.56/1.49      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 7.56/1.49  
% 7.56/1.49  cnf(c_10,plain,
% 7.56/1.49      ( r2_hidden(sK3(X0,X1,X2),X1)
% 7.56/1.49      | r2_hidden(sK2(X0,X1,X2),X2)
% 7.56/1.49      | ~ v1_relat_1(X0)
% 7.56/1.49      | k10_relat_1(X0,X1) = X2 ),
% 7.56/1.49      inference(cnf_transformation,[],[f54]) ).
% 7.56/1.49  
% 7.56/1.49  cnf(c_770,plain,
% 7.56/1.49      ( k10_relat_1(X0,X1) = X2
% 7.56/1.49      | r2_hidden(sK3(X0,X1,X2),X1) = iProver_top
% 7.56/1.49      | r2_hidden(sK2(X0,X1,X2),X2) = iProver_top
% 7.56/1.49      | v1_relat_1(X0) != iProver_top ),
% 7.56/1.49      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 7.56/1.49  
% 7.56/1.49  cnf(c_759,plain,
% 7.56/1.49      ( k1_xboole_0 = k10_relat_1(sK9,sK8)
% 7.56/1.49      | r1_xboole_0(k2_relat_1(sK9),sK8) = iProver_top ),
% 7.56/1.49      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 7.56/1.49  
% 7.56/1.49  cnf(c_8,plain,
% 7.56/1.49      ( ~ r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) = X0 ),
% 7.56/1.49      inference(cnf_transformation,[],[f48]) ).
% 7.56/1.49  
% 7.56/1.49  cnf(c_772,plain,
% 7.56/1.49      ( k4_xboole_0(X0,X1) = X0 | r1_xboole_0(X0,X1) != iProver_top ),
% 7.56/1.49      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 7.56/1.49  
% 7.56/1.49  cnf(c_1030,plain,
% 7.56/1.49      ( k10_relat_1(sK9,sK8) = k1_xboole_0
% 7.56/1.49      | k4_xboole_0(k2_relat_1(sK9),sK8) = k2_relat_1(sK9) ),
% 7.56/1.49      inference(superposition,[status(thm)],[c_759,c_772]) ).
% 7.56/1.49  
% 7.56/1.49  cnf(c_7,plain,
% 7.56/1.49      ( r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) != X0 ),
% 7.56/1.49      inference(cnf_transformation,[],[f49]) ).
% 7.56/1.49  
% 7.56/1.49  cnf(c_773,plain,
% 7.56/1.49      ( k4_xboole_0(X0,X1) != X0 | r1_xboole_0(X0,X1) = iProver_top ),
% 7.56/1.49      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 7.56/1.49  
% 7.56/1.49  cnf(c_1129,plain,
% 7.56/1.49      ( k10_relat_1(sK9,sK8) = k1_xboole_0
% 7.56/1.49      | r1_xboole_0(k2_relat_1(sK9),sK8) = iProver_top ),
% 7.56/1.49      inference(superposition,[status(thm)],[c_1030,c_773]) ).
% 7.56/1.49  
% 7.56/1.49  cnf(c_3,plain,
% 7.56/1.49      ( ~ r2_hidden(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2)))
% 7.56/1.49      | ~ r1_xboole_0(X1,X2) ),
% 7.56/1.49      inference(cnf_transformation,[],[f64]) ).
% 7.56/1.49  
% 7.56/1.49  cnf(c_775,plain,
% 7.56/1.49      ( r2_hidden(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2))) != iProver_top
% 7.56/1.49      | r1_xboole_0(X1,X2) != iProver_top ),
% 7.56/1.49      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 7.56/1.49  
% 7.56/1.49  cnf(c_1906,plain,
% 7.56/1.49      ( k10_relat_1(sK9,sK8) = k1_xboole_0
% 7.56/1.49      | r2_hidden(X0,k4_xboole_0(k2_relat_1(sK9),k2_relat_1(sK9))) != iProver_top
% 7.56/1.49      | r1_xboole_0(k2_relat_1(sK9),sK8) != iProver_top ),
% 7.56/1.49      inference(superposition,[status(thm)],[c_1030,c_775]) ).
% 7.56/1.49  
% 7.56/1.49  cnf(c_5,plain,
% 7.56/1.49      ( k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) = k1_xboole_0 ),
% 7.56/1.49      inference(cnf_transformation,[],[f66]) ).
% 7.56/1.49  
% 7.56/1.49  cnf(c_6,plain,
% 7.56/1.49      ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
% 7.56/1.49      inference(cnf_transformation,[],[f46]) ).
% 7.56/1.49  
% 7.56/1.49  cnf(c_783,plain,
% 7.56/1.49      ( k4_xboole_0(X0,X0) = k1_xboole_0 ),
% 7.56/1.49      inference(light_normalisation,[status(thm)],[c_5,c_6]) ).
% 7.56/1.49  
% 7.56/1.49  cnf(c_1910,plain,
% 7.56/1.49      ( k10_relat_1(sK9,sK8) = k1_xboole_0
% 7.56/1.49      | r2_hidden(X0,k1_xboole_0) != iProver_top
% 7.56/1.49      | r1_xboole_0(k2_relat_1(sK9),sK8) != iProver_top ),
% 7.56/1.49      inference(demodulation,[status(thm)],[c_1906,c_783]) ).
% 7.56/1.49  
% 7.56/1.49  cnf(c_20,negated_conjecture,
% 7.56/1.49      ( ~ r1_xboole_0(k2_relat_1(sK9),sK8)
% 7.56/1.49      | k1_xboole_0 != k10_relat_1(sK9,sK8) ),
% 7.56/1.49      inference(cnf_transformation,[],[f63]) ).
% 7.56/1.49  
% 7.56/1.49  cnf(c_25,plain,
% 7.56/1.49      ( k1_xboole_0 != k10_relat_1(sK9,sK8)
% 7.56/1.49      | r1_xboole_0(k2_relat_1(sK9),sK8) != iProver_top ),
% 7.56/1.49      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 7.56/1.49  
% 7.56/1.49  cnf(c_281,plain,
% 7.56/1.49      ( k1_xboole_0 = k1_xboole_0 ),
% 7.56/1.49      inference(instantiation,[status(thm)],[c_264]) ).
% 7.56/1.49  
% 7.56/1.49  cnf(c_1726,plain,
% 7.56/1.49      ( k10_relat_1(sK9,sK8) != X0
% 7.56/1.49      | k1_xboole_0 != X0
% 7.56/1.49      | k1_xboole_0 = k10_relat_1(sK9,sK8) ),
% 7.56/1.49      inference(instantiation,[status(thm)],[c_265]) ).
% 7.56/1.49  
% 7.56/1.49  cnf(c_1727,plain,
% 7.56/1.49      ( k10_relat_1(sK9,sK8) != k1_xboole_0
% 7.56/1.49      | k1_xboole_0 = k10_relat_1(sK9,sK8)
% 7.56/1.49      | k1_xboole_0 != k1_xboole_0 ),
% 7.56/1.49      inference(instantiation,[status(thm)],[c_1726]) ).
% 7.56/1.49  
% 7.56/1.49  cnf(c_2437,plain,
% 7.56/1.49      ( r2_hidden(X0,k1_xboole_0) != iProver_top
% 7.56/1.49      | r1_xboole_0(k2_relat_1(sK9),sK8) != iProver_top ),
% 7.56/1.49      inference(global_propositional_subsumption,
% 7.56/1.49                [status(thm)],
% 7.56/1.49                [c_1910,c_25,c_281,c_1727]) ).
% 7.56/1.49  
% 7.56/1.49  cnf(c_2443,plain,
% 7.56/1.49      ( k10_relat_1(sK9,sK8) = k1_xboole_0
% 7.56/1.49      | r2_hidden(X0,k1_xboole_0) != iProver_top ),
% 7.56/1.49      inference(superposition,[status(thm)],[c_1129,c_2437]) ).
% 7.56/1.49  
% 7.56/1.49  cnf(c_3883,plain,
% 7.56/1.49      ( k10_relat_1(X0,X1) = k1_xboole_0
% 7.56/1.49      | k10_relat_1(sK9,sK8) = k1_xboole_0
% 7.56/1.49      | r2_hidden(sK3(X0,X1,k1_xboole_0),X1) = iProver_top
% 7.56/1.49      | v1_relat_1(X0) != iProver_top ),
% 7.56/1.49      inference(superposition,[status(thm)],[c_770,c_2443]) ).
% 7.56/1.49  
% 7.56/1.49  cnf(c_4463,plain,
% 7.56/1.49      ( k10_relat_1(X0,k1_xboole_0) = k1_xboole_0
% 7.56/1.49      | k10_relat_1(sK9,sK8) = k1_xboole_0
% 7.56/1.49      | v1_relat_1(X0) != iProver_top ),
% 7.56/1.49      inference(superposition,[status(thm)],[c_3883,c_2443]) ).
% 7.56/1.49  
% 7.56/1.49  cnf(c_4544,plain,
% 7.56/1.49      ( k10_relat_1(sK9,sK8) = k1_xboole_0
% 7.56/1.49      | k10_relat_1(sK9,k1_xboole_0) = k1_xboole_0 ),
% 7.56/1.49      inference(superposition,[status(thm)],[c_758,c_4463]) ).
% 7.56/1.49  
% 7.56/1.49  cnf(c_19,plain,
% 7.56/1.49      ( ~ v1_relat_1(X0)
% 7.56/1.49      | k10_relat_1(X0,k4_xboole_0(k2_relat_1(X0),k4_xboole_0(k2_relat_1(X0),X1))) = k10_relat_1(X0,X1) ),
% 7.56/1.49      inference(cnf_transformation,[],[f67]) ).
% 7.56/1.49  
% 7.56/1.49  cnf(c_761,plain,
% 7.56/1.49      ( k10_relat_1(X0,k4_xboole_0(k2_relat_1(X0),k4_xboole_0(k2_relat_1(X0),X1))) = k10_relat_1(X0,X1)
% 7.56/1.49      | v1_relat_1(X0) != iProver_top ),
% 7.56/1.49      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 7.56/1.49  
% 7.56/1.49  cnf(c_1255,plain,
% 7.56/1.49      ( k10_relat_1(sK9,k4_xboole_0(k2_relat_1(sK9),k4_xboole_0(k2_relat_1(sK9),X0))) = k10_relat_1(sK9,X0) ),
% 7.56/1.49      inference(superposition,[status(thm)],[c_758,c_761]) ).
% 7.56/1.49  
% 7.56/1.49  cnf(c_1689,plain,
% 7.56/1.49      ( k10_relat_1(sK9,k4_xboole_0(k2_relat_1(sK9),k2_relat_1(sK9))) = k10_relat_1(sK9,sK8)
% 7.56/1.49      | k10_relat_1(sK9,sK8) = k1_xboole_0 ),
% 7.56/1.49      inference(superposition,[status(thm)],[c_1030,c_1255]) ).
% 7.56/1.49  
% 7.56/1.49  cnf(c_1692,plain,
% 7.56/1.49      ( k10_relat_1(sK9,sK8) = k1_xboole_0
% 7.56/1.49      | k10_relat_1(sK9,k1_xboole_0) = k10_relat_1(sK9,sK8) ),
% 7.56/1.49      inference(demodulation,[status(thm)],[c_1689,c_783]) ).
% 7.56/1.49  
% 7.56/1.49  cnf(c_760,plain,
% 7.56/1.49      ( k1_xboole_0 != k10_relat_1(sK9,sK8)
% 7.56/1.49      | r1_xboole_0(k2_relat_1(sK9),sK8) != iProver_top ),
% 7.56/1.49      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 7.56/1.49  
% 7.56/1.49  cnf(c_1750,plain,
% 7.56/1.49      ( k10_relat_1(sK9,sK8) = k1_xboole_0
% 7.56/1.49      | k10_relat_1(sK9,k1_xboole_0) != k1_xboole_0
% 7.56/1.49      | r1_xboole_0(k2_relat_1(sK9),sK8) != iProver_top ),
% 7.56/1.49      inference(superposition,[status(thm)],[c_1692,c_760]) ).
% 7.56/1.49  
% 7.56/1.49  cnf(c_4629,plain,
% 7.56/1.49      ( k10_relat_1(sK9,sK8) = k1_xboole_0 ),
% 7.56/1.49      inference(global_propositional_subsumption,
% 7.56/1.49                [status(thm)],
% 7.56/1.49                [c_4544,c_1129,c_1750]) ).
% 7.56/1.49  
% 7.56/1.49  cnf(c_7303,plain,
% 7.56/1.49      ( k10_relat_1(sK9,sK8) = k1_xboole_0 ),
% 7.56/1.49      inference(global_propositional_subsumption,
% 7.56/1.49                [status(thm)],
% 7.56/1.49                [c_6676,c_1129,c_1750,c_4544]) ).
% 7.56/1.49  
% 7.56/1.49  cnf(c_266,plain,
% 7.56/1.49      ( ~ r1_xboole_0(X0,X1) | r1_xboole_0(X2,X3) | X2 != X0 | X3 != X1 ),
% 7.56/1.49      theory(equality) ).
% 7.56/1.49  
% 7.56/1.49  cnf(c_2300,plain,
% 7.56/1.49      ( ~ r1_xboole_0(X0,X1) | r1_xboole_0(X2,X1) | X2 != X0 ),
% 7.56/1.49      inference(resolution,[status(thm)],[c_266,c_264]) ).
% 7.56/1.49  
% 7.56/1.49  cnf(c_7311,plain,
% 7.56/1.49      ( r1_xboole_0(k10_relat_1(sK9,sK8),X0)
% 7.56/1.49      | ~ r1_xboole_0(k1_xboole_0,X0) ),
% 7.56/1.49      inference(resolution,[status(thm)],[c_7303,c_2300]) ).
% 7.56/1.49  
% 7.56/1.49  cnf(c_7315,plain,
% 7.56/1.49      ( r1_xboole_0(k10_relat_1(sK9,sK8),k1_xboole_0)
% 7.56/1.49      | ~ r1_xboole_0(k1_xboole_0,k1_xboole_0) ),
% 7.56/1.49      inference(instantiation,[status(thm)],[c_7311]) ).
% 7.56/1.49  
% 7.56/1.49  cnf(c_3070,plain,
% 7.56/1.49      ( sK7(sK9,sK0(k2_relat_1(sK9),sK8)) = sK7(sK9,sK0(k2_relat_1(sK9),sK8)) ),
% 7.56/1.49      inference(instantiation,[status(thm)],[c_264]) ).
% 7.56/1.49  
% 7.56/1.49  cnf(c_12,plain,
% 7.56/1.49      ( ~ r2_hidden(X0,X1)
% 7.56/1.49      | r2_hidden(X2,k10_relat_1(X3,X1))
% 7.56/1.49      | ~ r2_hidden(k4_tarski(X2,X0),X3)
% 7.56/1.49      | ~ v1_relat_1(X3) ),
% 7.56/1.49      inference(cnf_transformation,[],[f68]) ).
% 7.56/1.49  
% 7.56/1.49  cnf(c_1202,plain,
% 7.56/1.49      ( r2_hidden(sK7(sK9,sK0(k2_relat_1(sK9),sK8)),k10_relat_1(sK9,X0))
% 7.56/1.49      | ~ r2_hidden(k4_tarski(sK7(sK9,sK0(k2_relat_1(sK9),sK8)),sK0(k2_relat_1(sK9),sK8)),sK9)
% 7.56/1.49      | ~ r2_hidden(sK0(k2_relat_1(sK9),sK8),X0)
% 7.56/1.49      | ~ v1_relat_1(sK9) ),
% 7.56/1.49      inference(instantiation,[status(thm)],[c_12]) ).
% 7.56/1.49  
% 7.56/1.49  cnf(c_1563,plain,
% 7.56/1.49      ( r2_hidden(sK7(sK9,sK0(k2_relat_1(sK9),sK8)),k10_relat_1(sK9,sK8))
% 7.56/1.49      | ~ r2_hidden(k4_tarski(sK7(sK9,sK0(k2_relat_1(sK9),sK8)),sK0(k2_relat_1(sK9),sK8)),sK9)
% 7.56/1.49      | ~ r2_hidden(sK0(k2_relat_1(sK9),sK8),sK8)
% 7.56/1.49      | ~ v1_relat_1(sK9) ),
% 7.56/1.49      inference(instantiation,[status(thm)],[c_1202]) ).
% 7.56/1.49  
% 7.56/1.49  cnf(c_18,plain,
% 7.56/1.49      ( ~ r2_hidden(X0,k2_relat_1(X1))
% 7.56/1.49      | r2_hidden(k4_tarski(sK7(X1,X0),X0),X1) ),
% 7.56/1.49      inference(cnf_transformation,[],[f72]) ).
% 7.56/1.49  
% 7.56/1.49  cnf(c_1071,plain,
% 7.56/1.49      ( r2_hidden(k4_tarski(sK7(sK9,sK0(k2_relat_1(sK9),sK8)),sK0(k2_relat_1(sK9),sK8)),sK9)
% 7.56/1.49      | ~ r2_hidden(sK0(k2_relat_1(sK9),sK8),k2_relat_1(sK9)) ),
% 7.56/1.49      inference(instantiation,[status(thm)],[c_18]) ).
% 7.56/1.49  
% 7.56/1.49  cnf(c_2,plain,
% 7.56/1.49      ( r2_hidden(sK0(X0,X1),X0) | r1_xboole_0(X0,X1) ),
% 7.56/1.49      inference(cnf_transformation,[],[f40]) ).
% 7.56/1.49  
% 7.56/1.49  cnf(c_963,plain,
% 7.56/1.49      ( r2_hidden(sK0(k2_relat_1(sK9),sK8),k2_relat_1(sK9))
% 7.56/1.49      | r1_xboole_0(k2_relat_1(sK9),sK8) ),
% 7.56/1.49      inference(instantiation,[status(thm)],[c_2]) ).
% 7.56/1.49  
% 7.56/1.49  cnf(c_1,plain,
% 7.56/1.49      ( r2_hidden(sK0(X0,X1),X1) | r1_xboole_0(X0,X1) ),
% 7.56/1.49      inference(cnf_transformation,[],[f41]) ).
% 7.56/1.49  
% 7.56/1.49  cnf(c_960,plain,
% 7.56/1.49      ( r2_hidden(sK0(k2_relat_1(sK9),sK8),sK8)
% 7.56/1.49      | r1_xboole_0(k2_relat_1(sK9),sK8) ),
% 7.56/1.49      inference(instantiation,[status(thm)],[c_1]) ).
% 7.56/1.49  
% 7.56/1.49  cnf(c_65,plain,
% 7.56/1.49      ( k4_xboole_0(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
% 7.56/1.49      inference(instantiation,[status(thm)],[c_6]) ).
% 7.56/1.49  
% 7.56/1.49  cnf(c_63,plain,
% 7.56/1.49      ( r1_xboole_0(k1_xboole_0,k1_xboole_0)
% 7.56/1.49      | k4_xboole_0(k1_xboole_0,k1_xboole_0) != k1_xboole_0 ),
% 7.56/1.49      inference(instantiation,[status(thm)],[c_7]) ).
% 7.56/1.49  
% 7.56/1.49  cnf(contradiction,plain,
% 7.56/1.49      ( $false ),
% 7.56/1.49      inference(minisat,
% 7.56/1.49                [status(thm)],
% 7.56/1.49                [c_22216,c_7412,c_7315,c_4629,c_3070,c_1727,c_1563,
% 7.56/1.49                 c_1071,c_963,c_960,c_281,c_65,c_63,c_20,c_22]) ).
% 7.56/1.49  
% 7.56/1.49  
% 7.56/1.49  % SZS output end CNFRefutation for theBenchmark.p
% 7.56/1.49  
% 7.56/1.49  ------                               Statistics
% 7.56/1.49  
% 7.56/1.49  ------ Selected
% 7.56/1.49  
% 7.56/1.49  total_time:                             0.607
% 7.56/1.49  
%------------------------------------------------------------------------------
