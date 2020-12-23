%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:54:00 EST 2020

% Result     : Theorem 15.70s
% Output     : CNFRefutation 15.70s
% Verified   : 
% Statistics : Number of formulae       :  318 (23371 expanded)
%              Number of clauses        :  222 (7123 expanded)
%              Number of leaves         :   23 (5211 expanded)
%              Depth                    :   38
%              Number of atoms          : 1051 (110520 expanded)
%              Number of equality atoms :  528 (20020 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal clause size      :   18 (   3 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3,axiom,(
    ! [X0,X1] :
      ( k3_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] :
              ( r2_hidden(X3,X0)
              & r2_hidden(X2,X3) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X0,X1] :
      ( ( k3_tarski(X0) = X1
        | ? [X2] :
            ( ( ! [X3] :
                  ( ~ r2_hidden(X3,X0)
                  | ~ r2_hidden(X2,X3) )
              | ~ r2_hidden(X2,X1) )
            & ( ? [X3] :
                  ( r2_hidden(X3,X0)
                  & r2_hidden(X2,X3) )
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | ! [X3] :
                  ( ~ r2_hidden(X3,X0)
                  | ~ r2_hidden(X2,X3) ) )
            & ( ? [X3] :
                  ( r2_hidden(X3,X0)
                  & r2_hidden(X2,X3) )
              | ~ r2_hidden(X2,X1) ) )
        | k3_tarski(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ( k3_tarski(X0) = X1
        | ? [X2] :
            ( ( ! [X3] :
                  ( ~ r2_hidden(X3,X0)
                  | ~ r2_hidden(X2,X3) )
              | ~ r2_hidden(X2,X1) )
            & ( ? [X4] :
                  ( r2_hidden(X4,X0)
                  & r2_hidden(X2,X4) )
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] :
                  ( ~ r2_hidden(X6,X0)
                  | ~ r2_hidden(X5,X6) ) )
            & ( ? [X7] :
                  ( r2_hidden(X7,X0)
                  & r2_hidden(X5,X7) )
              | ~ r2_hidden(X5,X1) ) )
        | k3_tarski(X0) != X1 ) ) ),
    inference(rectify,[],[f42])).

fof(f46,plain,(
    ! [X5,X0] :
      ( ? [X7] :
          ( r2_hidden(X7,X0)
          & r2_hidden(X5,X7) )
     => ( r2_hidden(sK3(X0,X5),X0)
        & r2_hidden(X5,sK3(X0,X5)) ) ) ),
    introduced(choice_axiom,[])).

fof(f45,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( r2_hidden(X4,X0)
          & r2_hidden(X2,X4) )
     => ( r2_hidden(sK2(X0,X1),X0)
        & r2_hidden(X2,sK2(X0,X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f44,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ! [X3] :
                ( ~ r2_hidden(X3,X0)
                | ~ r2_hidden(X2,X3) )
            | ~ r2_hidden(X2,X1) )
          & ( ? [X4] :
                ( r2_hidden(X4,X0)
                & r2_hidden(X2,X4) )
            | r2_hidden(X2,X1) ) )
     => ( ( ! [X3] :
              ( ~ r2_hidden(X3,X0)
              | ~ r2_hidden(sK1(X0,X1),X3) )
          | ~ r2_hidden(sK1(X0,X1),X1) )
        & ( ? [X4] :
              ( r2_hidden(X4,X0)
              & r2_hidden(sK1(X0,X1),X4) )
          | r2_hidden(sK1(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ( k3_tarski(X0) = X1
        | ( ( ! [X3] :
                ( ~ r2_hidden(X3,X0)
                | ~ r2_hidden(sK1(X0,X1),X3) )
            | ~ r2_hidden(sK1(X0,X1),X1) )
          & ( ( r2_hidden(sK2(X0,X1),X0)
              & r2_hidden(sK1(X0,X1),sK2(X0,X1)) )
            | r2_hidden(sK1(X0,X1),X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] :
                  ( ~ r2_hidden(X6,X0)
                  | ~ r2_hidden(X5,X6) ) )
            & ( ( r2_hidden(sK3(X0,X5),X0)
                & r2_hidden(X5,sK3(X0,X5)) )
              | ~ r2_hidden(X5,X1) ) )
        | k3_tarski(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f43,f46,f45,f44])).

fof(f73,plain,(
    ! [X0,X1] :
      ( k3_tarski(X0) = X1
      | r2_hidden(sK2(X0,X1),X0)
      | r2_hidden(sK1(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,k1_ordinal1(X1))
    <=> ( X0 = X1
        | r2_hidden(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f50,plain,(
    ! [X0,X1] :
      ( ( r2_hidden(X0,k1_ordinal1(X1))
        | ( X0 != X1
          & ~ r2_hidden(X0,X1) ) )
      & ( X0 = X1
        | r2_hidden(X0,X1)
        | ~ r2_hidden(X0,k1_ordinal1(X1)) ) ) ),
    inference(nnf_transformation,[],[f9])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ( r2_hidden(X0,k1_ordinal1(X1))
        | ( X0 != X1
          & ~ r2_hidden(X0,X1) ) )
      & ( X0 = X1
        | r2_hidden(X0,X1)
        | ~ r2_hidden(X0,k1_ordinal1(X1)) ) ) ),
    inference(flattening,[],[f50])).

fof(f82,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | r2_hidden(X0,X1)
      | ~ r2_hidden(X0,k1_ordinal1(X1)) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f5,axiom,(
    ! [X0] : k1_ordinal1(X0) = k2_xboole_0(X0,k1_tarski(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f76,plain,(
    ! [X0] : k1_ordinal1(X0) = k2_xboole_0(X0,k1_tarski(X0)) ),
    inference(cnf_transformation,[],[f5])).

fof(f104,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | r2_hidden(X0,X1)
      | ~ r2_hidden(X0,k2_xboole_0(X1,k1_tarski(X1))) ) ),
    inference(definition_unfolding,[],[f82,f76])).

fof(f72,plain,(
    ! [X0,X1] :
      ( k3_tarski(X0) = X1
      | r2_hidden(sK1(X0,X1),sK2(X0,X1))
      | r2_hidden(sK1(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f18,conjecture,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ( v4_ordinal1(X0)
      <=> ! [X1] :
            ( v3_ordinal1(X1)
           => ( r2_hidden(X1,X0)
             => r2_hidden(k1_ordinal1(X1),X0) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,negated_conjecture,(
    ~ ! [X0] :
        ( v3_ordinal1(X0)
       => ( v4_ordinal1(X0)
        <=> ! [X1] :
              ( v3_ordinal1(X1)
             => ( r2_hidden(X1,X0)
               => r2_hidden(k1_ordinal1(X1),X0) ) ) ) ) ),
    inference(negated_conjecture,[],[f18])).

fof(f34,plain,(
    ? [X0] :
      ( ( v4_ordinal1(X0)
      <~> ! [X1] :
            ( r2_hidden(k1_ordinal1(X1),X0)
            | ~ r2_hidden(X1,X0)
            | ~ v3_ordinal1(X1) ) )
      & v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f35,plain,(
    ? [X0] :
      ( ( v4_ordinal1(X0)
      <~> ! [X1] :
            ( r2_hidden(k1_ordinal1(X1),X0)
            | ~ r2_hidden(X1,X0)
            | ~ v3_ordinal1(X1) ) )
      & v3_ordinal1(X0) ) ),
    inference(flattening,[],[f34])).

fof(f57,plain,(
    ? [X0] :
      ( ( ? [X1] :
            ( ~ r2_hidden(k1_ordinal1(X1),X0)
            & r2_hidden(X1,X0)
            & v3_ordinal1(X1) )
        | ~ v4_ordinal1(X0) )
      & ( ! [X1] :
            ( r2_hidden(k1_ordinal1(X1),X0)
            | ~ r2_hidden(X1,X0)
            | ~ v3_ordinal1(X1) )
        | v4_ordinal1(X0) )
      & v3_ordinal1(X0) ) ),
    inference(nnf_transformation,[],[f35])).

fof(f58,plain,(
    ? [X0] :
      ( ( ? [X1] :
            ( ~ r2_hidden(k1_ordinal1(X1),X0)
            & r2_hidden(X1,X0)
            & v3_ordinal1(X1) )
        | ~ v4_ordinal1(X0) )
      & ( ! [X1] :
            ( r2_hidden(k1_ordinal1(X1),X0)
            | ~ r2_hidden(X1,X0)
            | ~ v3_ordinal1(X1) )
        | v4_ordinal1(X0) )
      & v3_ordinal1(X0) ) ),
    inference(flattening,[],[f57])).

fof(f59,plain,(
    ? [X0] :
      ( ( ? [X1] :
            ( ~ r2_hidden(k1_ordinal1(X1),X0)
            & r2_hidden(X1,X0)
            & v3_ordinal1(X1) )
        | ~ v4_ordinal1(X0) )
      & ( ! [X2] :
            ( r2_hidden(k1_ordinal1(X2),X0)
            | ~ r2_hidden(X2,X0)
            | ~ v3_ordinal1(X2) )
        | v4_ordinal1(X0) )
      & v3_ordinal1(X0) ) ),
    inference(rectify,[],[f58])).

fof(f61,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ r2_hidden(k1_ordinal1(X1),X0)
          & r2_hidden(X1,X0)
          & v3_ordinal1(X1) )
     => ( ~ r2_hidden(k1_ordinal1(sK7),X0)
        & r2_hidden(sK7,X0)
        & v3_ordinal1(sK7) ) ) ),
    introduced(choice_axiom,[])).

fof(f60,plain,
    ( ? [X0] :
        ( ( ? [X1] :
              ( ~ r2_hidden(k1_ordinal1(X1),X0)
              & r2_hidden(X1,X0)
              & v3_ordinal1(X1) )
          | ~ v4_ordinal1(X0) )
        & ( ! [X2] :
              ( r2_hidden(k1_ordinal1(X2),X0)
              | ~ r2_hidden(X2,X0)
              | ~ v3_ordinal1(X2) )
          | v4_ordinal1(X0) )
        & v3_ordinal1(X0) )
   => ( ( ? [X1] :
            ( ~ r2_hidden(k1_ordinal1(X1),sK6)
            & r2_hidden(X1,sK6)
            & v3_ordinal1(X1) )
        | ~ v4_ordinal1(sK6) )
      & ( ! [X2] :
            ( r2_hidden(k1_ordinal1(X2),sK6)
            | ~ r2_hidden(X2,sK6)
            | ~ v3_ordinal1(X2) )
        | v4_ordinal1(sK6) )
      & v3_ordinal1(sK6) ) ),
    introduced(choice_axiom,[])).

fof(f62,plain,
    ( ( ( ~ r2_hidden(k1_ordinal1(sK7),sK6)
        & r2_hidden(sK7,sK6)
        & v3_ordinal1(sK7) )
      | ~ v4_ordinal1(sK6) )
    & ( ! [X2] :
          ( r2_hidden(k1_ordinal1(X2),sK6)
          | ~ r2_hidden(X2,sK6)
          | ~ v3_ordinal1(X2) )
      | v4_ordinal1(sK6) )
    & v3_ordinal1(sK6) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7])],[f59,f61,f60])).

fof(f99,plain,
    ( r2_hidden(sK7,sK6)
    | ~ v4_ordinal1(sK6) ),
    inference(cnf_transformation,[],[f62])).

fof(f71,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | ~ r2_hidden(X6,X0)
      | ~ r2_hidden(X5,X6)
      | k3_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f47])).

fof(f113,plain,(
    ! [X6,X0,X5] :
      ( r2_hidden(X5,k3_tarski(X0))
      | ~ r2_hidden(X6,X0)
      | ~ r2_hidden(X5,X6) ) ),
    inference(equality_resolution,[],[f71])).

fof(f97,plain,(
    ! [X2] :
      ( r2_hidden(k1_ordinal1(X2),sK6)
      | ~ r2_hidden(X2,sK6)
      | ~ v3_ordinal1(X2)
      | v4_ordinal1(sK6) ) ),
    inference(cnf_transformation,[],[f62])).

fof(f110,plain,(
    ! [X2] :
      ( r2_hidden(k2_xboole_0(X2,k1_tarski(X2)),sK6)
      | ~ r2_hidden(X2,sK6)
      | ~ v3_ordinal1(X2)
      | v4_ordinal1(sK6) ) ),
    inference(definition_unfolding,[],[f97,f76])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f20])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f36])).

fof(f38,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK0(X0,X1),X1)
          & r2_hidden(sK0(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f37,f38])).

fof(f63,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f70,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(sK3(X0,X5),X0)
      | ~ r2_hidden(X5,X1)
      | k3_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f47])).

fof(f114,plain,(
    ! [X0,X5] :
      ( r2_hidden(sK3(X0,X5),X0)
      | ~ r2_hidden(X5,k3_tarski(X0)) ) ),
    inference(equality_resolution,[],[f70])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( v3_ordinal1(X1)
     => ( r2_hidden(X0,X1)
       => v3_ordinal1(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1] :
      ( v3_ordinal1(X0)
      | ~ r2_hidden(X0,X1)
      | ~ v3_ordinal1(X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f26,plain,(
    ! [X0,X1] :
      ( v3_ordinal1(X0)
      | ~ r2_hidden(X0,X1)
      | ~ v3_ordinal1(X1) ) ),
    inference(flattening,[],[f25])).

fof(f86,plain,(
    ! [X0,X1] :
      ( v3_ordinal1(X0)
      | ~ r2_hidden(X0,X1)
      | ~ v3_ordinal1(X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f96,plain,(
    v3_ordinal1(sK6) ),
    inference(cnf_transformation,[],[f62])).

fof(f6,axiom,(
    ! [X0] :
      ( v4_ordinal1(X0)
    <=> k3_tarski(X0) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
    ! [X0] :
      ( ( v4_ordinal1(X0)
        | k3_tarski(X0) != X0 )
      & ( k3_tarski(X0) = X0
        | ~ v4_ordinal1(X0) ) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f78,plain,(
    ! [X0] :
      ( v4_ordinal1(X0)
      | k3_tarski(X0) != X0 ) ),
    inference(cnf_transformation,[],[f48])).

fof(f12,axiom,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ! [X1] :
          ( v3_ordinal1(X1)
         => ~ ( ~ r2_hidden(X1,X0)
              & X0 != X1
              & ~ r2_hidden(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(X1,X0)
          | X0 = X1
          | r2_hidden(X0,X1)
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(X1,X0)
          | X0 = X1
          | r2_hidden(X0,X1)
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(flattening,[],[f27])).

fof(f87,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,X0)
      | X0 = X1
      | r2_hidden(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ( v3_ordinal1(X1)
        & v3_ordinal1(X0) )
     => ( r1_ordinal1(X0,X1)
      <=> r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( r1_ordinal1(X0,X1)
      <=> r1_tarski(X0,X1) )
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( r1_ordinal1(X0,X1)
      <=> r1_tarski(X0,X1) )
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(flattening,[],[f23])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ( ( r1_ordinal1(X0,X1)
          | ~ r1_tarski(X0,X1) )
        & ( r1_tarski(X0,X1)
          | ~ r1_ordinal1(X0,X1) ) )
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(nnf_transformation,[],[f24])).

fof(f79,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r1_ordinal1(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f69,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(X5,sK3(X0,X5))
      | ~ r2_hidden(X5,X1)
      | k3_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f47])).

fof(f115,plain,(
    ! [X0,X5] :
      ( r2_hidden(X5,sK3(X0,X5))
      | ~ r2_hidden(X5,k3_tarski(X0)) ) ),
    inference(equality_resolution,[],[f69])).

fof(f17,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f95,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f14,axiom,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ! [X1] :
          ( v3_ordinal1(X1)
         => ( r2_hidden(X0,k1_ordinal1(X1))
          <=> r1_ordinal1(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r2_hidden(X0,k1_ordinal1(X1))
          <=> r1_ordinal1(X0,X1) )
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f52,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( r2_hidden(X0,k1_ordinal1(X1))
              | ~ r1_ordinal1(X0,X1) )
            & ( r1_ordinal1(X0,X1)
              | ~ r2_hidden(X0,k1_ordinal1(X1)) ) )
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(nnf_transformation,[],[f30])).

fof(f89,plain,(
    ! [X0,X1] :
      ( r1_ordinal1(X0,X1)
      | ~ r2_hidden(X0,k1_ordinal1(X1))
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f108,plain,(
    ! [X0,X1] :
      ( r1_ordinal1(X0,X1)
      | ~ r2_hidden(X0,k2_xboole_0(X1,k1_tarski(X1)))
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(definition_unfolding,[],[f89,f76])).

fof(f15,axiom,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(X1,X0)
         => v3_ordinal1(X1) )
     => v3_ordinal1(k3_tarski(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0] :
      ( v3_ordinal1(k3_tarski(X0))
      | ? [X1] :
          ( ~ v3_ordinal1(X1)
          & r2_hidden(X1,X0) ) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f53,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ v3_ordinal1(X1)
          & r2_hidden(X1,X0) )
     => ( ~ v3_ordinal1(sK4(X0))
        & r2_hidden(sK4(X0),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f54,plain,(
    ! [X0] :
      ( v3_ordinal1(k3_tarski(X0))
      | ( ~ v3_ordinal1(sK4(X0))
        & r2_hidden(sK4(X0),X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f31,f53])).

fof(f91,plain,(
    ! [X0] :
      ( v3_ordinal1(k3_tarski(X0))
      | r2_hidden(sK4(X0),X0) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f92,plain,(
    ! [X0] :
      ( v3_ordinal1(k3_tarski(X0))
      | ~ v3_ordinal1(sK4(X0)) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f40])).

fof(f66,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f41])).

fof(f112,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f66])).

fof(f84,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,k1_ordinal1(X1))
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f51])).

fof(f102,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,k2_xboole_0(X1,k1_tarski(X1)))
      | X0 != X1 ) ),
    inference(definition_unfolding,[],[f84,f76])).

fof(f116,plain,(
    ! [X1] : r2_hidden(X1,k2_xboole_0(X1,k1_tarski(X1))) ),
    inference(equality_resolution,[],[f102])).

fof(f83,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,k1_ordinal1(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f103,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,k2_xboole_0(X1,k1_tarski(X1)))
      | ~ r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f83,f76])).

fof(f77,plain,(
    ! [X0] :
      ( k3_tarski(X0) = X0
      | ~ v4_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f100,plain,
    ( ~ r2_hidden(k1_ordinal1(sK7),sK6)
    | ~ v4_ordinal1(sK6) ),
    inference(cnf_transformation,[],[f62])).

fof(f109,plain,
    ( ~ r2_hidden(k2_xboole_0(sK7,k1_tarski(sK7)),sK6)
    | ~ v4_ordinal1(sK6) ),
    inference(definition_unfolding,[],[f100,f76])).

fof(f98,plain,
    ( v3_ordinal1(sK7)
    | ~ v4_ordinal1(sK6) ),
    inference(cnf_transformation,[],[f62])).

fof(f13,axiom,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => v3_ordinal1(k1_ordinal1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0] :
      ( v3_ordinal1(k1_ordinal1(X0))
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f88,plain,(
    ! [X0] :
      ( v3_ordinal1(k1_ordinal1(X0))
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f106,plain,(
    ! [X0] :
      ( v3_ordinal1(k2_xboole_0(X0,k1_tarski(X0)))
      | ~ v3_ordinal1(X0) ) ),
    inference(definition_unfolding,[],[f88,f76])).

fof(f65,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK0(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f74,plain,(
    ! [X0,X3,X1] :
      ( k3_tarski(X0) = X1
      | ~ r2_hidden(X3,X0)
      | ~ r2_hidden(sK1(X0,X1),X3)
      | ~ r2_hidden(sK1(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f64,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK0(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f90,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,k1_ordinal1(X1))
      | ~ r1_ordinal1(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f107,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,k2_xboole_0(X1,k1_tarski(X1)))
      | ~ r1_ordinal1(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(definition_unfolding,[],[f90,f76])).

cnf(c_7,plain,
    ( r2_hidden(sK2(X0,X1),X0)
    | r2_hidden(sK1(X0,X1),X1)
    | k3_tarski(X0) = X1 ),
    inference(cnf_transformation,[],[f73])).

cnf(c_1666,plain,
    ( k3_tarski(X0) = X1
    | r2_hidden(sK2(X0,X1),X0) = iProver_top
    | r2_hidden(sK1(X0,X1),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_20,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k2_xboole_0(X1,k1_tarski(X1)))
    | X1 = X0 ),
    inference(cnf_transformation,[],[f104])).

cnf(c_1654,plain,
    ( X0 = X1
    | r2_hidden(X1,X0) = iProver_top
    | r2_hidden(X1,k2_xboole_0(X0,k1_tarski(X0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_4525,plain,
    ( sK2(k2_xboole_0(X0,k1_tarski(X0)),X1) = X0
    | k3_tarski(k2_xboole_0(X0,k1_tarski(X0))) = X1
    | r2_hidden(sK2(k2_xboole_0(X0,k1_tarski(X0)),X1),X0) = iProver_top
    | r2_hidden(sK1(k2_xboole_0(X0,k1_tarski(X0)),X1),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_1666,c_1654])).

cnf(c_8,plain,
    ( r2_hidden(sK1(X0,X1),X1)
    | r2_hidden(sK1(X0,X1),sK2(X0,X1))
    | k3_tarski(X0) = X1 ),
    inference(cnf_transformation,[],[f72])).

cnf(c_1665,plain,
    ( k3_tarski(X0) = X1
    | r2_hidden(sK1(X0,X1),X1) = iProver_top
    | r2_hidden(sK1(X0,X1),sK2(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_33,negated_conjecture,
    ( r2_hidden(sK7,sK6)
    | ~ v4_ordinal1(sK6) ),
    inference(cnf_transformation,[],[f99])).

cnf(c_1642,plain,
    ( r2_hidden(sK7,sK6) = iProver_top
    | v4_ordinal1(sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_9,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X2,X0)
    | r2_hidden(X2,k3_tarski(X1)) ),
    inference(cnf_transformation,[],[f113])).

cnf(c_1664,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X2,X0) != iProver_top
    | r2_hidden(X2,k3_tarski(X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_4004,plain,
    ( r2_hidden(X0,k3_tarski(sK6)) = iProver_top
    | r2_hidden(X0,sK7) != iProver_top
    | v4_ordinal1(sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_1642,c_1664])).

cnf(c_4190,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,k3_tarski(k3_tarski(sK6))) = iProver_top
    | r2_hidden(X1,sK7) != iProver_top
    | v4_ordinal1(sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_4004,c_1664])).

cnf(c_5086,plain,
    ( k3_tarski(X0) = X1
    | r2_hidden(sK2(X0,X1),sK7) != iProver_top
    | r2_hidden(sK1(X0,X1),X1) = iProver_top
    | r2_hidden(sK1(X0,X1),k3_tarski(k3_tarski(sK6))) = iProver_top
    | v4_ordinal1(sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_1665,c_4190])).

cnf(c_35,negated_conjecture,
    ( ~ r2_hidden(X0,sK6)
    | r2_hidden(k2_xboole_0(X0,k1_tarski(X0)),sK6)
    | v4_ordinal1(sK6)
    | ~ v3_ordinal1(X0) ),
    inference(cnf_transformation,[],[f110])).

cnf(c_1640,plain,
    ( r2_hidden(X0,sK6) != iProver_top
    | r2_hidden(k2_xboole_0(X0,k1_tarski(X0)),sK6) = iProver_top
    | v4_ordinal1(sK6) = iProver_top
    | v3_ordinal1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_35])).

cnf(c_2,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | ~ r1_tarski(X1,X2) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_1670,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,X2) = iProver_top
    | r1_tarski(X1,X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_3771,plain,
    ( r2_hidden(X0,sK6) != iProver_top
    | r2_hidden(k2_xboole_0(X0,k1_tarski(X0)),X1) = iProver_top
    | r1_tarski(sK6,X1) != iProver_top
    | v4_ordinal1(sK6) = iProver_top
    | v3_ordinal1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1640,c_1670])).

cnf(c_10,plain,
    ( ~ r2_hidden(X0,k3_tarski(X1))
    | r2_hidden(sK3(X1,X0),X1) ),
    inference(cnf_transformation,[],[f114])).

cnf(c_1663,plain,
    ( r2_hidden(X0,k3_tarski(X1)) != iProver_top
    | r2_hidden(sK3(X1,X0),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_22,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ v3_ordinal1(X1)
    | v3_ordinal1(X0) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_1653,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | v3_ordinal1(X1) != iProver_top
    | v3_ordinal1(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_3085,plain,
    ( r2_hidden(X0,k3_tarski(X1)) != iProver_top
    | v3_ordinal1(X1) != iProver_top
    | v3_ordinal1(sK3(X1,X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1663,c_1653])).

cnf(c_9764,plain,
    ( r2_hidden(X0,sK6) != iProver_top
    | r1_tarski(sK6,k3_tarski(X1)) != iProver_top
    | v4_ordinal1(sK6) = iProver_top
    | v3_ordinal1(X0) != iProver_top
    | v3_ordinal1(X1) != iProver_top
    | v3_ordinal1(sK3(X1,k2_xboole_0(X0,k1_tarski(X0)))) = iProver_top ),
    inference(superposition,[status(thm)],[c_3771,c_3085])).

cnf(c_36,negated_conjecture,
    ( v3_ordinal1(sK6) ),
    inference(cnf_transformation,[],[f96])).

cnf(c_37,plain,
    ( v3_ordinal1(sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_36])).

cnf(c_13,plain,
    ( v4_ordinal1(X0)
    | k3_tarski(X0) != X0 ),
    inference(cnf_transformation,[],[f78])).

cnf(c_92,plain,
    ( k3_tarski(X0) != X0
    | v4_ordinal1(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_94,plain,
    ( k3_tarski(sK6) != sK6
    | v4_ordinal1(sK6) = iProver_top ),
    inference(instantiation,[status(thm)],[c_92])).

cnf(c_101,plain,
    ( r2_hidden(X0,k3_tarski(X1)) != iProver_top
    | r2_hidden(sK3(X1,X0),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_103,plain,
    ( r2_hidden(sK3(sK6,sK6),sK6) = iProver_top
    | r2_hidden(sK6,k3_tarski(sK6)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_101])).

cnf(c_23,plain,
    ( r2_hidden(X0,X1)
    | r2_hidden(X1,X0)
    | ~ v3_ordinal1(X1)
    | ~ v3_ordinal1(X0)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f87])).

cnf(c_1865,plain,
    ( r2_hidden(k3_tarski(sK6),sK6)
    | r2_hidden(sK6,k3_tarski(sK6))
    | ~ v3_ordinal1(k3_tarski(sK6))
    | ~ v3_ordinal1(sK6)
    | k3_tarski(sK6) = sK6 ),
    inference(instantiation,[status(thm)],[c_23])).

cnf(c_1872,plain,
    ( k3_tarski(sK6) = sK6
    | r2_hidden(k3_tarski(sK6),sK6) = iProver_top
    | r2_hidden(sK6,k3_tarski(sK6)) = iProver_top
    | v3_ordinal1(k3_tarski(sK6)) != iProver_top
    | v3_ordinal1(sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1865])).

cnf(c_16,plain,
    ( ~ r1_ordinal1(X0,X1)
    | r1_tarski(X0,X1)
    | ~ v3_ordinal1(X1)
    | ~ v3_ordinal1(X0) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_2335,plain,
    ( ~ r1_ordinal1(sK3(X0,X1),sK6)
    | r1_tarski(sK3(X0,X1),sK6)
    | ~ v3_ordinal1(sK3(X0,X1))
    | ~ v3_ordinal1(sK6) ),
    inference(instantiation,[status(thm)],[c_16])).

cnf(c_2346,plain,
    ( r1_ordinal1(sK3(X0,X1),sK6) != iProver_top
    | r1_tarski(sK3(X0,X1),sK6) = iProver_top
    | v3_ordinal1(sK3(X0,X1)) != iProver_top
    | v3_ordinal1(sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2335])).

cnf(c_2348,plain,
    ( r1_ordinal1(sK3(sK6,sK6),sK6) != iProver_top
    | r1_tarski(sK3(sK6,sK6),sK6) = iProver_top
    | v3_ordinal1(sK3(sK6,sK6)) != iProver_top
    | v3_ordinal1(sK6) != iProver_top ),
    inference(instantiation,[status(thm)],[c_2346])).

cnf(c_11,plain,
    ( r2_hidden(X0,sK3(X1,X0))
    | ~ r2_hidden(X0,k3_tarski(X1)) ),
    inference(cnf_transformation,[],[f115])).

cnf(c_1662,plain,
    ( r2_hidden(X0,sK3(X1,X0)) = iProver_top
    | r2_hidden(X0,k3_tarski(X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_31,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r1_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f95])).

cnf(c_1644,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_2907,plain,
    ( r2_hidden(X0,k3_tarski(X1)) != iProver_top
    | r1_tarski(sK3(X1,X0),X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1662,c_1644])).

cnf(c_2909,plain,
    ( r2_hidden(sK6,k3_tarski(sK6)) != iProver_top
    | r1_tarski(sK3(sK6,sK6),sK6) != iProver_top ),
    inference(instantiation,[status(thm)],[c_2907])).

cnf(c_26,plain,
    ( r1_ordinal1(X0,X1)
    | ~ r2_hidden(X0,k2_xboole_0(X1,k1_tarski(X1)))
    | ~ v3_ordinal1(X1)
    | ~ v3_ordinal1(X0) ),
    inference(cnf_transformation,[],[f108])).

cnf(c_5544,plain,
    ( r1_ordinal1(sK3(X0,X1),sK6)
    | ~ r2_hidden(sK3(X0,X1),k2_xboole_0(sK6,k1_tarski(sK6)))
    | ~ v3_ordinal1(sK3(X0,X1))
    | ~ v3_ordinal1(sK6) ),
    inference(instantiation,[status(thm)],[c_26])).

cnf(c_5555,plain,
    ( r1_ordinal1(sK3(X0,X1),sK6) = iProver_top
    | r2_hidden(sK3(X0,X1),k2_xboole_0(sK6,k1_tarski(sK6))) != iProver_top
    | v3_ordinal1(sK3(X0,X1)) != iProver_top
    | v3_ordinal1(sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5544])).

cnf(c_5557,plain,
    ( r1_ordinal1(sK3(sK6,sK6),sK6) = iProver_top
    | r2_hidden(sK3(sK6,sK6),k2_xboole_0(sK6,k1_tarski(sK6))) != iProver_top
    | v3_ordinal1(sK3(sK6,sK6)) != iProver_top
    | v3_ordinal1(sK6) != iProver_top ),
    inference(instantiation,[status(thm)],[c_5555])).

cnf(c_28,plain,
    ( r2_hidden(sK4(X0),X0)
    | v3_ordinal1(k3_tarski(X0)) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_1647,plain,
    ( r2_hidden(sK4(X0),X0) = iProver_top
    | v3_ordinal1(k3_tarski(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_3089,plain,
    ( v3_ordinal1(X0) != iProver_top
    | v3_ordinal1(sK4(X0)) = iProver_top
    | v3_ordinal1(k3_tarski(X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1647,c_1653])).

cnf(c_27,plain,
    ( ~ v3_ordinal1(sK4(X0))
    | v3_ordinal1(k3_tarski(X0)) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_56,plain,
    ( v3_ordinal1(sK4(X0)) != iProver_top
    | v3_ordinal1(k3_tarski(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_8421,plain,
    ( v3_ordinal1(X0) != iProver_top
    | v3_ordinal1(k3_tarski(X0)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3089,c_56])).

cnf(c_8424,plain,
    ( v3_ordinal1(k3_tarski(sK6)) = iProver_top
    | v3_ordinal1(sK6) != iProver_top ),
    inference(instantiation,[status(thm)],[c_8421])).

cnf(c_5,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f112])).

cnf(c_1668,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_18,plain,
    ( r2_hidden(X0,k2_xboole_0(X0,k1_tarski(X0))) ),
    inference(cnf_transformation,[],[f116])).

cnf(c_1656,plain,
    ( r2_hidden(X0,k2_xboole_0(X0,k1_tarski(X0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_4005,plain,
    ( r2_hidden(X0,k2_xboole_0(X1,k1_tarski(X1))) != iProver_top
    | r2_hidden(X0,k3_tarski(sK6)) = iProver_top
    | r2_hidden(X1,sK6) != iProver_top
    | v4_ordinal1(sK6) = iProver_top
    | v3_ordinal1(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1640,c_1664])).

cnf(c_4270,plain,
    ( r2_hidden(X0,k3_tarski(sK6)) = iProver_top
    | r2_hidden(X0,sK6) != iProver_top
    | v4_ordinal1(sK6) = iProver_top
    | v3_ordinal1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1656,c_4005])).

cnf(c_5317,plain,
    ( r2_hidden(X0,sK6) != iProver_top
    | r1_tarski(k3_tarski(sK6),X0) != iProver_top
    | v4_ordinal1(sK6) = iProver_top
    | v3_ordinal1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_4270,c_1644])).

cnf(c_9673,plain,
    ( r2_hidden(k3_tarski(sK6),sK6) != iProver_top
    | v4_ordinal1(sK6) = iProver_top
    | v3_ordinal1(k3_tarski(sK6)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1668,c_5317])).

cnf(c_1652,plain,
    ( X0 = X1
    | r2_hidden(X1,X0) = iProver_top
    | r2_hidden(X0,X1) = iProver_top
    | v3_ordinal1(X1) != iProver_top
    | v3_ordinal1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_9758,plain,
    ( k3_tarski(X0) = X1
    | r2_hidden(k3_tarski(X0),X1) = iProver_top
    | v3_ordinal1(X0) != iProver_top
    | v3_ordinal1(X1) != iProver_top
    | v3_ordinal1(sK3(X0,X1)) = iProver_top
    | v3_ordinal1(k3_tarski(X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1652,c_3085])).

cnf(c_9789,plain,
    ( k3_tarski(sK6) = sK6
    | r2_hidden(k3_tarski(sK6),sK6) = iProver_top
    | v3_ordinal1(sK3(sK6,sK6)) = iProver_top
    | v3_ordinal1(k3_tarski(sK6)) != iProver_top
    | v3_ordinal1(sK6) != iProver_top ),
    inference(instantiation,[status(thm)],[c_9758])).

cnf(c_19,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,k2_xboole_0(X1,k1_tarski(X1))) ),
    inference(cnf_transformation,[],[f103])).

cnf(c_9922,plain,
    ( ~ r2_hidden(sK3(sK6,X0),X1)
    | r2_hidden(sK3(sK6,X0),k2_xboole_0(X1,k1_tarski(X1))) ),
    inference(instantiation,[status(thm)],[c_19])).

cnf(c_9923,plain,
    ( r2_hidden(sK3(sK6,X0),X1) != iProver_top
    | r2_hidden(sK3(sK6,X0),k2_xboole_0(X1,k1_tarski(X1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9922])).

cnf(c_9925,plain,
    ( r2_hidden(sK3(sK6,sK6),k2_xboole_0(sK6,k1_tarski(sK6))) = iProver_top
    | r2_hidden(sK3(sK6,sK6),sK6) != iProver_top ),
    inference(instantiation,[status(thm)],[c_9923])).

cnf(c_10713,plain,
    ( v4_ordinal1(sK6) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_9764,c_37,c_94,c_103,c_1872,c_2348,c_2909,c_5557,c_8424,c_9673,c_9789,c_9925])).

cnf(c_20422,plain,
    ( r2_hidden(sK1(X0,X1),k3_tarski(k3_tarski(sK6))) = iProver_top
    | r2_hidden(sK1(X0,X1),X1) = iProver_top
    | r2_hidden(sK2(X0,X1),sK7) != iProver_top
    | k3_tarski(X0) = X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_5086,c_37,c_94,c_103,c_1872,c_2348,c_2909,c_5557,c_8424,c_9673,c_9789,c_9925])).

cnf(c_20423,plain,
    ( k3_tarski(X0) = X1
    | r2_hidden(sK2(X0,X1),sK7) != iProver_top
    | r2_hidden(sK1(X0,X1),X1) = iProver_top
    | r2_hidden(sK1(X0,X1),k3_tarski(k3_tarski(sK6))) = iProver_top ),
    inference(renaming,[status(thm)],[c_20422])).

cnf(c_14,plain,
    ( ~ v4_ordinal1(X0)
    | k3_tarski(X0) = X0 ),
    inference(cnf_transformation,[],[f77])).

cnf(c_1659,plain,
    ( k3_tarski(X0) = X0
    | v4_ordinal1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_10717,plain,
    ( k3_tarski(sK6) = sK6 ),
    inference(superposition,[status(thm)],[c_10713,c_1659])).

cnf(c_20426,plain,
    ( k3_tarski(X0) = X1
    | r2_hidden(sK2(X0,X1),sK7) != iProver_top
    | r2_hidden(sK1(X0,X1),X1) = iProver_top
    | r2_hidden(sK1(X0,X1),sK6) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_20423,c_10717])).

cnf(c_45060,plain,
    ( sK2(k2_xboole_0(sK7,k1_tarski(sK7)),X0) = sK7
    | k3_tarski(k2_xboole_0(sK7,k1_tarski(sK7))) = X0
    | r2_hidden(sK1(k2_xboole_0(sK7,k1_tarski(sK7)),X0),X0) = iProver_top
    | r2_hidden(sK1(k2_xboole_0(sK7,k1_tarski(sK7)),X0),sK6) = iProver_top ),
    inference(superposition,[status(thm)],[c_4525,c_20426])).

cnf(c_32,negated_conjecture,
    ( ~ r2_hidden(k2_xboole_0(sK7,k1_tarski(sK7)),sK6)
    | ~ v4_ordinal1(sK6) ),
    inference(cnf_transformation,[],[f109])).

cnf(c_1643,plain,
    ( r2_hidden(k2_xboole_0(sK7,k1_tarski(sK7)),sK6) != iProver_top
    | v4_ordinal1(sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_5497,plain,
    ( k2_xboole_0(sK7,k1_tarski(sK7)) = sK6
    | r2_hidden(sK6,k2_xboole_0(sK7,k1_tarski(sK7))) = iProver_top
    | v4_ordinal1(sK6) != iProver_top
    | v3_ordinal1(k2_xboole_0(sK7,k1_tarski(sK7))) != iProver_top
    | v3_ordinal1(sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_1652,c_1643])).

cnf(c_34,negated_conjecture,
    ( ~ v4_ordinal1(sK6)
    | v3_ordinal1(sK7) ),
    inference(cnf_transformation,[],[f98])).

cnf(c_41,plain,
    ( v4_ordinal1(sK6) != iProver_top
    | v3_ordinal1(sK7) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_42,plain,
    ( r2_hidden(sK7,sK6) = iProver_top
    | v4_ordinal1(sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_43,plain,
    ( r2_hidden(k2_xboole_0(sK7,k1_tarski(sK7)),sK6) != iProver_top
    | v4_ordinal1(sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_45,plain,
    ( ~ r2_hidden(sK6,sK6)
    | ~ r1_tarski(sK6,sK6) ),
    inference(instantiation,[status(thm)],[c_31])).

cnf(c_44,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_46,plain,
    ( r2_hidden(sK6,sK6) != iProver_top
    | r1_tarski(sK6,sK6) != iProver_top ),
    inference(instantiation,[status(thm)],[c_44])).

cnf(c_60,plain,
    ( r1_ordinal1(sK6,sK6)
    | ~ r2_hidden(sK6,k2_xboole_0(sK6,k1_tarski(sK6)))
    | ~ v3_ordinal1(sK6) ),
    inference(instantiation,[status(thm)],[c_26])).

cnf(c_59,plain,
    ( r1_ordinal1(X0,X1) = iProver_top
    | r2_hidden(X0,k2_xboole_0(X1,k1_tarski(X1))) != iProver_top
    | v3_ordinal1(X0) != iProver_top
    | v3_ordinal1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_61,plain,
    ( r1_ordinal1(sK6,sK6) = iProver_top
    | r2_hidden(sK6,k2_xboole_0(sK6,k1_tarski(sK6))) != iProver_top
    | v3_ordinal1(sK6) != iProver_top ),
    inference(instantiation,[status(thm)],[c_59])).

cnf(c_69,plain,
    ( r2_hidden(sK6,sK6)
    | ~ v3_ordinal1(sK6)
    | sK6 = sK6 ),
    inference(instantiation,[status(thm)],[c_23])).

cnf(c_80,plain,
    ( r2_hidden(sK6,k2_xboole_0(sK6,k1_tarski(sK6))) ),
    inference(instantiation,[status(thm)],[c_18])).

cnf(c_79,plain,
    ( r2_hidden(X0,k2_xboole_0(X0,k1_tarski(X0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_81,plain,
    ( r2_hidden(sK6,k2_xboole_0(sK6,k1_tarski(sK6))) = iProver_top ),
    inference(instantiation,[status(thm)],[c_79])).

cnf(c_84,plain,
    ( ~ r1_ordinal1(sK6,sK6)
    | r1_tarski(sK6,sK6)
    | ~ v3_ordinal1(sK6) ),
    inference(instantiation,[status(thm)],[c_16])).

cnf(c_83,plain,
    ( r1_ordinal1(X0,X1) != iProver_top
    | r1_tarski(X0,X1) = iProver_top
    | v3_ordinal1(X0) != iProver_top
    | v3_ordinal1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_85,plain,
    ( r1_ordinal1(sK6,sK6) != iProver_top
    | r1_tarski(sK6,sK6) = iProver_top
    | v3_ordinal1(sK6) != iProver_top ),
    inference(instantiation,[status(thm)],[c_83])).

cnf(c_1765,plain,
    ( r2_hidden(X0,k2_xboole_0(sK7,k1_tarski(sK7)))
    | r2_hidden(k2_xboole_0(sK7,k1_tarski(sK7)),X0)
    | ~ v3_ordinal1(X0)
    | ~ v3_ordinal1(k2_xboole_0(sK7,k1_tarski(sK7)))
    | k2_xboole_0(sK7,k1_tarski(sK7)) = X0 ),
    inference(instantiation,[status(thm)],[c_23])).

cnf(c_1776,plain,
    ( k2_xboole_0(sK7,k1_tarski(sK7)) = X0
    | r2_hidden(X0,k2_xboole_0(sK7,k1_tarski(sK7))) = iProver_top
    | r2_hidden(k2_xboole_0(sK7,k1_tarski(sK7)),X0) = iProver_top
    | v3_ordinal1(X0) != iProver_top
    | v3_ordinal1(k2_xboole_0(sK7,k1_tarski(sK7))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1765])).

cnf(c_1778,plain,
    ( k2_xboole_0(sK7,k1_tarski(sK7)) = sK6
    | r2_hidden(k2_xboole_0(sK7,k1_tarski(sK7)),sK6) = iProver_top
    | r2_hidden(sK6,k2_xboole_0(sK7,k1_tarski(sK7))) = iProver_top
    | v3_ordinal1(k2_xboole_0(sK7,k1_tarski(sK7))) != iProver_top
    | v3_ordinal1(sK6) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1776])).

cnf(c_973,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_1817,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,sK6)
    | X2 != X0
    | sK6 != X1 ),
    inference(instantiation,[status(thm)],[c_973])).

cnf(c_2060,plain,
    ( r2_hidden(X0,sK6)
    | ~ r2_hidden(sK7,sK6)
    | X0 != sK7
    | sK6 != sK6 ),
    inference(instantiation,[status(thm)],[c_1817])).

cnf(c_2062,plain,
    ( X0 != sK7
    | sK6 != sK6
    | r2_hidden(X0,sK6) = iProver_top
    | r2_hidden(sK7,sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2060])).

cnf(c_2064,plain,
    ( sK6 != sK6
    | sK6 != sK7
    | r2_hidden(sK6,sK6) = iProver_top
    | r2_hidden(sK7,sK6) != iProver_top ),
    inference(instantiation,[status(thm)],[c_2062])).

cnf(c_24,plain,
    ( ~ v3_ordinal1(X0)
    | v3_ordinal1(k2_xboole_0(X0,k1_tarski(X0))) ),
    inference(cnf_transformation,[],[f106])).

cnf(c_2214,plain,
    ( v3_ordinal1(k2_xboole_0(sK7,k1_tarski(sK7)))
    | ~ v3_ordinal1(sK7) ),
    inference(instantiation,[status(thm)],[c_24])).

cnf(c_2215,plain,
    ( v3_ordinal1(k2_xboole_0(sK7,k1_tarski(sK7))) = iProver_top
    | v3_ordinal1(sK7) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2214])).

cnf(c_972,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_2558,plain,
    ( X0 != X1
    | X0 = sK7
    | sK7 != X1 ),
    inference(instantiation,[status(thm)],[c_972])).

cnf(c_2559,plain,
    ( sK6 != sK6
    | sK6 = sK7
    | sK7 != sK6 ),
    inference(instantiation,[status(thm)],[c_2558])).

cnf(c_3554,plain,
    ( ~ r2_hidden(X0,k2_xboole_0(sK7,k1_tarski(sK7)))
    | r2_hidden(X0,sK7)
    | sK7 = X0 ),
    inference(instantiation,[status(thm)],[c_20])).

cnf(c_3560,plain,
    ( sK7 = X0
    | r2_hidden(X0,k2_xboole_0(sK7,k1_tarski(sK7))) != iProver_top
    | r2_hidden(X0,sK7) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3554])).

cnf(c_3562,plain,
    ( sK7 = sK6
    | r2_hidden(sK6,k2_xboole_0(sK7,k1_tarski(sK7))) != iProver_top
    | r2_hidden(sK6,sK7) = iProver_top ),
    inference(instantiation,[status(thm)],[c_3560])).

cnf(c_5093,plain,
    ( r2_hidden(sK6,sK7) != iProver_top
    | r2_hidden(sK7,k3_tarski(k3_tarski(sK6))) = iProver_top
    | v4_ordinal1(sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_1642,c_4190])).

cnf(c_1723,plain,
    ( ~ r1_ordinal1(sK6,sK7)
    | r1_tarski(sK6,sK7)
    | ~ v3_ordinal1(sK6)
    | ~ v3_ordinal1(sK7) ),
    inference(instantiation,[status(thm)],[c_16])).

cnf(c_1730,plain,
    ( r1_ordinal1(sK6,sK7) != iProver_top
    | r1_tarski(sK6,sK7) = iProver_top
    | v3_ordinal1(sK6) != iProver_top
    | v3_ordinal1(sK7) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1723])).

cnf(c_2077,plain,
    ( r1_ordinal1(sK6,sK7)
    | ~ r2_hidden(sK6,k2_xboole_0(sK7,k1_tarski(sK7)))
    | ~ v3_ordinal1(sK6)
    | ~ v3_ordinal1(sK7) ),
    inference(instantiation,[status(thm)],[c_26])).

cnf(c_2084,plain,
    ( r1_ordinal1(sK6,sK7) = iProver_top
    | r2_hidden(sK6,k2_xboole_0(sK7,k1_tarski(sK7))) != iProver_top
    | v3_ordinal1(sK6) != iProver_top
    | v3_ordinal1(sK7) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2077])).

cnf(c_2498,plain,
    ( r1_tarski(sK6,sK7) != iProver_top
    | v4_ordinal1(sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_1642,c_1644])).

cnf(c_2861,plain,
    ( r2_hidden(X0,k2_xboole_0(sK7,k1_tarski(sK7)))
    | ~ r2_hidden(X0,sK7) ),
    inference(instantiation,[status(thm)],[c_19])).

cnf(c_2862,plain,
    ( r2_hidden(X0,k2_xboole_0(sK7,k1_tarski(sK7))) = iProver_top
    | r2_hidden(X0,sK7) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2861])).

cnf(c_2864,plain,
    ( r2_hidden(sK6,k2_xboole_0(sK7,k1_tarski(sK7))) = iProver_top
    | r2_hidden(sK6,sK7) != iProver_top ),
    inference(instantiation,[status(thm)],[c_2862])).

cnf(c_5256,plain,
    ( r2_hidden(sK6,sK7) != iProver_top
    | v4_ordinal1(sK6) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5093,c_37,c_41,c_1730,c_2084,c_2498,c_2864])).

cnf(c_6118,plain,
    ( k2_xboole_0(sK7,k1_tarski(sK7)) = sK6
    | v4_ordinal1(sK6) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5497,c_36,c_37,c_41,c_42,c_43,c_45,c_46,c_60,c_61,c_69,c_80,c_81,c_84,c_85,c_1778,c_2064,c_2215,c_2559,c_3562,c_5256])).

cnf(c_10718,plain,
    ( k2_xboole_0(sK7,k1_tarski(sK7)) = sK6 ),
    inference(superposition,[status(thm)],[c_10713,c_6118])).

cnf(c_45070,plain,
    ( sK2(sK6,X0) = sK7
    | sK6 = X0
    | r2_hidden(sK1(sK6,X0),X0) = iProver_top
    | r2_hidden(sK1(sK6,X0),sK6) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_45060,c_10717,c_10718])).

cnf(c_1655,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,k2_xboole_0(X1,k1_tarski(X1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_10832,plain,
    ( r2_hidden(X0,sK6) = iProver_top
    | r2_hidden(X0,sK7) != iProver_top ),
    inference(superposition,[status(thm)],[c_10718,c_1655])).

cnf(c_45475,plain,
    ( sK2(sK6,sK7) = sK7
    | sK6 = sK7
    | r2_hidden(sK1(sK6,sK7),sK6) = iProver_top ),
    inference(superposition,[status(thm)],[c_45070,c_10832])).

cnf(c_89,plain,
    ( k3_tarski(X0) = X0
    | v4_ordinal1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_91,plain,
    ( k3_tarski(sK6) = sK6
    | v4_ordinal1(sK6) != iProver_top ),
    inference(instantiation,[status(thm)],[c_89])).

cnf(c_282,plain,
    ( v4_ordinal1(X0)
    | k3_tarski(X0) != X0 ),
    inference(prop_impl,[status(thm)],[c_13])).

cnf(c_512,plain,
    ( r2_hidden(sK7,sK6)
    | k3_tarski(X0) != X0
    | sK6 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_282,c_33])).

cnf(c_513,plain,
    ( r2_hidden(sK7,sK6)
    | k3_tarski(sK6) != sK6 ),
    inference(unflattening,[status(thm)],[c_512])).

cnf(c_0,plain,
    ( ~ r2_hidden(sK0(X0,X1),X1)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_1832,plain,
    ( ~ r2_hidden(sK0(k3_tarski(X0),sK6),sK6)
    | r1_tarski(k3_tarski(X0),sK6) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_1838,plain,
    ( r2_hidden(sK0(k3_tarski(X0),sK6),sK6) != iProver_top
    | r1_tarski(k3_tarski(X0),sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1832])).

cnf(c_1840,plain,
    ( r2_hidden(sK0(k3_tarski(sK6),sK6),sK6) != iProver_top
    | r1_tarski(k3_tarski(sK6),sK6) = iProver_top ),
    inference(instantiation,[status(thm)],[c_1838])).

cnf(c_2371,plain,
    ( k3_tarski(X0) != X1
    | sK6 != X1
    | sK6 = k3_tarski(X0) ),
    inference(instantiation,[status(thm)],[c_972])).

cnf(c_2372,plain,
    ( k3_tarski(sK6) != sK6
    | sK6 = k3_tarski(sK6)
    | sK6 != sK6 ),
    inference(instantiation,[status(thm)],[c_2371])).

cnf(c_2550,plain,
    ( r2_hidden(k3_tarski(X0),sK6)
    | ~ r2_hidden(sK7,sK6)
    | k3_tarski(X0) != sK7
    | sK6 != sK6 ),
    inference(instantiation,[status(thm)],[c_2060])).

cnf(c_2552,plain,
    ( r2_hidden(k3_tarski(sK6),sK6)
    | ~ r2_hidden(sK7,sK6)
    | k3_tarski(sK6) != sK7
    | sK6 != sK6 ),
    inference(instantiation,[status(thm)],[c_2550])).

cnf(c_2580,plain,
    ( r2_hidden(X0,sK6)
    | ~ r2_hidden(k3_tarski(sK6),sK6)
    | X0 != k3_tarski(sK6)
    | sK6 != sK6 ),
    inference(instantiation,[status(thm)],[c_1817])).

cnf(c_2583,plain,
    ( ~ r2_hidden(k3_tarski(sK6),sK6)
    | r2_hidden(sK6,sK6)
    | sK6 != k3_tarski(sK6)
    | sK6 != sK6 ),
    inference(instantiation,[status(thm)],[c_2580])).

cnf(c_7318,plain,
    ( r2_hidden(sK1(X0,sK7),sK2(X0,sK7))
    | r2_hidden(sK1(X0,sK7),sK7)
    | k3_tarski(X0) = sK7 ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_7320,plain,
    ( k3_tarski(X0) = sK7
    | r2_hidden(sK1(X0,sK7),sK2(X0,sK7)) = iProver_top
    | r2_hidden(sK1(X0,sK7),sK7) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7318])).

cnf(c_7322,plain,
    ( k3_tarski(sK6) = sK7
    | r2_hidden(sK1(sK6,sK7),sK2(sK6,sK7)) = iProver_top
    | r2_hidden(sK1(sK6,sK7),sK7) = iProver_top ),
    inference(instantiation,[status(thm)],[c_7320])).

cnf(c_11218,plain,
    ( r2_hidden(sK2(X0,sK7),X0)
    | r2_hidden(sK1(X0,sK7),sK7)
    | k3_tarski(X0) = sK7 ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_11221,plain,
    ( k3_tarski(X0) = sK7
    | r2_hidden(sK2(X0,sK7),X0) = iProver_top
    | r2_hidden(sK1(X0,sK7),sK7) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11218])).

cnf(c_11223,plain,
    ( k3_tarski(sK6) = sK7
    | r2_hidden(sK2(sK6,sK7),sK6) = iProver_top
    | r2_hidden(sK1(sK6,sK7),sK7) = iProver_top ),
    inference(instantiation,[status(thm)],[c_11221])).

cnf(c_3928,plain,
    ( ~ r2_hidden(X0,sK2(X1,X2))
    | r2_hidden(X0,k3_tarski(X1))
    | ~ r2_hidden(sK2(X1,X2),X1) ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_16591,plain,
    ( ~ r2_hidden(sK2(X0,sK7),X0)
    | ~ r2_hidden(sK1(X0,sK7),sK2(X0,sK7))
    | r2_hidden(sK1(X0,sK7),k3_tarski(X0)) ),
    inference(instantiation,[status(thm)],[c_3928])).

cnf(c_16592,plain,
    ( r2_hidden(sK2(X0,sK7),X0) != iProver_top
    | r2_hidden(sK1(X0,sK7),sK2(X0,sK7)) != iProver_top
    | r2_hidden(sK1(X0,sK7),k3_tarski(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16591])).

cnf(c_16594,plain,
    ( r2_hidden(sK2(sK6,sK7),sK6) != iProver_top
    | r2_hidden(sK1(sK6,sK7),sK2(sK6,sK7)) != iProver_top
    | r2_hidden(sK1(sK6,sK7),k3_tarski(sK6)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_16592])).

cnf(c_6,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(sK1(X1,X2),X0)
    | ~ r2_hidden(sK1(X1,X2),X2)
    | k3_tarski(X1) = X2 ),
    inference(cnf_transformation,[],[f74])).

cnf(c_10571,plain,
    ( ~ r2_hidden(sK1(sK6,X0),X0)
    | ~ r2_hidden(sK1(sK6,X0),sK7)
    | ~ r2_hidden(sK7,sK6)
    | k3_tarski(sK6) = X0 ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_22966,plain,
    ( ~ r2_hidden(sK1(sK6,sK7),sK7)
    | ~ r2_hidden(sK7,sK6)
    | k3_tarski(sK6) = sK7 ),
    inference(instantiation,[status(thm)],[c_10571])).

cnf(c_22977,plain,
    ( k3_tarski(sK6) = sK7
    | r2_hidden(sK1(sK6,sK7),sK7) != iProver_top
    | r2_hidden(sK7,sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22966])).

cnf(c_4084,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k3_tarski(X2))
    | ~ r1_tarski(k3_tarski(X2),X1) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_33153,plain,
    ( r2_hidden(sK1(X0,sK7),X1)
    | ~ r2_hidden(sK1(X0,sK7),k3_tarski(X2))
    | ~ r1_tarski(k3_tarski(X2),X1) ),
    inference(instantiation,[status(thm)],[c_4084])).

cnf(c_33154,plain,
    ( r2_hidden(sK1(X0,sK7),X1) = iProver_top
    | r2_hidden(sK1(X0,sK7),k3_tarski(X2)) != iProver_top
    | r1_tarski(k3_tarski(X2),X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33153])).

cnf(c_33156,plain,
    ( r2_hidden(sK1(sK6,sK7),k3_tarski(sK6)) != iProver_top
    | r2_hidden(sK1(sK6,sK7),sK6) = iProver_top
    | r1_tarski(k3_tarski(sK6),sK6) != iProver_top ),
    inference(instantiation,[status(thm)],[c_33154])).

cnf(c_1,plain,
    ( r2_hidden(sK0(X0,X1),X0)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_1671,plain,
    ( r2_hidden(sK0(X0,X1),X0) = iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_3765,plain,
    ( r2_hidden(X0,k3_tarski(X1)) != iProver_top
    | r2_hidden(sK3(X1,X0),X2) = iProver_top
    | r1_tarski(X1,X2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1663,c_1670])).

cnf(c_1649,plain,
    ( r1_ordinal1(X0,X1) = iProver_top
    | r2_hidden(X0,k2_xboole_0(X1,k1_tarski(X1))) != iProver_top
    | v3_ordinal1(X0) != iProver_top
    | v3_ordinal1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_10830,plain,
    ( r1_ordinal1(X0,sK7) = iProver_top
    | r2_hidden(X0,sK6) != iProver_top
    | v3_ordinal1(X0) != iProver_top
    | v3_ordinal1(sK7) != iProver_top ),
    inference(superposition,[status(thm)],[c_10718,c_1649])).

cnf(c_11044,plain,
    ( r2_hidden(X0,sK6) != iProver_top
    | v3_ordinal1(sK3(sK6,X0)) = iProver_top
    | v3_ordinal1(sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_10717,c_3085])).

cnf(c_3086,plain,
    ( r2_hidden(X0,k3_tarski(X1)) != iProver_top
    | v3_ordinal1(X0) = iProver_top
    | v3_ordinal1(sK3(X1,X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1662,c_1653])).

cnf(c_11121,plain,
    ( r2_hidden(X0,sK6) != iProver_top
    | v3_ordinal1(X0) = iProver_top
    | v3_ordinal1(sK3(sK6,X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_10717,c_3086])).

cnf(c_13100,plain,
    ( r1_ordinal1(X0,sK7) = iProver_top
    | r2_hidden(X0,sK6) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_10830,c_37,c_41,c_94,c_103,c_1872,c_2348,c_2909,c_5557,c_8424,c_9673,c_9789,c_9925,c_11044,c_11121])).

cnf(c_20701,plain,
    ( r1_ordinal1(sK3(X0,X1),sK7) = iProver_top
    | r2_hidden(X1,k3_tarski(X0)) != iProver_top
    | r1_tarski(X0,sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_3765,c_13100])).

cnf(c_25,plain,
    ( ~ r1_ordinal1(X0,X1)
    | r2_hidden(X0,k2_xboole_0(X1,k1_tarski(X1)))
    | ~ v3_ordinal1(X1)
    | ~ v3_ordinal1(X0) ),
    inference(cnf_transformation,[],[f107])).

cnf(c_1650,plain,
    ( r1_ordinal1(X0,X1) != iProver_top
    | r2_hidden(X0,k2_xboole_0(X1,k1_tarski(X1))) = iProver_top
    | v3_ordinal1(X0) != iProver_top
    | v3_ordinal1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_4439,plain,
    ( r1_ordinal1(X0,X1) != iProver_top
    | r2_hidden(X2,X0) != iProver_top
    | r2_hidden(X2,k3_tarski(k2_xboole_0(X1,k1_tarski(X1)))) = iProver_top
    | v3_ordinal1(X0) != iProver_top
    | v3_ordinal1(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1650,c_1664])).

cnf(c_34138,plain,
    ( r2_hidden(X0,sK3(X1,X2)) != iProver_top
    | r2_hidden(X2,k3_tarski(X1)) != iProver_top
    | r2_hidden(X0,k3_tarski(k2_xboole_0(sK7,k1_tarski(sK7)))) = iProver_top
    | r1_tarski(X1,sK6) != iProver_top
    | v3_ordinal1(sK3(X1,X2)) != iProver_top
    | v3_ordinal1(sK7) != iProver_top ),
    inference(superposition,[status(thm)],[c_20701,c_4439])).

cnf(c_34143,plain,
    ( r2_hidden(X0,sK3(X1,X2)) != iProver_top
    | r2_hidden(X2,k3_tarski(X1)) != iProver_top
    | r2_hidden(X0,sK6) = iProver_top
    | r1_tarski(X1,sK6) != iProver_top
    | v3_ordinal1(sK3(X1,X2)) != iProver_top
    | v3_ordinal1(sK7) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_34138,c_10717,c_10718])).

cnf(c_34152,plain,
    ( v3_ordinal1(sK3(X1,X2)) != iProver_top
    | r1_tarski(X1,sK6) != iProver_top
    | r2_hidden(X0,sK6) = iProver_top
    | r2_hidden(X2,k3_tarski(X1)) != iProver_top
    | r2_hidden(X0,sK3(X1,X2)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_34143,c_37,c_41,c_94,c_103,c_1872,c_2348,c_2909,c_5557,c_8424,c_9673,c_9789,c_9925])).

cnf(c_34153,plain,
    ( r2_hidden(X0,sK3(X1,X2)) != iProver_top
    | r2_hidden(X2,k3_tarski(X1)) != iProver_top
    | r2_hidden(X0,sK6) = iProver_top
    | r1_tarski(X1,sK6) != iProver_top
    | v3_ordinal1(sK3(X1,X2)) != iProver_top ),
    inference(renaming,[status(thm)],[c_34152])).

cnf(c_34165,plain,
    ( r2_hidden(X0,k3_tarski(X1)) != iProver_top
    | r2_hidden(X0,sK6) = iProver_top
    | r1_tarski(X1,sK6) != iProver_top
    | v3_ordinal1(sK3(X1,X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1662,c_34153])).

cnf(c_31947,plain,
    ( v3_ordinal1(X0) = iProver_top
    | r2_hidden(X0,sK6) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_11121,c_37,c_11044])).

cnf(c_31948,plain,
    ( r2_hidden(X0,sK6) != iProver_top
    | v3_ordinal1(X0) = iProver_top ),
    inference(renaming,[status(thm)],[c_31947])).

cnf(c_31969,plain,
    ( r2_hidden(X0,k3_tarski(X1)) != iProver_top
    | r1_tarski(X1,sK6) != iProver_top
    | v3_ordinal1(sK3(X1,X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_3765,c_31948])).

cnf(c_37236,plain,
    ( r1_tarski(X1,sK6) != iProver_top
    | r2_hidden(X0,sK6) = iProver_top
    | r2_hidden(X0,k3_tarski(X1)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_34165,c_31969])).

cnf(c_37237,plain,
    ( r2_hidden(X0,k3_tarski(X1)) != iProver_top
    | r2_hidden(X0,sK6) = iProver_top
    | r1_tarski(X1,sK6) != iProver_top ),
    inference(renaming,[status(thm)],[c_37236])).

cnf(c_37242,plain,
    ( r2_hidden(sK0(k3_tarski(X0),X1),sK6) = iProver_top
    | r1_tarski(X0,sK6) != iProver_top
    | r1_tarski(k3_tarski(X0),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_1671,c_37237])).

cnf(c_37284,plain,
    ( r2_hidden(sK0(k3_tarski(sK6),sK6),sK6) = iProver_top
    | r1_tarski(k3_tarski(sK6),sK6) = iProver_top
    | r1_tarski(sK6,sK6) != iProver_top ),
    inference(instantiation,[status(thm)],[c_37242])).

cnf(c_46316,plain,
    ( r2_hidden(sK1(sK6,sK7),sK6) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_45475,c_36,c_37,c_42,c_45,c_60,c_61,c_69,c_80,c_81,c_84,c_85,c_91,c_94,c_103,c_513,c_1840,c_1872,c_2348,c_2372,c_2552,c_2583,c_2909,c_5557,c_7322,c_8424,c_9673,c_9789,c_9925,c_11223,c_16594,c_22977,c_33156,c_37284])).

cnf(c_10818,plain,
    ( sK7 = X0
    | r2_hidden(X0,sK6) != iProver_top
    | r2_hidden(X0,sK7) = iProver_top ),
    inference(superposition,[status(thm)],[c_10718,c_1654])).

cnf(c_46329,plain,
    ( sK1(sK6,sK7) = sK7
    | r2_hidden(sK1(sK6,sK7),sK7) = iProver_top ),
    inference(superposition,[status(thm)],[c_46316,c_10818])).

cnf(c_47372,plain,
    ( sK1(sK6,sK7) = sK7 ),
    inference(global_propositional_subsumption,[status(thm)],[c_46329,c_36,c_37,c_42,c_45,c_60,c_69,c_80,c_84,c_91,c_94,c_103,c_513,c_1872,c_2348,c_2372,c_2552,c_2583,c_2909,c_5557,c_8424,c_9673,c_9789,c_9925,c_22977])).

cnf(c_47389,plain,
    ( k3_tarski(sK6) = sK7
    | r2_hidden(sK1(sK6,sK7),sK7) = iProver_top
    | r2_hidden(sK7,sK2(sK6,sK7)) = iProver_top ),
    inference(superposition,[status(thm)],[c_47372,c_1665])).

cnf(c_47402,plain,
    ( k3_tarski(sK6) = sK7
    | r2_hidden(sK7,sK2(sK6,sK7)) = iProver_top
    | r2_hidden(sK7,sK7) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_47389,c_47372])).

cnf(c_47403,plain,
    ( sK6 = sK7
    | r2_hidden(sK7,sK2(sK6,sK7)) = iProver_top
    | r2_hidden(sK7,sK7) = iProver_top ),
    inference(demodulation,[status(thm)],[c_47402,c_10717])).

cnf(c_6165,plain,
    ( r1_tarski(sK7,sK7) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_6166,plain,
    ( r1_tarski(sK7,sK7) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6165])).

cnf(c_2576,plain,
    ( ~ r2_hidden(sK7,X0)
    | ~ r1_tarski(X0,sK7) ),
    inference(instantiation,[status(thm)],[c_31])).

cnf(c_7203,plain,
    ( ~ r2_hidden(sK7,sK7)
    | ~ r1_tarski(sK7,sK7) ),
    inference(instantiation,[status(thm)],[c_2576])).

cnf(c_7208,plain,
    ( r2_hidden(sK7,sK7) != iProver_top
    | r1_tarski(sK7,sK7) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7203])).

cnf(c_48597,plain,
    ( r2_hidden(sK7,sK2(sK6,sK7)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_47403,c_36,c_37,c_42,c_45,c_46,c_60,c_61,c_69,c_80,c_81,c_84,c_85,c_94,c_103,c_1872,c_2064,c_2348,c_2909,c_5557,c_6166,c_7208,c_8424,c_9673,c_9789,c_9925])).

cnf(c_48607,plain,
    ( r1_tarski(sK2(sK6,sK7),sK7) != iProver_top ),
    inference(superposition,[status(thm)],[c_48597,c_1644])).

cnf(c_4524,plain,
    ( k3_tarski(k2_xboole_0(X0,k1_tarski(X0))) = X1
    | r1_ordinal1(sK2(k2_xboole_0(X0,k1_tarski(X0)),X1),X0) = iProver_top
    | r2_hidden(sK1(k2_xboole_0(X0,k1_tarski(X0)),X1),X1) = iProver_top
    | v3_ordinal1(X0) != iProver_top
    | v3_ordinal1(sK2(k2_xboole_0(X0,k1_tarski(X0)),X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1666,c_1649])).

cnf(c_10829,plain,
    ( r1_ordinal1(X0,sK7) != iProver_top
    | r2_hidden(X0,sK6) = iProver_top
    | v3_ordinal1(X0) != iProver_top
    | v3_ordinal1(sK7) != iProver_top ),
    inference(superposition,[status(thm)],[c_10718,c_1650])).

cnf(c_13087,plain,
    ( v3_ordinal1(X0) != iProver_top
    | r2_hidden(X0,sK6) = iProver_top
    | r1_ordinal1(X0,sK7) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_10829,c_37,c_41,c_94,c_103,c_1872,c_2348,c_2909,c_5557,c_8424,c_9673,c_9789,c_9925])).

cnf(c_13088,plain,
    ( r1_ordinal1(X0,sK7) != iProver_top
    | r2_hidden(X0,sK6) = iProver_top
    | v3_ordinal1(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_13087])).

cnf(c_44248,plain,
    ( k3_tarski(k2_xboole_0(sK7,k1_tarski(sK7))) = X0
    | r2_hidden(sK2(k2_xboole_0(sK7,k1_tarski(sK7)),X0),sK6) = iProver_top
    | r2_hidden(sK1(k2_xboole_0(sK7,k1_tarski(sK7)),X0),X0) = iProver_top
    | v3_ordinal1(sK2(k2_xboole_0(sK7,k1_tarski(sK7)),X0)) != iProver_top
    | v3_ordinal1(sK7) != iProver_top ),
    inference(superposition,[status(thm)],[c_4524,c_13088])).

cnf(c_44249,plain,
    ( sK6 = X0
    | r2_hidden(sK2(sK6,X0),sK6) = iProver_top
    | r2_hidden(sK1(sK6,X0),X0) = iProver_top
    | v3_ordinal1(sK2(sK6,X0)) != iProver_top
    | v3_ordinal1(sK7) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_44248,c_10717,c_10718])).

cnf(c_31956,plain,
    ( k3_tarski(sK6) = X0
    | r2_hidden(sK1(sK6,X0),X0) = iProver_top
    | v3_ordinal1(sK2(sK6,X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1666,c_31948])).

cnf(c_31997,plain,
    ( sK6 = X0
    | r2_hidden(sK1(sK6,X0),X0) = iProver_top
    | v3_ordinal1(sK2(sK6,X0)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_31956,c_10717])).

cnf(c_44511,plain,
    ( sK6 = X0
    | r2_hidden(sK2(sK6,X0),sK6) = iProver_top
    | r2_hidden(sK1(sK6,X0),X0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_44249,c_37,c_41,c_94,c_103,c_1872,c_2348,c_2909,c_5557,c_8424,c_9673,c_9789,c_9925,c_31997])).

cnf(c_47398,plain,
    ( sK6 = sK7
    | r2_hidden(sK2(sK6,sK7),sK6) = iProver_top
    | r2_hidden(sK7,sK7) = iProver_top ),
    inference(superposition,[status(thm)],[c_47372,c_44511])).

cnf(c_47551,plain,
    ( r2_hidden(sK2(sK6,sK7),sK6) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_47398,c_36,c_37,c_42,c_45,c_60,c_69,c_80,c_84,c_91,c_94,c_103,c_513,c_1872,c_2348,c_2372,c_2552,c_2583,c_2909,c_5557,c_8424,c_9673,c_9789,c_9925,c_11223,c_22977])).

cnf(c_47563,plain,
    ( r1_ordinal1(sK2(sK6,sK7),sK7) = iProver_top ),
    inference(superposition,[status(thm)],[c_47551,c_13100])).

cnf(c_1657,plain,
    ( r1_ordinal1(X0,X1) != iProver_top
    | r1_tarski(X0,X1) = iProver_top
    | v3_ordinal1(X0) != iProver_top
    | v3_ordinal1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_47578,plain,
    ( r1_tarski(sK2(sK6,sK7),sK7) = iProver_top
    | v3_ordinal1(sK2(sK6,sK7)) != iProver_top
    | v3_ordinal1(sK7) != iProver_top ),
    inference(superposition,[status(thm)],[c_47563,c_1657])).

cnf(c_6007,plain,
    ( ~ r2_hidden(sK2(sK6,X0),X1)
    | ~ v3_ordinal1(X1)
    | v3_ordinal1(sK2(sK6,X0)) ),
    inference(instantiation,[status(thm)],[c_22])).

cnf(c_22944,plain,
    ( ~ r2_hidden(sK2(sK6,sK7),sK6)
    | v3_ordinal1(sK2(sK6,sK7))
    | ~ v3_ordinal1(sK6) ),
    inference(instantiation,[status(thm)],[c_6007])).

cnf(c_22945,plain,
    ( r2_hidden(sK2(sK6,sK7),sK6) != iProver_top
    | v3_ordinal1(sK2(sK6,sK7)) = iProver_top
    | v3_ordinal1(sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22944])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_48607,c_47578,c_22977,c_22945,c_11223,c_10713,c_2583,c_2552,c_2372,c_513,c_91,c_84,c_80,c_69,c_60,c_45,c_42,c_41,c_37,c_36])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.00/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n012.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 18:51:22 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  % Running in FOF mode
% 15.70/2.41  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 15.70/2.41  
% 15.70/2.41  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 15.70/2.41  
% 15.70/2.41  ------  iProver source info
% 15.70/2.41  
% 15.70/2.41  git: date: 2020-06-30 10:37:57 +0100
% 15.70/2.41  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 15.70/2.41  git: non_committed_changes: false
% 15.70/2.41  git: last_make_outside_of_git: false
% 15.70/2.41  
% 15.70/2.41  ------ 
% 15.70/2.41  
% 15.70/2.41  ------ Input Options
% 15.70/2.41  
% 15.70/2.41  --out_options                           all
% 15.70/2.41  --tptp_safe_out                         true
% 15.70/2.41  --problem_path                          ""
% 15.70/2.41  --include_path                          ""
% 15.70/2.41  --clausifier                            res/vclausify_rel
% 15.70/2.41  --clausifier_options                    ""
% 15.70/2.41  --stdin                                 false
% 15.70/2.41  --stats_out                             all
% 15.70/2.41  
% 15.70/2.41  ------ General Options
% 15.70/2.41  
% 15.70/2.41  --fof                                   false
% 15.70/2.41  --time_out_real                         305.
% 15.70/2.41  --time_out_virtual                      -1.
% 15.70/2.41  --symbol_type_check                     false
% 15.70/2.41  --clausify_out                          false
% 15.70/2.41  --sig_cnt_out                           false
% 15.70/2.41  --trig_cnt_out                          false
% 15.70/2.41  --trig_cnt_out_tolerance                1.
% 15.70/2.41  --trig_cnt_out_sk_spl                   false
% 15.70/2.41  --abstr_cl_out                          false
% 15.70/2.41  
% 15.70/2.41  ------ Global Options
% 15.70/2.41  
% 15.70/2.41  --schedule                              default
% 15.70/2.41  --add_important_lit                     false
% 15.70/2.41  --prop_solver_per_cl                    1000
% 15.70/2.41  --min_unsat_core                        false
% 15.70/2.41  --soft_assumptions                      false
% 15.70/2.41  --soft_lemma_size                       3
% 15.70/2.41  --prop_impl_unit_size                   0
% 15.70/2.41  --prop_impl_unit                        []
% 15.70/2.41  --share_sel_clauses                     true
% 15.70/2.41  --reset_solvers                         false
% 15.70/2.41  --bc_imp_inh                            [conj_cone]
% 15.70/2.41  --conj_cone_tolerance                   3.
% 15.70/2.41  --extra_neg_conj                        none
% 15.70/2.41  --large_theory_mode                     true
% 15.70/2.41  --prolific_symb_bound                   200
% 15.70/2.41  --lt_threshold                          2000
% 15.70/2.41  --clause_weak_htbl                      true
% 15.70/2.41  --gc_record_bc_elim                     false
% 15.70/2.41  
% 15.70/2.41  ------ Preprocessing Options
% 15.70/2.41  
% 15.70/2.41  --preprocessing_flag                    true
% 15.70/2.41  --time_out_prep_mult                    0.1
% 15.70/2.41  --splitting_mode                        input
% 15.70/2.41  --splitting_grd                         true
% 15.70/2.41  --splitting_cvd                         false
% 15.70/2.41  --splitting_cvd_svl                     false
% 15.70/2.41  --splitting_nvd                         32
% 15.70/2.41  --sub_typing                            true
% 15.70/2.41  --prep_gs_sim                           true
% 15.70/2.41  --prep_unflatten                        true
% 15.70/2.41  --prep_res_sim                          true
% 15.70/2.41  --prep_upred                            true
% 15.70/2.41  --prep_sem_filter                       exhaustive
% 15.70/2.41  --prep_sem_filter_out                   false
% 15.70/2.41  --pred_elim                             true
% 15.70/2.41  --res_sim_input                         true
% 15.70/2.41  --eq_ax_congr_red                       true
% 15.70/2.41  --pure_diseq_elim                       true
% 15.70/2.41  --brand_transform                       false
% 15.70/2.41  --non_eq_to_eq                          false
% 15.70/2.41  --prep_def_merge                        true
% 15.70/2.41  --prep_def_merge_prop_impl              false
% 15.70/2.41  --prep_def_merge_mbd                    true
% 15.70/2.41  --prep_def_merge_tr_red                 false
% 15.70/2.41  --prep_def_merge_tr_cl                  false
% 15.70/2.41  --smt_preprocessing                     true
% 15.70/2.41  --smt_ac_axioms                         fast
% 15.70/2.41  --preprocessed_out                      false
% 15.70/2.41  --preprocessed_stats                    false
% 15.70/2.41  
% 15.70/2.41  ------ Abstraction refinement Options
% 15.70/2.41  
% 15.70/2.41  --abstr_ref                             []
% 15.70/2.41  --abstr_ref_prep                        false
% 15.70/2.41  --abstr_ref_until_sat                   false
% 15.70/2.41  --abstr_ref_sig_restrict                funpre
% 15.70/2.41  --abstr_ref_af_restrict_to_split_sk     false
% 15.70/2.41  --abstr_ref_under                       []
% 15.70/2.41  
% 15.70/2.41  ------ SAT Options
% 15.70/2.41  
% 15.70/2.41  --sat_mode                              false
% 15.70/2.41  --sat_fm_restart_options                ""
% 15.70/2.41  --sat_gr_def                            false
% 15.70/2.41  --sat_epr_types                         true
% 15.70/2.41  --sat_non_cyclic_types                  false
% 15.70/2.41  --sat_finite_models                     false
% 15.70/2.41  --sat_fm_lemmas                         false
% 15.70/2.41  --sat_fm_prep                           false
% 15.70/2.41  --sat_fm_uc_incr                        true
% 15.70/2.41  --sat_out_model                         small
% 15.70/2.41  --sat_out_clauses                       false
% 15.70/2.41  
% 15.70/2.41  ------ QBF Options
% 15.70/2.41  
% 15.70/2.41  --qbf_mode                              false
% 15.70/2.41  --qbf_elim_univ                         false
% 15.70/2.41  --qbf_dom_inst                          none
% 15.70/2.41  --qbf_dom_pre_inst                      false
% 15.70/2.41  --qbf_sk_in                             false
% 15.70/2.41  --qbf_pred_elim                         true
% 15.70/2.41  --qbf_split                             512
% 15.70/2.41  
% 15.70/2.41  ------ BMC1 Options
% 15.70/2.41  
% 15.70/2.41  --bmc1_incremental                      false
% 15.70/2.41  --bmc1_axioms                           reachable_all
% 15.70/2.41  --bmc1_min_bound                        0
% 15.70/2.41  --bmc1_max_bound                        -1
% 15.70/2.41  --bmc1_max_bound_default                -1
% 15.70/2.41  --bmc1_symbol_reachability              true
% 15.70/2.41  --bmc1_property_lemmas                  false
% 15.70/2.41  --bmc1_k_induction                      false
% 15.70/2.41  --bmc1_non_equiv_states                 false
% 15.70/2.41  --bmc1_deadlock                         false
% 15.70/2.41  --bmc1_ucm                              false
% 15.70/2.41  --bmc1_add_unsat_core                   none
% 15.70/2.41  --bmc1_unsat_core_children              false
% 15.70/2.41  --bmc1_unsat_core_extrapolate_axioms    false
% 15.70/2.41  --bmc1_out_stat                         full
% 15.70/2.41  --bmc1_ground_init                      false
% 15.70/2.41  --bmc1_pre_inst_next_state              false
% 15.70/2.41  --bmc1_pre_inst_state                   false
% 15.70/2.41  --bmc1_pre_inst_reach_state             false
% 15.70/2.41  --bmc1_out_unsat_core                   false
% 15.70/2.41  --bmc1_aig_witness_out                  false
% 15.70/2.41  --bmc1_verbose                          false
% 15.70/2.41  --bmc1_dump_clauses_tptp                false
% 15.70/2.41  --bmc1_dump_unsat_core_tptp             false
% 15.70/2.41  --bmc1_dump_file                        -
% 15.70/2.41  --bmc1_ucm_expand_uc_limit              128
% 15.70/2.41  --bmc1_ucm_n_expand_iterations          6
% 15.70/2.41  --bmc1_ucm_extend_mode                  1
% 15.70/2.41  --bmc1_ucm_init_mode                    2
% 15.70/2.41  --bmc1_ucm_cone_mode                    none
% 15.70/2.41  --bmc1_ucm_reduced_relation_type        0
% 15.70/2.41  --bmc1_ucm_relax_model                  4
% 15.70/2.41  --bmc1_ucm_full_tr_after_sat            true
% 15.70/2.41  --bmc1_ucm_expand_neg_assumptions       false
% 15.70/2.41  --bmc1_ucm_layered_model                none
% 15.70/2.41  --bmc1_ucm_max_lemma_size               10
% 15.70/2.41  
% 15.70/2.41  ------ AIG Options
% 15.70/2.41  
% 15.70/2.41  --aig_mode                              false
% 15.70/2.41  
% 15.70/2.41  ------ Instantiation Options
% 15.70/2.41  
% 15.70/2.41  --instantiation_flag                    true
% 15.70/2.41  --inst_sos_flag                         true
% 15.70/2.41  --inst_sos_phase                        true
% 15.70/2.41  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 15.70/2.41  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 15.70/2.41  --inst_lit_sel_side                     num_symb
% 15.70/2.41  --inst_solver_per_active                1400
% 15.70/2.41  --inst_solver_calls_frac                1.
% 15.70/2.41  --inst_passive_queue_type               priority_queues
% 15.70/2.41  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 15.70/2.41  --inst_passive_queues_freq              [25;2]
% 15.70/2.41  --inst_dismatching                      true
% 15.70/2.41  --inst_eager_unprocessed_to_passive     true
% 15.70/2.41  --inst_prop_sim_given                   true
% 15.70/2.41  --inst_prop_sim_new                     false
% 15.70/2.41  --inst_subs_new                         false
% 15.70/2.41  --inst_eq_res_simp                      false
% 15.70/2.41  --inst_subs_given                       false
% 15.70/2.41  --inst_orphan_elimination               true
% 15.70/2.41  --inst_learning_loop_flag               true
% 15.70/2.41  --inst_learning_start                   3000
% 15.70/2.41  --inst_learning_factor                  2
% 15.70/2.41  --inst_start_prop_sim_after_learn       3
% 15.70/2.41  --inst_sel_renew                        solver
% 15.70/2.41  --inst_lit_activity_flag                true
% 15.70/2.41  --inst_restr_to_given                   false
% 15.70/2.41  --inst_activity_threshold               500
% 15.70/2.41  --inst_out_proof                        true
% 15.70/2.41  
% 15.70/2.41  ------ Resolution Options
% 15.70/2.41  
% 15.70/2.41  --resolution_flag                       true
% 15.70/2.41  --res_lit_sel                           adaptive
% 15.70/2.41  --res_lit_sel_side                      none
% 15.70/2.41  --res_ordering                          kbo
% 15.70/2.41  --res_to_prop_solver                    active
% 15.70/2.41  --res_prop_simpl_new                    false
% 15.70/2.41  --res_prop_simpl_given                  true
% 15.70/2.41  --res_passive_queue_type                priority_queues
% 15.70/2.41  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 15.70/2.41  --res_passive_queues_freq               [15;5]
% 15.70/2.41  --res_forward_subs                      full
% 15.70/2.41  --res_backward_subs                     full
% 15.70/2.41  --res_forward_subs_resolution           true
% 15.70/2.41  --res_backward_subs_resolution          true
% 15.70/2.41  --res_orphan_elimination                true
% 15.70/2.41  --res_time_limit                        2.
% 15.70/2.41  --res_out_proof                         true
% 15.70/2.41  
% 15.70/2.41  ------ Superposition Options
% 15.70/2.41  
% 15.70/2.41  --superposition_flag                    true
% 15.70/2.41  --sup_passive_queue_type                priority_queues
% 15.70/2.41  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 15.70/2.41  --sup_passive_queues_freq               [8;1;4]
% 15.70/2.41  --demod_completeness_check              fast
% 15.70/2.41  --demod_use_ground                      true
% 15.70/2.41  --sup_to_prop_solver                    passive
% 15.70/2.41  --sup_prop_simpl_new                    true
% 15.70/2.41  --sup_prop_simpl_given                  true
% 15.70/2.41  --sup_fun_splitting                     true
% 15.70/2.41  --sup_smt_interval                      50000
% 15.70/2.41  
% 15.70/2.41  ------ Superposition Simplification Setup
% 15.70/2.41  
% 15.70/2.41  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 15.70/2.41  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 15.70/2.41  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 15.70/2.41  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 15.70/2.41  --sup_full_triv                         [TrivRules;PropSubs]
% 15.70/2.41  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 15.70/2.41  --sup_full_bw                           [BwDemod;BwSubsumption]
% 15.70/2.41  --sup_immed_triv                        [TrivRules]
% 15.70/2.41  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 15.70/2.41  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 15.70/2.41  --sup_immed_bw_main                     []
% 15.70/2.41  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 15.70/2.41  --sup_input_triv                        [Unflattening;TrivRules]
% 15.70/2.41  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 15.70/2.41  --sup_input_bw                          []
% 15.70/2.41  
% 15.70/2.41  ------ Combination Options
% 15.70/2.41  
% 15.70/2.41  --comb_res_mult                         3
% 15.70/2.41  --comb_sup_mult                         2
% 15.70/2.41  --comb_inst_mult                        10
% 15.70/2.41  
% 15.70/2.41  ------ Debug Options
% 15.70/2.41  
% 15.70/2.41  --dbg_backtrace                         false
% 15.70/2.41  --dbg_dump_prop_clauses                 false
% 15.70/2.41  --dbg_dump_prop_clauses_file            -
% 15.70/2.41  --dbg_out_stat                          false
% 15.70/2.41  ------ Parsing...
% 15.70/2.41  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 15.70/2.41  
% 15.70/2.41  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e  sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 15.70/2.41  
% 15.70/2.41  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 15.70/2.41  
% 15.70/2.41  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 15.70/2.41  ------ Proving...
% 15.70/2.41  ------ Problem Properties 
% 15.70/2.41  
% 15.70/2.41  
% 15.70/2.41  clauses                                 35
% 15.70/2.41  conjectures                             5
% 15.70/2.41  EPR                                     12
% 15.70/2.41  Horn                                    27
% 15.70/2.41  unary                                   6
% 15.70/2.41  binary                                  14
% 15.70/2.41  lits                                    88
% 15.70/2.41  lits eq                                 9
% 15.70/2.41  fd_pure                                 0
% 15.70/2.41  fd_pseudo                               0
% 15.70/2.41  fd_cond                                 0
% 15.70/2.41  fd_pseudo_cond                          6
% 15.70/2.41  AC symbols                              0
% 15.70/2.41  
% 15.70/2.41  ------ Schedule dynamic 5 is on 
% 15.70/2.41  
% 15.70/2.41  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 15.70/2.41  
% 15.70/2.41  
% 15.70/2.41  ------ 
% 15.70/2.41  Current options:
% 15.70/2.41  ------ 
% 15.70/2.41  
% 15.70/2.41  ------ Input Options
% 15.70/2.41  
% 15.70/2.41  --out_options                           all
% 15.70/2.41  --tptp_safe_out                         true
% 15.70/2.41  --problem_path                          ""
% 15.70/2.41  --include_path                          ""
% 15.70/2.41  --clausifier                            res/vclausify_rel
% 15.70/2.41  --clausifier_options                    ""
% 15.70/2.41  --stdin                                 false
% 15.70/2.41  --stats_out                             all
% 15.70/2.41  
% 15.70/2.41  ------ General Options
% 15.70/2.41  
% 15.70/2.41  --fof                                   false
% 15.70/2.41  --time_out_real                         305.
% 15.70/2.41  --time_out_virtual                      -1.
% 15.70/2.41  --symbol_type_check                     false
% 15.70/2.41  --clausify_out                          false
% 15.70/2.41  --sig_cnt_out                           false
% 15.70/2.41  --trig_cnt_out                          false
% 15.70/2.41  --trig_cnt_out_tolerance                1.
% 15.70/2.41  --trig_cnt_out_sk_spl                   false
% 15.70/2.41  --abstr_cl_out                          false
% 15.70/2.41  
% 15.70/2.41  ------ Global Options
% 15.70/2.41  
% 15.70/2.41  --schedule                              default
% 15.70/2.41  --add_important_lit                     false
% 15.70/2.41  --prop_solver_per_cl                    1000
% 15.70/2.41  --min_unsat_core                        false
% 15.70/2.41  --soft_assumptions                      false
% 15.70/2.41  --soft_lemma_size                       3
% 15.70/2.41  --prop_impl_unit_size                   0
% 15.70/2.41  --prop_impl_unit                        []
% 15.70/2.41  --share_sel_clauses                     true
% 15.70/2.41  --reset_solvers                         false
% 15.70/2.41  --bc_imp_inh                            [conj_cone]
% 15.70/2.41  --conj_cone_tolerance                   3.
% 15.70/2.41  --extra_neg_conj                        none
% 15.70/2.41  --large_theory_mode                     true
% 15.70/2.41  --prolific_symb_bound                   200
% 15.70/2.41  --lt_threshold                          2000
% 15.70/2.41  --clause_weak_htbl                      true
% 15.70/2.41  --gc_record_bc_elim                     false
% 15.70/2.41  
% 15.70/2.41  ------ Preprocessing Options
% 15.70/2.41  
% 15.70/2.41  --preprocessing_flag                    true
% 15.70/2.41  --time_out_prep_mult                    0.1
% 15.70/2.41  --splitting_mode                        input
% 15.70/2.41  --splitting_grd                         true
% 15.70/2.41  --splitting_cvd                         false
% 15.70/2.41  --splitting_cvd_svl                     false
% 15.70/2.41  --splitting_nvd                         32
% 15.70/2.41  --sub_typing                            true
% 15.70/2.41  --prep_gs_sim                           true
% 15.70/2.41  --prep_unflatten                        true
% 15.70/2.41  --prep_res_sim                          true
% 15.70/2.41  --prep_upred                            true
% 15.70/2.41  --prep_sem_filter                       exhaustive
% 15.70/2.41  --prep_sem_filter_out                   false
% 15.70/2.41  --pred_elim                             true
% 15.70/2.41  --res_sim_input                         true
% 15.70/2.41  --eq_ax_congr_red                       true
% 15.70/2.41  --pure_diseq_elim                       true
% 15.70/2.41  --brand_transform                       false
% 15.70/2.41  --non_eq_to_eq                          false
% 15.70/2.41  --prep_def_merge                        true
% 15.70/2.41  --prep_def_merge_prop_impl              false
% 15.70/2.41  --prep_def_merge_mbd                    true
% 15.70/2.41  --prep_def_merge_tr_red                 false
% 15.70/2.41  --prep_def_merge_tr_cl                  false
% 15.70/2.41  --smt_preprocessing                     true
% 15.70/2.41  --smt_ac_axioms                         fast
% 15.70/2.41  --preprocessed_out                      false
% 15.70/2.41  --preprocessed_stats                    false
% 15.70/2.41  
% 15.70/2.41  ------ Abstraction refinement Options
% 15.70/2.41  
% 15.70/2.41  --abstr_ref                             []
% 15.70/2.41  --abstr_ref_prep                        false
% 15.70/2.41  --abstr_ref_until_sat                   false
% 15.70/2.41  --abstr_ref_sig_restrict                funpre
% 15.70/2.41  --abstr_ref_af_restrict_to_split_sk     false
% 15.70/2.41  --abstr_ref_under                       []
% 15.70/2.41  
% 15.70/2.41  ------ SAT Options
% 15.70/2.41  
% 15.70/2.41  --sat_mode                              false
% 15.70/2.41  --sat_fm_restart_options                ""
% 15.70/2.41  --sat_gr_def                            false
% 15.70/2.41  --sat_epr_types                         true
% 15.70/2.41  --sat_non_cyclic_types                  false
% 15.70/2.41  --sat_finite_models                     false
% 15.70/2.41  --sat_fm_lemmas                         false
% 15.70/2.41  --sat_fm_prep                           false
% 15.70/2.41  --sat_fm_uc_incr                        true
% 15.70/2.41  --sat_out_model                         small
% 15.70/2.41  --sat_out_clauses                       false
% 15.70/2.41  
% 15.70/2.41  ------ QBF Options
% 15.70/2.41  
% 15.70/2.41  --qbf_mode                              false
% 15.70/2.41  --qbf_elim_univ                         false
% 15.70/2.41  --qbf_dom_inst                          none
% 15.70/2.41  --qbf_dom_pre_inst                      false
% 15.70/2.41  --qbf_sk_in                             false
% 15.70/2.41  --qbf_pred_elim                         true
% 15.70/2.41  --qbf_split                             512
% 15.70/2.41  
% 15.70/2.41  ------ BMC1 Options
% 15.70/2.41  
% 15.70/2.41  --bmc1_incremental                      false
% 15.70/2.41  --bmc1_axioms                           reachable_all
% 15.70/2.41  --bmc1_min_bound                        0
% 15.70/2.41  --bmc1_max_bound                        -1
% 15.70/2.41  --bmc1_max_bound_default                -1
% 15.70/2.41  --bmc1_symbol_reachability              true
% 15.70/2.41  --bmc1_property_lemmas                  false
% 15.70/2.41  --bmc1_k_induction                      false
% 15.70/2.41  --bmc1_non_equiv_states                 false
% 15.70/2.41  --bmc1_deadlock                         false
% 15.70/2.41  --bmc1_ucm                              false
% 15.70/2.41  --bmc1_add_unsat_core                   none
% 15.70/2.41  --bmc1_unsat_core_children              false
% 15.70/2.41  --bmc1_unsat_core_extrapolate_axioms    false
% 15.70/2.41  --bmc1_out_stat                         full
% 15.70/2.41  --bmc1_ground_init                      false
% 15.70/2.41  --bmc1_pre_inst_next_state              false
% 15.70/2.41  --bmc1_pre_inst_state                   false
% 15.70/2.41  --bmc1_pre_inst_reach_state             false
% 15.70/2.41  --bmc1_out_unsat_core                   false
% 15.70/2.41  --bmc1_aig_witness_out                  false
% 15.70/2.41  --bmc1_verbose                          false
% 15.70/2.41  --bmc1_dump_clauses_tptp                false
% 15.70/2.41  --bmc1_dump_unsat_core_tptp             false
% 15.70/2.41  --bmc1_dump_file                        -
% 15.70/2.41  --bmc1_ucm_expand_uc_limit              128
% 15.70/2.41  --bmc1_ucm_n_expand_iterations          6
% 15.70/2.41  --bmc1_ucm_extend_mode                  1
% 15.70/2.41  --bmc1_ucm_init_mode                    2
% 15.70/2.41  --bmc1_ucm_cone_mode                    none
% 15.70/2.41  --bmc1_ucm_reduced_relation_type        0
% 15.70/2.41  --bmc1_ucm_relax_model                  4
% 15.70/2.41  --bmc1_ucm_full_tr_after_sat            true
% 15.70/2.41  --bmc1_ucm_expand_neg_assumptions       false
% 15.70/2.41  --bmc1_ucm_layered_model                none
% 15.70/2.41  --bmc1_ucm_max_lemma_size               10
% 15.70/2.41  
% 15.70/2.41  ------ AIG Options
% 15.70/2.41  
% 15.70/2.41  --aig_mode                              false
% 15.70/2.41  
% 15.70/2.41  ------ Instantiation Options
% 15.70/2.41  
% 15.70/2.41  --instantiation_flag                    true
% 15.70/2.41  --inst_sos_flag                         true
% 15.70/2.41  --inst_sos_phase                        true
% 15.70/2.41  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 15.70/2.41  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 15.70/2.41  --inst_lit_sel_side                     none
% 15.70/2.41  --inst_solver_per_active                1400
% 15.70/2.41  --inst_solver_calls_frac                1.
% 15.70/2.41  --inst_passive_queue_type               priority_queues
% 15.70/2.41  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 15.70/2.41  --inst_passive_queues_freq              [25;2]
% 15.70/2.41  --inst_dismatching                      true
% 15.70/2.41  --inst_eager_unprocessed_to_passive     true
% 15.70/2.41  --inst_prop_sim_given                   true
% 15.70/2.41  --inst_prop_sim_new                     false
% 15.70/2.41  --inst_subs_new                         false
% 15.70/2.41  --inst_eq_res_simp                      false
% 15.70/2.41  --inst_subs_given                       false
% 15.70/2.41  --inst_orphan_elimination               true
% 15.70/2.41  --inst_learning_loop_flag               true
% 15.70/2.41  --inst_learning_start                   3000
% 15.70/2.41  --inst_learning_factor                  2
% 15.70/2.41  --inst_start_prop_sim_after_learn       3
% 15.70/2.41  --inst_sel_renew                        solver
% 15.70/2.41  --inst_lit_activity_flag                true
% 15.70/2.41  --inst_restr_to_given                   false
% 15.70/2.41  --inst_activity_threshold               500
% 15.70/2.41  --inst_out_proof                        true
% 15.70/2.41  
% 15.70/2.41  ------ Resolution Options
% 15.70/2.41  
% 15.70/2.41  --resolution_flag                       false
% 15.70/2.41  --res_lit_sel                           adaptive
% 15.70/2.41  --res_lit_sel_side                      none
% 15.70/2.41  --res_ordering                          kbo
% 15.70/2.41  --res_to_prop_solver                    active
% 15.70/2.41  --res_prop_simpl_new                    false
% 15.70/2.41  --res_prop_simpl_given                  true
% 15.70/2.41  --res_passive_queue_type                priority_queues
% 15.70/2.41  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 15.70/2.41  --res_passive_queues_freq               [15;5]
% 15.70/2.41  --res_forward_subs                      full
% 15.70/2.41  --res_backward_subs                     full
% 15.70/2.41  --res_forward_subs_resolution           true
% 15.70/2.41  --res_backward_subs_resolution          true
% 15.70/2.41  --res_orphan_elimination                true
% 15.70/2.41  --res_time_limit                        2.
% 15.70/2.41  --res_out_proof                         true
% 15.70/2.41  
% 15.70/2.41  ------ Superposition Options
% 15.70/2.41  
% 15.70/2.41  --superposition_flag                    true
% 15.70/2.41  --sup_passive_queue_type                priority_queues
% 15.70/2.41  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 15.70/2.41  --sup_passive_queues_freq               [8;1;4]
% 15.70/2.41  --demod_completeness_check              fast
% 15.70/2.41  --demod_use_ground                      true
% 15.70/2.41  --sup_to_prop_solver                    passive
% 15.70/2.41  --sup_prop_simpl_new                    true
% 15.70/2.41  --sup_prop_simpl_given                  true
% 15.70/2.41  --sup_fun_splitting                     true
% 15.70/2.41  --sup_smt_interval                      50000
% 15.70/2.41  
% 15.70/2.41  ------ Superposition Simplification Setup
% 15.70/2.41  
% 15.70/2.41  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 15.70/2.41  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 15.70/2.41  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 15.70/2.41  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 15.70/2.41  --sup_full_triv                         [TrivRules;PropSubs]
% 15.70/2.41  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 15.70/2.41  --sup_full_bw                           [BwDemod;BwSubsumption]
% 15.70/2.41  --sup_immed_triv                        [TrivRules]
% 15.70/2.41  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 15.70/2.41  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 15.70/2.41  --sup_immed_bw_main                     []
% 15.70/2.41  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 15.70/2.41  --sup_input_triv                        [Unflattening;TrivRules]
% 15.70/2.41  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 15.70/2.41  --sup_input_bw                          []
% 15.70/2.41  
% 15.70/2.41  ------ Combination Options
% 15.70/2.41  
% 15.70/2.41  --comb_res_mult                         3
% 15.70/2.41  --comb_sup_mult                         2
% 15.70/2.41  --comb_inst_mult                        10
% 15.70/2.41  
% 15.70/2.41  ------ Debug Options
% 15.70/2.41  
% 15.70/2.41  --dbg_backtrace                         false
% 15.70/2.41  --dbg_dump_prop_clauses                 false
% 15.70/2.41  --dbg_dump_prop_clauses_file            -
% 15.70/2.41  --dbg_out_stat                          false
% 15.70/2.41  
% 15.70/2.41  
% 15.70/2.41  
% 15.70/2.41  
% 15.70/2.41  ------ Proving...
% 15.70/2.41  
% 15.70/2.41  
% 15.70/2.41  % SZS status Theorem for theBenchmark.p
% 15.70/2.41  
% 15.70/2.41  % SZS output start CNFRefutation for theBenchmark.p
% 15.70/2.41  
% 15.70/2.41  fof(f3,axiom,(
% 15.70/2.41    ! [X0,X1] : (k3_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (r2_hidden(X3,X0) & r2_hidden(X2,X3))))),
% 15.70/2.41    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.70/2.41  
% 15.70/2.41  fof(f42,plain,(
% 15.70/2.41    ! [X0,X1] : ((k3_tarski(X0) = X1 | ? [X2] : ((! [X3] : (~r2_hidden(X3,X0) | ~r2_hidden(X2,X3)) | ~r2_hidden(X2,X1)) & (? [X3] : (r2_hidden(X3,X0) & r2_hidden(X2,X3)) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ! [X3] : (~r2_hidden(X3,X0) | ~r2_hidden(X2,X3))) & (? [X3] : (r2_hidden(X3,X0) & r2_hidden(X2,X3)) | ~r2_hidden(X2,X1))) | k3_tarski(X0) != X1))),
% 15.70/2.41    inference(nnf_transformation,[],[f3])).
% 15.70/2.41  
% 15.70/2.41  fof(f43,plain,(
% 15.70/2.41    ! [X0,X1] : ((k3_tarski(X0) = X1 | ? [X2] : ((! [X3] : (~r2_hidden(X3,X0) | ~r2_hidden(X2,X3)) | ~r2_hidden(X2,X1)) & (? [X4] : (r2_hidden(X4,X0) & r2_hidden(X2,X4)) | r2_hidden(X2,X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : (~r2_hidden(X6,X0) | ~r2_hidden(X5,X6))) & (? [X7] : (r2_hidden(X7,X0) & r2_hidden(X5,X7)) | ~r2_hidden(X5,X1))) | k3_tarski(X0) != X1))),
% 15.70/2.41    inference(rectify,[],[f42])).
% 15.70/2.41  
% 15.70/2.41  fof(f46,plain,(
% 15.70/2.41    ! [X5,X0] : (? [X7] : (r2_hidden(X7,X0) & r2_hidden(X5,X7)) => (r2_hidden(sK3(X0,X5),X0) & r2_hidden(X5,sK3(X0,X5))))),
% 15.70/2.41    introduced(choice_axiom,[])).
% 15.70/2.41  
% 15.70/2.41  fof(f45,plain,(
% 15.70/2.41    ( ! [X2] : (! [X1,X0] : (? [X4] : (r2_hidden(X4,X0) & r2_hidden(X2,X4)) => (r2_hidden(sK2(X0,X1),X0) & r2_hidden(X2,sK2(X0,X1))))) )),
% 15.70/2.41    introduced(choice_axiom,[])).
% 15.70/2.41  
% 15.70/2.41  fof(f44,plain,(
% 15.70/2.41    ! [X1,X0] : (? [X2] : ((! [X3] : (~r2_hidden(X3,X0) | ~r2_hidden(X2,X3)) | ~r2_hidden(X2,X1)) & (? [X4] : (r2_hidden(X4,X0) & r2_hidden(X2,X4)) | r2_hidden(X2,X1))) => ((! [X3] : (~r2_hidden(X3,X0) | ~r2_hidden(sK1(X0,X1),X3)) | ~r2_hidden(sK1(X0,X1),X1)) & (? [X4] : (r2_hidden(X4,X0) & r2_hidden(sK1(X0,X1),X4)) | r2_hidden(sK1(X0,X1),X1))))),
% 15.70/2.41    introduced(choice_axiom,[])).
% 15.70/2.41  
% 15.70/2.41  fof(f47,plain,(
% 15.70/2.41    ! [X0,X1] : ((k3_tarski(X0) = X1 | ((! [X3] : (~r2_hidden(X3,X0) | ~r2_hidden(sK1(X0,X1),X3)) | ~r2_hidden(sK1(X0,X1),X1)) & ((r2_hidden(sK2(X0,X1),X0) & r2_hidden(sK1(X0,X1),sK2(X0,X1))) | r2_hidden(sK1(X0,X1),X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : (~r2_hidden(X6,X0) | ~r2_hidden(X5,X6))) & ((r2_hidden(sK3(X0,X5),X0) & r2_hidden(X5,sK3(X0,X5))) | ~r2_hidden(X5,X1))) | k3_tarski(X0) != X1))),
% 15.70/2.41    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f43,f46,f45,f44])).
% 15.70/2.41  
% 15.70/2.41  fof(f73,plain,(
% 15.70/2.41    ( ! [X0,X1] : (k3_tarski(X0) = X1 | r2_hidden(sK2(X0,X1),X0) | r2_hidden(sK1(X0,X1),X1)) )),
% 15.70/2.41    inference(cnf_transformation,[],[f47])).
% 15.70/2.41  
% 15.70/2.41  fof(f9,axiom,(
% 15.70/2.41    ! [X0,X1] : (r2_hidden(X0,k1_ordinal1(X1)) <=> (X0 = X1 | r2_hidden(X0,X1)))),
% 15.70/2.41    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.70/2.41  
% 15.70/2.41  fof(f50,plain,(
% 15.70/2.41    ! [X0,X1] : ((r2_hidden(X0,k1_ordinal1(X1)) | (X0 != X1 & ~r2_hidden(X0,X1))) & ((X0 = X1 | r2_hidden(X0,X1)) | ~r2_hidden(X0,k1_ordinal1(X1))))),
% 15.70/2.41    inference(nnf_transformation,[],[f9])).
% 15.70/2.41  
% 15.70/2.41  fof(f51,plain,(
% 15.70/2.41    ! [X0,X1] : ((r2_hidden(X0,k1_ordinal1(X1)) | (X0 != X1 & ~r2_hidden(X0,X1))) & (X0 = X1 | r2_hidden(X0,X1) | ~r2_hidden(X0,k1_ordinal1(X1))))),
% 15.70/2.41    inference(flattening,[],[f50])).
% 15.70/2.41  
% 15.70/2.41  fof(f82,plain,(
% 15.70/2.41    ( ! [X0,X1] : (X0 = X1 | r2_hidden(X0,X1) | ~r2_hidden(X0,k1_ordinal1(X1))) )),
% 15.70/2.41    inference(cnf_transformation,[],[f51])).
% 15.70/2.41  
% 15.70/2.41  fof(f5,axiom,(
% 15.70/2.41    ! [X0] : k1_ordinal1(X0) = k2_xboole_0(X0,k1_tarski(X0))),
% 15.70/2.41    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.70/2.41  
% 15.70/2.41  fof(f76,plain,(
% 15.70/2.41    ( ! [X0] : (k1_ordinal1(X0) = k2_xboole_0(X0,k1_tarski(X0))) )),
% 15.70/2.41    inference(cnf_transformation,[],[f5])).
% 15.70/2.41  
% 15.70/2.41  fof(f104,plain,(
% 15.70/2.41    ( ! [X0,X1] : (X0 = X1 | r2_hidden(X0,X1) | ~r2_hidden(X0,k2_xboole_0(X1,k1_tarski(X1)))) )),
% 15.70/2.41    inference(definition_unfolding,[],[f82,f76])).
% 15.70/2.41  
% 15.70/2.41  fof(f72,plain,(
% 15.70/2.41    ( ! [X0,X1] : (k3_tarski(X0) = X1 | r2_hidden(sK1(X0,X1),sK2(X0,X1)) | r2_hidden(sK1(X0,X1),X1)) )),
% 15.70/2.41    inference(cnf_transformation,[],[f47])).
% 15.70/2.41  
% 15.70/2.41  fof(f18,conjecture,(
% 15.70/2.41    ! [X0] : (v3_ordinal1(X0) => (v4_ordinal1(X0) <=> ! [X1] : (v3_ordinal1(X1) => (r2_hidden(X1,X0) => r2_hidden(k1_ordinal1(X1),X0)))))),
% 15.70/2.41    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.70/2.41  
% 15.70/2.41  fof(f19,negated_conjecture,(
% 15.70/2.41    ~! [X0] : (v3_ordinal1(X0) => (v4_ordinal1(X0) <=> ! [X1] : (v3_ordinal1(X1) => (r2_hidden(X1,X0) => r2_hidden(k1_ordinal1(X1),X0)))))),
% 15.70/2.41    inference(negated_conjecture,[],[f18])).
% 15.70/2.41  
% 15.70/2.41  fof(f34,plain,(
% 15.70/2.41    ? [X0] : ((v4_ordinal1(X0) <~> ! [X1] : ((r2_hidden(k1_ordinal1(X1),X0) | ~r2_hidden(X1,X0)) | ~v3_ordinal1(X1))) & v3_ordinal1(X0))),
% 15.70/2.41    inference(ennf_transformation,[],[f19])).
% 15.70/2.41  
% 15.70/2.41  fof(f35,plain,(
% 15.70/2.41    ? [X0] : ((v4_ordinal1(X0) <~> ! [X1] : (r2_hidden(k1_ordinal1(X1),X0) | ~r2_hidden(X1,X0) | ~v3_ordinal1(X1))) & v3_ordinal1(X0))),
% 15.70/2.41    inference(flattening,[],[f34])).
% 15.70/2.41  
% 15.70/2.41  fof(f57,plain,(
% 15.70/2.41    ? [X0] : (((? [X1] : (~r2_hidden(k1_ordinal1(X1),X0) & r2_hidden(X1,X0) & v3_ordinal1(X1)) | ~v4_ordinal1(X0)) & (! [X1] : (r2_hidden(k1_ordinal1(X1),X0) | ~r2_hidden(X1,X0) | ~v3_ordinal1(X1)) | v4_ordinal1(X0))) & v3_ordinal1(X0))),
% 15.70/2.41    inference(nnf_transformation,[],[f35])).
% 15.70/2.41  
% 15.70/2.41  fof(f58,plain,(
% 15.70/2.41    ? [X0] : ((? [X1] : (~r2_hidden(k1_ordinal1(X1),X0) & r2_hidden(X1,X0) & v3_ordinal1(X1)) | ~v4_ordinal1(X0)) & (! [X1] : (r2_hidden(k1_ordinal1(X1),X0) | ~r2_hidden(X1,X0) | ~v3_ordinal1(X1)) | v4_ordinal1(X0)) & v3_ordinal1(X0))),
% 15.70/2.41    inference(flattening,[],[f57])).
% 15.70/2.41  
% 15.70/2.41  fof(f59,plain,(
% 15.70/2.41    ? [X0] : ((? [X1] : (~r2_hidden(k1_ordinal1(X1),X0) & r2_hidden(X1,X0) & v3_ordinal1(X1)) | ~v4_ordinal1(X0)) & (! [X2] : (r2_hidden(k1_ordinal1(X2),X0) | ~r2_hidden(X2,X0) | ~v3_ordinal1(X2)) | v4_ordinal1(X0)) & v3_ordinal1(X0))),
% 15.70/2.41    inference(rectify,[],[f58])).
% 15.70/2.41  
% 15.70/2.41  fof(f61,plain,(
% 15.70/2.41    ( ! [X0] : (? [X1] : (~r2_hidden(k1_ordinal1(X1),X0) & r2_hidden(X1,X0) & v3_ordinal1(X1)) => (~r2_hidden(k1_ordinal1(sK7),X0) & r2_hidden(sK7,X0) & v3_ordinal1(sK7))) )),
% 15.70/2.41    introduced(choice_axiom,[])).
% 15.70/2.41  
% 15.70/2.41  fof(f60,plain,(
% 15.70/2.41    ? [X0] : ((? [X1] : (~r2_hidden(k1_ordinal1(X1),X0) & r2_hidden(X1,X0) & v3_ordinal1(X1)) | ~v4_ordinal1(X0)) & (! [X2] : (r2_hidden(k1_ordinal1(X2),X0) | ~r2_hidden(X2,X0) | ~v3_ordinal1(X2)) | v4_ordinal1(X0)) & v3_ordinal1(X0)) => ((? [X1] : (~r2_hidden(k1_ordinal1(X1),sK6) & r2_hidden(X1,sK6) & v3_ordinal1(X1)) | ~v4_ordinal1(sK6)) & (! [X2] : (r2_hidden(k1_ordinal1(X2),sK6) | ~r2_hidden(X2,sK6) | ~v3_ordinal1(X2)) | v4_ordinal1(sK6)) & v3_ordinal1(sK6))),
% 15.70/2.41    introduced(choice_axiom,[])).
% 15.70/2.41  
% 15.70/2.41  fof(f62,plain,(
% 15.70/2.41    ((~r2_hidden(k1_ordinal1(sK7),sK6) & r2_hidden(sK7,sK6) & v3_ordinal1(sK7)) | ~v4_ordinal1(sK6)) & (! [X2] : (r2_hidden(k1_ordinal1(X2),sK6) | ~r2_hidden(X2,sK6) | ~v3_ordinal1(X2)) | v4_ordinal1(sK6)) & v3_ordinal1(sK6)),
% 15.70/2.41    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7])],[f59,f61,f60])).
% 15.70/2.41  
% 15.70/2.41  fof(f99,plain,(
% 15.70/2.41    r2_hidden(sK7,sK6) | ~v4_ordinal1(sK6)),
% 15.70/2.41    inference(cnf_transformation,[],[f62])).
% 15.70/2.41  
% 15.70/2.41  fof(f71,plain,(
% 15.70/2.41    ( ! [X6,X0,X5,X1] : (r2_hidden(X5,X1) | ~r2_hidden(X6,X0) | ~r2_hidden(X5,X6) | k3_tarski(X0) != X1) )),
% 15.70/2.41    inference(cnf_transformation,[],[f47])).
% 15.70/2.41  
% 15.70/2.41  fof(f113,plain,(
% 15.70/2.41    ( ! [X6,X0,X5] : (r2_hidden(X5,k3_tarski(X0)) | ~r2_hidden(X6,X0) | ~r2_hidden(X5,X6)) )),
% 15.70/2.41    inference(equality_resolution,[],[f71])).
% 15.70/2.41  
% 15.70/2.41  fof(f97,plain,(
% 15.70/2.41    ( ! [X2] : (r2_hidden(k1_ordinal1(X2),sK6) | ~r2_hidden(X2,sK6) | ~v3_ordinal1(X2) | v4_ordinal1(sK6)) )),
% 15.70/2.41    inference(cnf_transformation,[],[f62])).
% 15.70/2.41  
% 15.70/2.41  fof(f110,plain,(
% 15.70/2.41    ( ! [X2] : (r2_hidden(k2_xboole_0(X2,k1_tarski(X2)),sK6) | ~r2_hidden(X2,sK6) | ~v3_ordinal1(X2) | v4_ordinal1(sK6)) )),
% 15.70/2.41    inference(definition_unfolding,[],[f97,f76])).
% 15.70/2.41  
% 15.70/2.41  fof(f1,axiom,(
% 15.70/2.41    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 15.70/2.41    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.70/2.41  
% 15.70/2.41  fof(f20,plain,(
% 15.70/2.41    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 15.70/2.41    inference(ennf_transformation,[],[f1])).
% 15.70/2.41  
% 15.70/2.41  fof(f36,plain,(
% 15.70/2.41    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 15.70/2.41    inference(nnf_transformation,[],[f20])).
% 15.70/2.41  
% 15.70/2.41  fof(f37,plain,(
% 15.70/2.41    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 15.70/2.41    inference(rectify,[],[f36])).
% 15.70/2.41  
% 15.70/2.41  fof(f38,plain,(
% 15.70/2.41    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 15.70/2.41    introduced(choice_axiom,[])).
% 15.70/2.41  
% 15.70/2.41  fof(f39,plain,(
% 15.70/2.41    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 15.70/2.41    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f37,f38])).
% 15.70/2.41  
% 15.70/2.41  fof(f63,plain,(
% 15.70/2.41    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,X1)) )),
% 15.70/2.41    inference(cnf_transformation,[],[f39])).
% 15.70/2.41  
% 15.70/2.41  fof(f70,plain,(
% 15.70/2.41    ( ! [X0,X5,X1] : (r2_hidden(sK3(X0,X5),X0) | ~r2_hidden(X5,X1) | k3_tarski(X0) != X1) )),
% 15.70/2.41    inference(cnf_transformation,[],[f47])).
% 15.70/2.41  
% 15.70/2.41  fof(f114,plain,(
% 15.70/2.41    ( ! [X0,X5] : (r2_hidden(sK3(X0,X5),X0) | ~r2_hidden(X5,k3_tarski(X0))) )),
% 15.70/2.41    inference(equality_resolution,[],[f70])).
% 15.70/2.41  
% 15.70/2.41  fof(f11,axiom,(
% 15.70/2.41    ! [X0,X1] : (v3_ordinal1(X1) => (r2_hidden(X0,X1) => v3_ordinal1(X0)))),
% 15.70/2.41    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.70/2.41  
% 15.70/2.41  fof(f25,plain,(
% 15.70/2.41    ! [X0,X1] : ((v3_ordinal1(X0) | ~r2_hidden(X0,X1)) | ~v3_ordinal1(X1))),
% 15.70/2.41    inference(ennf_transformation,[],[f11])).
% 15.70/2.41  
% 15.70/2.41  fof(f26,plain,(
% 15.70/2.41    ! [X0,X1] : (v3_ordinal1(X0) | ~r2_hidden(X0,X1) | ~v3_ordinal1(X1))),
% 15.70/2.41    inference(flattening,[],[f25])).
% 15.70/2.41  
% 15.70/2.41  fof(f86,plain,(
% 15.70/2.41    ( ! [X0,X1] : (v3_ordinal1(X0) | ~r2_hidden(X0,X1) | ~v3_ordinal1(X1)) )),
% 15.70/2.41    inference(cnf_transformation,[],[f26])).
% 15.70/2.41  
% 15.70/2.41  fof(f96,plain,(
% 15.70/2.41    v3_ordinal1(sK6)),
% 15.70/2.41    inference(cnf_transformation,[],[f62])).
% 15.70/2.41  
% 15.70/2.41  fof(f6,axiom,(
% 15.70/2.41    ! [X0] : (v4_ordinal1(X0) <=> k3_tarski(X0) = X0)),
% 15.70/2.41    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.70/2.41  
% 15.70/2.41  fof(f48,plain,(
% 15.70/2.41    ! [X0] : ((v4_ordinal1(X0) | k3_tarski(X0) != X0) & (k3_tarski(X0) = X0 | ~v4_ordinal1(X0)))),
% 15.70/2.41    inference(nnf_transformation,[],[f6])).
% 15.70/2.41  
% 15.70/2.41  fof(f78,plain,(
% 15.70/2.41    ( ! [X0] : (v4_ordinal1(X0) | k3_tarski(X0) != X0) )),
% 15.70/2.41    inference(cnf_transformation,[],[f48])).
% 15.70/2.41  
% 15.70/2.41  fof(f12,axiom,(
% 15.70/2.41    ! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => ~(~r2_hidden(X1,X0) & X0 != X1 & ~r2_hidden(X0,X1))))),
% 15.70/2.41    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.70/2.41  
% 15.70/2.41  fof(f27,plain,(
% 15.70/2.41    ! [X0] : (! [X1] : ((r2_hidden(X1,X0) | X0 = X1 | r2_hidden(X0,X1)) | ~v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 15.70/2.41    inference(ennf_transformation,[],[f12])).
% 15.70/2.41  
% 15.70/2.41  fof(f28,plain,(
% 15.70/2.41    ! [X0] : (! [X1] : (r2_hidden(X1,X0) | X0 = X1 | r2_hidden(X0,X1) | ~v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 15.70/2.41    inference(flattening,[],[f27])).
% 15.70/2.41  
% 15.70/2.41  fof(f87,plain,(
% 15.70/2.41    ( ! [X0,X1] : (r2_hidden(X1,X0) | X0 = X1 | r2_hidden(X0,X1) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0)) )),
% 15.70/2.41    inference(cnf_transformation,[],[f28])).
% 15.70/2.41  
% 15.70/2.41  fof(f7,axiom,(
% 15.70/2.41    ! [X0,X1] : ((v3_ordinal1(X1) & v3_ordinal1(X0)) => (r1_ordinal1(X0,X1) <=> r1_tarski(X0,X1)))),
% 15.70/2.41    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.70/2.41  
% 15.70/2.41  fof(f23,plain,(
% 15.70/2.41    ! [X0,X1] : ((r1_ordinal1(X0,X1) <=> r1_tarski(X0,X1)) | (~v3_ordinal1(X1) | ~v3_ordinal1(X0)))),
% 15.70/2.41    inference(ennf_transformation,[],[f7])).
% 15.70/2.41  
% 15.70/2.41  fof(f24,plain,(
% 15.70/2.41    ! [X0,X1] : ((r1_ordinal1(X0,X1) <=> r1_tarski(X0,X1)) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0))),
% 15.70/2.41    inference(flattening,[],[f23])).
% 15.70/2.41  
% 15.70/2.41  fof(f49,plain,(
% 15.70/2.41    ! [X0,X1] : (((r1_ordinal1(X0,X1) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~r1_ordinal1(X0,X1))) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0))),
% 15.70/2.41    inference(nnf_transformation,[],[f24])).
% 15.70/2.41  
% 15.70/2.41  fof(f79,plain,(
% 15.70/2.41    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r1_ordinal1(X0,X1) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0)) )),
% 15.70/2.41    inference(cnf_transformation,[],[f49])).
% 15.70/2.41  
% 15.70/2.41  fof(f69,plain,(
% 15.70/2.41    ( ! [X0,X5,X1] : (r2_hidden(X5,sK3(X0,X5)) | ~r2_hidden(X5,X1) | k3_tarski(X0) != X1) )),
% 15.70/2.41    inference(cnf_transformation,[],[f47])).
% 15.70/2.41  
% 15.70/2.41  fof(f115,plain,(
% 15.70/2.41    ( ! [X0,X5] : (r2_hidden(X5,sK3(X0,X5)) | ~r2_hidden(X5,k3_tarski(X0))) )),
% 15.70/2.41    inference(equality_resolution,[],[f69])).
% 15.70/2.41  
% 15.70/2.41  fof(f17,axiom,(
% 15.70/2.41    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 15.70/2.41    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.70/2.41  
% 15.70/2.41  fof(f33,plain,(
% 15.70/2.41    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 15.70/2.41    inference(ennf_transformation,[],[f17])).
% 15.70/2.41  
% 15.70/2.41  fof(f95,plain,(
% 15.70/2.41    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1)) )),
% 15.70/2.41    inference(cnf_transformation,[],[f33])).
% 15.70/2.41  
% 15.70/2.41  fof(f14,axiom,(
% 15.70/2.41    ! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => (r2_hidden(X0,k1_ordinal1(X1)) <=> r1_ordinal1(X0,X1))))),
% 15.70/2.41    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.70/2.41  
% 15.70/2.41  fof(f30,plain,(
% 15.70/2.41    ! [X0] : (! [X1] : ((r2_hidden(X0,k1_ordinal1(X1)) <=> r1_ordinal1(X0,X1)) | ~v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 15.70/2.41    inference(ennf_transformation,[],[f14])).
% 15.70/2.41  
% 15.70/2.41  fof(f52,plain,(
% 15.70/2.41    ! [X0] : (! [X1] : (((r2_hidden(X0,k1_ordinal1(X1)) | ~r1_ordinal1(X0,X1)) & (r1_ordinal1(X0,X1) | ~r2_hidden(X0,k1_ordinal1(X1)))) | ~v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 15.70/2.41    inference(nnf_transformation,[],[f30])).
% 15.70/2.41  
% 15.70/2.41  fof(f89,plain,(
% 15.70/2.41    ( ! [X0,X1] : (r1_ordinal1(X0,X1) | ~r2_hidden(X0,k1_ordinal1(X1)) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0)) )),
% 15.70/2.41    inference(cnf_transformation,[],[f52])).
% 15.70/2.41  
% 15.70/2.41  fof(f108,plain,(
% 15.70/2.41    ( ! [X0,X1] : (r1_ordinal1(X0,X1) | ~r2_hidden(X0,k2_xboole_0(X1,k1_tarski(X1))) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0)) )),
% 15.70/2.41    inference(definition_unfolding,[],[f89,f76])).
% 15.70/2.41  
% 15.70/2.41  fof(f15,axiom,(
% 15.70/2.41    ! [X0] : (! [X1] : (r2_hidden(X1,X0) => v3_ordinal1(X1)) => v3_ordinal1(k3_tarski(X0)))),
% 15.70/2.41    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.70/2.41  
% 15.70/2.41  fof(f31,plain,(
% 15.70/2.41    ! [X0] : (v3_ordinal1(k3_tarski(X0)) | ? [X1] : (~v3_ordinal1(X1) & r2_hidden(X1,X0)))),
% 15.70/2.41    inference(ennf_transformation,[],[f15])).
% 15.70/2.41  
% 15.70/2.41  fof(f53,plain,(
% 15.70/2.41    ! [X0] : (? [X1] : (~v3_ordinal1(X1) & r2_hidden(X1,X0)) => (~v3_ordinal1(sK4(X0)) & r2_hidden(sK4(X0),X0)))),
% 15.70/2.41    introduced(choice_axiom,[])).
% 15.70/2.41  
% 15.70/2.41  fof(f54,plain,(
% 15.70/2.41    ! [X0] : (v3_ordinal1(k3_tarski(X0)) | (~v3_ordinal1(sK4(X0)) & r2_hidden(sK4(X0),X0)))),
% 15.70/2.41    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f31,f53])).
% 15.70/2.41  
% 15.70/2.41  fof(f91,plain,(
% 15.70/2.41    ( ! [X0] : (v3_ordinal1(k3_tarski(X0)) | r2_hidden(sK4(X0),X0)) )),
% 15.70/2.41    inference(cnf_transformation,[],[f54])).
% 15.70/2.41  
% 15.70/2.41  fof(f92,plain,(
% 15.70/2.41    ( ! [X0] : (v3_ordinal1(k3_tarski(X0)) | ~v3_ordinal1(sK4(X0))) )),
% 15.70/2.41    inference(cnf_transformation,[],[f54])).
% 15.70/2.41  
% 15.70/2.41  fof(f2,axiom,(
% 15.70/2.41    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 15.70/2.41    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.70/2.41  
% 15.70/2.41  fof(f40,plain,(
% 15.70/2.41    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 15.70/2.41    inference(nnf_transformation,[],[f2])).
% 15.70/2.41  
% 15.70/2.41  fof(f41,plain,(
% 15.70/2.41    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 15.70/2.41    inference(flattening,[],[f40])).
% 15.70/2.41  
% 15.70/2.41  fof(f66,plain,(
% 15.70/2.41    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 15.70/2.41    inference(cnf_transformation,[],[f41])).
% 15.70/2.41  
% 15.70/2.41  fof(f112,plain,(
% 15.70/2.41    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 15.70/2.41    inference(equality_resolution,[],[f66])).
% 15.70/2.41  
% 15.70/2.41  fof(f84,plain,(
% 15.70/2.41    ( ! [X0,X1] : (r2_hidden(X0,k1_ordinal1(X1)) | X0 != X1) )),
% 15.70/2.41    inference(cnf_transformation,[],[f51])).
% 15.70/2.41  
% 15.70/2.41  fof(f102,plain,(
% 15.70/2.41    ( ! [X0,X1] : (r2_hidden(X0,k2_xboole_0(X1,k1_tarski(X1))) | X0 != X1) )),
% 15.70/2.41    inference(definition_unfolding,[],[f84,f76])).
% 15.70/2.41  
% 15.70/2.41  fof(f116,plain,(
% 15.70/2.41    ( ! [X1] : (r2_hidden(X1,k2_xboole_0(X1,k1_tarski(X1)))) )),
% 15.70/2.41    inference(equality_resolution,[],[f102])).
% 15.70/2.41  
% 15.70/2.41  fof(f83,plain,(
% 15.70/2.41    ( ! [X0,X1] : (r2_hidden(X0,k1_ordinal1(X1)) | ~r2_hidden(X0,X1)) )),
% 15.70/2.41    inference(cnf_transformation,[],[f51])).
% 15.70/2.41  
% 15.70/2.41  fof(f103,plain,(
% 15.70/2.41    ( ! [X0,X1] : (r2_hidden(X0,k2_xboole_0(X1,k1_tarski(X1))) | ~r2_hidden(X0,X1)) )),
% 15.70/2.41    inference(definition_unfolding,[],[f83,f76])).
% 15.70/2.41  
% 15.70/2.41  fof(f77,plain,(
% 15.70/2.41    ( ! [X0] : (k3_tarski(X0) = X0 | ~v4_ordinal1(X0)) )),
% 15.70/2.41    inference(cnf_transformation,[],[f48])).
% 15.70/2.41  
% 15.70/2.41  fof(f100,plain,(
% 15.70/2.41    ~r2_hidden(k1_ordinal1(sK7),sK6) | ~v4_ordinal1(sK6)),
% 15.70/2.41    inference(cnf_transformation,[],[f62])).
% 15.70/2.41  
% 15.70/2.41  fof(f109,plain,(
% 15.70/2.41    ~r2_hidden(k2_xboole_0(sK7,k1_tarski(sK7)),sK6) | ~v4_ordinal1(sK6)),
% 15.70/2.41    inference(definition_unfolding,[],[f100,f76])).
% 15.70/2.41  
% 15.70/2.41  fof(f98,plain,(
% 15.70/2.41    v3_ordinal1(sK7) | ~v4_ordinal1(sK6)),
% 15.70/2.41    inference(cnf_transformation,[],[f62])).
% 15.70/2.41  
% 15.70/2.41  fof(f13,axiom,(
% 15.70/2.41    ! [X0] : (v3_ordinal1(X0) => v3_ordinal1(k1_ordinal1(X0)))),
% 15.70/2.41    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.70/2.41  
% 15.70/2.41  fof(f29,plain,(
% 15.70/2.41    ! [X0] : (v3_ordinal1(k1_ordinal1(X0)) | ~v3_ordinal1(X0))),
% 15.70/2.41    inference(ennf_transformation,[],[f13])).
% 15.70/2.41  
% 15.70/2.41  fof(f88,plain,(
% 15.70/2.41    ( ! [X0] : (v3_ordinal1(k1_ordinal1(X0)) | ~v3_ordinal1(X0)) )),
% 15.70/2.41    inference(cnf_transformation,[],[f29])).
% 15.70/2.41  
% 15.70/2.41  fof(f106,plain,(
% 15.70/2.41    ( ! [X0] : (v3_ordinal1(k2_xboole_0(X0,k1_tarski(X0))) | ~v3_ordinal1(X0)) )),
% 15.70/2.41    inference(definition_unfolding,[],[f88,f76])).
% 15.70/2.41  
% 15.70/2.41  fof(f65,plain,(
% 15.70/2.41    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r2_hidden(sK0(X0,X1),X1)) )),
% 15.70/2.41    inference(cnf_transformation,[],[f39])).
% 15.70/2.41  
% 15.70/2.41  fof(f74,plain,(
% 15.70/2.41    ( ! [X0,X3,X1] : (k3_tarski(X0) = X1 | ~r2_hidden(X3,X0) | ~r2_hidden(sK1(X0,X1),X3) | ~r2_hidden(sK1(X0,X1),X1)) )),
% 15.70/2.41    inference(cnf_transformation,[],[f47])).
% 15.70/2.41  
% 15.70/2.41  fof(f64,plain,(
% 15.70/2.41    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK0(X0,X1),X0)) )),
% 15.70/2.41    inference(cnf_transformation,[],[f39])).
% 15.70/2.41  
% 15.70/2.41  fof(f90,plain,(
% 15.70/2.41    ( ! [X0,X1] : (r2_hidden(X0,k1_ordinal1(X1)) | ~r1_ordinal1(X0,X1) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0)) )),
% 15.70/2.41    inference(cnf_transformation,[],[f52])).
% 15.70/2.41  
% 15.70/2.41  fof(f107,plain,(
% 15.70/2.41    ( ! [X0,X1] : (r2_hidden(X0,k2_xboole_0(X1,k1_tarski(X1))) | ~r1_ordinal1(X0,X1) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0)) )),
% 15.70/2.41    inference(definition_unfolding,[],[f90,f76])).
% 15.70/2.41  
% 15.70/2.41  cnf(c_7,plain,
% 15.70/2.41      ( r2_hidden(sK2(X0,X1),X0)
% 15.70/2.41      | r2_hidden(sK1(X0,X1),X1)
% 15.70/2.41      | k3_tarski(X0) = X1 ),
% 15.70/2.41      inference(cnf_transformation,[],[f73]) ).
% 15.70/2.41  
% 15.70/2.41  cnf(c_1666,plain,
% 15.70/2.41      ( k3_tarski(X0) = X1
% 15.70/2.41      | r2_hidden(sK2(X0,X1),X0) = iProver_top
% 15.70/2.41      | r2_hidden(sK1(X0,X1),X1) = iProver_top ),
% 15.70/2.41      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 15.70/2.41  
% 15.70/2.41  cnf(c_20,plain,
% 15.70/2.41      ( r2_hidden(X0,X1)
% 15.70/2.41      | ~ r2_hidden(X0,k2_xboole_0(X1,k1_tarski(X1)))
% 15.70/2.41      | X1 = X0 ),
% 15.70/2.41      inference(cnf_transformation,[],[f104]) ).
% 15.70/2.41  
% 15.70/2.41  cnf(c_1654,plain,
% 15.70/2.41      ( X0 = X1
% 15.70/2.41      | r2_hidden(X1,X0) = iProver_top
% 15.70/2.41      | r2_hidden(X1,k2_xboole_0(X0,k1_tarski(X0))) != iProver_top ),
% 15.70/2.41      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 15.70/2.41  
% 15.70/2.41  cnf(c_4525,plain,
% 15.70/2.41      ( sK2(k2_xboole_0(X0,k1_tarski(X0)),X1) = X0
% 15.70/2.41      | k3_tarski(k2_xboole_0(X0,k1_tarski(X0))) = X1
% 15.70/2.41      | r2_hidden(sK2(k2_xboole_0(X0,k1_tarski(X0)),X1),X0) = iProver_top
% 15.70/2.41      | r2_hidden(sK1(k2_xboole_0(X0,k1_tarski(X0)),X1),X1) = iProver_top ),
% 15.70/2.41      inference(superposition,[status(thm)],[c_1666,c_1654]) ).
% 15.70/2.41  
% 15.70/2.41  cnf(c_8,plain,
% 15.70/2.41      ( r2_hidden(sK1(X0,X1),X1)
% 15.70/2.41      | r2_hidden(sK1(X0,X1),sK2(X0,X1))
% 15.70/2.41      | k3_tarski(X0) = X1 ),
% 15.70/2.41      inference(cnf_transformation,[],[f72]) ).
% 15.70/2.41  
% 15.70/2.41  cnf(c_1665,plain,
% 15.70/2.41      ( k3_tarski(X0) = X1
% 15.70/2.41      | r2_hidden(sK1(X0,X1),X1) = iProver_top
% 15.70/2.41      | r2_hidden(sK1(X0,X1),sK2(X0,X1)) = iProver_top ),
% 15.70/2.41      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 15.70/2.41  
% 15.70/2.41  cnf(c_33,negated_conjecture,
% 15.70/2.41      ( r2_hidden(sK7,sK6) | ~ v4_ordinal1(sK6) ),
% 15.70/2.41      inference(cnf_transformation,[],[f99]) ).
% 15.70/2.41  
% 15.70/2.41  cnf(c_1642,plain,
% 15.70/2.41      ( r2_hidden(sK7,sK6) = iProver_top
% 15.70/2.41      | v4_ordinal1(sK6) != iProver_top ),
% 15.70/2.41      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 15.70/2.41  
% 15.70/2.41  cnf(c_9,plain,
% 15.70/2.41      ( ~ r2_hidden(X0,X1)
% 15.70/2.41      | ~ r2_hidden(X2,X0)
% 15.70/2.41      | r2_hidden(X2,k3_tarski(X1)) ),
% 15.70/2.41      inference(cnf_transformation,[],[f113]) ).
% 15.70/2.41  
% 15.70/2.41  cnf(c_1664,plain,
% 15.70/2.41      ( r2_hidden(X0,X1) != iProver_top
% 15.70/2.41      | r2_hidden(X2,X0) != iProver_top
% 15.70/2.41      | r2_hidden(X2,k3_tarski(X1)) = iProver_top ),
% 15.70/2.41      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 15.70/2.41  
% 15.70/2.41  cnf(c_4004,plain,
% 15.70/2.41      ( r2_hidden(X0,k3_tarski(sK6)) = iProver_top
% 15.70/2.41      | r2_hidden(X0,sK7) != iProver_top
% 15.70/2.41      | v4_ordinal1(sK6) != iProver_top ),
% 15.70/2.41      inference(superposition,[status(thm)],[c_1642,c_1664]) ).
% 15.70/2.41  
% 15.70/2.41  cnf(c_4190,plain,
% 15.70/2.41      ( r2_hidden(X0,X1) != iProver_top
% 15.70/2.41      | r2_hidden(X0,k3_tarski(k3_tarski(sK6))) = iProver_top
% 15.70/2.41      | r2_hidden(X1,sK7) != iProver_top
% 15.70/2.41      | v4_ordinal1(sK6) != iProver_top ),
% 15.70/2.41      inference(superposition,[status(thm)],[c_4004,c_1664]) ).
% 15.70/2.41  
% 15.70/2.41  cnf(c_5086,plain,
% 15.70/2.41      ( k3_tarski(X0) = X1
% 15.70/2.41      | r2_hidden(sK2(X0,X1),sK7) != iProver_top
% 15.70/2.41      | r2_hidden(sK1(X0,X1),X1) = iProver_top
% 15.70/2.41      | r2_hidden(sK1(X0,X1),k3_tarski(k3_tarski(sK6))) = iProver_top
% 15.70/2.41      | v4_ordinal1(sK6) != iProver_top ),
% 15.70/2.41      inference(superposition,[status(thm)],[c_1665,c_4190]) ).
% 15.70/2.41  
% 15.70/2.41  cnf(c_35,negated_conjecture,
% 15.70/2.41      ( ~ r2_hidden(X0,sK6)
% 15.70/2.41      | r2_hidden(k2_xboole_0(X0,k1_tarski(X0)),sK6)
% 15.70/2.41      | v4_ordinal1(sK6)
% 15.70/2.41      | ~ v3_ordinal1(X0) ),
% 15.70/2.41      inference(cnf_transformation,[],[f110]) ).
% 15.70/2.41  
% 15.70/2.41  cnf(c_1640,plain,
% 15.70/2.41      ( r2_hidden(X0,sK6) != iProver_top
% 15.70/2.41      | r2_hidden(k2_xboole_0(X0,k1_tarski(X0)),sK6) = iProver_top
% 15.70/2.41      | v4_ordinal1(sK6) = iProver_top
% 15.70/2.41      | v3_ordinal1(X0) != iProver_top ),
% 15.70/2.41      inference(predicate_to_equality,[status(thm)],[c_35]) ).
% 15.70/2.41  
% 15.70/2.41  cnf(c_2,plain,
% 15.70/2.41      ( ~ r2_hidden(X0,X1) | r2_hidden(X0,X2) | ~ r1_tarski(X1,X2) ),
% 15.70/2.41      inference(cnf_transformation,[],[f63]) ).
% 15.70/2.41  
% 15.70/2.41  cnf(c_1670,plain,
% 15.70/2.41      ( r2_hidden(X0,X1) != iProver_top
% 15.70/2.41      | r2_hidden(X0,X2) = iProver_top
% 15.70/2.41      | r1_tarski(X1,X2) != iProver_top ),
% 15.70/2.41      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 15.70/2.41  
% 15.70/2.41  cnf(c_3771,plain,
% 15.70/2.41      ( r2_hidden(X0,sK6) != iProver_top
% 15.70/2.41      | r2_hidden(k2_xboole_0(X0,k1_tarski(X0)),X1) = iProver_top
% 15.70/2.41      | r1_tarski(sK6,X1) != iProver_top
% 15.70/2.41      | v4_ordinal1(sK6) = iProver_top
% 15.70/2.41      | v3_ordinal1(X0) != iProver_top ),
% 15.70/2.41      inference(superposition,[status(thm)],[c_1640,c_1670]) ).
% 15.70/2.41  
% 15.70/2.41  cnf(c_10,plain,
% 15.70/2.41      ( ~ r2_hidden(X0,k3_tarski(X1)) | r2_hidden(sK3(X1,X0),X1) ),
% 15.70/2.41      inference(cnf_transformation,[],[f114]) ).
% 15.70/2.41  
% 15.70/2.41  cnf(c_1663,plain,
% 15.70/2.41      ( r2_hidden(X0,k3_tarski(X1)) != iProver_top
% 15.70/2.41      | r2_hidden(sK3(X1,X0),X1) = iProver_top ),
% 15.70/2.41      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 15.70/2.41  
% 15.70/2.41  cnf(c_22,plain,
% 15.70/2.41      ( ~ r2_hidden(X0,X1) | ~ v3_ordinal1(X1) | v3_ordinal1(X0) ),
% 15.70/2.41      inference(cnf_transformation,[],[f86]) ).
% 15.70/2.41  
% 15.70/2.41  cnf(c_1653,plain,
% 15.70/2.41      ( r2_hidden(X0,X1) != iProver_top
% 15.70/2.41      | v3_ordinal1(X1) != iProver_top
% 15.70/2.41      | v3_ordinal1(X0) = iProver_top ),
% 15.70/2.41      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 15.70/2.41  
% 15.70/2.41  cnf(c_3085,plain,
% 15.70/2.41      ( r2_hidden(X0,k3_tarski(X1)) != iProver_top
% 15.70/2.41      | v3_ordinal1(X1) != iProver_top
% 15.70/2.41      | v3_ordinal1(sK3(X1,X0)) = iProver_top ),
% 15.70/2.41      inference(superposition,[status(thm)],[c_1663,c_1653]) ).
% 15.70/2.41  
% 15.70/2.41  cnf(c_9764,plain,
% 15.70/2.41      ( r2_hidden(X0,sK6) != iProver_top
% 15.70/2.41      | r1_tarski(sK6,k3_tarski(X1)) != iProver_top
% 15.70/2.41      | v4_ordinal1(sK6) = iProver_top
% 15.70/2.41      | v3_ordinal1(X0) != iProver_top
% 15.70/2.41      | v3_ordinal1(X1) != iProver_top
% 15.70/2.41      | v3_ordinal1(sK3(X1,k2_xboole_0(X0,k1_tarski(X0)))) = iProver_top ),
% 15.70/2.41      inference(superposition,[status(thm)],[c_3771,c_3085]) ).
% 15.70/2.41  
% 15.70/2.41  cnf(c_36,negated_conjecture,
% 15.70/2.41      ( v3_ordinal1(sK6) ),
% 15.70/2.41      inference(cnf_transformation,[],[f96]) ).
% 15.70/2.41  
% 15.70/2.41  cnf(c_37,plain,
% 15.70/2.41      ( v3_ordinal1(sK6) = iProver_top ),
% 15.70/2.41      inference(predicate_to_equality,[status(thm)],[c_36]) ).
% 15.70/2.41  
% 15.70/2.41  cnf(c_13,plain,
% 15.70/2.41      ( v4_ordinal1(X0) | k3_tarski(X0) != X0 ),
% 15.70/2.41      inference(cnf_transformation,[],[f78]) ).
% 15.70/2.41  
% 15.70/2.41  cnf(c_92,plain,
% 15.70/2.41      ( k3_tarski(X0) != X0 | v4_ordinal1(X0) = iProver_top ),
% 15.70/2.41      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 15.70/2.41  
% 15.70/2.41  cnf(c_94,plain,
% 15.70/2.41      ( k3_tarski(sK6) != sK6 | v4_ordinal1(sK6) = iProver_top ),
% 15.70/2.41      inference(instantiation,[status(thm)],[c_92]) ).
% 15.70/2.41  
% 15.70/2.41  cnf(c_101,plain,
% 15.70/2.41      ( r2_hidden(X0,k3_tarski(X1)) != iProver_top
% 15.70/2.41      | r2_hidden(sK3(X1,X0),X1) = iProver_top ),
% 15.70/2.41      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 15.70/2.41  
% 15.70/2.41  cnf(c_103,plain,
% 15.70/2.41      ( r2_hidden(sK3(sK6,sK6),sK6) = iProver_top
% 15.70/2.41      | r2_hidden(sK6,k3_tarski(sK6)) != iProver_top ),
% 15.70/2.41      inference(instantiation,[status(thm)],[c_101]) ).
% 15.70/2.41  
% 15.70/2.41  cnf(c_23,plain,
% 15.70/2.41      ( r2_hidden(X0,X1)
% 15.70/2.41      | r2_hidden(X1,X0)
% 15.70/2.41      | ~ v3_ordinal1(X1)
% 15.70/2.41      | ~ v3_ordinal1(X0)
% 15.70/2.41      | X1 = X0 ),
% 15.70/2.41      inference(cnf_transformation,[],[f87]) ).
% 15.70/2.41  
% 15.70/2.41  cnf(c_1865,plain,
% 15.70/2.41      ( r2_hidden(k3_tarski(sK6),sK6)
% 15.70/2.41      | r2_hidden(sK6,k3_tarski(sK6))
% 15.70/2.41      | ~ v3_ordinal1(k3_tarski(sK6))
% 15.70/2.41      | ~ v3_ordinal1(sK6)
% 15.70/2.41      | k3_tarski(sK6) = sK6 ),
% 15.70/2.41      inference(instantiation,[status(thm)],[c_23]) ).
% 15.70/2.41  
% 15.70/2.41  cnf(c_1872,plain,
% 15.70/2.41      ( k3_tarski(sK6) = sK6
% 15.70/2.41      | r2_hidden(k3_tarski(sK6),sK6) = iProver_top
% 15.70/2.41      | r2_hidden(sK6,k3_tarski(sK6)) = iProver_top
% 15.70/2.41      | v3_ordinal1(k3_tarski(sK6)) != iProver_top
% 15.70/2.41      | v3_ordinal1(sK6) != iProver_top ),
% 15.70/2.41      inference(predicate_to_equality,[status(thm)],[c_1865]) ).
% 15.70/2.41  
% 15.70/2.41  cnf(c_16,plain,
% 15.70/2.41      ( ~ r1_ordinal1(X0,X1)
% 15.70/2.41      | r1_tarski(X0,X1)
% 15.70/2.41      | ~ v3_ordinal1(X1)
% 15.70/2.41      | ~ v3_ordinal1(X0) ),
% 15.70/2.41      inference(cnf_transformation,[],[f79]) ).
% 15.70/2.41  
% 15.70/2.41  cnf(c_2335,plain,
% 15.70/2.41      ( ~ r1_ordinal1(sK3(X0,X1),sK6)
% 15.70/2.41      | r1_tarski(sK3(X0,X1),sK6)
% 15.70/2.41      | ~ v3_ordinal1(sK3(X0,X1))
% 15.70/2.41      | ~ v3_ordinal1(sK6) ),
% 15.70/2.41      inference(instantiation,[status(thm)],[c_16]) ).
% 15.70/2.41  
% 15.70/2.41  cnf(c_2346,plain,
% 15.70/2.41      ( r1_ordinal1(sK3(X0,X1),sK6) != iProver_top
% 15.70/2.41      | r1_tarski(sK3(X0,X1),sK6) = iProver_top
% 15.70/2.41      | v3_ordinal1(sK3(X0,X1)) != iProver_top
% 15.70/2.41      | v3_ordinal1(sK6) != iProver_top ),
% 15.70/2.41      inference(predicate_to_equality,[status(thm)],[c_2335]) ).
% 15.70/2.41  
% 15.70/2.41  cnf(c_2348,plain,
% 15.70/2.41      ( r1_ordinal1(sK3(sK6,sK6),sK6) != iProver_top
% 15.70/2.41      | r1_tarski(sK3(sK6,sK6),sK6) = iProver_top
% 15.70/2.41      | v3_ordinal1(sK3(sK6,sK6)) != iProver_top
% 15.70/2.41      | v3_ordinal1(sK6) != iProver_top ),
% 15.70/2.41      inference(instantiation,[status(thm)],[c_2346]) ).
% 15.70/2.41  
% 15.70/2.41  cnf(c_11,plain,
% 15.70/2.41      ( r2_hidden(X0,sK3(X1,X0)) | ~ r2_hidden(X0,k3_tarski(X1)) ),
% 15.70/2.41      inference(cnf_transformation,[],[f115]) ).
% 15.70/2.41  
% 15.70/2.41  cnf(c_1662,plain,
% 15.70/2.41      ( r2_hidden(X0,sK3(X1,X0)) = iProver_top
% 15.70/2.41      | r2_hidden(X0,k3_tarski(X1)) != iProver_top ),
% 15.70/2.41      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 15.70/2.41  
% 15.70/2.41  cnf(c_31,plain,
% 15.70/2.41      ( ~ r2_hidden(X0,X1) | ~ r1_tarski(X1,X0) ),
% 15.70/2.41      inference(cnf_transformation,[],[f95]) ).
% 15.70/2.41  
% 15.70/2.41  cnf(c_1644,plain,
% 15.70/2.41      ( r2_hidden(X0,X1) != iProver_top
% 15.70/2.41      | r1_tarski(X1,X0) != iProver_top ),
% 15.70/2.41      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 15.70/2.41  
% 15.70/2.41  cnf(c_2907,plain,
% 15.70/2.41      ( r2_hidden(X0,k3_tarski(X1)) != iProver_top
% 15.70/2.41      | r1_tarski(sK3(X1,X0),X0) != iProver_top ),
% 15.70/2.41      inference(superposition,[status(thm)],[c_1662,c_1644]) ).
% 15.70/2.41  
% 15.70/2.41  cnf(c_2909,plain,
% 15.70/2.41      ( r2_hidden(sK6,k3_tarski(sK6)) != iProver_top
% 15.70/2.41      | r1_tarski(sK3(sK6,sK6),sK6) != iProver_top ),
% 15.70/2.41      inference(instantiation,[status(thm)],[c_2907]) ).
% 15.70/2.41  
% 15.70/2.41  cnf(c_26,plain,
% 15.70/2.41      ( r1_ordinal1(X0,X1)
% 15.70/2.41      | ~ r2_hidden(X0,k2_xboole_0(X1,k1_tarski(X1)))
% 15.70/2.41      | ~ v3_ordinal1(X1)
% 15.70/2.41      | ~ v3_ordinal1(X0) ),
% 15.70/2.41      inference(cnf_transformation,[],[f108]) ).
% 15.70/2.41  
% 15.70/2.41  cnf(c_5544,plain,
% 15.70/2.41      ( r1_ordinal1(sK3(X0,X1),sK6)
% 15.70/2.41      | ~ r2_hidden(sK3(X0,X1),k2_xboole_0(sK6,k1_tarski(sK6)))
% 15.70/2.41      | ~ v3_ordinal1(sK3(X0,X1))
% 15.70/2.41      | ~ v3_ordinal1(sK6) ),
% 15.70/2.41      inference(instantiation,[status(thm)],[c_26]) ).
% 15.70/2.41  
% 15.70/2.41  cnf(c_5555,plain,
% 15.70/2.41      ( r1_ordinal1(sK3(X0,X1),sK6) = iProver_top
% 15.70/2.41      | r2_hidden(sK3(X0,X1),k2_xboole_0(sK6,k1_tarski(sK6))) != iProver_top
% 15.70/2.41      | v3_ordinal1(sK3(X0,X1)) != iProver_top
% 15.70/2.41      | v3_ordinal1(sK6) != iProver_top ),
% 15.70/2.41      inference(predicate_to_equality,[status(thm)],[c_5544]) ).
% 15.70/2.41  
% 15.70/2.41  cnf(c_5557,plain,
% 15.70/2.41      ( r1_ordinal1(sK3(sK6,sK6),sK6) = iProver_top
% 15.70/2.41      | r2_hidden(sK3(sK6,sK6),k2_xboole_0(sK6,k1_tarski(sK6))) != iProver_top
% 15.70/2.41      | v3_ordinal1(sK3(sK6,sK6)) != iProver_top
% 15.70/2.41      | v3_ordinal1(sK6) != iProver_top ),
% 15.70/2.41      inference(instantiation,[status(thm)],[c_5555]) ).
% 15.70/2.41  
% 15.70/2.41  cnf(c_28,plain,
% 15.70/2.41      ( r2_hidden(sK4(X0),X0) | v3_ordinal1(k3_tarski(X0)) ),
% 15.70/2.41      inference(cnf_transformation,[],[f91]) ).
% 15.70/2.41  
% 15.70/2.41  cnf(c_1647,plain,
% 15.70/2.41      ( r2_hidden(sK4(X0),X0) = iProver_top
% 15.70/2.41      | v3_ordinal1(k3_tarski(X0)) = iProver_top ),
% 15.70/2.41      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 15.70/2.41  
% 15.70/2.41  cnf(c_3089,plain,
% 15.70/2.41      ( v3_ordinal1(X0) != iProver_top
% 15.70/2.41      | v3_ordinal1(sK4(X0)) = iProver_top
% 15.70/2.41      | v3_ordinal1(k3_tarski(X0)) = iProver_top ),
% 15.70/2.41      inference(superposition,[status(thm)],[c_1647,c_1653]) ).
% 15.70/2.41  
% 15.70/2.41  cnf(c_27,plain,
% 15.70/2.41      ( ~ v3_ordinal1(sK4(X0)) | v3_ordinal1(k3_tarski(X0)) ),
% 15.70/2.41      inference(cnf_transformation,[],[f92]) ).
% 15.70/2.41  
% 15.70/2.41  cnf(c_56,plain,
% 15.70/2.41      ( v3_ordinal1(sK4(X0)) != iProver_top
% 15.70/2.41      | v3_ordinal1(k3_tarski(X0)) = iProver_top ),
% 15.70/2.41      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 15.70/2.41  
% 15.70/2.41  cnf(c_8421,plain,
% 15.70/2.41      ( v3_ordinal1(X0) != iProver_top
% 15.70/2.41      | v3_ordinal1(k3_tarski(X0)) = iProver_top ),
% 15.70/2.41      inference(global_propositional_subsumption,
% 15.70/2.41                [status(thm)],
% 15.70/2.41                [c_3089,c_56]) ).
% 15.70/2.41  
% 15.70/2.41  cnf(c_8424,plain,
% 15.70/2.41      ( v3_ordinal1(k3_tarski(sK6)) = iProver_top
% 15.70/2.41      | v3_ordinal1(sK6) != iProver_top ),
% 15.70/2.41      inference(instantiation,[status(thm)],[c_8421]) ).
% 15.70/2.41  
% 15.70/2.41  cnf(c_5,plain,
% 15.70/2.41      ( r1_tarski(X0,X0) ),
% 15.70/2.41      inference(cnf_transformation,[],[f112]) ).
% 15.70/2.41  
% 15.70/2.41  cnf(c_1668,plain,
% 15.70/2.41      ( r1_tarski(X0,X0) = iProver_top ),
% 15.70/2.41      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 15.70/2.41  
% 15.70/2.41  cnf(c_18,plain,
% 15.70/2.41      ( r2_hidden(X0,k2_xboole_0(X0,k1_tarski(X0))) ),
% 15.70/2.41      inference(cnf_transformation,[],[f116]) ).
% 15.70/2.41  
% 15.70/2.41  cnf(c_1656,plain,
% 15.70/2.41      ( r2_hidden(X0,k2_xboole_0(X0,k1_tarski(X0))) = iProver_top ),
% 15.70/2.41      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 15.70/2.41  
% 15.70/2.41  cnf(c_4005,plain,
% 15.70/2.41      ( r2_hidden(X0,k2_xboole_0(X1,k1_tarski(X1))) != iProver_top
% 15.70/2.41      | r2_hidden(X0,k3_tarski(sK6)) = iProver_top
% 15.70/2.41      | r2_hidden(X1,sK6) != iProver_top
% 15.70/2.41      | v4_ordinal1(sK6) = iProver_top
% 15.70/2.41      | v3_ordinal1(X1) != iProver_top ),
% 15.70/2.41      inference(superposition,[status(thm)],[c_1640,c_1664]) ).
% 15.70/2.41  
% 15.70/2.41  cnf(c_4270,plain,
% 15.70/2.41      ( r2_hidden(X0,k3_tarski(sK6)) = iProver_top
% 15.70/2.41      | r2_hidden(X0,sK6) != iProver_top
% 15.70/2.41      | v4_ordinal1(sK6) = iProver_top
% 15.70/2.41      | v3_ordinal1(X0) != iProver_top ),
% 15.70/2.41      inference(superposition,[status(thm)],[c_1656,c_4005]) ).
% 15.70/2.41  
% 15.70/2.41  cnf(c_5317,plain,
% 15.70/2.41      ( r2_hidden(X0,sK6) != iProver_top
% 15.70/2.41      | r1_tarski(k3_tarski(sK6),X0) != iProver_top
% 15.70/2.41      | v4_ordinal1(sK6) = iProver_top
% 15.70/2.41      | v3_ordinal1(X0) != iProver_top ),
% 15.70/2.41      inference(superposition,[status(thm)],[c_4270,c_1644]) ).
% 15.70/2.41  
% 15.70/2.41  cnf(c_9673,plain,
% 15.70/2.41      ( r2_hidden(k3_tarski(sK6),sK6) != iProver_top
% 15.70/2.41      | v4_ordinal1(sK6) = iProver_top
% 15.70/2.41      | v3_ordinal1(k3_tarski(sK6)) != iProver_top ),
% 15.70/2.41      inference(superposition,[status(thm)],[c_1668,c_5317]) ).
% 15.70/2.41  
% 15.70/2.41  cnf(c_1652,plain,
% 15.70/2.41      ( X0 = X1
% 15.70/2.41      | r2_hidden(X1,X0) = iProver_top
% 15.70/2.41      | r2_hidden(X0,X1) = iProver_top
% 15.70/2.41      | v3_ordinal1(X1) != iProver_top
% 15.70/2.41      | v3_ordinal1(X0) != iProver_top ),
% 15.70/2.41      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 15.70/2.41  
% 15.70/2.41  cnf(c_9758,plain,
% 15.70/2.41      ( k3_tarski(X0) = X1
% 15.70/2.41      | r2_hidden(k3_tarski(X0),X1) = iProver_top
% 15.70/2.41      | v3_ordinal1(X0) != iProver_top
% 15.70/2.41      | v3_ordinal1(X1) != iProver_top
% 15.70/2.41      | v3_ordinal1(sK3(X0,X1)) = iProver_top
% 15.70/2.41      | v3_ordinal1(k3_tarski(X0)) != iProver_top ),
% 15.70/2.41      inference(superposition,[status(thm)],[c_1652,c_3085]) ).
% 15.70/2.41  
% 15.70/2.41  cnf(c_9789,plain,
% 15.70/2.41      ( k3_tarski(sK6) = sK6
% 15.70/2.41      | r2_hidden(k3_tarski(sK6),sK6) = iProver_top
% 15.70/2.41      | v3_ordinal1(sK3(sK6,sK6)) = iProver_top
% 15.70/2.41      | v3_ordinal1(k3_tarski(sK6)) != iProver_top
% 15.70/2.41      | v3_ordinal1(sK6) != iProver_top ),
% 15.70/2.41      inference(instantiation,[status(thm)],[c_9758]) ).
% 15.70/2.41  
% 15.70/2.41  cnf(c_19,plain,
% 15.70/2.41      ( ~ r2_hidden(X0,X1)
% 15.70/2.41      | r2_hidden(X0,k2_xboole_0(X1,k1_tarski(X1))) ),
% 15.70/2.41      inference(cnf_transformation,[],[f103]) ).
% 15.70/2.41  
% 15.70/2.41  cnf(c_9922,plain,
% 15.70/2.41      ( ~ r2_hidden(sK3(sK6,X0),X1)
% 15.70/2.41      | r2_hidden(sK3(sK6,X0),k2_xboole_0(X1,k1_tarski(X1))) ),
% 15.70/2.41      inference(instantiation,[status(thm)],[c_19]) ).
% 15.70/2.41  
% 15.70/2.41  cnf(c_9923,plain,
% 15.70/2.41      ( r2_hidden(sK3(sK6,X0),X1) != iProver_top
% 15.70/2.41      | r2_hidden(sK3(sK6,X0),k2_xboole_0(X1,k1_tarski(X1))) = iProver_top ),
% 15.70/2.41      inference(predicate_to_equality,[status(thm)],[c_9922]) ).
% 15.70/2.41  
% 15.70/2.41  cnf(c_9925,plain,
% 15.70/2.41      ( r2_hidden(sK3(sK6,sK6),k2_xboole_0(sK6,k1_tarski(sK6))) = iProver_top
% 15.70/2.41      | r2_hidden(sK3(sK6,sK6),sK6) != iProver_top ),
% 15.70/2.41      inference(instantiation,[status(thm)],[c_9923]) ).
% 15.70/2.41  
% 15.70/2.41  cnf(c_10713,plain,
% 15.70/2.41      ( v4_ordinal1(sK6) = iProver_top ),
% 15.70/2.41      inference(global_propositional_subsumption,
% 15.70/2.41                [status(thm)],
% 15.70/2.41                [c_9764,c_37,c_94,c_103,c_1872,c_2348,c_2909,c_5557,
% 15.70/2.41                 c_8424,c_9673,c_9789,c_9925]) ).
% 15.70/2.41  
% 15.70/2.41  cnf(c_20422,plain,
% 15.70/2.41      ( r2_hidden(sK1(X0,X1),k3_tarski(k3_tarski(sK6))) = iProver_top
% 15.70/2.41      | r2_hidden(sK1(X0,X1),X1) = iProver_top
% 15.70/2.41      | r2_hidden(sK2(X0,X1),sK7) != iProver_top
% 15.70/2.41      | k3_tarski(X0) = X1 ),
% 15.70/2.41      inference(global_propositional_subsumption,
% 15.70/2.41                [status(thm)],
% 15.70/2.41                [c_5086,c_37,c_94,c_103,c_1872,c_2348,c_2909,c_5557,
% 15.70/2.41                 c_8424,c_9673,c_9789,c_9925]) ).
% 15.70/2.41  
% 15.70/2.41  cnf(c_20423,plain,
% 15.70/2.41      ( k3_tarski(X0) = X1
% 15.70/2.41      | r2_hidden(sK2(X0,X1),sK7) != iProver_top
% 15.70/2.41      | r2_hidden(sK1(X0,X1),X1) = iProver_top
% 15.70/2.41      | r2_hidden(sK1(X0,X1),k3_tarski(k3_tarski(sK6))) = iProver_top ),
% 15.70/2.41      inference(renaming,[status(thm)],[c_20422]) ).
% 15.70/2.41  
% 15.70/2.41  cnf(c_14,plain,
% 15.70/2.41      ( ~ v4_ordinal1(X0) | k3_tarski(X0) = X0 ),
% 15.70/2.41      inference(cnf_transformation,[],[f77]) ).
% 15.70/2.41  
% 15.70/2.41  cnf(c_1659,plain,
% 15.70/2.41      ( k3_tarski(X0) = X0 | v4_ordinal1(X0) != iProver_top ),
% 15.70/2.41      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 15.70/2.41  
% 15.70/2.41  cnf(c_10717,plain,
% 15.70/2.41      ( k3_tarski(sK6) = sK6 ),
% 15.70/2.41      inference(superposition,[status(thm)],[c_10713,c_1659]) ).
% 15.70/2.41  
% 15.70/2.41  cnf(c_20426,plain,
% 15.70/2.41      ( k3_tarski(X0) = X1
% 15.70/2.41      | r2_hidden(sK2(X0,X1),sK7) != iProver_top
% 15.70/2.41      | r2_hidden(sK1(X0,X1),X1) = iProver_top
% 15.70/2.41      | r2_hidden(sK1(X0,X1),sK6) = iProver_top ),
% 15.70/2.41      inference(light_normalisation,[status(thm)],[c_20423,c_10717]) ).
% 15.70/2.41  
% 15.70/2.41  cnf(c_45060,plain,
% 15.70/2.41      ( sK2(k2_xboole_0(sK7,k1_tarski(sK7)),X0) = sK7
% 15.70/2.41      | k3_tarski(k2_xboole_0(sK7,k1_tarski(sK7))) = X0
% 15.70/2.41      | r2_hidden(sK1(k2_xboole_0(sK7,k1_tarski(sK7)),X0),X0) = iProver_top
% 15.70/2.41      | r2_hidden(sK1(k2_xboole_0(sK7,k1_tarski(sK7)),X0),sK6) = iProver_top ),
% 15.70/2.41      inference(superposition,[status(thm)],[c_4525,c_20426]) ).
% 15.70/2.41  
% 15.70/2.41  cnf(c_32,negated_conjecture,
% 15.70/2.41      ( ~ r2_hidden(k2_xboole_0(sK7,k1_tarski(sK7)),sK6)
% 15.70/2.41      | ~ v4_ordinal1(sK6) ),
% 15.70/2.41      inference(cnf_transformation,[],[f109]) ).
% 15.70/2.41  
% 15.70/2.41  cnf(c_1643,plain,
% 15.70/2.41      ( r2_hidden(k2_xboole_0(sK7,k1_tarski(sK7)),sK6) != iProver_top
% 15.70/2.41      | v4_ordinal1(sK6) != iProver_top ),
% 15.70/2.41      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 15.70/2.41  
% 15.70/2.41  cnf(c_5497,plain,
% 15.70/2.41      ( k2_xboole_0(sK7,k1_tarski(sK7)) = sK6
% 15.70/2.41      | r2_hidden(sK6,k2_xboole_0(sK7,k1_tarski(sK7))) = iProver_top
% 15.70/2.41      | v4_ordinal1(sK6) != iProver_top
% 15.70/2.41      | v3_ordinal1(k2_xboole_0(sK7,k1_tarski(sK7))) != iProver_top
% 15.70/2.41      | v3_ordinal1(sK6) != iProver_top ),
% 15.70/2.41      inference(superposition,[status(thm)],[c_1652,c_1643]) ).
% 15.70/2.41  
% 15.70/2.41  cnf(c_34,negated_conjecture,
% 15.70/2.41      ( ~ v4_ordinal1(sK6) | v3_ordinal1(sK7) ),
% 15.70/2.41      inference(cnf_transformation,[],[f98]) ).
% 15.70/2.41  
% 15.70/2.41  cnf(c_41,plain,
% 15.70/2.41      ( v4_ordinal1(sK6) != iProver_top
% 15.70/2.41      | v3_ordinal1(sK7) = iProver_top ),
% 15.70/2.41      inference(predicate_to_equality,[status(thm)],[c_34]) ).
% 15.70/2.41  
% 15.70/2.41  cnf(c_42,plain,
% 15.70/2.41      ( r2_hidden(sK7,sK6) = iProver_top
% 15.70/2.41      | v4_ordinal1(sK6) != iProver_top ),
% 15.70/2.41      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 15.70/2.41  
% 15.70/2.41  cnf(c_43,plain,
% 15.70/2.41      ( r2_hidden(k2_xboole_0(sK7,k1_tarski(sK7)),sK6) != iProver_top
% 15.70/2.41      | v4_ordinal1(sK6) != iProver_top ),
% 15.70/2.41      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 15.70/2.41  
% 15.70/2.41  cnf(c_45,plain,
% 15.70/2.41      ( ~ r2_hidden(sK6,sK6) | ~ r1_tarski(sK6,sK6) ),
% 15.70/2.41      inference(instantiation,[status(thm)],[c_31]) ).
% 15.70/2.41  
% 15.70/2.41  cnf(c_44,plain,
% 15.70/2.41      ( r2_hidden(X0,X1) != iProver_top
% 15.70/2.41      | r1_tarski(X1,X0) != iProver_top ),
% 15.70/2.41      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 15.70/2.41  
% 15.70/2.41  cnf(c_46,plain,
% 15.70/2.41      ( r2_hidden(sK6,sK6) != iProver_top
% 15.70/2.41      | r1_tarski(sK6,sK6) != iProver_top ),
% 15.70/2.41      inference(instantiation,[status(thm)],[c_44]) ).
% 15.70/2.41  
% 15.70/2.41  cnf(c_60,plain,
% 15.70/2.41      ( r1_ordinal1(sK6,sK6)
% 15.70/2.41      | ~ r2_hidden(sK6,k2_xboole_0(sK6,k1_tarski(sK6)))
% 15.70/2.41      | ~ v3_ordinal1(sK6) ),
% 15.70/2.41      inference(instantiation,[status(thm)],[c_26]) ).
% 15.70/2.41  
% 15.70/2.41  cnf(c_59,plain,
% 15.70/2.41      ( r1_ordinal1(X0,X1) = iProver_top
% 15.70/2.41      | r2_hidden(X0,k2_xboole_0(X1,k1_tarski(X1))) != iProver_top
% 15.70/2.41      | v3_ordinal1(X0) != iProver_top
% 15.70/2.41      | v3_ordinal1(X1) != iProver_top ),
% 15.70/2.41      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 15.70/2.41  
% 15.70/2.41  cnf(c_61,plain,
% 15.70/2.41      ( r1_ordinal1(sK6,sK6) = iProver_top
% 15.70/2.41      | r2_hidden(sK6,k2_xboole_0(sK6,k1_tarski(sK6))) != iProver_top
% 15.70/2.41      | v3_ordinal1(sK6) != iProver_top ),
% 15.70/2.41      inference(instantiation,[status(thm)],[c_59]) ).
% 15.70/2.41  
% 15.70/2.41  cnf(c_69,plain,
% 15.70/2.41      ( r2_hidden(sK6,sK6) | ~ v3_ordinal1(sK6) | sK6 = sK6 ),
% 15.70/2.41      inference(instantiation,[status(thm)],[c_23]) ).
% 15.70/2.41  
% 15.70/2.41  cnf(c_80,plain,
% 15.70/2.41      ( r2_hidden(sK6,k2_xboole_0(sK6,k1_tarski(sK6))) ),
% 15.70/2.41      inference(instantiation,[status(thm)],[c_18]) ).
% 15.70/2.41  
% 15.70/2.41  cnf(c_79,plain,
% 15.70/2.41      ( r2_hidden(X0,k2_xboole_0(X0,k1_tarski(X0))) = iProver_top ),
% 15.70/2.41      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 15.70/2.41  
% 15.70/2.41  cnf(c_81,plain,
% 15.70/2.41      ( r2_hidden(sK6,k2_xboole_0(sK6,k1_tarski(sK6))) = iProver_top ),
% 15.70/2.41      inference(instantiation,[status(thm)],[c_79]) ).
% 15.70/2.41  
% 15.70/2.41  cnf(c_84,plain,
% 15.70/2.41      ( ~ r1_ordinal1(sK6,sK6)
% 15.70/2.41      | r1_tarski(sK6,sK6)
% 15.70/2.41      | ~ v3_ordinal1(sK6) ),
% 15.70/2.41      inference(instantiation,[status(thm)],[c_16]) ).
% 15.70/2.41  
% 15.70/2.41  cnf(c_83,plain,
% 15.70/2.41      ( r1_ordinal1(X0,X1) != iProver_top
% 15.70/2.41      | r1_tarski(X0,X1) = iProver_top
% 15.70/2.41      | v3_ordinal1(X0) != iProver_top
% 15.70/2.41      | v3_ordinal1(X1) != iProver_top ),
% 15.70/2.41      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 15.70/2.41  
% 15.70/2.41  cnf(c_85,plain,
% 15.70/2.41      ( r1_ordinal1(sK6,sK6) != iProver_top
% 15.70/2.41      | r1_tarski(sK6,sK6) = iProver_top
% 15.70/2.41      | v3_ordinal1(sK6) != iProver_top ),
% 15.70/2.41      inference(instantiation,[status(thm)],[c_83]) ).
% 15.70/2.41  
% 15.70/2.41  cnf(c_1765,plain,
% 15.70/2.41      ( r2_hidden(X0,k2_xboole_0(sK7,k1_tarski(sK7)))
% 15.70/2.41      | r2_hidden(k2_xboole_0(sK7,k1_tarski(sK7)),X0)
% 15.70/2.41      | ~ v3_ordinal1(X0)
% 15.70/2.41      | ~ v3_ordinal1(k2_xboole_0(sK7,k1_tarski(sK7)))
% 15.70/2.41      | k2_xboole_0(sK7,k1_tarski(sK7)) = X0 ),
% 15.70/2.41      inference(instantiation,[status(thm)],[c_23]) ).
% 15.70/2.41  
% 15.70/2.41  cnf(c_1776,plain,
% 15.70/2.41      ( k2_xboole_0(sK7,k1_tarski(sK7)) = X0
% 15.70/2.41      | r2_hidden(X0,k2_xboole_0(sK7,k1_tarski(sK7))) = iProver_top
% 15.70/2.41      | r2_hidden(k2_xboole_0(sK7,k1_tarski(sK7)),X0) = iProver_top
% 15.70/2.41      | v3_ordinal1(X0) != iProver_top
% 15.70/2.41      | v3_ordinal1(k2_xboole_0(sK7,k1_tarski(sK7))) != iProver_top ),
% 15.70/2.41      inference(predicate_to_equality,[status(thm)],[c_1765]) ).
% 15.70/2.41  
% 15.70/2.41  cnf(c_1778,plain,
% 15.70/2.41      ( k2_xboole_0(sK7,k1_tarski(sK7)) = sK6
% 15.70/2.41      | r2_hidden(k2_xboole_0(sK7,k1_tarski(sK7)),sK6) = iProver_top
% 15.70/2.41      | r2_hidden(sK6,k2_xboole_0(sK7,k1_tarski(sK7))) = iProver_top
% 15.70/2.41      | v3_ordinal1(k2_xboole_0(sK7,k1_tarski(sK7))) != iProver_top
% 15.70/2.41      | v3_ordinal1(sK6) != iProver_top ),
% 15.70/2.41      inference(instantiation,[status(thm)],[c_1776]) ).
% 15.70/2.41  
% 15.70/2.41  cnf(c_973,plain,
% 15.70/2.41      ( ~ r2_hidden(X0,X1) | r2_hidden(X2,X3) | X2 != X0 | X3 != X1 ),
% 15.70/2.41      theory(equality) ).
% 15.70/2.41  
% 15.70/2.41  cnf(c_1817,plain,
% 15.70/2.41      ( ~ r2_hidden(X0,X1) | r2_hidden(X2,sK6) | X2 != X0 | sK6 != X1 ),
% 15.70/2.41      inference(instantiation,[status(thm)],[c_973]) ).
% 15.70/2.41  
% 15.70/2.41  cnf(c_2060,plain,
% 15.70/2.41      ( r2_hidden(X0,sK6)
% 15.70/2.41      | ~ r2_hidden(sK7,sK6)
% 15.70/2.41      | X0 != sK7
% 15.70/2.41      | sK6 != sK6 ),
% 15.70/2.41      inference(instantiation,[status(thm)],[c_1817]) ).
% 15.70/2.41  
% 15.70/2.41  cnf(c_2062,plain,
% 15.70/2.41      ( X0 != sK7
% 15.70/2.41      | sK6 != sK6
% 15.70/2.41      | r2_hidden(X0,sK6) = iProver_top
% 15.70/2.41      | r2_hidden(sK7,sK6) != iProver_top ),
% 15.70/2.41      inference(predicate_to_equality,[status(thm)],[c_2060]) ).
% 15.70/2.41  
% 15.70/2.41  cnf(c_2064,plain,
% 15.70/2.41      ( sK6 != sK6
% 15.70/2.41      | sK6 != sK7
% 15.70/2.41      | r2_hidden(sK6,sK6) = iProver_top
% 15.70/2.41      | r2_hidden(sK7,sK6) != iProver_top ),
% 15.70/2.41      inference(instantiation,[status(thm)],[c_2062]) ).
% 15.70/2.41  
% 15.70/2.41  cnf(c_24,plain,
% 15.70/2.41      ( ~ v3_ordinal1(X0) | v3_ordinal1(k2_xboole_0(X0,k1_tarski(X0))) ),
% 15.70/2.41      inference(cnf_transformation,[],[f106]) ).
% 15.70/2.41  
% 15.70/2.41  cnf(c_2214,plain,
% 15.70/2.41      ( v3_ordinal1(k2_xboole_0(sK7,k1_tarski(sK7)))
% 15.70/2.41      | ~ v3_ordinal1(sK7) ),
% 15.70/2.41      inference(instantiation,[status(thm)],[c_24]) ).
% 15.70/2.41  
% 15.70/2.41  cnf(c_2215,plain,
% 15.70/2.41      ( v3_ordinal1(k2_xboole_0(sK7,k1_tarski(sK7))) = iProver_top
% 15.70/2.41      | v3_ordinal1(sK7) != iProver_top ),
% 15.70/2.41      inference(predicate_to_equality,[status(thm)],[c_2214]) ).
% 15.70/2.41  
% 15.70/2.41  cnf(c_972,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 15.70/2.41  
% 15.70/2.41  cnf(c_2558,plain,
% 15.70/2.41      ( X0 != X1 | X0 = sK7 | sK7 != X1 ),
% 15.70/2.41      inference(instantiation,[status(thm)],[c_972]) ).
% 15.70/2.41  
% 15.70/2.41  cnf(c_2559,plain,
% 15.70/2.41      ( sK6 != sK6 | sK6 = sK7 | sK7 != sK6 ),
% 15.70/2.41      inference(instantiation,[status(thm)],[c_2558]) ).
% 15.70/2.41  
% 15.70/2.41  cnf(c_3554,plain,
% 15.70/2.41      ( ~ r2_hidden(X0,k2_xboole_0(sK7,k1_tarski(sK7)))
% 15.70/2.41      | r2_hidden(X0,sK7)
% 15.70/2.41      | sK7 = X0 ),
% 15.70/2.41      inference(instantiation,[status(thm)],[c_20]) ).
% 15.70/2.41  
% 15.70/2.41  cnf(c_3560,plain,
% 15.70/2.41      ( sK7 = X0
% 15.70/2.41      | r2_hidden(X0,k2_xboole_0(sK7,k1_tarski(sK7))) != iProver_top
% 15.70/2.41      | r2_hidden(X0,sK7) = iProver_top ),
% 15.70/2.41      inference(predicate_to_equality,[status(thm)],[c_3554]) ).
% 15.70/2.41  
% 15.70/2.41  cnf(c_3562,plain,
% 15.70/2.41      ( sK7 = sK6
% 15.70/2.41      | r2_hidden(sK6,k2_xboole_0(sK7,k1_tarski(sK7))) != iProver_top
% 15.70/2.41      | r2_hidden(sK6,sK7) = iProver_top ),
% 15.70/2.41      inference(instantiation,[status(thm)],[c_3560]) ).
% 15.70/2.41  
% 15.70/2.41  cnf(c_5093,plain,
% 15.70/2.41      ( r2_hidden(sK6,sK7) != iProver_top
% 15.70/2.41      | r2_hidden(sK7,k3_tarski(k3_tarski(sK6))) = iProver_top
% 15.70/2.41      | v4_ordinal1(sK6) != iProver_top ),
% 15.70/2.41      inference(superposition,[status(thm)],[c_1642,c_4190]) ).
% 15.70/2.41  
% 15.70/2.41  cnf(c_1723,plain,
% 15.70/2.41      ( ~ r1_ordinal1(sK6,sK7)
% 15.70/2.41      | r1_tarski(sK6,sK7)
% 15.70/2.41      | ~ v3_ordinal1(sK6)
% 15.70/2.41      | ~ v3_ordinal1(sK7) ),
% 15.70/2.41      inference(instantiation,[status(thm)],[c_16]) ).
% 15.70/2.41  
% 15.70/2.41  cnf(c_1730,plain,
% 15.70/2.41      ( r1_ordinal1(sK6,sK7) != iProver_top
% 15.70/2.41      | r1_tarski(sK6,sK7) = iProver_top
% 15.70/2.41      | v3_ordinal1(sK6) != iProver_top
% 15.70/2.41      | v3_ordinal1(sK7) != iProver_top ),
% 15.70/2.41      inference(predicate_to_equality,[status(thm)],[c_1723]) ).
% 15.70/2.41  
% 15.70/2.41  cnf(c_2077,plain,
% 15.70/2.41      ( r1_ordinal1(sK6,sK7)
% 15.70/2.41      | ~ r2_hidden(sK6,k2_xboole_0(sK7,k1_tarski(sK7)))
% 15.70/2.41      | ~ v3_ordinal1(sK6)
% 15.70/2.41      | ~ v3_ordinal1(sK7) ),
% 15.70/2.41      inference(instantiation,[status(thm)],[c_26]) ).
% 15.70/2.41  
% 15.70/2.41  cnf(c_2084,plain,
% 15.70/2.41      ( r1_ordinal1(sK6,sK7) = iProver_top
% 15.70/2.41      | r2_hidden(sK6,k2_xboole_0(sK7,k1_tarski(sK7))) != iProver_top
% 15.70/2.41      | v3_ordinal1(sK6) != iProver_top
% 15.70/2.41      | v3_ordinal1(sK7) != iProver_top ),
% 15.70/2.41      inference(predicate_to_equality,[status(thm)],[c_2077]) ).
% 15.70/2.41  
% 15.70/2.41  cnf(c_2498,plain,
% 15.70/2.41      ( r1_tarski(sK6,sK7) != iProver_top
% 15.70/2.41      | v4_ordinal1(sK6) != iProver_top ),
% 15.70/2.41      inference(superposition,[status(thm)],[c_1642,c_1644]) ).
% 15.70/2.41  
% 15.70/2.41  cnf(c_2861,plain,
% 15.70/2.41      ( r2_hidden(X0,k2_xboole_0(sK7,k1_tarski(sK7)))
% 15.70/2.41      | ~ r2_hidden(X0,sK7) ),
% 15.70/2.41      inference(instantiation,[status(thm)],[c_19]) ).
% 15.70/2.41  
% 15.70/2.41  cnf(c_2862,plain,
% 15.70/2.41      ( r2_hidden(X0,k2_xboole_0(sK7,k1_tarski(sK7))) = iProver_top
% 15.70/2.41      | r2_hidden(X0,sK7) != iProver_top ),
% 15.70/2.41      inference(predicate_to_equality,[status(thm)],[c_2861]) ).
% 15.70/2.41  
% 15.70/2.41  cnf(c_2864,plain,
% 15.70/2.41      ( r2_hidden(sK6,k2_xboole_0(sK7,k1_tarski(sK7))) = iProver_top
% 15.70/2.41      | r2_hidden(sK6,sK7) != iProver_top ),
% 15.70/2.41      inference(instantiation,[status(thm)],[c_2862]) ).
% 15.70/2.41  
% 15.70/2.41  cnf(c_5256,plain,
% 15.70/2.41      ( r2_hidden(sK6,sK7) != iProver_top
% 15.70/2.41      | v4_ordinal1(sK6) != iProver_top ),
% 15.70/2.41      inference(global_propositional_subsumption,
% 15.70/2.41                [status(thm)],
% 15.70/2.41                [c_5093,c_37,c_41,c_1730,c_2084,c_2498,c_2864]) ).
% 15.70/2.41  
% 15.70/2.41  cnf(c_6118,plain,
% 15.70/2.41      ( k2_xboole_0(sK7,k1_tarski(sK7)) = sK6
% 15.70/2.41      | v4_ordinal1(sK6) != iProver_top ),
% 15.70/2.41      inference(global_propositional_subsumption,
% 15.70/2.41                [status(thm)],
% 15.70/2.41                [c_5497,c_36,c_37,c_41,c_42,c_43,c_45,c_46,c_60,c_61,
% 15.70/2.41                 c_69,c_80,c_81,c_84,c_85,c_1778,c_2064,c_2215,c_2559,
% 15.70/2.41                 c_3562,c_5256]) ).
% 15.70/2.41  
% 15.70/2.41  cnf(c_10718,plain,
% 15.70/2.41      ( k2_xboole_0(sK7,k1_tarski(sK7)) = sK6 ),
% 15.70/2.41      inference(superposition,[status(thm)],[c_10713,c_6118]) ).
% 15.70/2.41  
% 15.70/2.41  cnf(c_45070,plain,
% 15.70/2.41      ( sK2(sK6,X0) = sK7
% 15.70/2.41      | sK6 = X0
% 15.70/2.41      | r2_hidden(sK1(sK6,X0),X0) = iProver_top
% 15.70/2.41      | r2_hidden(sK1(sK6,X0),sK6) = iProver_top ),
% 15.70/2.41      inference(light_normalisation,
% 15.70/2.41                [status(thm)],
% 15.70/2.41                [c_45060,c_10717,c_10718]) ).
% 15.70/2.41  
% 15.70/2.41  cnf(c_1655,plain,
% 15.70/2.41      ( r2_hidden(X0,X1) != iProver_top
% 15.70/2.41      | r2_hidden(X0,k2_xboole_0(X1,k1_tarski(X1))) = iProver_top ),
% 15.70/2.41      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 15.70/2.41  
% 15.70/2.41  cnf(c_10832,plain,
% 15.70/2.41      ( r2_hidden(X0,sK6) = iProver_top
% 15.70/2.41      | r2_hidden(X0,sK7) != iProver_top ),
% 15.70/2.41      inference(superposition,[status(thm)],[c_10718,c_1655]) ).
% 15.70/2.41  
% 15.70/2.41  cnf(c_45475,plain,
% 15.70/2.41      ( sK2(sK6,sK7) = sK7
% 15.70/2.41      | sK6 = sK7
% 15.70/2.41      | r2_hidden(sK1(sK6,sK7),sK6) = iProver_top ),
% 15.70/2.41      inference(superposition,[status(thm)],[c_45070,c_10832]) ).
% 15.70/2.41  
% 15.70/2.41  cnf(c_89,plain,
% 15.70/2.41      ( k3_tarski(X0) = X0 | v4_ordinal1(X0) != iProver_top ),
% 15.70/2.41      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 15.70/2.41  
% 15.70/2.41  cnf(c_91,plain,
% 15.70/2.41      ( k3_tarski(sK6) = sK6 | v4_ordinal1(sK6) != iProver_top ),
% 15.70/2.41      inference(instantiation,[status(thm)],[c_89]) ).
% 15.70/2.41  
% 15.70/2.41  cnf(c_282,plain,
% 15.70/2.41      ( v4_ordinal1(X0) | k3_tarski(X0) != X0 ),
% 15.70/2.41      inference(prop_impl,[status(thm)],[c_13]) ).
% 15.70/2.41  
% 15.70/2.41  cnf(c_512,plain,
% 15.70/2.41      ( r2_hidden(sK7,sK6) | k3_tarski(X0) != X0 | sK6 != X0 ),
% 15.70/2.41      inference(resolution_lifted,[status(thm)],[c_282,c_33]) ).
% 15.70/2.41  
% 15.70/2.41  cnf(c_513,plain,
% 15.70/2.41      ( r2_hidden(sK7,sK6) | k3_tarski(sK6) != sK6 ),
% 15.70/2.41      inference(unflattening,[status(thm)],[c_512]) ).
% 15.70/2.41  
% 15.70/2.41  cnf(c_0,plain,
% 15.70/2.41      ( ~ r2_hidden(sK0(X0,X1),X1) | r1_tarski(X0,X1) ),
% 15.70/2.41      inference(cnf_transformation,[],[f65]) ).
% 15.70/2.41  
% 15.70/2.41  cnf(c_1832,plain,
% 15.70/2.41      ( ~ r2_hidden(sK0(k3_tarski(X0),sK6),sK6)
% 15.70/2.41      | r1_tarski(k3_tarski(X0),sK6) ),
% 15.70/2.41      inference(instantiation,[status(thm)],[c_0]) ).
% 15.70/2.41  
% 15.70/2.41  cnf(c_1838,plain,
% 15.70/2.41      ( r2_hidden(sK0(k3_tarski(X0),sK6),sK6) != iProver_top
% 15.70/2.41      | r1_tarski(k3_tarski(X0),sK6) = iProver_top ),
% 15.70/2.41      inference(predicate_to_equality,[status(thm)],[c_1832]) ).
% 15.70/2.41  
% 15.70/2.41  cnf(c_1840,plain,
% 15.70/2.41      ( r2_hidden(sK0(k3_tarski(sK6),sK6),sK6) != iProver_top
% 15.70/2.41      | r1_tarski(k3_tarski(sK6),sK6) = iProver_top ),
% 15.70/2.41      inference(instantiation,[status(thm)],[c_1838]) ).
% 15.70/2.41  
% 15.70/2.41  cnf(c_2371,plain,
% 15.70/2.41      ( k3_tarski(X0) != X1 | sK6 != X1 | sK6 = k3_tarski(X0) ),
% 15.70/2.41      inference(instantiation,[status(thm)],[c_972]) ).
% 15.70/2.41  
% 15.70/2.41  cnf(c_2372,plain,
% 15.70/2.41      ( k3_tarski(sK6) != sK6 | sK6 = k3_tarski(sK6) | sK6 != sK6 ),
% 15.70/2.41      inference(instantiation,[status(thm)],[c_2371]) ).
% 15.70/2.41  
% 15.70/2.41  cnf(c_2550,plain,
% 15.70/2.41      ( r2_hidden(k3_tarski(X0),sK6)
% 15.70/2.41      | ~ r2_hidden(sK7,sK6)
% 15.70/2.41      | k3_tarski(X0) != sK7
% 15.70/2.41      | sK6 != sK6 ),
% 15.70/2.41      inference(instantiation,[status(thm)],[c_2060]) ).
% 15.70/2.41  
% 15.70/2.41  cnf(c_2552,plain,
% 15.70/2.41      ( r2_hidden(k3_tarski(sK6),sK6)
% 15.70/2.41      | ~ r2_hidden(sK7,sK6)
% 15.70/2.41      | k3_tarski(sK6) != sK7
% 15.70/2.41      | sK6 != sK6 ),
% 15.70/2.41      inference(instantiation,[status(thm)],[c_2550]) ).
% 15.70/2.41  
% 15.70/2.41  cnf(c_2580,plain,
% 15.70/2.41      ( r2_hidden(X0,sK6)
% 15.70/2.41      | ~ r2_hidden(k3_tarski(sK6),sK6)
% 15.70/2.41      | X0 != k3_tarski(sK6)
% 15.70/2.41      | sK6 != sK6 ),
% 15.70/2.41      inference(instantiation,[status(thm)],[c_1817]) ).
% 15.70/2.41  
% 15.70/2.41  cnf(c_2583,plain,
% 15.70/2.41      ( ~ r2_hidden(k3_tarski(sK6),sK6)
% 15.70/2.41      | r2_hidden(sK6,sK6)
% 15.70/2.41      | sK6 != k3_tarski(sK6)
% 15.70/2.41      | sK6 != sK6 ),
% 15.70/2.41      inference(instantiation,[status(thm)],[c_2580]) ).
% 15.70/2.41  
% 15.70/2.41  cnf(c_7318,plain,
% 15.70/2.41      ( r2_hidden(sK1(X0,sK7),sK2(X0,sK7))
% 15.70/2.41      | r2_hidden(sK1(X0,sK7),sK7)
% 15.70/2.41      | k3_tarski(X0) = sK7 ),
% 15.70/2.41      inference(instantiation,[status(thm)],[c_8]) ).
% 15.70/2.41  
% 15.70/2.41  cnf(c_7320,plain,
% 15.70/2.41      ( k3_tarski(X0) = sK7
% 15.70/2.41      | r2_hidden(sK1(X0,sK7),sK2(X0,sK7)) = iProver_top
% 15.70/2.41      | r2_hidden(sK1(X0,sK7),sK7) = iProver_top ),
% 15.70/2.41      inference(predicate_to_equality,[status(thm)],[c_7318]) ).
% 15.70/2.41  
% 15.70/2.41  cnf(c_7322,plain,
% 15.70/2.41      ( k3_tarski(sK6) = sK7
% 15.70/2.41      | r2_hidden(sK1(sK6,sK7),sK2(sK6,sK7)) = iProver_top
% 15.70/2.41      | r2_hidden(sK1(sK6,sK7),sK7) = iProver_top ),
% 15.70/2.41      inference(instantiation,[status(thm)],[c_7320]) ).
% 15.70/2.41  
% 15.70/2.41  cnf(c_11218,plain,
% 15.70/2.41      ( r2_hidden(sK2(X0,sK7),X0)
% 15.70/2.41      | r2_hidden(sK1(X0,sK7),sK7)
% 15.70/2.41      | k3_tarski(X0) = sK7 ),
% 15.70/2.41      inference(instantiation,[status(thm)],[c_7]) ).
% 15.70/2.41  
% 15.70/2.41  cnf(c_11221,plain,
% 15.70/2.41      ( k3_tarski(X0) = sK7
% 15.70/2.41      | r2_hidden(sK2(X0,sK7),X0) = iProver_top
% 15.70/2.41      | r2_hidden(sK1(X0,sK7),sK7) = iProver_top ),
% 15.70/2.41      inference(predicate_to_equality,[status(thm)],[c_11218]) ).
% 15.70/2.41  
% 15.70/2.41  cnf(c_11223,plain,
% 15.70/2.41      ( k3_tarski(sK6) = sK7
% 15.70/2.41      | r2_hidden(sK2(sK6,sK7),sK6) = iProver_top
% 15.70/2.41      | r2_hidden(sK1(sK6,sK7),sK7) = iProver_top ),
% 15.70/2.41      inference(instantiation,[status(thm)],[c_11221]) ).
% 15.70/2.41  
% 15.70/2.41  cnf(c_3928,plain,
% 15.70/2.41      ( ~ r2_hidden(X0,sK2(X1,X2))
% 15.70/2.41      | r2_hidden(X0,k3_tarski(X1))
% 15.70/2.41      | ~ r2_hidden(sK2(X1,X2),X1) ),
% 15.70/2.41      inference(instantiation,[status(thm)],[c_9]) ).
% 15.70/2.41  
% 15.70/2.41  cnf(c_16591,plain,
% 15.70/2.41      ( ~ r2_hidden(sK2(X0,sK7),X0)
% 15.70/2.41      | ~ r2_hidden(sK1(X0,sK7),sK2(X0,sK7))
% 15.70/2.41      | r2_hidden(sK1(X0,sK7),k3_tarski(X0)) ),
% 15.70/2.41      inference(instantiation,[status(thm)],[c_3928]) ).
% 15.70/2.41  
% 15.70/2.41  cnf(c_16592,plain,
% 15.70/2.41      ( r2_hidden(sK2(X0,sK7),X0) != iProver_top
% 15.70/2.41      | r2_hidden(sK1(X0,sK7),sK2(X0,sK7)) != iProver_top
% 15.70/2.41      | r2_hidden(sK1(X0,sK7),k3_tarski(X0)) = iProver_top ),
% 15.70/2.41      inference(predicate_to_equality,[status(thm)],[c_16591]) ).
% 15.70/2.41  
% 15.70/2.41  cnf(c_16594,plain,
% 15.70/2.41      ( r2_hidden(sK2(sK6,sK7),sK6) != iProver_top
% 15.70/2.41      | r2_hidden(sK1(sK6,sK7),sK2(sK6,sK7)) != iProver_top
% 15.70/2.41      | r2_hidden(sK1(sK6,sK7),k3_tarski(sK6)) = iProver_top ),
% 15.70/2.41      inference(instantiation,[status(thm)],[c_16592]) ).
% 15.70/2.41  
% 15.70/2.41  cnf(c_6,plain,
% 15.70/2.41      ( ~ r2_hidden(X0,X1)
% 15.70/2.41      | ~ r2_hidden(sK1(X1,X2),X0)
% 15.70/2.41      | ~ r2_hidden(sK1(X1,X2),X2)
% 15.70/2.41      | k3_tarski(X1) = X2 ),
% 15.70/2.41      inference(cnf_transformation,[],[f74]) ).
% 15.70/2.41  
% 15.70/2.41  cnf(c_10571,plain,
% 15.70/2.41      ( ~ r2_hidden(sK1(sK6,X0),X0)
% 15.70/2.41      | ~ r2_hidden(sK1(sK6,X0),sK7)
% 15.70/2.41      | ~ r2_hidden(sK7,sK6)
% 15.70/2.41      | k3_tarski(sK6) = X0 ),
% 15.70/2.41      inference(instantiation,[status(thm)],[c_6]) ).
% 15.70/2.41  
% 15.70/2.41  cnf(c_22966,plain,
% 15.70/2.41      ( ~ r2_hidden(sK1(sK6,sK7),sK7)
% 15.70/2.41      | ~ r2_hidden(sK7,sK6)
% 15.70/2.41      | k3_tarski(sK6) = sK7 ),
% 15.70/2.41      inference(instantiation,[status(thm)],[c_10571]) ).
% 15.70/2.41  
% 15.70/2.41  cnf(c_22977,plain,
% 15.70/2.41      ( k3_tarski(sK6) = sK7
% 15.70/2.41      | r2_hidden(sK1(sK6,sK7),sK7) != iProver_top
% 15.70/2.41      | r2_hidden(sK7,sK6) != iProver_top ),
% 15.70/2.41      inference(predicate_to_equality,[status(thm)],[c_22966]) ).
% 15.70/2.41  
% 15.70/2.41  cnf(c_4084,plain,
% 15.70/2.41      ( r2_hidden(X0,X1)
% 15.70/2.41      | ~ r2_hidden(X0,k3_tarski(X2))
% 15.70/2.41      | ~ r1_tarski(k3_tarski(X2),X1) ),
% 15.70/2.41      inference(instantiation,[status(thm)],[c_2]) ).
% 15.70/2.41  
% 15.70/2.41  cnf(c_33153,plain,
% 15.70/2.41      ( r2_hidden(sK1(X0,sK7),X1)
% 15.70/2.41      | ~ r2_hidden(sK1(X0,sK7),k3_tarski(X2))
% 15.70/2.41      | ~ r1_tarski(k3_tarski(X2),X1) ),
% 15.70/2.41      inference(instantiation,[status(thm)],[c_4084]) ).
% 15.70/2.41  
% 15.70/2.41  cnf(c_33154,plain,
% 15.70/2.41      ( r2_hidden(sK1(X0,sK7),X1) = iProver_top
% 15.70/2.41      | r2_hidden(sK1(X0,sK7),k3_tarski(X2)) != iProver_top
% 15.70/2.41      | r1_tarski(k3_tarski(X2),X1) != iProver_top ),
% 15.70/2.41      inference(predicate_to_equality,[status(thm)],[c_33153]) ).
% 15.70/2.41  
% 15.70/2.41  cnf(c_33156,plain,
% 15.70/2.41      ( r2_hidden(sK1(sK6,sK7),k3_tarski(sK6)) != iProver_top
% 15.70/2.41      | r2_hidden(sK1(sK6,sK7),sK6) = iProver_top
% 15.70/2.41      | r1_tarski(k3_tarski(sK6),sK6) != iProver_top ),
% 15.70/2.41      inference(instantiation,[status(thm)],[c_33154]) ).
% 15.70/2.41  
% 15.70/2.41  cnf(c_1,plain,
% 15.70/2.41      ( r2_hidden(sK0(X0,X1),X0) | r1_tarski(X0,X1) ),
% 15.70/2.41      inference(cnf_transformation,[],[f64]) ).
% 15.70/2.41  
% 15.70/2.41  cnf(c_1671,plain,
% 15.70/2.41      ( r2_hidden(sK0(X0,X1),X0) = iProver_top
% 15.70/2.41      | r1_tarski(X0,X1) = iProver_top ),
% 15.70/2.41      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 15.70/2.41  
% 15.70/2.41  cnf(c_3765,plain,
% 15.70/2.41      ( r2_hidden(X0,k3_tarski(X1)) != iProver_top
% 15.70/2.41      | r2_hidden(sK3(X1,X0),X2) = iProver_top
% 15.70/2.41      | r1_tarski(X1,X2) != iProver_top ),
% 15.70/2.41      inference(superposition,[status(thm)],[c_1663,c_1670]) ).
% 15.70/2.41  
% 15.70/2.41  cnf(c_1649,plain,
% 15.70/2.41      ( r1_ordinal1(X0,X1) = iProver_top
% 15.70/2.41      | r2_hidden(X0,k2_xboole_0(X1,k1_tarski(X1))) != iProver_top
% 15.70/2.41      | v3_ordinal1(X0) != iProver_top
% 15.70/2.41      | v3_ordinal1(X1) != iProver_top ),
% 15.70/2.41      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 15.70/2.41  
% 15.70/2.41  cnf(c_10830,plain,
% 15.70/2.41      ( r1_ordinal1(X0,sK7) = iProver_top
% 15.70/2.41      | r2_hidden(X0,sK6) != iProver_top
% 15.70/2.41      | v3_ordinal1(X0) != iProver_top
% 15.70/2.41      | v3_ordinal1(sK7) != iProver_top ),
% 15.70/2.41      inference(superposition,[status(thm)],[c_10718,c_1649]) ).
% 15.70/2.41  
% 15.70/2.41  cnf(c_11044,plain,
% 15.70/2.41      ( r2_hidden(X0,sK6) != iProver_top
% 15.70/2.41      | v3_ordinal1(sK3(sK6,X0)) = iProver_top
% 15.70/2.41      | v3_ordinal1(sK6) != iProver_top ),
% 15.70/2.41      inference(superposition,[status(thm)],[c_10717,c_3085]) ).
% 15.70/2.41  
% 15.70/2.41  cnf(c_3086,plain,
% 15.70/2.41      ( r2_hidden(X0,k3_tarski(X1)) != iProver_top
% 15.70/2.41      | v3_ordinal1(X0) = iProver_top
% 15.70/2.41      | v3_ordinal1(sK3(X1,X0)) != iProver_top ),
% 15.70/2.41      inference(superposition,[status(thm)],[c_1662,c_1653]) ).
% 15.70/2.41  
% 15.70/2.41  cnf(c_11121,plain,
% 15.70/2.41      ( r2_hidden(X0,sK6) != iProver_top
% 15.70/2.41      | v3_ordinal1(X0) = iProver_top
% 15.70/2.41      | v3_ordinal1(sK3(sK6,X0)) != iProver_top ),
% 15.70/2.41      inference(superposition,[status(thm)],[c_10717,c_3086]) ).
% 15.70/2.41  
% 15.70/2.41  cnf(c_13100,plain,
% 15.70/2.41      ( r1_ordinal1(X0,sK7) = iProver_top
% 15.70/2.41      | r2_hidden(X0,sK6) != iProver_top ),
% 15.70/2.41      inference(global_propositional_subsumption,
% 15.70/2.41                [status(thm)],
% 15.70/2.41                [c_10830,c_37,c_41,c_94,c_103,c_1872,c_2348,c_2909,
% 15.70/2.41                 c_5557,c_8424,c_9673,c_9789,c_9925,c_11044,c_11121]) ).
% 15.70/2.41  
% 15.70/2.41  cnf(c_20701,plain,
% 15.70/2.41      ( r1_ordinal1(sK3(X0,X1),sK7) = iProver_top
% 15.70/2.41      | r2_hidden(X1,k3_tarski(X0)) != iProver_top
% 15.70/2.41      | r1_tarski(X0,sK6) != iProver_top ),
% 15.70/2.41      inference(superposition,[status(thm)],[c_3765,c_13100]) ).
% 15.70/2.41  
% 15.70/2.41  cnf(c_25,plain,
% 15.70/2.41      ( ~ r1_ordinal1(X0,X1)
% 15.70/2.41      | r2_hidden(X0,k2_xboole_0(X1,k1_tarski(X1)))
% 15.70/2.41      | ~ v3_ordinal1(X1)
% 15.70/2.41      | ~ v3_ordinal1(X0) ),
% 15.70/2.41      inference(cnf_transformation,[],[f107]) ).
% 15.70/2.41  
% 15.70/2.41  cnf(c_1650,plain,
% 15.70/2.41      ( r1_ordinal1(X0,X1) != iProver_top
% 15.70/2.41      | r2_hidden(X0,k2_xboole_0(X1,k1_tarski(X1))) = iProver_top
% 15.70/2.41      | v3_ordinal1(X0) != iProver_top
% 15.70/2.41      | v3_ordinal1(X1) != iProver_top ),
% 15.70/2.41      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 15.70/2.41  
% 15.70/2.41  cnf(c_4439,plain,
% 15.70/2.41      ( r1_ordinal1(X0,X1) != iProver_top
% 15.70/2.41      | r2_hidden(X2,X0) != iProver_top
% 15.70/2.41      | r2_hidden(X2,k3_tarski(k2_xboole_0(X1,k1_tarski(X1)))) = iProver_top
% 15.70/2.41      | v3_ordinal1(X0) != iProver_top
% 15.70/2.41      | v3_ordinal1(X1) != iProver_top ),
% 15.70/2.41      inference(superposition,[status(thm)],[c_1650,c_1664]) ).
% 15.70/2.41  
% 15.70/2.41  cnf(c_34138,plain,
% 15.70/2.41      ( r2_hidden(X0,sK3(X1,X2)) != iProver_top
% 15.70/2.41      | r2_hidden(X2,k3_tarski(X1)) != iProver_top
% 15.70/2.41      | r2_hidden(X0,k3_tarski(k2_xboole_0(sK7,k1_tarski(sK7)))) = iProver_top
% 15.70/2.41      | r1_tarski(X1,sK6) != iProver_top
% 15.70/2.41      | v3_ordinal1(sK3(X1,X2)) != iProver_top
% 15.70/2.41      | v3_ordinal1(sK7) != iProver_top ),
% 15.70/2.41      inference(superposition,[status(thm)],[c_20701,c_4439]) ).
% 15.70/2.41  
% 15.70/2.41  cnf(c_34143,plain,
% 15.70/2.41      ( r2_hidden(X0,sK3(X1,X2)) != iProver_top
% 15.70/2.41      | r2_hidden(X2,k3_tarski(X1)) != iProver_top
% 15.70/2.41      | r2_hidden(X0,sK6) = iProver_top
% 15.70/2.41      | r1_tarski(X1,sK6) != iProver_top
% 15.70/2.41      | v3_ordinal1(sK3(X1,X2)) != iProver_top
% 15.70/2.41      | v3_ordinal1(sK7) != iProver_top ),
% 15.70/2.41      inference(light_normalisation,
% 15.70/2.41                [status(thm)],
% 15.70/2.41                [c_34138,c_10717,c_10718]) ).
% 15.70/2.41  
% 15.70/2.41  cnf(c_34152,plain,
% 15.70/2.41      ( v3_ordinal1(sK3(X1,X2)) != iProver_top
% 15.70/2.41      | r1_tarski(X1,sK6) != iProver_top
% 15.70/2.41      | r2_hidden(X0,sK6) = iProver_top
% 15.70/2.41      | r2_hidden(X2,k3_tarski(X1)) != iProver_top
% 15.70/2.41      | r2_hidden(X0,sK3(X1,X2)) != iProver_top ),
% 15.70/2.41      inference(global_propositional_subsumption,
% 15.70/2.41                [status(thm)],
% 15.70/2.41                [c_34143,c_37,c_41,c_94,c_103,c_1872,c_2348,c_2909,
% 15.70/2.41                 c_5557,c_8424,c_9673,c_9789,c_9925]) ).
% 15.70/2.41  
% 15.70/2.41  cnf(c_34153,plain,
% 15.70/2.41      ( r2_hidden(X0,sK3(X1,X2)) != iProver_top
% 15.70/2.41      | r2_hidden(X2,k3_tarski(X1)) != iProver_top
% 15.70/2.41      | r2_hidden(X0,sK6) = iProver_top
% 15.70/2.41      | r1_tarski(X1,sK6) != iProver_top
% 15.70/2.41      | v3_ordinal1(sK3(X1,X2)) != iProver_top ),
% 15.70/2.41      inference(renaming,[status(thm)],[c_34152]) ).
% 15.70/2.41  
% 15.70/2.41  cnf(c_34165,plain,
% 15.70/2.41      ( r2_hidden(X0,k3_tarski(X1)) != iProver_top
% 15.70/2.41      | r2_hidden(X0,sK6) = iProver_top
% 15.70/2.41      | r1_tarski(X1,sK6) != iProver_top
% 15.70/2.41      | v3_ordinal1(sK3(X1,X0)) != iProver_top ),
% 15.70/2.41      inference(superposition,[status(thm)],[c_1662,c_34153]) ).
% 15.70/2.41  
% 15.70/2.41  cnf(c_31947,plain,
% 15.70/2.41      ( v3_ordinal1(X0) = iProver_top
% 15.70/2.41      | r2_hidden(X0,sK6) != iProver_top ),
% 15.70/2.41      inference(global_propositional_subsumption,
% 15.70/2.41                [status(thm)],
% 15.70/2.41                [c_11121,c_37,c_11044]) ).
% 15.70/2.41  
% 15.70/2.41  cnf(c_31948,plain,
% 15.70/2.41      ( r2_hidden(X0,sK6) != iProver_top
% 15.70/2.41      | v3_ordinal1(X0) = iProver_top ),
% 15.70/2.41      inference(renaming,[status(thm)],[c_31947]) ).
% 15.70/2.41  
% 15.70/2.41  cnf(c_31969,plain,
% 15.70/2.41      ( r2_hidden(X0,k3_tarski(X1)) != iProver_top
% 15.70/2.41      | r1_tarski(X1,sK6) != iProver_top
% 15.70/2.41      | v3_ordinal1(sK3(X1,X0)) = iProver_top ),
% 15.70/2.41      inference(superposition,[status(thm)],[c_3765,c_31948]) ).
% 15.70/2.41  
% 15.70/2.41  cnf(c_37236,plain,
% 15.70/2.41      ( r1_tarski(X1,sK6) != iProver_top
% 15.70/2.41      | r2_hidden(X0,sK6) = iProver_top
% 15.70/2.41      | r2_hidden(X0,k3_tarski(X1)) != iProver_top ),
% 15.70/2.41      inference(global_propositional_subsumption,
% 15.70/2.41                [status(thm)],
% 15.70/2.41                [c_34165,c_31969]) ).
% 15.70/2.41  
% 15.70/2.41  cnf(c_37237,plain,
% 15.70/2.41      ( r2_hidden(X0,k3_tarski(X1)) != iProver_top
% 15.70/2.41      | r2_hidden(X0,sK6) = iProver_top
% 15.70/2.41      | r1_tarski(X1,sK6) != iProver_top ),
% 15.70/2.41      inference(renaming,[status(thm)],[c_37236]) ).
% 15.70/2.41  
% 15.70/2.41  cnf(c_37242,plain,
% 15.70/2.41      ( r2_hidden(sK0(k3_tarski(X0),X1),sK6) = iProver_top
% 15.70/2.41      | r1_tarski(X0,sK6) != iProver_top
% 15.70/2.41      | r1_tarski(k3_tarski(X0),X1) = iProver_top ),
% 15.70/2.41      inference(superposition,[status(thm)],[c_1671,c_37237]) ).
% 15.70/2.41  
% 15.70/2.41  cnf(c_37284,plain,
% 15.70/2.41      ( r2_hidden(sK0(k3_tarski(sK6),sK6),sK6) = iProver_top
% 15.70/2.41      | r1_tarski(k3_tarski(sK6),sK6) = iProver_top
% 15.70/2.41      | r1_tarski(sK6,sK6) != iProver_top ),
% 15.70/2.41      inference(instantiation,[status(thm)],[c_37242]) ).
% 15.70/2.41  
% 15.70/2.41  cnf(c_46316,plain,
% 15.70/2.41      ( r2_hidden(sK1(sK6,sK7),sK6) = iProver_top ),
% 15.70/2.41      inference(global_propositional_subsumption,
% 15.70/2.41                [status(thm)],
% 15.70/2.41                [c_45475,c_36,c_37,c_42,c_45,c_60,c_61,c_69,c_80,c_81,
% 15.70/2.41                 c_84,c_85,c_91,c_94,c_103,c_513,c_1840,c_1872,c_2348,
% 15.70/2.41                 c_2372,c_2552,c_2583,c_2909,c_5557,c_7322,c_8424,c_9673,
% 15.70/2.41                 c_9789,c_9925,c_11223,c_16594,c_22977,c_33156,c_37284]) ).
% 15.70/2.41  
% 15.70/2.41  cnf(c_10818,plain,
% 15.70/2.41      ( sK7 = X0
% 15.70/2.41      | r2_hidden(X0,sK6) != iProver_top
% 15.70/2.41      | r2_hidden(X0,sK7) = iProver_top ),
% 15.70/2.41      inference(superposition,[status(thm)],[c_10718,c_1654]) ).
% 15.70/2.41  
% 15.70/2.41  cnf(c_46329,plain,
% 15.70/2.41      ( sK1(sK6,sK7) = sK7 | r2_hidden(sK1(sK6,sK7),sK7) = iProver_top ),
% 15.70/2.41      inference(superposition,[status(thm)],[c_46316,c_10818]) ).
% 15.70/2.41  
% 15.70/2.41  cnf(c_47372,plain,
% 15.70/2.41      ( sK1(sK6,sK7) = sK7 ),
% 15.70/2.41      inference(global_propositional_subsumption,
% 15.70/2.41                [status(thm)],
% 15.70/2.41                [c_46329,c_36,c_37,c_42,c_45,c_60,c_69,c_80,c_84,c_91,
% 15.70/2.41                 c_94,c_103,c_513,c_1872,c_2348,c_2372,c_2552,c_2583,
% 15.70/2.41                 c_2909,c_5557,c_8424,c_9673,c_9789,c_9925,c_22977]) ).
% 15.70/2.41  
% 15.70/2.41  cnf(c_47389,plain,
% 15.70/2.41      ( k3_tarski(sK6) = sK7
% 15.70/2.41      | r2_hidden(sK1(sK6,sK7),sK7) = iProver_top
% 15.70/2.41      | r2_hidden(sK7,sK2(sK6,sK7)) = iProver_top ),
% 15.70/2.41      inference(superposition,[status(thm)],[c_47372,c_1665]) ).
% 15.70/2.41  
% 15.70/2.41  cnf(c_47402,plain,
% 15.70/2.41      ( k3_tarski(sK6) = sK7
% 15.70/2.41      | r2_hidden(sK7,sK2(sK6,sK7)) = iProver_top
% 15.70/2.41      | r2_hidden(sK7,sK7) = iProver_top ),
% 15.70/2.41      inference(light_normalisation,[status(thm)],[c_47389,c_47372]) ).
% 15.70/2.41  
% 15.70/2.41  cnf(c_47403,plain,
% 15.70/2.41      ( sK6 = sK7
% 15.70/2.41      | r2_hidden(sK7,sK2(sK6,sK7)) = iProver_top
% 15.70/2.41      | r2_hidden(sK7,sK7) = iProver_top ),
% 15.70/2.41      inference(demodulation,[status(thm)],[c_47402,c_10717]) ).
% 15.70/2.41  
% 15.70/2.41  cnf(c_6165,plain,
% 15.70/2.41      ( r1_tarski(sK7,sK7) ),
% 15.70/2.41      inference(instantiation,[status(thm)],[c_5]) ).
% 15.70/2.41  
% 15.70/2.41  cnf(c_6166,plain,
% 15.70/2.41      ( r1_tarski(sK7,sK7) = iProver_top ),
% 15.70/2.41      inference(predicate_to_equality,[status(thm)],[c_6165]) ).
% 15.70/2.41  
% 15.70/2.41  cnf(c_2576,plain,
% 15.70/2.41      ( ~ r2_hidden(sK7,X0) | ~ r1_tarski(X0,sK7) ),
% 15.70/2.41      inference(instantiation,[status(thm)],[c_31]) ).
% 15.70/2.41  
% 15.70/2.41  cnf(c_7203,plain,
% 15.70/2.41      ( ~ r2_hidden(sK7,sK7) | ~ r1_tarski(sK7,sK7) ),
% 15.70/2.41      inference(instantiation,[status(thm)],[c_2576]) ).
% 15.70/2.41  
% 15.70/2.41  cnf(c_7208,plain,
% 15.70/2.41      ( r2_hidden(sK7,sK7) != iProver_top
% 15.70/2.41      | r1_tarski(sK7,sK7) != iProver_top ),
% 15.70/2.41      inference(predicate_to_equality,[status(thm)],[c_7203]) ).
% 15.70/2.41  
% 15.70/2.41  cnf(c_48597,plain,
% 15.70/2.41      ( r2_hidden(sK7,sK2(sK6,sK7)) = iProver_top ),
% 15.70/2.41      inference(global_propositional_subsumption,
% 15.70/2.41                [status(thm)],
% 15.70/2.41                [c_47403,c_36,c_37,c_42,c_45,c_46,c_60,c_61,c_69,c_80,
% 15.70/2.41                 c_81,c_84,c_85,c_94,c_103,c_1872,c_2064,c_2348,c_2909,
% 15.70/2.41                 c_5557,c_6166,c_7208,c_8424,c_9673,c_9789,c_9925]) ).
% 15.70/2.41  
% 15.70/2.41  cnf(c_48607,plain,
% 15.70/2.41      ( r1_tarski(sK2(sK6,sK7),sK7) != iProver_top ),
% 15.70/2.41      inference(superposition,[status(thm)],[c_48597,c_1644]) ).
% 15.70/2.41  
% 15.70/2.41  cnf(c_4524,plain,
% 15.70/2.41      ( k3_tarski(k2_xboole_0(X0,k1_tarski(X0))) = X1
% 15.70/2.41      | r1_ordinal1(sK2(k2_xboole_0(X0,k1_tarski(X0)),X1),X0) = iProver_top
% 15.70/2.41      | r2_hidden(sK1(k2_xboole_0(X0,k1_tarski(X0)),X1),X1) = iProver_top
% 15.70/2.41      | v3_ordinal1(X0) != iProver_top
% 15.70/2.41      | v3_ordinal1(sK2(k2_xboole_0(X0,k1_tarski(X0)),X1)) != iProver_top ),
% 15.70/2.41      inference(superposition,[status(thm)],[c_1666,c_1649]) ).
% 15.70/2.41  
% 15.70/2.41  cnf(c_10829,plain,
% 15.70/2.41      ( r1_ordinal1(X0,sK7) != iProver_top
% 15.70/2.41      | r2_hidden(X0,sK6) = iProver_top
% 15.70/2.41      | v3_ordinal1(X0) != iProver_top
% 15.70/2.41      | v3_ordinal1(sK7) != iProver_top ),
% 15.70/2.41      inference(superposition,[status(thm)],[c_10718,c_1650]) ).
% 15.70/2.41  
% 15.70/2.41  cnf(c_13087,plain,
% 15.70/2.41      ( v3_ordinal1(X0) != iProver_top
% 15.70/2.41      | r2_hidden(X0,sK6) = iProver_top
% 15.70/2.41      | r1_ordinal1(X0,sK7) != iProver_top ),
% 15.70/2.41      inference(global_propositional_subsumption,
% 15.70/2.41                [status(thm)],
% 15.70/2.41                [c_10829,c_37,c_41,c_94,c_103,c_1872,c_2348,c_2909,
% 15.70/2.41                 c_5557,c_8424,c_9673,c_9789,c_9925]) ).
% 15.70/2.41  
% 15.70/2.41  cnf(c_13088,plain,
% 15.70/2.41      ( r1_ordinal1(X0,sK7) != iProver_top
% 15.70/2.41      | r2_hidden(X0,sK6) = iProver_top
% 15.70/2.41      | v3_ordinal1(X0) != iProver_top ),
% 15.70/2.41      inference(renaming,[status(thm)],[c_13087]) ).
% 15.70/2.41  
% 15.70/2.41  cnf(c_44248,plain,
% 15.70/2.41      ( k3_tarski(k2_xboole_0(sK7,k1_tarski(sK7))) = X0
% 15.70/2.41      | r2_hidden(sK2(k2_xboole_0(sK7,k1_tarski(sK7)),X0),sK6) = iProver_top
% 15.70/2.41      | r2_hidden(sK1(k2_xboole_0(sK7,k1_tarski(sK7)),X0),X0) = iProver_top
% 15.70/2.41      | v3_ordinal1(sK2(k2_xboole_0(sK7,k1_tarski(sK7)),X0)) != iProver_top
% 15.70/2.41      | v3_ordinal1(sK7) != iProver_top ),
% 15.70/2.41      inference(superposition,[status(thm)],[c_4524,c_13088]) ).
% 15.70/2.41  
% 15.70/2.41  cnf(c_44249,plain,
% 15.70/2.41      ( sK6 = X0
% 15.70/2.41      | r2_hidden(sK2(sK6,X0),sK6) = iProver_top
% 15.70/2.41      | r2_hidden(sK1(sK6,X0),X0) = iProver_top
% 15.70/2.41      | v3_ordinal1(sK2(sK6,X0)) != iProver_top
% 15.70/2.41      | v3_ordinal1(sK7) != iProver_top ),
% 15.70/2.41      inference(light_normalisation,
% 15.70/2.41                [status(thm)],
% 15.70/2.41                [c_44248,c_10717,c_10718]) ).
% 15.70/2.41  
% 15.70/2.41  cnf(c_31956,plain,
% 15.70/2.41      ( k3_tarski(sK6) = X0
% 15.70/2.41      | r2_hidden(sK1(sK6,X0),X0) = iProver_top
% 15.70/2.41      | v3_ordinal1(sK2(sK6,X0)) = iProver_top ),
% 15.70/2.41      inference(superposition,[status(thm)],[c_1666,c_31948]) ).
% 15.70/2.41  
% 15.70/2.41  cnf(c_31997,plain,
% 15.70/2.41      ( sK6 = X0
% 15.70/2.41      | r2_hidden(sK1(sK6,X0),X0) = iProver_top
% 15.70/2.41      | v3_ordinal1(sK2(sK6,X0)) = iProver_top ),
% 15.70/2.41      inference(demodulation,[status(thm)],[c_31956,c_10717]) ).
% 15.70/2.41  
% 15.70/2.41  cnf(c_44511,plain,
% 15.70/2.41      ( sK6 = X0
% 15.70/2.41      | r2_hidden(sK2(sK6,X0),sK6) = iProver_top
% 15.70/2.41      | r2_hidden(sK1(sK6,X0),X0) = iProver_top ),
% 15.70/2.41      inference(global_propositional_subsumption,
% 15.70/2.41                [status(thm)],
% 15.70/2.41                [c_44249,c_37,c_41,c_94,c_103,c_1872,c_2348,c_2909,
% 15.70/2.41                 c_5557,c_8424,c_9673,c_9789,c_9925,c_31997]) ).
% 15.70/2.41  
% 15.70/2.41  cnf(c_47398,plain,
% 15.70/2.41      ( sK6 = sK7
% 15.70/2.41      | r2_hidden(sK2(sK6,sK7),sK6) = iProver_top
% 15.70/2.41      | r2_hidden(sK7,sK7) = iProver_top ),
% 15.70/2.41      inference(superposition,[status(thm)],[c_47372,c_44511]) ).
% 15.70/2.41  
% 15.70/2.41  cnf(c_47551,plain,
% 15.70/2.41      ( r2_hidden(sK2(sK6,sK7),sK6) = iProver_top ),
% 15.70/2.41      inference(global_propositional_subsumption,
% 15.70/2.41                [status(thm)],
% 15.70/2.41                [c_47398,c_36,c_37,c_42,c_45,c_60,c_69,c_80,c_84,c_91,
% 15.70/2.41                 c_94,c_103,c_513,c_1872,c_2348,c_2372,c_2552,c_2583,
% 15.70/2.41                 c_2909,c_5557,c_8424,c_9673,c_9789,c_9925,c_11223,
% 15.70/2.41                 c_22977]) ).
% 15.70/2.41  
% 15.70/2.41  cnf(c_47563,plain,
% 15.70/2.41      ( r1_ordinal1(sK2(sK6,sK7),sK7) = iProver_top ),
% 15.70/2.41      inference(superposition,[status(thm)],[c_47551,c_13100]) ).
% 15.70/2.41  
% 15.70/2.41  cnf(c_1657,plain,
% 15.70/2.41      ( r1_ordinal1(X0,X1) != iProver_top
% 15.70/2.41      | r1_tarski(X0,X1) = iProver_top
% 15.70/2.41      | v3_ordinal1(X0) != iProver_top
% 15.70/2.41      | v3_ordinal1(X1) != iProver_top ),
% 15.70/2.41      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 15.70/2.41  
% 15.70/2.41  cnf(c_47578,plain,
% 15.70/2.41      ( r1_tarski(sK2(sK6,sK7),sK7) = iProver_top
% 15.70/2.41      | v3_ordinal1(sK2(sK6,sK7)) != iProver_top
% 15.70/2.41      | v3_ordinal1(sK7) != iProver_top ),
% 15.70/2.41      inference(superposition,[status(thm)],[c_47563,c_1657]) ).
% 15.70/2.41  
% 15.70/2.41  cnf(c_6007,plain,
% 15.70/2.41      ( ~ r2_hidden(sK2(sK6,X0),X1)
% 15.70/2.41      | ~ v3_ordinal1(X1)
% 15.70/2.41      | v3_ordinal1(sK2(sK6,X0)) ),
% 15.70/2.41      inference(instantiation,[status(thm)],[c_22]) ).
% 15.70/2.41  
% 15.70/2.41  cnf(c_22944,plain,
% 15.70/2.41      ( ~ r2_hidden(sK2(sK6,sK7),sK6)
% 15.70/2.41      | v3_ordinal1(sK2(sK6,sK7))
% 15.70/2.41      | ~ v3_ordinal1(sK6) ),
% 15.70/2.41      inference(instantiation,[status(thm)],[c_6007]) ).
% 15.70/2.41  
% 15.70/2.41  cnf(c_22945,plain,
% 15.70/2.41      ( r2_hidden(sK2(sK6,sK7),sK6) != iProver_top
% 15.70/2.41      | v3_ordinal1(sK2(sK6,sK7)) = iProver_top
% 15.70/2.41      | v3_ordinal1(sK6) != iProver_top ),
% 15.70/2.41      inference(predicate_to_equality,[status(thm)],[c_22944]) ).
% 15.70/2.41  
% 15.70/2.41  cnf(contradiction,plain,
% 15.70/2.41      ( $false ),
% 15.70/2.41      inference(minisat,
% 15.70/2.41                [status(thm)],
% 15.70/2.41                [c_48607,c_47578,c_22977,c_22945,c_11223,c_10713,c_2583,
% 15.70/2.41                 c_2552,c_2372,c_513,c_91,c_84,c_80,c_69,c_60,c_45,c_42,
% 15.70/2.41                 c_41,c_37,c_36]) ).
% 15.70/2.41  
% 15.70/2.41  
% 15.70/2.41  % SZS output end CNFRefutation for theBenchmark.p
% 15.70/2.41  
% 15.70/2.41  ------                               Statistics
% 15.70/2.41  
% 15.70/2.41  ------ General
% 15.70/2.41  
% 15.70/2.41  abstr_ref_over_cycles:                  0
% 15.70/2.41  abstr_ref_under_cycles:                 0
% 15.70/2.41  gc_basic_clause_elim:                   0
% 15.70/2.41  forced_gc_time:                         0
% 15.70/2.41  parsing_time:                           0.009
% 15.70/2.41  unif_index_cands_time:                  0.
% 15.70/2.41  unif_index_add_time:                    0.
% 15.70/2.41  orderings_time:                         0.
% 15.70/2.41  out_proof_time:                         0.027
% 15.70/2.41  total_time:                             1.892
% 15.70/2.41  num_of_symbols:                         47
% 15.70/2.41  num_of_terms:                           46880
% 15.70/2.41  
% 15.70/2.41  ------ Preprocessing
% 15.70/2.41  
% 15.70/2.41  num_of_splits:                          0
% 15.70/2.41  num_of_split_atoms:                     0
% 15.70/2.41  num_of_reused_defs:                     0
% 15.70/2.41  num_eq_ax_congr_red:                    45
% 15.70/2.41  num_of_sem_filtered_clauses:            1
% 15.70/2.41  num_of_subtypes:                        0
% 15.70/2.41  monotx_restored_types:                  0
% 15.70/2.41  sat_num_of_epr_types:                   0
% 15.70/2.41  sat_num_of_non_cyclic_types:            0
% 15.70/2.41  sat_guarded_non_collapsed_types:        0
% 15.70/2.41  num_pure_diseq_elim:                    0
% 15.70/2.41  simp_replaced_by:                       0
% 15.70/2.41  res_preprocessed:                       155
% 15.70/2.41  prep_upred:                             0
% 15.70/2.41  prep_unflattend:                        8
% 15.70/2.41  smt_new_axioms:                         0
% 15.70/2.41  pred_elim_cands:                        5
% 15.70/2.41  pred_elim:                              0
% 15.70/2.41  pred_elim_cl:                           0
% 15.70/2.41  pred_elim_cycles:                       2
% 15.70/2.41  merged_defs:                            8
% 15.70/2.41  merged_defs_ncl:                        0
% 15.70/2.41  bin_hyper_res:                          8
% 15.70/2.41  prep_cycles:                            4
% 15.70/2.41  pred_elim_time:                         0.004
% 15.70/2.41  splitting_time:                         0.
% 15.70/2.41  sem_filter_time:                        0.
% 15.70/2.41  monotx_time:                            0.
% 15.70/2.41  subtype_inf_time:                       0.
% 15.70/2.41  
% 15.70/2.41  ------ Problem properties
% 15.70/2.41  
% 15.70/2.41  clauses:                                35
% 15.70/2.41  conjectures:                            5
% 15.70/2.41  epr:                                    12
% 15.70/2.41  horn:                                   27
% 15.70/2.41  ground:                                 4
% 15.70/2.41  unary:                                  6
% 15.70/2.41  binary:                                 14
% 15.70/2.41  lits:                                   88
% 15.70/2.41  lits_eq:                                9
% 15.70/2.41  fd_pure:                                0
% 15.70/2.41  fd_pseudo:                              0
% 15.70/2.41  fd_cond:                                0
% 15.70/2.41  fd_pseudo_cond:                         6
% 15.70/2.41  ac_symbols:                             0
% 15.70/2.41  
% 15.70/2.41  ------ Propositional Solver
% 15.70/2.41  
% 15.70/2.41  prop_solver_calls:                      32
% 15.70/2.41  prop_fast_solver_calls:                 3372
% 15.70/2.41  smt_solver_calls:                       0
% 15.70/2.41  smt_fast_solver_calls:                  0
% 15.70/2.41  prop_num_of_clauses:                    20888
% 15.70/2.41  prop_preprocess_simplified:             38162
% 15.70/2.41  prop_fo_subsumed:                       693
% 15.70/2.41  prop_solver_time:                       0.
% 15.70/2.41  smt_solver_time:                        0.
% 15.70/2.41  smt_fast_solver_time:                   0.
% 15.70/2.41  prop_fast_solver_time:                  0.
% 15.70/2.41  prop_unsat_core_time:                   0.001
% 15.70/2.41  
% 15.70/2.41  ------ QBF
% 15.70/2.41  
% 15.70/2.41  qbf_q_res:                              0
% 15.70/2.41  qbf_num_tautologies:                    0
% 15.70/2.41  qbf_prep_cycles:                        0
% 15.70/2.41  
% 15.70/2.41  ------ BMC1
% 15.70/2.41  
% 15.70/2.41  bmc1_current_bound:                     -1
% 15.70/2.41  bmc1_last_solved_bound:                 -1
% 15.70/2.41  bmc1_unsat_core_size:                   -1
% 15.70/2.41  bmc1_unsat_core_parents_size:           -1
% 15.70/2.41  bmc1_merge_next_fun:                    0
% 15.70/2.41  bmc1_unsat_core_clauses_time:           0.
% 15.70/2.41  
% 15.70/2.41  ------ Instantiation
% 15.70/2.41  
% 15.70/2.41  inst_num_of_clauses:                    4631
% 15.70/2.41  inst_num_in_passive:                    812
% 15.70/2.41  inst_num_in_active:                     1714
% 15.70/2.41  inst_num_in_unprocessed:                2105
% 15.70/2.41  inst_num_of_loops:                      2160
% 15.70/2.41  inst_num_of_learning_restarts:          0
% 15.70/2.41  inst_num_moves_active_passive:          445
% 15.70/2.41  inst_lit_activity:                      0
% 15.70/2.41  inst_lit_activity_moves:                0
% 15.70/2.41  inst_num_tautologies:                   0
% 15.70/2.41  inst_num_prop_implied:                  0
% 15.70/2.41  inst_num_existing_simplified:           0
% 15.70/2.41  inst_num_eq_res_simplified:             0
% 15.70/2.41  inst_num_child_elim:                    0
% 15.70/2.41  inst_num_of_dismatching_blockings:      5298
% 15.70/2.41  inst_num_of_non_proper_insts:           3793
% 15.70/2.41  inst_num_of_duplicates:                 0
% 15.70/2.41  inst_inst_num_from_inst_to_res:         0
% 15.70/2.41  inst_dismatching_checking_time:         0.
% 15.70/2.41  
% 15.70/2.41  ------ Resolution
% 15.70/2.41  
% 15.70/2.41  res_num_of_clauses:                     0
% 15.70/2.41  res_num_in_passive:                     0
% 15.70/2.41  res_num_in_active:                      0
% 15.70/2.41  res_num_of_loops:                       159
% 15.70/2.41  res_forward_subset_subsumed:            154
% 15.70/2.41  res_backward_subset_subsumed:           4
% 15.70/2.41  res_forward_subsumed:                   0
% 15.70/2.41  res_backward_subsumed:                  0
% 15.70/2.41  res_forward_subsumption_resolution:     0
% 15.70/2.41  res_backward_subsumption_resolution:    0
% 15.70/2.41  res_clause_to_clause_subsumption:       22898
% 15.70/2.41  res_orphan_elimination:                 0
% 15.70/2.41  res_tautology_del:                      316
% 15.70/2.41  res_num_eq_res_simplified:              0
% 15.70/2.41  res_num_sel_changes:                    0
% 15.70/2.41  res_moves_from_active_to_pass:          0
% 15.70/2.41  
% 15.70/2.41  ------ Superposition
% 15.70/2.41  
% 15.70/2.41  sup_time_total:                         0.
% 15.70/2.41  sup_time_generating:                    0.
% 15.70/2.41  sup_time_sim_full:                      0.
% 15.70/2.41  sup_time_sim_immed:                     0.
% 15.70/2.41  
% 15.70/2.41  sup_num_of_clauses:                     2995
% 15.70/2.41  sup_num_in_active:                      358
% 15.70/2.41  sup_num_in_passive:                     2637
% 15.70/2.41  sup_num_of_loops:                       430
% 15.70/2.41  sup_fw_superposition:                   1707
% 15.70/2.41  sup_bw_superposition:                   3030
% 15.70/2.41  sup_immediate_simplified:               1095
% 15.70/2.41  sup_given_eliminated:                   0
% 15.70/2.41  comparisons_done:                       0
% 15.70/2.41  comparisons_avoided:                    21
% 15.70/2.41  
% 15.70/2.41  ------ Simplifications
% 15.70/2.41  
% 15.70/2.41  
% 15.70/2.41  sim_fw_subset_subsumed:                 609
% 15.70/2.41  sim_bw_subset_subsumed:                 125
% 15.70/2.41  sim_fw_subsumed:                        274
% 15.70/2.41  sim_bw_subsumed:                        59
% 15.70/2.41  sim_fw_subsumption_res:                 0
% 15.70/2.41  sim_bw_subsumption_res:                 0
% 15.70/2.41  sim_tautology_del:                      74
% 15.70/2.41  sim_eq_tautology_del:                   47
% 15.70/2.41  sim_eq_res_simp:                        1
% 15.70/2.41  sim_fw_demodulated:                     48
% 15.70/2.41  sim_bw_demodulated:                     28
% 15.70/2.41  sim_light_normalised:                   193
% 15.70/2.41  sim_joinable_taut:                      0
% 15.70/2.41  sim_joinable_simp:                      0
% 15.70/2.41  sim_ac_normalised:                      0
% 15.70/2.41  sim_smt_subsumption:                    0
% 15.70/2.41  
%------------------------------------------------------------------------------
