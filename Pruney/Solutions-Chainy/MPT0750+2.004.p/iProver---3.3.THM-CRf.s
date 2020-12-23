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
% DateTime   : Thu Dec  3 11:54:00 EST 2020

% Result     : Theorem 3.97s
% Output     : CNFRefutation 3.97s
% Verified   : 
% Statistics : Number of formulae       :  209 (1002 expanded)
%              Number of clauses        :  114 ( 279 expanded)
%              Number of leaves         :   26 ( 239 expanded)
%              Depth                    :   23
%              Number of atoms          :  706 (4754 expanded)
%              Number of equality atoms :  196 ( 513 expanded)
%              Maximal formula depth    :   11 (   5 average)
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

fof(f48,plain,(
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

fof(f49,plain,(
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
    inference(rectify,[],[f48])).

fof(f52,plain,(
    ! [X5,X0] :
      ( ? [X7] :
          ( r2_hidden(X7,X0)
          & r2_hidden(X5,X7) )
     => ( r2_hidden(sK3(X0,X5),X0)
        & r2_hidden(X5,sK3(X0,X5)) ) ) ),
    introduced(choice_axiom,[])).

fof(f51,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( r2_hidden(X4,X0)
          & r2_hidden(X2,X4) )
     => ( r2_hidden(sK2(X0,X1),X0)
        & r2_hidden(X2,sK2(X0,X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f50,plain,(
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

fof(f53,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f49,f52,f51,f50])).

fof(f74,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(X5,sK3(X0,X5))
      | ~ r2_hidden(X5,X1)
      | k3_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f53])).

fof(f118,plain,(
    ! [X0,X5] :
      ( r2_hidden(X5,sK3(X0,X5))
      | ~ r2_hidden(X5,k3_tarski(X0)) ) ),
    inference(equality_resolution,[],[f74])).

fof(f19,conjecture,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ( v4_ordinal1(X0)
      <=> ! [X1] :
            ( v3_ordinal1(X1)
           => ( r2_hidden(X1,X0)
             => r2_hidden(k1_ordinal1(X1),X0) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,negated_conjecture,(
    ~ ! [X0] :
        ( v3_ordinal1(X0)
       => ( v4_ordinal1(X0)
        <=> ! [X1] :
              ( v3_ordinal1(X1)
             => ( r2_hidden(X1,X0)
               => r2_hidden(k1_ordinal1(X1),X0) ) ) ) ) ),
    inference(negated_conjecture,[],[f19])).

fof(f40,plain,(
    ? [X0] :
      ( ( v4_ordinal1(X0)
      <~> ! [X1] :
            ( r2_hidden(k1_ordinal1(X1),X0)
            | ~ r2_hidden(X1,X0)
            | ~ v3_ordinal1(X1) ) )
      & v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f41,plain,(
    ? [X0] :
      ( ( v4_ordinal1(X0)
      <~> ! [X1] :
            ( r2_hidden(k1_ordinal1(X1),X0)
            | ~ r2_hidden(X1,X0)
            | ~ v3_ordinal1(X1) ) )
      & v3_ordinal1(X0) ) ),
    inference(flattening,[],[f40])).

fof(f62,plain,(
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
    inference(nnf_transformation,[],[f41])).

fof(f63,plain,(
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
    inference(flattening,[],[f62])).

fof(f64,plain,(
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
    inference(rectify,[],[f63])).

fof(f66,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ r2_hidden(k1_ordinal1(X1),X0)
          & r2_hidden(X1,X0)
          & v3_ordinal1(X1) )
     => ( ~ r2_hidden(k1_ordinal1(sK7),X0)
        & r2_hidden(sK7,X0)
        & v3_ordinal1(sK7) ) ) ),
    introduced(choice_axiom,[])).

fof(f65,plain,
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

fof(f67,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7])],[f64,f66,f65])).

fof(f102,plain,(
    ! [X2] :
      ( r2_hidden(k1_ordinal1(X2),sK6)
      | ~ r2_hidden(X2,sK6)
      | ~ v3_ordinal1(X2)
      | v4_ordinal1(sK6) ) ),
    inference(cnf_transformation,[],[f67])).

fof(f6,axiom,(
    ! [X0] : k1_ordinal1(X0) = k2_xboole_0(X0,k1_tarski(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f82,plain,(
    ! [X0] : k1_ordinal1(X0) = k2_xboole_0(X0,k1_tarski(X0)) ),
    inference(cnf_transformation,[],[f6])).

fof(f113,plain,(
    ! [X2] :
      ( r2_hidden(k2_xboole_0(X2,k1_tarski(X2)),sK6)
      | ~ r2_hidden(X2,sK6)
      | ~ v3_ordinal1(X2)
      | v4_ordinal1(sK6) ) ),
    inference(definition_unfolding,[],[f102,f82])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f23])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f42])).

fof(f44,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK0(X0,X1),X1)
          & r2_hidden(sK0(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f43,f44])).

fof(f68,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f75,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(sK3(X0,X5),X0)
      | ~ r2_hidden(X5,X1)
      | k3_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f53])).

fof(f117,plain,(
    ! [X0,X5] :
      ( r2_hidden(sK3(X0,X5),X0)
      | ~ r2_hidden(X5,k3_tarski(X0)) ) ),
    inference(equality_resolution,[],[f75])).

fof(f104,plain,
    ( r2_hidden(sK7,sK6)
    | ~ v4_ordinal1(sK6) ),
    inference(cnf_transformation,[],[f67])).

fof(f76,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | ~ r2_hidden(X6,X0)
      | ~ r2_hidden(X5,X6)
      | k3_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f53])).

fof(f116,plain,(
    ! [X6,X0,X5] :
      ( r2_hidden(X5,k3_tarski(X0))
      | ~ r2_hidden(X6,X0)
      | ~ r2_hidden(X5,X6) ) ),
    inference(equality_resolution,[],[f76])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( v3_ordinal1(X1)
     => ( r2_hidden(X0,X1)
       => v3_ordinal1(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1] :
      ( v3_ordinal1(X0)
      | ~ r2_hidden(X0,X1)
      | ~ v3_ordinal1(X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f31,plain,(
    ! [X0,X1] :
      ( v3_ordinal1(X0)
      | ~ r2_hidden(X0,X1)
      | ~ v3_ordinal1(X1) ) ),
    inference(flattening,[],[f30])).

fof(f89,plain,(
    ! [X0,X1] :
      ( v3_ordinal1(X0)
      | ~ r2_hidden(X0,X1)
      | ~ v3_ordinal1(X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f101,plain,(
    v3_ordinal1(sK6) ),
    inference(cnf_transformation,[],[f67])).

fof(f16,axiom,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(X1,X0)
         => v3_ordinal1(X1) )
     => v3_ordinal1(k3_tarski(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0] :
      ( v3_ordinal1(k3_tarski(X0))
      | ? [X1] :
          ( ~ v3_ordinal1(X1)
          & r2_hidden(X1,X0) ) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f58,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ v3_ordinal1(X1)
          & r2_hidden(X1,X0) )
     => ( ~ v3_ordinal1(sK4(X0))
        & r2_hidden(sK4(X0),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f59,plain,(
    ! [X0] :
      ( v3_ordinal1(k3_tarski(X0))
      | ( ~ v3_ordinal1(sK4(X0))
        & r2_hidden(sK4(X0),X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f37,f58])).

fof(f96,plain,(
    ! [X0] :
      ( v3_ordinal1(k3_tarski(X0))
      | r2_hidden(sK4(X0),X0) ) ),
    inference(cnf_transformation,[],[f59])).

fof(f97,plain,(
    ! [X0] :
      ( v3_ordinal1(k3_tarski(X0))
      | ~ v3_ordinal1(sK4(X0)) ) ),
    inference(cnf_transformation,[],[f59])).

fof(f8,axiom,(
    ! [X0] :
      ( v4_ordinal1(X0)
    <=> k3_tarski(X0) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f54,plain,(
    ! [X0] :
      ( ( v4_ordinal1(X0)
        | k3_tarski(X0) != X0 )
      & ( k3_tarski(X0) = X0
        | ~ v4_ordinal1(X0) ) ) ),
    inference(nnf_transformation,[],[f8])).

fof(f84,plain,(
    ! [X0] :
      ( k3_tarski(X0) = X0
      | ~ v4_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f85,plain,(
    ! [X0] :
      ( v4_ordinal1(X0)
      | k3_tarski(X0) != X0 ) ),
    inference(cnf_transformation,[],[f54])).

fof(f10,axiom,(
    ! [X0] : r2_hidden(X0,k1_ordinal1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f88,plain,(
    ! [X0] : r2_hidden(X0,k1_ordinal1(X0)) ),
    inference(cnf_transformation,[],[f10])).

fof(f106,plain,(
    ! [X0] : r2_hidden(X0,k2_xboole_0(X0,k1_tarski(X0))) ),
    inference(definition_unfolding,[],[f88,f82])).

fof(f7,axiom,(
    ! [X0] :
      ( v1_ordinal1(X0)
    <=> ! [X1] :
          ( r2_hidden(X1,X0)
         => r1_tarski(X1,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0] :
      ( v1_ordinal1(X0)
     => ! [X1] :
          ( r2_hidden(X1,X0)
         => r1_tarski(X1,X0) ) ) ),
    inference(unused_predicate_definition_removal,[],[f7])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(X1,X0)
          | ~ r2_hidden(X1,X0) )
      | ~ v1_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f83,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | ~ r2_hidden(X1,X0)
      | ~ v1_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f4,axiom,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ( v2_ordinal1(X0)
        & v1_ordinal1(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => v1_ordinal1(X0) ) ),
    inference(pure_predicate_removal,[],[f4])).

fof(f24,plain,(
    ! [X0] :
      ( v1_ordinal1(X0)
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f80,plain,(
    ! [X0] :
      ( v1_ordinal1(X0)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f18,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f100,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f12,axiom,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ! [X1] :
          ( v3_ordinal1(X1)
         => ~ ( ~ r2_hidden(X1,X0)
              & X0 != X1
              & ~ r2_hidden(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(X1,X0)
          | X0 = X1
          | r2_hidden(X0,X1)
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(X1,X0)
          | X0 = X1
          | r2_hidden(X0,X1)
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(flattening,[],[f32])).

fof(f90,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,X0)
      | X0 = X1
      | r2_hidden(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f46])).

fof(f71,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f47])).

fof(f115,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f71])).

fof(f105,plain,
    ( ~ r2_hidden(k1_ordinal1(sK7),sK6)
    | ~ v4_ordinal1(sK6) ),
    inference(cnf_transformation,[],[f67])).

fof(f112,plain,
    ( ~ r2_hidden(k2_xboole_0(sK7,k1_tarski(sK7)),sK6)
    | ~ v4_ordinal1(sK6) ),
    inference(definition_unfolding,[],[f105,f82])).

fof(f103,plain,
    ( v3_ordinal1(sK7)
    | ~ v4_ordinal1(sK6) ),
    inference(cnf_transformation,[],[f67])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( ( v3_ordinal1(X1)
        & v3_ordinal1(X0) )
     => ( r1_ordinal1(X0,X1)
      <=> r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( r1_ordinal1(X0,X1)
      <=> r1_tarski(X0,X1) )
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( r1_ordinal1(X0,X1)
      <=> r1_tarski(X0,X1) )
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(flattening,[],[f28])).

fof(f55,plain,(
    ! [X0,X1] :
      ( ( ( r1_ordinal1(X0,X1)
          | ~ r1_tarski(X0,X1) )
        & ( r1_tarski(X0,X1)
          | ~ r1_ordinal1(X0,X1) ) )
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(nnf_transformation,[],[f29])).

fof(f86,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r1_ordinal1(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f13,axiom,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => v3_ordinal1(k1_ordinal1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0] :
      ( v3_ordinal1(k1_ordinal1(X0))
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f91,plain,(
    ! [X0] :
      ( v3_ordinal1(k1_ordinal1(X0))
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f107,plain,(
    ! [X0] :
      ( v3_ordinal1(k2_xboole_0(X0,k1_tarski(X0)))
      | ~ v3_ordinal1(X0) ) ),
    inference(definition_unfolding,[],[f91,f82])).

fof(f15,axiom,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ! [X1] :
          ( v3_ordinal1(X1)
         => ( r2_hidden(X0,k1_ordinal1(X1))
          <=> r1_ordinal1(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r2_hidden(X0,k1_ordinal1(X1))
          <=> r1_ordinal1(X0,X1) )
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f57,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( r2_hidden(X0,k1_ordinal1(X1))
              | ~ r1_ordinal1(X0,X1) )
            & ( r1_ordinal1(X0,X1)
              | ~ r2_hidden(X0,k1_ordinal1(X1)) ) )
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(nnf_transformation,[],[f36])).

fof(f94,plain,(
    ! [X0,X1] :
      ( r1_ordinal1(X0,X1)
      | ~ r2_hidden(X0,k1_ordinal1(X1))
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f111,plain,(
    ! [X0,X1] :
      ( r1_ordinal1(X0,X1)
      | ~ r2_hidden(X0,k2_xboole_0(X1,k1_tarski(X1)))
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(definition_unfolding,[],[f94,f82])).

fof(f14,axiom,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ! [X1] :
          ( v3_ordinal1(X1)
         => ( r2_hidden(X0,X1)
          <=> r1_ordinal1(k1_ordinal1(X0),X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r2_hidden(X0,X1)
          <=> r1_ordinal1(k1_ordinal1(X0),X1) )
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f56,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( r2_hidden(X0,X1)
              | ~ r1_ordinal1(k1_ordinal1(X0),X1) )
            & ( r1_ordinal1(k1_ordinal1(X0),X1)
              | ~ r2_hidden(X0,X1) ) )
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(nnf_transformation,[],[f35])).

fof(f92,plain,(
    ! [X0,X1] :
      ( r1_ordinal1(k1_ordinal1(X0),X1)
      | ~ r2_hidden(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f109,plain,(
    ! [X0,X1] :
      ( r1_ordinal1(k2_xboole_0(X0,k1_tarski(X0)),X1)
      | ~ r2_hidden(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(definition_unfolding,[],[f92,f82])).

cnf(c_11,plain,
    ( r2_hidden(X0,sK3(X1,X0))
    | ~ r2_hidden(X0,k3_tarski(X1)) ),
    inference(cnf_transformation,[],[f118])).

cnf(c_1366,plain,
    ( r2_hidden(X0,sK3(X1,X0)) = iProver_top
    | r2_hidden(X0,k3_tarski(X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_35,negated_conjecture,
    ( ~ r2_hidden(X0,sK6)
    | r2_hidden(k2_xboole_0(X0,k1_tarski(X0)),sK6)
    | v4_ordinal1(sK6)
    | ~ v3_ordinal1(X0) ),
    inference(cnf_transformation,[],[f113])).

cnf(c_1343,plain,
    ( r2_hidden(X0,sK6) != iProver_top
    | r2_hidden(k2_xboole_0(X0,k1_tarski(X0)),sK6) = iProver_top
    | v4_ordinal1(sK6) = iProver_top
    | v3_ordinal1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_35])).

cnf(c_2,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | ~ r1_tarski(X1,X2) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_1374,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,X2) = iProver_top
    | r1_tarski(X1,X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_3810,plain,
    ( r2_hidden(X0,sK6) != iProver_top
    | r2_hidden(k2_xboole_0(X0,k1_tarski(X0)),X1) = iProver_top
    | r1_tarski(sK6,X1) != iProver_top
    | v4_ordinal1(sK6) = iProver_top
    | v3_ordinal1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1343,c_1374])).

cnf(c_10,plain,
    ( ~ r2_hidden(X0,k3_tarski(X1))
    | r2_hidden(sK3(X1,X0),X1) ),
    inference(cnf_transformation,[],[f117])).

cnf(c_1367,plain,
    ( r2_hidden(X0,k3_tarski(X1)) != iProver_top
    | r2_hidden(sK3(X1,X0),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_33,negated_conjecture,
    ( r2_hidden(sK7,sK6)
    | ~ v4_ordinal1(sK6) ),
    inference(cnf_transformation,[],[f104])).

cnf(c_1345,plain,
    ( r2_hidden(sK7,sK6) = iProver_top
    | v4_ordinal1(sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_9,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X2,X0)
    | r2_hidden(X2,k3_tarski(X1)) ),
    inference(cnf_transformation,[],[f116])).

cnf(c_1368,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X2,X0) != iProver_top
    | r2_hidden(X2,k3_tarski(X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_3871,plain,
    ( r2_hidden(X0,k3_tarski(sK6)) = iProver_top
    | r2_hidden(X0,sK7) != iProver_top
    | v4_ordinal1(sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_1345,c_1368])).

cnf(c_20,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ v3_ordinal1(X1)
    | v3_ordinal1(X0) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_1357,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | v3_ordinal1(X1) != iProver_top
    | v3_ordinal1(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_4371,plain,
    ( r2_hidden(X0,sK7) != iProver_top
    | v4_ordinal1(sK6) != iProver_top
    | v3_ordinal1(X0) = iProver_top
    | v3_ordinal1(k3_tarski(sK6)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3871,c_1357])).

cnf(c_36,negated_conjecture,
    ( v3_ordinal1(sK6) ),
    inference(cnf_transformation,[],[f101])).

cnf(c_37,plain,
    ( v3_ordinal1(sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_36])).

cnf(c_28,plain,
    ( r2_hidden(sK4(X0),X0)
    | v3_ordinal1(k3_tarski(X0)) ),
    inference(cnf_transformation,[],[f96])).

cnf(c_2418,plain,
    ( ~ v3_ordinal1(X0)
    | v3_ordinal1(sK4(X0))
    | v3_ordinal1(k3_tarski(X0)) ),
    inference(resolution,[status(thm)],[c_20,c_28])).

cnf(c_27,plain,
    ( ~ v3_ordinal1(sK4(X0))
    | v3_ordinal1(k3_tarski(X0)) ),
    inference(cnf_transformation,[],[f97])).

cnf(c_2431,plain,
    ( ~ v3_ordinal1(X0)
    | v3_ordinal1(k3_tarski(X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2418,c_27])).

cnf(c_2433,plain,
    ( v3_ordinal1(X0) != iProver_top
    | v3_ordinal1(k3_tarski(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2431])).

cnf(c_2435,plain,
    ( v3_ordinal1(k3_tarski(sK6)) = iProver_top
    | v3_ordinal1(sK6) != iProver_top ),
    inference(instantiation,[status(thm)],[c_2433])).

cnf(c_5943,plain,
    ( v3_ordinal1(X0) = iProver_top
    | v4_ordinal1(sK6) != iProver_top
    | r2_hidden(X0,sK7) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4371,c_37,c_2435])).

cnf(c_5944,plain,
    ( r2_hidden(X0,sK7) != iProver_top
    | v4_ordinal1(sK6) != iProver_top
    | v3_ordinal1(X0) = iProver_top ),
    inference(renaming,[status(thm)],[c_5943])).

cnf(c_5953,plain,
    ( r2_hidden(X0,k3_tarski(sK7)) != iProver_top
    | v4_ordinal1(sK6) != iProver_top
    | v3_ordinal1(sK3(sK7,X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1367,c_5944])).

cnf(c_16,plain,
    ( ~ v4_ordinal1(X0)
    | k3_tarski(X0) = X0 ),
    inference(cnf_transformation,[],[f84])).

cnf(c_88,plain,
    ( ~ v4_ordinal1(sK6)
    | k3_tarski(sK6) = sK6 ),
    inference(instantiation,[status(thm)],[c_16])).

cnf(c_15,plain,
    ( v4_ordinal1(X0)
    | k3_tarski(X0) != X0 ),
    inference(cnf_transformation,[],[f85])).

cnf(c_90,plain,
    ( k3_tarski(X0) != X0
    | v4_ordinal1(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_92,plain,
    ( k3_tarski(sK6) != sK6
    | v4_ordinal1(sK6) = iProver_top ),
    inference(instantiation,[status(thm)],[c_90])).

cnf(c_19,plain,
    ( r2_hidden(X0,k2_xboole_0(X0,k1_tarski(X0))) ),
    inference(cnf_transformation,[],[f106])).

cnf(c_3675,plain,
    ( r2_hidden(X0,k3_tarski(X1))
    | ~ r2_hidden(k2_xboole_0(X0,k1_tarski(X0)),X1) ),
    inference(resolution,[status(thm)],[c_9,c_19])).

cnf(c_12635,plain,
    ( r2_hidden(X0,k3_tarski(sK6))
    | ~ r2_hidden(X0,sK6)
    | v4_ordinal1(sK6)
    | ~ v3_ordinal1(X0) ),
    inference(resolution,[status(thm)],[c_3675,c_35])).

cnf(c_14,plain,
    ( ~ r2_hidden(X0,X1)
    | r1_tarski(X0,X1)
    | ~ v1_ordinal1(X1) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_12663,plain,
    ( ~ r2_hidden(X0,sK6)
    | r1_tarski(X0,k3_tarski(sK6))
    | v4_ordinal1(sK6)
    | ~ v3_ordinal1(X0)
    | ~ v1_ordinal1(k3_tarski(sK6)) ),
    inference(resolution,[status(thm)],[c_12635,c_14])).

cnf(c_12,plain,
    ( ~ v3_ordinal1(X0)
    | v1_ordinal1(X0) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_100,plain,
    ( ~ v3_ordinal1(sK6)
    | v1_ordinal1(sK6) ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_2434,plain,
    ( v3_ordinal1(k3_tarski(sK6))
    | ~ v3_ordinal1(sK6) ),
    inference(instantiation,[status(thm)],[c_2431])).

cnf(c_31,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r1_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f100])).

cnf(c_2725,plain,
    ( ~ r2_hidden(X0,k3_tarski(X1))
    | ~ r1_tarski(sK3(X1,X0),X0) ),
    inference(resolution,[status(thm)],[c_11,c_31])).

cnf(c_2729,plain,
    ( ~ r2_hidden(sK6,k3_tarski(sK6))
    | ~ r1_tarski(sK3(sK6,sK6),sK6) ),
    inference(instantiation,[status(thm)],[c_2725])).

cnf(c_2741,plain,
    ( ~ r2_hidden(X0,k3_tarski(X1))
    | r1_tarski(sK3(X1,X0),X1)
    | ~ v1_ordinal1(X1) ),
    inference(resolution,[status(thm)],[c_14,c_10])).

cnf(c_2743,plain,
    ( ~ r2_hidden(sK6,k3_tarski(sK6))
    | r1_tarski(sK3(sK6,sK6),sK6)
    | ~ v1_ordinal1(sK6) ),
    inference(instantiation,[status(thm)],[c_2741])).

cnf(c_21,plain,
    ( r2_hidden(X0,X1)
    | r2_hidden(X1,X0)
    | ~ v3_ordinal1(X0)
    | ~ v3_ordinal1(X1)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f90])).

cnf(c_5727,plain,
    ( r2_hidden(X0,k3_tarski(X0))
    | r2_hidden(k3_tarski(X0),X0)
    | v4_ordinal1(X0)
    | ~ v3_ordinal1(X0)
    | ~ v3_ordinal1(k3_tarski(X0)) ),
    inference(resolution,[status(thm)],[c_21,c_15])).

cnf(c_5729,plain,
    ( r2_hidden(k3_tarski(sK6),sK6)
    | r2_hidden(sK6,k3_tarski(sK6))
    | v4_ordinal1(sK6)
    | ~ v3_ordinal1(k3_tarski(sK6))
    | ~ v3_ordinal1(sK6) ),
    inference(instantiation,[status(thm)],[c_5727])).

cnf(c_12661,plain,
    ( ~ r2_hidden(X0,sK6)
    | ~ r1_tarski(k3_tarski(sK6),X0)
    | v4_ordinal1(sK6)
    | ~ v3_ordinal1(X0) ),
    inference(resolution,[status(thm)],[c_12635,c_31])).

cnf(c_5,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f115])).

cnf(c_13023,plain,
    ( ~ r2_hidden(k3_tarski(sK6),sK6)
    | v4_ordinal1(sK6)
    | ~ v3_ordinal1(k3_tarski(sK6)) ),
    inference(resolution,[status(thm)],[c_12661,c_5])).

cnf(c_13026,plain,
    ( v4_ordinal1(sK6) ),
    inference(global_propositional_subsumption,[status(thm)],[c_12663,c_36,c_100,c_2434,c_2729,c_2743,c_5729,c_13023])).

cnf(c_15691,plain,
    ( r2_hidden(X0,k3_tarski(sK7)) != iProver_top
    | v3_ordinal1(sK3(sK7,X0)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5953,c_36,c_88,c_92,c_100,c_2434,c_2729,c_2743,c_5729,c_13023])).

cnf(c_15707,plain,
    ( r2_hidden(X0,sK6) != iProver_top
    | r1_tarski(sK6,k3_tarski(sK7)) != iProver_top
    | v4_ordinal1(sK6) = iProver_top
    | v3_ordinal1(X0) != iProver_top
    | v3_ordinal1(sK3(sK7,k2_xboole_0(X0,k1_tarski(X0)))) = iProver_top ),
    inference(superposition,[status(thm)],[c_3810,c_15691])).

cnf(c_15813,plain,
    ( v4_ordinal1(sK6) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_15707,c_36,c_88,c_92,c_100,c_2434,c_2729,c_2743,c_5729,c_13023])).

cnf(c_1356,plain,
    ( X0 = X1
    | r2_hidden(X1,X0) = iProver_top
    | r2_hidden(X0,X1) = iProver_top
    | v3_ordinal1(X1) != iProver_top
    | v3_ordinal1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_32,negated_conjecture,
    ( ~ r2_hidden(k2_xboole_0(sK7,k1_tarski(sK7)),sK6)
    | ~ v4_ordinal1(sK6) ),
    inference(cnf_transformation,[],[f112])).

cnf(c_1346,plain,
    ( r2_hidden(k2_xboole_0(sK7,k1_tarski(sK7)),sK6) != iProver_top
    | v4_ordinal1(sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_7115,plain,
    ( k2_xboole_0(sK7,k1_tarski(sK7)) = sK6
    | r2_hidden(sK6,k2_xboole_0(sK7,k1_tarski(sK7))) = iProver_top
    | v4_ordinal1(sK6) != iProver_top
    | v3_ordinal1(k2_xboole_0(sK7,k1_tarski(sK7))) != iProver_top
    | v3_ordinal1(sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_1356,c_1346])).

cnf(c_34,negated_conjecture,
    ( ~ v4_ordinal1(sK6)
    | v3_ordinal1(sK7) ),
    inference(cnf_transformation,[],[f103])).

cnf(c_41,plain,
    ( v4_ordinal1(sK6) != iProver_top
    | v3_ordinal1(sK7) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_1347,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_2384,plain,
    ( r1_tarski(sK6,sK7) != iProver_top
    | v4_ordinal1(sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_1345,c_1347])).

cnf(c_18,plain,
    ( ~ r1_ordinal1(X0,X1)
    | r1_tarski(X0,X1)
    | ~ v3_ordinal1(X0)
    | ~ v3_ordinal1(X1) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_2997,plain,
    ( ~ r1_ordinal1(sK6,sK7)
    | r1_tarski(sK6,sK7)
    | ~ v3_ordinal1(sK6)
    | ~ v3_ordinal1(sK7) ),
    inference(instantiation,[status(thm)],[c_18])).

cnf(c_3007,plain,
    ( r1_ordinal1(sK6,sK7) != iProver_top
    | r1_tarski(sK6,sK7) = iProver_top
    | v3_ordinal1(sK6) != iProver_top
    | v3_ordinal1(sK7) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2997])).

cnf(c_22,plain,
    ( ~ v3_ordinal1(X0)
    | v3_ordinal1(k2_xboole_0(X0,k1_tarski(X0))) ),
    inference(cnf_transformation,[],[f107])).

cnf(c_5757,plain,
    ( v3_ordinal1(k2_xboole_0(sK7,k1_tarski(sK7)))
    | ~ v3_ordinal1(sK7) ),
    inference(instantiation,[status(thm)],[c_22])).

cnf(c_5758,plain,
    ( v3_ordinal1(k2_xboole_0(sK7,k1_tarski(sK7))) = iProver_top
    | v3_ordinal1(sK7) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5757])).

cnf(c_26,plain,
    ( r1_ordinal1(X0,X1)
    | ~ r2_hidden(X0,k2_xboole_0(X1,k1_tarski(X1)))
    | ~ v3_ordinal1(X0)
    | ~ v3_ordinal1(X1) ),
    inference(cnf_transformation,[],[f111])).

cnf(c_5899,plain,
    ( r1_ordinal1(sK6,sK7)
    | ~ r2_hidden(sK6,k2_xboole_0(sK7,k1_tarski(sK7)))
    | ~ v3_ordinal1(sK6)
    | ~ v3_ordinal1(sK7) ),
    inference(instantiation,[status(thm)],[c_26])).

cnf(c_5903,plain,
    ( r1_ordinal1(sK6,sK7) = iProver_top
    | r2_hidden(sK6,k2_xboole_0(sK7,k1_tarski(sK7))) != iProver_top
    | v3_ordinal1(sK6) != iProver_top
    | v3_ordinal1(sK7) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5899])).

cnf(c_7526,plain,
    ( k2_xboole_0(sK7,k1_tarski(sK7)) = sK6
    | v4_ordinal1(sK6) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_7115,c_37,c_41,c_2384,c_3007,c_5758,c_5903])).

cnf(c_15819,plain,
    ( k2_xboole_0(sK7,k1_tarski(sK7)) = sK6 ),
    inference(superposition,[status(thm)],[c_15813,c_7526])).

cnf(c_24,plain,
    ( r1_ordinal1(k2_xboole_0(X0,k1_tarski(X0)),X1)
    | ~ r2_hidden(X0,X1)
    | ~ v3_ordinal1(X0)
    | ~ v3_ordinal1(X1) ),
    inference(cnf_transformation,[],[f109])).

cnf(c_378,plain,
    ( ~ r2_hidden(X0,X1)
    | r1_ordinal1(k2_xboole_0(X0,k1_tarski(X0)),X1)
    | ~ v3_ordinal1(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_24,c_20])).

cnf(c_379,plain,
    ( r1_ordinal1(k2_xboole_0(X0,k1_tarski(X0)),X1)
    | ~ r2_hidden(X0,X1)
    | ~ v3_ordinal1(X1) ),
    inference(renaming,[status(thm)],[c_378])).

cnf(c_1341,plain,
    ( r1_ordinal1(k2_xboole_0(X0,k1_tarski(X0)),X1) = iProver_top
    | r2_hidden(X0,X1) != iProver_top
    | v3_ordinal1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_379])).

cnf(c_16082,plain,
    ( r1_ordinal1(sK6,X0) = iProver_top
    | r2_hidden(sK7,X0) != iProver_top
    | v3_ordinal1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_15819,c_1341])).

cnf(c_17107,plain,
    ( r1_ordinal1(sK6,sK3(X0,sK7)) = iProver_top
    | r2_hidden(sK7,k3_tarski(X0)) != iProver_top
    | v3_ordinal1(sK3(X0,sK7)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1366,c_16082])).

cnf(c_17165,plain,
    ( r1_ordinal1(sK6,sK3(sK6,sK7)) = iProver_top
    | r2_hidden(sK7,k3_tarski(sK6)) != iProver_top
    | v3_ordinal1(sK3(sK6,sK7)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_17107])).

cnf(c_12205,plain,
    ( ~ r1_ordinal1(sK6,sK3(X0,sK7))
    | r1_tarski(sK6,sK3(X0,sK7))
    | ~ v3_ordinal1(sK3(X0,sK7))
    | ~ v3_ordinal1(sK6) ),
    inference(instantiation,[status(thm)],[c_18])).

cnf(c_12221,plain,
    ( r1_ordinal1(sK6,sK3(X0,sK7)) != iProver_top
    | r1_tarski(sK6,sK3(X0,sK7)) = iProver_top
    | v3_ordinal1(sK3(X0,sK7)) != iProver_top
    | v3_ordinal1(sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12205])).

cnf(c_12223,plain,
    ( r1_ordinal1(sK6,sK3(sK6,sK7)) != iProver_top
    | r1_tarski(sK6,sK3(sK6,sK7)) = iProver_top
    | v3_ordinal1(sK3(sK6,sK7)) != iProver_top
    | v3_ordinal1(sK6) != iProver_top ),
    inference(instantiation,[status(thm)],[c_12221])).

cnf(c_2258,plain,
    ( ~ r2_hidden(sK3(X0,X1),X0)
    | ~ r1_tarski(X0,sK3(X0,X1)) ),
    inference(instantiation,[status(thm)],[c_31])).

cnf(c_12166,plain,
    ( ~ r2_hidden(sK3(sK6,sK7),sK6)
    | ~ r1_tarski(sK6,sK3(sK6,sK7)) ),
    inference(instantiation,[status(thm)],[c_2258])).

cnf(c_12167,plain,
    ( r2_hidden(sK3(sK6,sK7),sK6) != iProver_top
    | r1_tarski(sK6,sK3(sK6,sK7)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12166])).

cnf(c_1363,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r1_tarski(X0,X1) = iProver_top
    | v1_ordinal1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_4370,plain,
    ( r2_hidden(X0,sK7) != iProver_top
    | r1_tarski(X0,k3_tarski(sK6)) = iProver_top
    | v4_ordinal1(sK6) != iProver_top
    | v1_ordinal1(k3_tarski(sK6)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3871,c_1363])).

cnf(c_2530,plain,
    ( ~ v3_ordinal1(X0)
    | v1_ordinal1(k3_tarski(X0)) ),
    inference(resolution,[status(thm)],[c_2431,c_12])).

cnf(c_2531,plain,
    ( v3_ordinal1(X0) != iProver_top
    | v1_ordinal1(k3_tarski(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2530])).

cnf(c_2533,plain,
    ( v3_ordinal1(sK6) != iProver_top
    | v1_ordinal1(k3_tarski(sK6)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_2531])).

cnf(c_6231,plain,
    ( v4_ordinal1(sK6) != iProver_top
    | r1_tarski(X0,k3_tarski(sK6)) = iProver_top
    | r2_hidden(X0,sK7) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4370,c_37,c_2533])).

cnf(c_6232,plain,
    ( r2_hidden(X0,sK7) != iProver_top
    | r1_tarski(X0,k3_tarski(sK6)) = iProver_top
    | v4_ordinal1(sK6) != iProver_top ),
    inference(renaming,[status(thm)],[c_6231])).

cnf(c_3809,plain,
    ( r2_hidden(sK7,X0) = iProver_top
    | r1_tarski(sK6,X0) != iProver_top
    | v4_ordinal1(sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_1345,c_1374])).

cnf(c_6242,plain,
    ( r2_hidden(sK6,sK7) != iProver_top
    | r2_hidden(sK7,k3_tarski(sK6)) = iProver_top
    | v4_ordinal1(sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_6232,c_3809])).

cnf(c_42,plain,
    ( r2_hidden(sK7,sK6) = iProver_top
    | v4_ordinal1(sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_87,plain,
    ( k3_tarski(X0) = X0
    | v4_ordinal1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_89,plain,
    ( k3_tarski(sK6) = sK6
    | v4_ordinal1(sK6) != iProver_top ),
    inference(instantiation,[status(thm)],[c_87])).

cnf(c_630,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_3121,plain,
    ( sK7 = sK7 ),
    inference(instantiation,[status(thm)],[c_630])).

cnf(c_632,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_1852,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(sK7,sK6)
    | X1 != sK6
    | X0 != sK7 ),
    inference(instantiation,[status(thm)],[c_632])).

cnf(c_3120,plain,
    ( r2_hidden(sK7,X0)
    | ~ r2_hidden(sK7,sK6)
    | X0 != sK6
    | sK7 != sK7 ),
    inference(instantiation,[status(thm)],[c_1852])).

cnf(c_6343,plain,
    ( r2_hidden(sK7,k3_tarski(sK6))
    | ~ r2_hidden(sK7,sK6)
    | k3_tarski(sK6) != sK6
    | sK7 != sK7 ),
    inference(instantiation,[status(thm)],[c_3120])).

cnf(c_6345,plain,
    ( k3_tarski(sK6) != sK6
    | sK7 != sK7
    | r2_hidden(sK7,k3_tarski(sK6)) = iProver_top
    | r2_hidden(sK7,sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6343])).

cnf(c_6436,plain,
    ( r2_hidden(sK7,k3_tarski(sK6)) = iProver_top
    | v4_ordinal1(sK6) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6242,c_42,c_89,c_3121,c_6345])).

cnf(c_3288,plain,
    ( r2_hidden(X0,k3_tarski(X1)) != iProver_top
    | v3_ordinal1(X1) != iProver_top
    | v3_ordinal1(sK3(X1,X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1367,c_1357])).

cnf(c_10851,plain,
    ( v4_ordinal1(sK6) != iProver_top
    | v3_ordinal1(sK3(sK6,sK7)) = iProver_top
    | v3_ordinal1(sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_6436,c_3288])).

cnf(c_3069,plain,
    ( r2_hidden(sK3(X0,sK7),X0)
    | ~ r2_hidden(sK7,k3_tarski(X0)) ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_3074,plain,
    ( r2_hidden(sK3(X0,sK7),X0) = iProver_top
    | r2_hidden(sK7,k3_tarski(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3069])).

cnf(c_3076,plain,
    ( r2_hidden(sK3(sK6,sK7),sK6) = iProver_top
    | r2_hidden(sK7,k3_tarski(sK6)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_3074])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_17165,c_13026,c_12223,c_12167,c_10851,c_6436,c_3076,c_92,c_88,c_37])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : iproveropt_run.sh %d %s
% 0.13/0.33  % Computer   : n001.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 18:51:15 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 3.97/0.99  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.97/0.99  
% 3.97/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.97/0.99  
% 3.97/0.99  ------  iProver source info
% 3.97/0.99  
% 3.97/0.99  git: date: 2020-06-30 10:37:57 +0100
% 3.97/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.97/0.99  git: non_committed_changes: false
% 3.97/0.99  git: last_make_outside_of_git: false
% 3.97/0.99  
% 3.97/0.99  ------ 
% 3.97/0.99  ------ Parsing...
% 3.97/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.97/0.99  
% 3.97/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 1 0s  sf_e 
% 3.97/0.99  
% 3.97/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.97/0.99  
% 3.97/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.97/0.99  ------ Proving...
% 3.97/0.99  ------ Problem Properties 
% 3.97/0.99  
% 3.97/0.99  
% 3.97/0.99  clauses                                 36
% 3.97/0.99  conjectures                             5
% 3.97/0.99  EPR                                     14
% 3.97/0.99  Horn                                    29
% 3.97/0.99  unary                                   5
% 3.97/0.99  binary                                  14
% 3.97/0.99  lits                                    94
% 3.97/0.99  lits eq                                 7
% 3.97/0.99  fd_pure                                 0
% 3.97/0.99  fd_pseudo                               0
% 3.97/0.99  fd_cond                                 0
% 3.97/0.99  fd_pseudo_cond                          5
% 3.97/0.99  AC symbols                              0
% 3.97/0.99  
% 3.97/0.99  ------ Input Options Time Limit: Unbounded
% 3.97/0.99  
% 3.97/0.99  
% 3.97/0.99  ------ 
% 3.97/0.99  Current options:
% 3.97/0.99  ------ 
% 3.97/0.99  
% 3.97/0.99  
% 3.97/0.99  
% 3.97/0.99  
% 3.97/0.99  ------ Proving...
% 3.97/0.99  
% 3.97/0.99  
% 3.97/0.99  % SZS status Theorem for theBenchmark.p
% 3.97/0.99  
% 3.97/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 3.97/0.99  
% 3.97/0.99  fof(f3,axiom,(
% 3.97/0.99    ! [X0,X1] : (k3_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (r2_hidden(X3,X0) & r2_hidden(X2,X3))))),
% 3.97/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.97/0.99  
% 3.97/0.99  fof(f48,plain,(
% 3.97/0.99    ! [X0,X1] : ((k3_tarski(X0) = X1 | ? [X2] : ((! [X3] : (~r2_hidden(X3,X0) | ~r2_hidden(X2,X3)) | ~r2_hidden(X2,X1)) & (? [X3] : (r2_hidden(X3,X0) & r2_hidden(X2,X3)) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ! [X3] : (~r2_hidden(X3,X0) | ~r2_hidden(X2,X3))) & (? [X3] : (r2_hidden(X3,X0) & r2_hidden(X2,X3)) | ~r2_hidden(X2,X1))) | k3_tarski(X0) != X1))),
% 3.97/0.99    inference(nnf_transformation,[],[f3])).
% 3.97/0.99  
% 3.97/0.99  fof(f49,plain,(
% 3.97/0.99    ! [X0,X1] : ((k3_tarski(X0) = X1 | ? [X2] : ((! [X3] : (~r2_hidden(X3,X0) | ~r2_hidden(X2,X3)) | ~r2_hidden(X2,X1)) & (? [X4] : (r2_hidden(X4,X0) & r2_hidden(X2,X4)) | r2_hidden(X2,X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : (~r2_hidden(X6,X0) | ~r2_hidden(X5,X6))) & (? [X7] : (r2_hidden(X7,X0) & r2_hidden(X5,X7)) | ~r2_hidden(X5,X1))) | k3_tarski(X0) != X1))),
% 3.97/0.99    inference(rectify,[],[f48])).
% 3.97/0.99  
% 3.97/0.99  fof(f52,plain,(
% 3.97/0.99    ! [X5,X0] : (? [X7] : (r2_hidden(X7,X0) & r2_hidden(X5,X7)) => (r2_hidden(sK3(X0,X5),X0) & r2_hidden(X5,sK3(X0,X5))))),
% 3.97/0.99    introduced(choice_axiom,[])).
% 3.97/0.99  
% 3.97/0.99  fof(f51,plain,(
% 3.97/0.99    ( ! [X2] : (! [X1,X0] : (? [X4] : (r2_hidden(X4,X0) & r2_hidden(X2,X4)) => (r2_hidden(sK2(X0,X1),X0) & r2_hidden(X2,sK2(X0,X1))))) )),
% 3.97/0.99    introduced(choice_axiom,[])).
% 3.97/0.99  
% 3.97/0.99  fof(f50,plain,(
% 3.97/0.99    ! [X1,X0] : (? [X2] : ((! [X3] : (~r2_hidden(X3,X0) | ~r2_hidden(X2,X3)) | ~r2_hidden(X2,X1)) & (? [X4] : (r2_hidden(X4,X0) & r2_hidden(X2,X4)) | r2_hidden(X2,X1))) => ((! [X3] : (~r2_hidden(X3,X0) | ~r2_hidden(sK1(X0,X1),X3)) | ~r2_hidden(sK1(X0,X1),X1)) & (? [X4] : (r2_hidden(X4,X0) & r2_hidden(sK1(X0,X1),X4)) | r2_hidden(sK1(X0,X1),X1))))),
% 3.97/0.99    introduced(choice_axiom,[])).
% 3.97/0.99  
% 3.97/0.99  fof(f53,plain,(
% 3.97/0.99    ! [X0,X1] : ((k3_tarski(X0) = X1 | ((! [X3] : (~r2_hidden(X3,X0) | ~r2_hidden(sK1(X0,X1),X3)) | ~r2_hidden(sK1(X0,X1),X1)) & ((r2_hidden(sK2(X0,X1),X0) & r2_hidden(sK1(X0,X1),sK2(X0,X1))) | r2_hidden(sK1(X0,X1),X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : (~r2_hidden(X6,X0) | ~r2_hidden(X5,X6))) & ((r2_hidden(sK3(X0,X5),X0) & r2_hidden(X5,sK3(X0,X5))) | ~r2_hidden(X5,X1))) | k3_tarski(X0) != X1))),
% 3.97/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f49,f52,f51,f50])).
% 3.97/0.99  
% 3.97/0.99  fof(f74,plain,(
% 3.97/0.99    ( ! [X0,X5,X1] : (r2_hidden(X5,sK3(X0,X5)) | ~r2_hidden(X5,X1) | k3_tarski(X0) != X1) )),
% 3.97/0.99    inference(cnf_transformation,[],[f53])).
% 3.97/0.99  
% 3.97/0.99  fof(f118,plain,(
% 3.97/0.99    ( ! [X0,X5] : (r2_hidden(X5,sK3(X0,X5)) | ~r2_hidden(X5,k3_tarski(X0))) )),
% 3.97/0.99    inference(equality_resolution,[],[f74])).
% 3.97/0.99  
% 3.97/0.99  fof(f19,conjecture,(
% 3.97/0.99    ! [X0] : (v3_ordinal1(X0) => (v4_ordinal1(X0) <=> ! [X1] : (v3_ordinal1(X1) => (r2_hidden(X1,X0) => r2_hidden(k1_ordinal1(X1),X0)))))),
% 3.97/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.97/0.99  
% 3.97/0.99  fof(f20,negated_conjecture,(
% 3.97/0.99    ~! [X0] : (v3_ordinal1(X0) => (v4_ordinal1(X0) <=> ! [X1] : (v3_ordinal1(X1) => (r2_hidden(X1,X0) => r2_hidden(k1_ordinal1(X1),X0)))))),
% 3.97/0.99    inference(negated_conjecture,[],[f19])).
% 3.97/0.99  
% 3.97/0.99  fof(f40,plain,(
% 3.97/0.99    ? [X0] : ((v4_ordinal1(X0) <~> ! [X1] : ((r2_hidden(k1_ordinal1(X1),X0) | ~r2_hidden(X1,X0)) | ~v3_ordinal1(X1))) & v3_ordinal1(X0))),
% 3.97/0.99    inference(ennf_transformation,[],[f20])).
% 3.97/0.99  
% 3.97/0.99  fof(f41,plain,(
% 3.97/0.99    ? [X0] : ((v4_ordinal1(X0) <~> ! [X1] : (r2_hidden(k1_ordinal1(X1),X0) | ~r2_hidden(X1,X0) | ~v3_ordinal1(X1))) & v3_ordinal1(X0))),
% 3.97/0.99    inference(flattening,[],[f40])).
% 3.97/0.99  
% 3.97/0.99  fof(f62,plain,(
% 3.97/0.99    ? [X0] : (((? [X1] : (~r2_hidden(k1_ordinal1(X1),X0) & r2_hidden(X1,X0) & v3_ordinal1(X1)) | ~v4_ordinal1(X0)) & (! [X1] : (r2_hidden(k1_ordinal1(X1),X0) | ~r2_hidden(X1,X0) | ~v3_ordinal1(X1)) | v4_ordinal1(X0))) & v3_ordinal1(X0))),
% 3.97/0.99    inference(nnf_transformation,[],[f41])).
% 3.97/0.99  
% 3.97/0.99  fof(f63,plain,(
% 3.97/0.99    ? [X0] : ((? [X1] : (~r2_hidden(k1_ordinal1(X1),X0) & r2_hidden(X1,X0) & v3_ordinal1(X1)) | ~v4_ordinal1(X0)) & (! [X1] : (r2_hidden(k1_ordinal1(X1),X0) | ~r2_hidden(X1,X0) | ~v3_ordinal1(X1)) | v4_ordinal1(X0)) & v3_ordinal1(X0))),
% 3.97/0.99    inference(flattening,[],[f62])).
% 3.97/0.99  
% 3.97/0.99  fof(f64,plain,(
% 3.97/0.99    ? [X0] : ((? [X1] : (~r2_hidden(k1_ordinal1(X1),X0) & r2_hidden(X1,X0) & v3_ordinal1(X1)) | ~v4_ordinal1(X0)) & (! [X2] : (r2_hidden(k1_ordinal1(X2),X0) | ~r2_hidden(X2,X0) | ~v3_ordinal1(X2)) | v4_ordinal1(X0)) & v3_ordinal1(X0))),
% 3.97/0.99    inference(rectify,[],[f63])).
% 3.97/0.99  
% 3.97/0.99  fof(f66,plain,(
% 3.97/0.99    ( ! [X0] : (? [X1] : (~r2_hidden(k1_ordinal1(X1),X0) & r2_hidden(X1,X0) & v3_ordinal1(X1)) => (~r2_hidden(k1_ordinal1(sK7),X0) & r2_hidden(sK7,X0) & v3_ordinal1(sK7))) )),
% 3.97/0.99    introduced(choice_axiom,[])).
% 3.97/0.99  
% 3.97/0.99  fof(f65,plain,(
% 3.97/0.99    ? [X0] : ((? [X1] : (~r2_hidden(k1_ordinal1(X1),X0) & r2_hidden(X1,X0) & v3_ordinal1(X1)) | ~v4_ordinal1(X0)) & (! [X2] : (r2_hidden(k1_ordinal1(X2),X0) | ~r2_hidden(X2,X0) | ~v3_ordinal1(X2)) | v4_ordinal1(X0)) & v3_ordinal1(X0)) => ((? [X1] : (~r2_hidden(k1_ordinal1(X1),sK6) & r2_hidden(X1,sK6) & v3_ordinal1(X1)) | ~v4_ordinal1(sK6)) & (! [X2] : (r2_hidden(k1_ordinal1(X2),sK6) | ~r2_hidden(X2,sK6) | ~v3_ordinal1(X2)) | v4_ordinal1(sK6)) & v3_ordinal1(sK6))),
% 3.97/0.99    introduced(choice_axiom,[])).
% 3.97/0.99  
% 3.97/0.99  fof(f67,plain,(
% 3.97/0.99    ((~r2_hidden(k1_ordinal1(sK7),sK6) & r2_hidden(sK7,sK6) & v3_ordinal1(sK7)) | ~v4_ordinal1(sK6)) & (! [X2] : (r2_hidden(k1_ordinal1(X2),sK6) | ~r2_hidden(X2,sK6) | ~v3_ordinal1(X2)) | v4_ordinal1(sK6)) & v3_ordinal1(sK6)),
% 3.97/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7])],[f64,f66,f65])).
% 3.97/0.99  
% 3.97/0.99  fof(f102,plain,(
% 3.97/0.99    ( ! [X2] : (r2_hidden(k1_ordinal1(X2),sK6) | ~r2_hidden(X2,sK6) | ~v3_ordinal1(X2) | v4_ordinal1(sK6)) )),
% 3.97/0.99    inference(cnf_transformation,[],[f67])).
% 3.97/0.99  
% 3.97/0.99  fof(f6,axiom,(
% 3.97/0.99    ! [X0] : k1_ordinal1(X0) = k2_xboole_0(X0,k1_tarski(X0))),
% 3.97/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.97/0.99  
% 3.97/0.99  fof(f82,plain,(
% 3.97/0.99    ( ! [X0] : (k1_ordinal1(X0) = k2_xboole_0(X0,k1_tarski(X0))) )),
% 3.97/1.00    inference(cnf_transformation,[],[f6])).
% 3.97/1.00  
% 3.97/1.00  fof(f113,plain,(
% 3.97/1.00    ( ! [X2] : (r2_hidden(k2_xboole_0(X2,k1_tarski(X2)),sK6) | ~r2_hidden(X2,sK6) | ~v3_ordinal1(X2) | v4_ordinal1(sK6)) )),
% 3.97/1.00    inference(definition_unfolding,[],[f102,f82])).
% 3.97/1.00  
% 3.97/1.00  fof(f1,axiom,(
% 3.97/1.00    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 3.97/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.97/1.00  
% 3.97/1.00  fof(f23,plain,(
% 3.97/1.00    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 3.97/1.00    inference(ennf_transformation,[],[f1])).
% 3.97/1.00  
% 3.97/1.00  fof(f42,plain,(
% 3.97/1.00    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 3.97/1.00    inference(nnf_transformation,[],[f23])).
% 3.97/1.00  
% 3.97/1.00  fof(f43,plain,(
% 3.97/1.00    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 3.97/1.00    inference(rectify,[],[f42])).
% 3.97/1.00  
% 3.97/1.00  fof(f44,plain,(
% 3.97/1.00    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 3.97/1.00    introduced(choice_axiom,[])).
% 3.97/1.00  
% 3.97/1.00  fof(f45,plain,(
% 3.97/1.00    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 3.97/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f43,f44])).
% 3.97/1.00  
% 3.97/1.00  fof(f68,plain,(
% 3.97/1.00    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,X1)) )),
% 3.97/1.00    inference(cnf_transformation,[],[f45])).
% 3.97/1.00  
% 3.97/1.00  fof(f75,plain,(
% 3.97/1.00    ( ! [X0,X5,X1] : (r2_hidden(sK3(X0,X5),X0) | ~r2_hidden(X5,X1) | k3_tarski(X0) != X1) )),
% 3.97/1.00    inference(cnf_transformation,[],[f53])).
% 3.97/1.00  
% 3.97/1.00  fof(f117,plain,(
% 3.97/1.00    ( ! [X0,X5] : (r2_hidden(sK3(X0,X5),X0) | ~r2_hidden(X5,k3_tarski(X0))) )),
% 3.97/1.00    inference(equality_resolution,[],[f75])).
% 3.97/1.00  
% 3.97/1.00  fof(f104,plain,(
% 3.97/1.00    r2_hidden(sK7,sK6) | ~v4_ordinal1(sK6)),
% 3.97/1.00    inference(cnf_transformation,[],[f67])).
% 3.97/1.00  
% 3.97/1.00  fof(f76,plain,(
% 3.97/1.00    ( ! [X6,X0,X5,X1] : (r2_hidden(X5,X1) | ~r2_hidden(X6,X0) | ~r2_hidden(X5,X6) | k3_tarski(X0) != X1) )),
% 3.97/1.00    inference(cnf_transformation,[],[f53])).
% 3.97/1.00  
% 3.97/1.00  fof(f116,plain,(
% 3.97/1.00    ( ! [X6,X0,X5] : (r2_hidden(X5,k3_tarski(X0)) | ~r2_hidden(X6,X0) | ~r2_hidden(X5,X6)) )),
% 3.97/1.00    inference(equality_resolution,[],[f76])).
% 3.97/1.00  
% 3.97/1.00  fof(f11,axiom,(
% 3.97/1.00    ! [X0,X1] : (v3_ordinal1(X1) => (r2_hidden(X0,X1) => v3_ordinal1(X0)))),
% 3.97/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.97/1.00  
% 3.97/1.00  fof(f30,plain,(
% 3.97/1.00    ! [X0,X1] : ((v3_ordinal1(X0) | ~r2_hidden(X0,X1)) | ~v3_ordinal1(X1))),
% 3.97/1.00    inference(ennf_transformation,[],[f11])).
% 3.97/1.00  
% 3.97/1.00  fof(f31,plain,(
% 3.97/1.00    ! [X0,X1] : (v3_ordinal1(X0) | ~r2_hidden(X0,X1) | ~v3_ordinal1(X1))),
% 3.97/1.00    inference(flattening,[],[f30])).
% 3.97/1.00  
% 3.97/1.00  fof(f89,plain,(
% 3.97/1.00    ( ! [X0,X1] : (v3_ordinal1(X0) | ~r2_hidden(X0,X1) | ~v3_ordinal1(X1)) )),
% 3.97/1.00    inference(cnf_transformation,[],[f31])).
% 3.97/1.00  
% 3.97/1.00  fof(f101,plain,(
% 3.97/1.00    v3_ordinal1(sK6)),
% 3.97/1.00    inference(cnf_transformation,[],[f67])).
% 3.97/1.00  
% 3.97/1.00  fof(f16,axiom,(
% 3.97/1.00    ! [X0] : (! [X1] : (r2_hidden(X1,X0) => v3_ordinal1(X1)) => v3_ordinal1(k3_tarski(X0)))),
% 3.97/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.97/1.00  
% 3.97/1.00  fof(f37,plain,(
% 3.97/1.00    ! [X0] : (v3_ordinal1(k3_tarski(X0)) | ? [X1] : (~v3_ordinal1(X1) & r2_hidden(X1,X0)))),
% 3.97/1.00    inference(ennf_transformation,[],[f16])).
% 3.97/1.00  
% 3.97/1.00  fof(f58,plain,(
% 3.97/1.00    ! [X0] : (? [X1] : (~v3_ordinal1(X1) & r2_hidden(X1,X0)) => (~v3_ordinal1(sK4(X0)) & r2_hidden(sK4(X0),X0)))),
% 3.97/1.00    introduced(choice_axiom,[])).
% 3.97/1.00  
% 3.97/1.00  fof(f59,plain,(
% 3.97/1.00    ! [X0] : (v3_ordinal1(k3_tarski(X0)) | (~v3_ordinal1(sK4(X0)) & r2_hidden(sK4(X0),X0)))),
% 3.97/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f37,f58])).
% 3.97/1.00  
% 3.97/1.00  fof(f96,plain,(
% 3.97/1.00    ( ! [X0] : (v3_ordinal1(k3_tarski(X0)) | r2_hidden(sK4(X0),X0)) )),
% 3.97/1.00    inference(cnf_transformation,[],[f59])).
% 3.97/1.00  
% 3.97/1.00  fof(f97,plain,(
% 3.97/1.00    ( ! [X0] : (v3_ordinal1(k3_tarski(X0)) | ~v3_ordinal1(sK4(X0))) )),
% 3.97/1.00    inference(cnf_transformation,[],[f59])).
% 3.97/1.00  
% 3.97/1.00  fof(f8,axiom,(
% 3.97/1.00    ! [X0] : (v4_ordinal1(X0) <=> k3_tarski(X0) = X0)),
% 3.97/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.97/1.00  
% 3.97/1.00  fof(f54,plain,(
% 3.97/1.00    ! [X0] : ((v4_ordinal1(X0) | k3_tarski(X0) != X0) & (k3_tarski(X0) = X0 | ~v4_ordinal1(X0)))),
% 3.97/1.00    inference(nnf_transformation,[],[f8])).
% 3.97/1.00  
% 3.97/1.00  fof(f84,plain,(
% 3.97/1.00    ( ! [X0] : (k3_tarski(X0) = X0 | ~v4_ordinal1(X0)) )),
% 3.97/1.00    inference(cnf_transformation,[],[f54])).
% 3.97/1.00  
% 3.97/1.00  fof(f85,plain,(
% 3.97/1.00    ( ! [X0] : (v4_ordinal1(X0) | k3_tarski(X0) != X0) )),
% 3.97/1.00    inference(cnf_transformation,[],[f54])).
% 3.97/1.00  
% 3.97/1.00  fof(f10,axiom,(
% 3.97/1.00    ! [X0] : r2_hidden(X0,k1_ordinal1(X0))),
% 3.97/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.97/1.00  
% 3.97/1.00  fof(f88,plain,(
% 3.97/1.00    ( ! [X0] : (r2_hidden(X0,k1_ordinal1(X0))) )),
% 3.97/1.00    inference(cnf_transformation,[],[f10])).
% 3.97/1.00  
% 3.97/1.00  fof(f106,plain,(
% 3.97/1.00    ( ! [X0] : (r2_hidden(X0,k2_xboole_0(X0,k1_tarski(X0)))) )),
% 3.97/1.00    inference(definition_unfolding,[],[f88,f82])).
% 3.97/1.00  
% 3.97/1.00  fof(f7,axiom,(
% 3.97/1.00    ! [X0] : (v1_ordinal1(X0) <=> ! [X1] : (r2_hidden(X1,X0) => r1_tarski(X1,X0)))),
% 3.97/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.97/1.00  
% 3.97/1.00  fof(f21,plain,(
% 3.97/1.00    ! [X0] : (v1_ordinal1(X0) => ! [X1] : (r2_hidden(X1,X0) => r1_tarski(X1,X0)))),
% 3.97/1.00    inference(unused_predicate_definition_removal,[],[f7])).
% 3.97/1.00  
% 3.97/1.00  fof(f27,plain,(
% 3.97/1.00    ! [X0] : (! [X1] : (r1_tarski(X1,X0) | ~r2_hidden(X1,X0)) | ~v1_ordinal1(X0))),
% 3.97/1.00    inference(ennf_transformation,[],[f21])).
% 3.97/1.00  
% 3.97/1.00  fof(f83,plain,(
% 3.97/1.00    ( ! [X0,X1] : (r1_tarski(X1,X0) | ~r2_hidden(X1,X0) | ~v1_ordinal1(X0)) )),
% 3.97/1.00    inference(cnf_transformation,[],[f27])).
% 3.97/1.00  
% 3.97/1.00  fof(f4,axiom,(
% 3.97/1.00    ! [X0] : (v3_ordinal1(X0) => (v2_ordinal1(X0) & v1_ordinal1(X0)))),
% 3.97/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.97/1.00  
% 3.97/1.00  fof(f22,plain,(
% 3.97/1.00    ! [X0] : (v3_ordinal1(X0) => v1_ordinal1(X0))),
% 3.97/1.00    inference(pure_predicate_removal,[],[f4])).
% 3.97/1.00  
% 3.97/1.00  fof(f24,plain,(
% 3.97/1.00    ! [X0] : (v1_ordinal1(X0) | ~v3_ordinal1(X0))),
% 3.97/1.00    inference(ennf_transformation,[],[f22])).
% 3.97/1.00  
% 3.97/1.00  fof(f80,plain,(
% 3.97/1.00    ( ! [X0] : (v1_ordinal1(X0) | ~v3_ordinal1(X0)) )),
% 3.97/1.00    inference(cnf_transformation,[],[f24])).
% 3.97/1.00  
% 3.97/1.00  fof(f18,axiom,(
% 3.97/1.00    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 3.97/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.97/1.00  
% 3.97/1.00  fof(f39,plain,(
% 3.97/1.00    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 3.97/1.00    inference(ennf_transformation,[],[f18])).
% 3.97/1.00  
% 3.97/1.00  fof(f100,plain,(
% 3.97/1.00    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1)) )),
% 3.97/1.00    inference(cnf_transformation,[],[f39])).
% 3.97/1.00  
% 3.97/1.00  fof(f12,axiom,(
% 3.97/1.00    ! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => ~(~r2_hidden(X1,X0) & X0 != X1 & ~r2_hidden(X0,X1))))),
% 3.97/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.97/1.00  
% 3.97/1.00  fof(f32,plain,(
% 3.97/1.00    ! [X0] : (! [X1] : ((r2_hidden(X1,X0) | X0 = X1 | r2_hidden(X0,X1)) | ~v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 3.97/1.00    inference(ennf_transformation,[],[f12])).
% 3.97/1.00  
% 3.97/1.00  fof(f33,plain,(
% 3.97/1.00    ! [X0] : (! [X1] : (r2_hidden(X1,X0) | X0 = X1 | r2_hidden(X0,X1) | ~v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 3.97/1.00    inference(flattening,[],[f32])).
% 3.97/1.00  
% 3.97/1.00  fof(f90,plain,(
% 3.97/1.00    ( ! [X0,X1] : (r2_hidden(X1,X0) | X0 = X1 | r2_hidden(X0,X1) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0)) )),
% 3.97/1.00    inference(cnf_transformation,[],[f33])).
% 3.97/1.00  
% 3.97/1.00  fof(f2,axiom,(
% 3.97/1.00    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 3.97/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.97/1.00  
% 3.97/1.00  fof(f46,plain,(
% 3.97/1.00    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.97/1.00    inference(nnf_transformation,[],[f2])).
% 3.97/1.00  
% 3.97/1.00  fof(f47,plain,(
% 3.97/1.00    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.97/1.00    inference(flattening,[],[f46])).
% 3.97/1.00  
% 3.97/1.00  fof(f71,plain,(
% 3.97/1.00    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 3.97/1.00    inference(cnf_transformation,[],[f47])).
% 3.97/1.00  
% 3.97/1.00  fof(f115,plain,(
% 3.97/1.00    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 3.97/1.00    inference(equality_resolution,[],[f71])).
% 3.97/1.00  
% 3.97/1.00  fof(f105,plain,(
% 3.97/1.00    ~r2_hidden(k1_ordinal1(sK7),sK6) | ~v4_ordinal1(sK6)),
% 3.97/1.00    inference(cnf_transformation,[],[f67])).
% 3.97/1.00  
% 3.97/1.00  fof(f112,plain,(
% 3.97/1.00    ~r2_hidden(k2_xboole_0(sK7,k1_tarski(sK7)),sK6) | ~v4_ordinal1(sK6)),
% 3.97/1.00    inference(definition_unfolding,[],[f105,f82])).
% 3.97/1.00  
% 3.97/1.00  fof(f103,plain,(
% 3.97/1.00    v3_ordinal1(sK7) | ~v4_ordinal1(sK6)),
% 3.97/1.00    inference(cnf_transformation,[],[f67])).
% 3.97/1.00  
% 3.97/1.00  fof(f9,axiom,(
% 3.97/1.00    ! [X0,X1] : ((v3_ordinal1(X1) & v3_ordinal1(X0)) => (r1_ordinal1(X0,X1) <=> r1_tarski(X0,X1)))),
% 3.97/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.97/1.00  
% 3.97/1.00  fof(f28,plain,(
% 3.97/1.00    ! [X0,X1] : ((r1_ordinal1(X0,X1) <=> r1_tarski(X0,X1)) | (~v3_ordinal1(X1) | ~v3_ordinal1(X0)))),
% 3.97/1.00    inference(ennf_transformation,[],[f9])).
% 3.97/1.00  
% 3.97/1.00  fof(f29,plain,(
% 3.97/1.00    ! [X0,X1] : ((r1_ordinal1(X0,X1) <=> r1_tarski(X0,X1)) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0))),
% 3.97/1.00    inference(flattening,[],[f28])).
% 3.97/1.00  
% 3.97/1.00  fof(f55,plain,(
% 3.97/1.00    ! [X0,X1] : (((r1_ordinal1(X0,X1) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~r1_ordinal1(X0,X1))) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0))),
% 3.97/1.00    inference(nnf_transformation,[],[f29])).
% 3.97/1.00  
% 3.97/1.00  fof(f86,plain,(
% 3.97/1.00    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r1_ordinal1(X0,X1) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0)) )),
% 3.97/1.00    inference(cnf_transformation,[],[f55])).
% 3.97/1.00  
% 3.97/1.00  fof(f13,axiom,(
% 3.97/1.00    ! [X0] : (v3_ordinal1(X0) => v3_ordinal1(k1_ordinal1(X0)))),
% 3.97/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.97/1.00  
% 3.97/1.00  fof(f34,plain,(
% 3.97/1.00    ! [X0] : (v3_ordinal1(k1_ordinal1(X0)) | ~v3_ordinal1(X0))),
% 3.97/1.00    inference(ennf_transformation,[],[f13])).
% 3.97/1.00  
% 3.97/1.00  fof(f91,plain,(
% 3.97/1.00    ( ! [X0] : (v3_ordinal1(k1_ordinal1(X0)) | ~v3_ordinal1(X0)) )),
% 3.97/1.00    inference(cnf_transformation,[],[f34])).
% 3.97/1.00  
% 3.97/1.00  fof(f107,plain,(
% 3.97/1.00    ( ! [X0] : (v3_ordinal1(k2_xboole_0(X0,k1_tarski(X0))) | ~v3_ordinal1(X0)) )),
% 3.97/1.00    inference(definition_unfolding,[],[f91,f82])).
% 3.97/1.00  
% 3.97/1.00  fof(f15,axiom,(
% 3.97/1.00    ! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => (r2_hidden(X0,k1_ordinal1(X1)) <=> r1_ordinal1(X0,X1))))),
% 3.97/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.97/1.00  
% 3.97/1.00  fof(f36,plain,(
% 3.97/1.00    ! [X0] : (! [X1] : ((r2_hidden(X0,k1_ordinal1(X1)) <=> r1_ordinal1(X0,X1)) | ~v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 3.97/1.00    inference(ennf_transformation,[],[f15])).
% 3.97/1.00  
% 3.97/1.00  fof(f57,plain,(
% 3.97/1.00    ! [X0] : (! [X1] : (((r2_hidden(X0,k1_ordinal1(X1)) | ~r1_ordinal1(X0,X1)) & (r1_ordinal1(X0,X1) | ~r2_hidden(X0,k1_ordinal1(X1)))) | ~v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 3.97/1.00    inference(nnf_transformation,[],[f36])).
% 3.97/1.00  
% 3.97/1.00  fof(f94,plain,(
% 3.97/1.00    ( ! [X0,X1] : (r1_ordinal1(X0,X1) | ~r2_hidden(X0,k1_ordinal1(X1)) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0)) )),
% 3.97/1.00    inference(cnf_transformation,[],[f57])).
% 3.97/1.00  
% 3.97/1.00  fof(f111,plain,(
% 3.97/1.00    ( ! [X0,X1] : (r1_ordinal1(X0,X1) | ~r2_hidden(X0,k2_xboole_0(X1,k1_tarski(X1))) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0)) )),
% 3.97/1.00    inference(definition_unfolding,[],[f94,f82])).
% 3.97/1.00  
% 3.97/1.00  fof(f14,axiom,(
% 3.97/1.00    ! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => (r2_hidden(X0,X1) <=> r1_ordinal1(k1_ordinal1(X0),X1))))),
% 3.97/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.97/1.00  
% 3.97/1.00  fof(f35,plain,(
% 3.97/1.00    ! [X0] : (! [X1] : ((r2_hidden(X0,X1) <=> r1_ordinal1(k1_ordinal1(X0),X1)) | ~v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 3.97/1.00    inference(ennf_transformation,[],[f14])).
% 3.97/1.00  
% 3.97/1.00  fof(f56,plain,(
% 3.97/1.00    ! [X0] : (! [X1] : (((r2_hidden(X0,X1) | ~r1_ordinal1(k1_ordinal1(X0),X1)) & (r1_ordinal1(k1_ordinal1(X0),X1) | ~r2_hidden(X0,X1))) | ~v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 3.97/1.00    inference(nnf_transformation,[],[f35])).
% 3.97/1.00  
% 3.97/1.00  fof(f92,plain,(
% 3.97/1.00    ( ! [X0,X1] : (r1_ordinal1(k1_ordinal1(X0),X1) | ~r2_hidden(X0,X1) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0)) )),
% 3.97/1.00    inference(cnf_transformation,[],[f56])).
% 3.97/1.00  
% 3.97/1.00  fof(f109,plain,(
% 3.97/1.00    ( ! [X0,X1] : (r1_ordinal1(k2_xboole_0(X0,k1_tarski(X0)),X1) | ~r2_hidden(X0,X1) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0)) )),
% 3.97/1.00    inference(definition_unfolding,[],[f92,f82])).
% 3.97/1.00  
% 3.97/1.00  cnf(c_11,plain,
% 3.97/1.00      ( r2_hidden(X0,sK3(X1,X0)) | ~ r2_hidden(X0,k3_tarski(X1)) ),
% 3.97/1.00      inference(cnf_transformation,[],[f118]) ).
% 3.97/1.00  
% 3.97/1.00  cnf(c_1366,plain,
% 3.97/1.00      ( r2_hidden(X0,sK3(X1,X0)) = iProver_top
% 3.97/1.00      | r2_hidden(X0,k3_tarski(X1)) != iProver_top ),
% 3.97/1.00      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 3.97/1.00  
% 3.97/1.00  cnf(c_35,negated_conjecture,
% 3.97/1.00      ( ~ r2_hidden(X0,sK6)
% 3.97/1.00      | r2_hidden(k2_xboole_0(X0,k1_tarski(X0)),sK6)
% 3.97/1.00      | v4_ordinal1(sK6)
% 3.97/1.00      | ~ v3_ordinal1(X0) ),
% 3.97/1.00      inference(cnf_transformation,[],[f113]) ).
% 3.97/1.00  
% 3.97/1.00  cnf(c_1343,plain,
% 3.97/1.00      ( r2_hidden(X0,sK6) != iProver_top
% 3.97/1.00      | r2_hidden(k2_xboole_0(X0,k1_tarski(X0)),sK6) = iProver_top
% 3.97/1.00      | v4_ordinal1(sK6) = iProver_top
% 3.97/1.00      | v3_ordinal1(X0) != iProver_top ),
% 3.97/1.00      inference(predicate_to_equality,[status(thm)],[c_35]) ).
% 3.97/1.00  
% 3.97/1.00  cnf(c_2,plain,
% 3.97/1.00      ( ~ r2_hidden(X0,X1) | r2_hidden(X0,X2) | ~ r1_tarski(X1,X2) ),
% 3.97/1.00      inference(cnf_transformation,[],[f68]) ).
% 3.97/1.00  
% 3.97/1.00  cnf(c_1374,plain,
% 3.97/1.00      ( r2_hidden(X0,X1) != iProver_top
% 3.97/1.00      | r2_hidden(X0,X2) = iProver_top
% 3.97/1.00      | r1_tarski(X1,X2) != iProver_top ),
% 3.97/1.00      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 3.97/1.00  
% 3.97/1.00  cnf(c_3810,plain,
% 3.97/1.00      ( r2_hidden(X0,sK6) != iProver_top
% 3.97/1.00      | r2_hidden(k2_xboole_0(X0,k1_tarski(X0)),X1) = iProver_top
% 3.97/1.00      | r1_tarski(sK6,X1) != iProver_top
% 3.97/1.00      | v4_ordinal1(sK6) = iProver_top
% 3.97/1.00      | v3_ordinal1(X0) != iProver_top ),
% 3.97/1.00      inference(superposition,[status(thm)],[c_1343,c_1374]) ).
% 3.97/1.00  
% 3.97/1.00  cnf(c_10,plain,
% 3.97/1.00      ( ~ r2_hidden(X0,k3_tarski(X1)) | r2_hidden(sK3(X1,X0),X1) ),
% 3.97/1.00      inference(cnf_transformation,[],[f117]) ).
% 3.97/1.00  
% 3.97/1.00  cnf(c_1367,plain,
% 3.97/1.00      ( r2_hidden(X0,k3_tarski(X1)) != iProver_top
% 3.97/1.00      | r2_hidden(sK3(X1,X0),X1) = iProver_top ),
% 3.97/1.00      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 3.97/1.00  
% 3.97/1.00  cnf(c_33,negated_conjecture,
% 3.97/1.00      ( r2_hidden(sK7,sK6) | ~ v4_ordinal1(sK6) ),
% 3.97/1.00      inference(cnf_transformation,[],[f104]) ).
% 3.97/1.00  
% 3.97/1.00  cnf(c_1345,plain,
% 3.97/1.00      ( r2_hidden(sK7,sK6) = iProver_top
% 3.97/1.00      | v4_ordinal1(sK6) != iProver_top ),
% 3.97/1.00      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 3.97/1.00  
% 3.97/1.00  cnf(c_9,plain,
% 3.97/1.00      ( ~ r2_hidden(X0,X1)
% 3.97/1.00      | ~ r2_hidden(X2,X0)
% 3.97/1.00      | r2_hidden(X2,k3_tarski(X1)) ),
% 3.97/1.00      inference(cnf_transformation,[],[f116]) ).
% 3.97/1.00  
% 3.97/1.00  cnf(c_1368,plain,
% 3.97/1.00      ( r2_hidden(X0,X1) != iProver_top
% 3.97/1.00      | r2_hidden(X2,X0) != iProver_top
% 3.97/1.00      | r2_hidden(X2,k3_tarski(X1)) = iProver_top ),
% 3.97/1.00      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 3.97/1.00  
% 3.97/1.00  cnf(c_3871,plain,
% 3.97/1.00      ( r2_hidden(X0,k3_tarski(sK6)) = iProver_top
% 3.97/1.00      | r2_hidden(X0,sK7) != iProver_top
% 3.97/1.00      | v4_ordinal1(sK6) != iProver_top ),
% 3.97/1.00      inference(superposition,[status(thm)],[c_1345,c_1368]) ).
% 3.97/1.00  
% 3.97/1.00  cnf(c_20,plain,
% 3.97/1.00      ( ~ r2_hidden(X0,X1) | ~ v3_ordinal1(X1) | v3_ordinal1(X0) ),
% 3.97/1.00      inference(cnf_transformation,[],[f89]) ).
% 3.97/1.00  
% 3.97/1.00  cnf(c_1357,plain,
% 3.97/1.00      ( r2_hidden(X0,X1) != iProver_top
% 3.97/1.00      | v3_ordinal1(X1) != iProver_top
% 3.97/1.00      | v3_ordinal1(X0) = iProver_top ),
% 3.97/1.00      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 3.97/1.00  
% 3.97/1.00  cnf(c_4371,plain,
% 3.97/1.00      ( r2_hidden(X0,sK7) != iProver_top
% 3.97/1.00      | v4_ordinal1(sK6) != iProver_top
% 3.97/1.00      | v3_ordinal1(X0) = iProver_top
% 3.97/1.00      | v3_ordinal1(k3_tarski(sK6)) != iProver_top ),
% 3.97/1.00      inference(superposition,[status(thm)],[c_3871,c_1357]) ).
% 3.97/1.00  
% 3.97/1.00  cnf(c_36,negated_conjecture,
% 3.97/1.00      ( v3_ordinal1(sK6) ),
% 3.97/1.00      inference(cnf_transformation,[],[f101]) ).
% 3.97/1.00  
% 3.97/1.00  cnf(c_37,plain,
% 3.97/1.00      ( v3_ordinal1(sK6) = iProver_top ),
% 3.97/1.00      inference(predicate_to_equality,[status(thm)],[c_36]) ).
% 3.97/1.00  
% 3.97/1.00  cnf(c_28,plain,
% 3.97/1.00      ( r2_hidden(sK4(X0),X0) | v3_ordinal1(k3_tarski(X0)) ),
% 3.97/1.00      inference(cnf_transformation,[],[f96]) ).
% 3.97/1.00  
% 3.97/1.00  cnf(c_2418,plain,
% 3.97/1.00      ( ~ v3_ordinal1(X0)
% 3.97/1.00      | v3_ordinal1(sK4(X0))
% 3.97/1.00      | v3_ordinal1(k3_tarski(X0)) ),
% 3.97/1.00      inference(resolution,[status(thm)],[c_20,c_28]) ).
% 3.97/1.00  
% 3.97/1.00  cnf(c_27,plain,
% 3.97/1.00      ( ~ v3_ordinal1(sK4(X0)) | v3_ordinal1(k3_tarski(X0)) ),
% 3.97/1.00      inference(cnf_transformation,[],[f97]) ).
% 3.97/1.00  
% 3.97/1.00  cnf(c_2431,plain,
% 3.97/1.00      ( ~ v3_ordinal1(X0) | v3_ordinal1(k3_tarski(X0)) ),
% 3.97/1.00      inference(global_propositional_subsumption,
% 3.97/1.00                [status(thm)],
% 3.97/1.00                [c_2418,c_27]) ).
% 3.97/1.00  
% 3.97/1.00  cnf(c_2433,plain,
% 3.97/1.00      ( v3_ordinal1(X0) != iProver_top
% 3.97/1.00      | v3_ordinal1(k3_tarski(X0)) = iProver_top ),
% 3.97/1.00      inference(predicate_to_equality,[status(thm)],[c_2431]) ).
% 3.97/1.00  
% 3.97/1.00  cnf(c_2435,plain,
% 3.97/1.00      ( v3_ordinal1(k3_tarski(sK6)) = iProver_top
% 3.97/1.00      | v3_ordinal1(sK6) != iProver_top ),
% 3.97/1.00      inference(instantiation,[status(thm)],[c_2433]) ).
% 3.97/1.00  
% 3.97/1.00  cnf(c_5943,plain,
% 3.97/1.00      ( v3_ordinal1(X0) = iProver_top
% 3.97/1.00      | v4_ordinal1(sK6) != iProver_top
% 3.97/1.00      | r2_hidden(X0,sK7) != iProver_top ),
% 3.97/1.00      inference(global_propositional_subsumption,
% 3.97/1.00                [status(thm)],
% 3.97/1.00                [c_4371,c_37,c_2435]) ).
% 3.97/1.00  
% 3.97/1.00  cnf(c_5944,plain,
% 3.97/1.00      ( r2_hidden(X0,sK7) != iProver_top
% 3.97/1.00      | v4_ordinal1(sK6) != iProver_top
% 3.97/1.00      | v3_ordinal1(X0) = iProver_top ),
% 3.97/1.00      inference(renaming,[status(thm)],[c_5943]) ).
% 3.97/1.00  
% 3.97/1.00  cnf(c_5953,plain,
% 3.97/1.00      ( r2_hidden(X0,k3_tarski(sK7)) != iProver_top
% 3.97/1.00      | v4_ordinal1(sK6) != iProver_top
% 3.97/1.00      | v3_ordinal1(sK3(sK7,X0)) = iProver_top ),
% 3.97/1.00      inference(superposition,[status(thm)],[c_1367,c_5944]) ).
% 3.97/1.00  
% 3.97/1.00  cnf(c_16,plain,
% 3.97/1.00      ( ~ v4_ordinal1(X0) | k3_tarski(X0) = X0 ),
% 3.97/1.00      inference(cnf_transformation,[],[f84]) ).
% 3.97/1.00  
% 3.97/1.00  cnf(c_88,plain,
% 3.97/1.00      ( ~ v4_ordinal1(sK6) | k3_tarski(sK6) = sK6 ),
% 3.97/1.00      inference(instantiation,[status(thm)],[c_16]) ).
% 3.97/1.00  
% 3.97/1.00  cnf(c_15,plain,
% 3.97/1.00      ( v4_ordinal1(X0) | k3_tarski(X0) != X0 ),
% 3.97/1.00      inference(cnf_transformation,[],[f85]) ).
% 3.97/1.00  
% 3.97/1.00  cnf(c_90,plain,
% 3.97/1.00      ( k3_tarski(X0) != X0 | v4_ordinal1(X0) = iProver_top ),
% 3.97/1.00      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 3.97/1.00  
% 3.97/1.00  cnf(c_92,plain,
% 3.97/1.00      ( k3_tarski(sK6) != sK6 | v4_ordinal1(sK6) = iProver_top ),
% 3.97/1.00      inference(instantiation,[status(thm)],[c_90]) ).
% 3.97/1.00  
% 3.97/1.00  cnf(c_19,plain,
% 3.97/1.00      ( r2_hidden(X0,k2_xboole_0(X0,k1_tarski(X0))) ),
% 3.97/1.00      inference(cnf_transformation,[],[f106]) ).
% 3.97/1.00  
% 3.97/1.00  cnf(c_3675,plain,
% 3.97/1.00      ( r2_hidden(X0,k3_tarski(X1))
% 3.97/1.00      | ~ r2_hidden(k2_xboole_0(X0,k1_tarski(X0)),X1) ),
% 3.97/1.00      inference(resolution,[status(thm)],[c_9,c_19]) ).
% 3.97/1.00  
% 3.97/1.00  cnf(c_12635,plain,
% 3.97/1.00      ( r2_hidden(X0,k3_tarski(sK6))
% 3.97/1.00      | ~ r2_hidden(X0,sK6)
% 3.97/1.00      | v4_ordinal1(sK6)
% 3.97/1.00      | ~ v3_ordinal1(X0) ),
% 3.97/1.00      inference(resolution,[status(thm)],[c_3675,c_35]) ).
% 3.97/1.00  
% 3.97/1.00  cnf(c_14,plain,
% 3.97/1.00      ( ~ r2_hidden(X0,X1) | r1_tarski(X0,X1) | ~ v1_ordinal1(X1) ),
% 3.97/1.00      inference(cnf_transformation,[],[f83]) ).
% 3.97/1.00  
% 3.97/1.00  cnf(c_12663,plain,
% 3.97/1.00      ( ~ r2_hidden(X0,sK6)
% 3.97/1.00      | r1_tarski(X0,k3_tarski(sK6))
% 3.97/1.00      | v4_ordinal1(sK6)
% 3.97/1.00      | ~ v3_ordinal1(X0)
% 3.97/1.00      | ~ v1_ordinal1(k3_tarski(sK6)) ),
% 3.97/1.00      inference(resolution,[status(thm)],[c_12635,c_14]) ).
% 3.97/1.00  
% 3.97/1.00  cnf(c_12,plain,
% 3.97/1.00      ( ~ v3_ordinal1(X0) | v1_ordinal1(X0) ),
% 3.97/1.00      inference(cnf_transformation,[],[f80]) ).
% 3.97/1.00  
% 3.97/1.00  cnf(c_100,plain,
% 3.97/1.00      ( ~ v3_ordinal1(sK6) | v1_ordinal1(sK6) ),
% 3.97/1.00      inference(instantiation,[status(thm)],[c_12]) ).
% 3.97/1.00  
% 3.97/1.00  cnf(c_2434,plain,
% 3.97/1.00      ( v3_ordinal1(k3_tarski(sK6)) | ~ v3_ordinal1(sK6) ),
% 3.97/1.00      inference(instantiation,[status(thm)],[c_2431]) ).
% 3.97/1.00  
% 3.97/1.00  cnf(c_31,plain,
% 3.97/1.00      ( ~ r2_hidden(X0,X1) | ~ r1_tarski(X1,X0) ),
% 3.97/1.00      inference(cnf_transformation,[],[f100]) ).
% 3.97/1.00  
% 3.97/1.00  cnf(c_2725,plain,
% 3.97/1.00      ( ~ r2_hidden(X0,k3_tarski(X1)) | ~ r1_tarski(sK3(X1,X0),X0) ),
% 3.97/1.00      inference(resolution,[status(thm)],[c_11,c_31]) ).
% 3.97/1.00  
% 3.97/1.00  cnf(c_2729,plain,
% 3.97/1.00      ( ~ r2_hidden(sK6,k3_tarski(sK6)) | ~ r1_tarski(sK3(sK6,sK6),sK6) ),
% 3.97/1.00      inference(instantiation,[status(thm)],[c_2725]) ).
% 3.97/1.00  
% 3.97/1.00  cnf(c_2741,plain,
% 3.97/1.00      ( ~ r2_hidden(X0,k3_tarski(X1))
% 3.97/1.00      | r1_tarski(sK3(X1,X0),X1)
% 3.97/1.00      | ~ v1_ordinal1(X1) ),
% 3.97/1.00      inference(resolution,[status(thm)],[c_14,c_10]) ).
% 3.97/1.00  
% 3.97/1.00  cnf(c_2743,plain,
% 3.97/1.00      ( ~ r2_hidden(sK6,k3_tarski(sK6))
% 3.97/1.00      | r1_tarski(sK3(sK6,sK6),sK6)
% 3.97/1.00      | ~ v1_ordinal1(sK6) ),
% 3.97/1.00      inference(instantiation,[status(thm)],[c_2741]) ).
% 3.97/1.00  
% 3.97/1.00  cnf(c_21,plain,
% 3.97/1.00      ( r2_hidden(X0,X1)
% 3.97/1.00      | r2_hidden(X1,X0)
% 3.97/1.00      | ~ v3_ordinal1(X0)
% 3.97/1.00      | ~ v3_ordinal1(X1)
% 3.97/1.00      | X1 = X0 ),
% 3.97/1.00      inference(cnf_transformation,[],[f90]) ).
% 3.97/1.00  
% 3.97/1.00  cnf(c_5727,plain,
% 3.97/1.00      ( r2_hidden(X0,k3_tarski(X0))
% 3.97/1.00      | r2_hidden(k3_tarski(X0),X0)
% 3.97/1.00      | v4_ordinal1(X0)
% 3.97/1.00      | ~ v3_ordinal1(X0)
% 3.97/1.00      | ~ v3_ordinal1(k3_tarski(X0)) ),
% 3.97/1.00      inference(resolution,[status(thm)],[c_21,c_15]) ).
% 3.97/1.00  
% 3.97/1.00  cnf(c_5729,plain,
% 3.97/1.00      ( r2_hidden(k3_tarski(sK6),sK6)
% 3.97/1.00      | r2_hidden(sK6,k3_tarski(sK6))
% 3.97/1.00      | v4_ordinal1(sK6)
% 3.97/1.00      | ~ v3_ordinal1(k3_tarski(sK6))
% 3.97/1.00      | ~ v3_ordinal1(sK6) ),
% 3.97/1.00      inference(instantiation,[status(thm)],[c_5727]) ).
% 3.97/1.00  
% 3.97/1.00  cnf(c_12661,plain,
% 3.97/1.00      ( ~ r2_hidden(X0,sK6)
% 3.97/1.00      | ~ r1_tarski(k3_tarski(sK6),X0)
% 3.97/1.00      | v4_ordinal1(sK6)
% 3.97/1.00      | ~ v3_ordinal1(X0) ),
% 3.97/1.00      inference(resolution,[status(thm)],[c_12635,c_31]) ).
% 3.97/1.00  
% 3.97/1.00  cnf(c_5,plain,
% 3.97/1.00      ( r1_tarski(X0,X0) ),
% 3.97/1.00      inference(cnf_transformation,[],[f115]) ).
% 3.97/1.00  
% 3.97/1.00  cnf(c_13023,plain,
% 3.97/1.00      ( ~ r2_hidden(k3_tarski(sK6),sK6)
% 3.97/1.00      | v4_ordinal1(sK6)
% 3.97/1.00      | ~ v3_ordinal1(k3_tarski(sK6)) ),
% 3.97/1.00      inference(resolution,[status(thm)],[c_12661,c_5]) ).
% 3.97/1.00  
% 3.97/1.00  cnf(c_13026,plain,
% 3.97/1.00      ( v4_ordinal1(sK6) ),
% 3.97/1.00      inference(global_propositional_subsumption,
% 3.97/1.00                [status(thm)],
% 3.97/1.00                [c_12663,c_36,c_100,c_2434,c_2729,c_2743,c_5729,c_13023]) ).
% 3.97/1.00  
% 3.97/1.00  cnf(c_15691,plain,
% 3.97/1.00      ( r2_hidden(X0,k3_tarski(sK7)) != iProver_top
% 3.97/1.00      | v3_ordinal1(sK3(sK7,X0)) = iProver_top ),
% 3.97/1.00      inference(global_propositional_subsumption,
% 3.97/1.00                [status(thm)],
% 3.97/1.00                [c_5953,c_36,c_88,c_92,c_100,c_2434,c_2729,c_2743,c_5729,
% 3.97/1.00                 c_13023]) ).
% 3.97/1.00  
% 3.97/1.00  cnf(c_15707,plain,
% 3.97/1.00      ( r2_hidden(X0,sK6) != iProver_top
% 3.97/1.00      | r1_tarski(sK6,k3_tarski(sK7)) != iProver_top
% 3.97/1.00      | v4_ordinal1(sK6) = iProver_top
% 3.97/1.00      | v3_ordinal1(X0) != iProver_top
% 3.97/1.00      | v3_ordinal1(sK3(sK7,k2_xboole_0(X0,k1_tarski(X0)))) = iProver_top ),
% 3.97/1.00      inference(superposition,[status(thm)],[c_3810,c_15691]) ).
% 3.97/1.00  
% 3.97/1.00  cnf(c_15813,plain,
% 3.97/1.00      ( v4_ordinal1(sK6) = iProver_top ),
% 3.97/1.00      inference(global_propositional_subsumption,
% 3.97/1.00                [status(thm)],
% 3.97/1.00                [c_15707,c_36,c_88,c_92,c_100,c_2434,c_2729,c_2743,
% 3.97/1.00                 c_5729,c_13023]) ).
% 3.97/1.00  
% 3.97/1.00  cnf(c_1356,plain,
% 3.97/1.00      ( X0 = X1
% 3.97/1.00      | r2_hidden(X1,X0) = iProver_top
% 3.97/1.00      | r2_hidden(X0,X1) = iProver_top
% 3.97/1.00      | v3_ordinal1(X1) != iProver_top
% 3.97/1.00      | v3_ordinal1(X0) != iProver_top ),
% 3.97/1.00      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 3.97/1.00  
% 3.97/1.00  cnf(c_32,negated_conjecture,
% 3.97/1.00      ( ~ r2_hidden(k2_xboole_0(sK7,k1_tarski(sK7)),sK6)
% 3.97/1.00      | ~ v4_ordinal1(sK6) ),
% 3.97/1.00      inference(cnf_transformation,[],[f112]) ).
% 3.97/1.00  
% 3.97/1.00  cnf(c_1346,plain,
% 3.97/1.00      ( r2_hidden(k2_xboole_0(sK7,k1_tarski(sK7)),sK6) != iProver_top
% 3.97/1.00      | v4_ordinal1(sK6) != iProver_top ),
% 3.97/1.00      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 3.97/1.00  
% 3.97/1.00  cnf(c_7115,plain,
% 3.97/1.00      ( k2_xboole_0(sK7,k1_tarski(sK7)) = sK6
% 3.97/1.00      | r2_hidden(sK6,k2_xboole_0(sK7,k1_tarski(sK7))) = iProver_top
% 3.97/1.00      | v4_ordinal1(sK6) != iProver_top
% 3.97/1.00      | v3_ordinal1(k2_xboole_0(sK7,k1_tarski(sK7))) != iProver_top
% 3.97/1.00      | v3_ordinal1(sK6) != iProver_top ),
% 3.97/1.00      inference(superposition,[status(thm)],[c_1356,c_1346]) ).
% 3.97/1.00  
% 3.97/1.00  cnf(c_34,negated_conjecture,
% 3.97/1.00      ( ~ v4_ordinal1(sK6) | v3_ordinal1(sK7) ),
% 3.97/1.00      inference(cnf_transformation,[],[f103]) ).
% 3.97/1.00  
% 3.97/1.00  cnf(c_41,plain,
% 3.97/1.00      ( v4_ordinal1(sK6) != iProver_top
% 3.97/1.00      | v3_ordinal1(sK7) = iProver_top ),
% 3.97/1.00      inference(predicate_to_equality,[status(thm)],[c_34]) ).
% 3.97/1.00  
% 3.97/1.00  cnf(c_1347,plain,
% 3.97/1.00      ( r2_hidden(X0,X1) != iProver_top
% 3.97/1.00      | r1_tarski(X1,X0) != iProver_top ),
% 3.97/1.00      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 3.97/1.00  
% 3.97/1.00  cnf(c_2384,plain,
% 3.97/1.00      ( r1_tarski(sK6,sK7) != iProver_top
% 3.97/1.00      | v4_ordinal1(sK6) != iProver_top ),
% 3.97/1.00      inference(superposition,[status(thm)],[c_1345,c_1347]) ).
% 3.97/1.00  
% 3.97/1.00  cnf(c_18,plain,
% 3.97/1.00      ( ~ r1_ordinal1(X0,X1)
% 3.97/1.00      | r1_tarski(X0,X1)
% 3.97/1.00      | ~ v3_ordinal1(X0)
% 3.97/1.00      | ~ v3_ordinal1(X1) ),
% 3.97/1.00      inference(cnf_transformation,[],[f86]) ).
% 3.97/1.00  
% 3.97/1.00  cnf(c_2997,plain,
% 3.97/1.00      ( ~ r1_ordinal1(sK6,sK7)
% 3.97/1.00      | r1_tarski(sK6,sK7)
% 3.97/1.00      | ~ v3_ordinal1(sK6)
% 3.97/1.00      | ~ v3_ordinal1(sK7) ),
% 3.97/1.00      inference(instantiation,[status(thm)],[c_18]) ).
% 3.97/1.00  
% 3.97/1.00  cnf(c_3007,plain,
% 3.97/1.00      ( r1_ordinal1(sK6,sK7) != iProver_top
% 3.97/1.00      | r1_tarski(sK6,sK7) = iProver_top
% 3.97/1.00      | v3_ordinal1(sK6) != iProver_top
% 3.97/1.00      | v3_ordinal1(sK7) != iProver_top ),
% 3.97/1.00      inference(predicate_to_equality,[status(thm)],[c_2997]) ).
% 3.97/1.00  
% 3.97/1.00  cnf(c_22,plain,
% 3.97/1.00      ( ~ v3_ordinal1(X0) | v3_ordinal1(k2_xboole_0(X0,k1_tarski(X0))) ),
% 3.97/1.00      inference(cnf_transformation,[],[f107]) ).
% 3.97/1.00  
% 3.97/1.00  cnf(c_5757,plain,
% 3.97/1.00      ( v3_ordinal1(k2_xboole_0(sK7,k1_tarski(sK7)))
% 3.97/1.00      | ~ v3_ordinal1(sK7) ),
% 3.97/1.00      inference(instantiation,[status(thm)],[c_22]) ).
% 3.97/1.00  
% 3.97/1.00  cnf(c_5758,plain,
% 3.97/1.00      ( v3_ordinal1(k2_xboole_0(sK7,k1_tarski(sK7))) = iProver_top
% 3.97/1.00      | v3_ordinal1(sK7) != iProver_top ),
% 3.97/1.00      inference(predicate_to_equality,[status(thm)],[c_5757]) ).
% 3.97/1.00  
% 3.97/1.00  cnf(c_26,plain,
% 3.97/1.00      ( r1_ordinal1(X0,X1)
% 3.97/1.00      | ~ r2_hidden(X0,k2_xboole_0(X1,k1_tarski(X1)))
% 3.97/1.00      | ~ v3_ordinal1(X0)
% 3.97/1.00      | ~ v3_ordinal1(X1) ),
% 3.97/1.00      inference(cnf_transformation,[],[f111]) ).
% 3.97/1.00  
% 3.97/1.00  cnf(c_5899,plain,
% 3.97/1.00      ( r1_ordinal1(sK6,sK7)
% 3.97/1.00      | ~ r2_hidden(sK6,k2_xboole_0(sK7,k1_tarski(sK7)))
% 3.97/1.00      | ~ v3_ordinal1(sK6)
% 3.97/1.00      | ~ v3_ordinal1(sK7) ),
% 3.97/1.00      inference(instantiation,[status(thm)],[c_26]) ).
% 3.97/1.00  
% 3.97/1.00  cnf(c_5903,plain,
% 3.97/1.00      ( r1_ordinal1(sK6,sK7) = iProver_top
% 3.97/1.00      | r2_hidden(sK6,k2_xboole_0(sK7,k1_tarski(sK7))) != iProver_top
% 3.97/1.00      | v3_ordinal1(sK6) != iProver_top
% 3.97/1.00      | v3_ordinal1(sK7) != iProver_top ),
% 3.97/1.00      inference(predicate_to_equality,[status(thm)],[c_5899]) ).
% 3.97/1.00  
% 3.97/1.00  cnf(c_7526,plain,
% 3.97/1.00      ( k2_xboole_0(sK7,k1_tarski(sK7)) = sK6
% 3.97/1.00      | v4_ordinal1(sK6) != iProver_top ),
% 3.97/1.00      inference(global_propositional_subsumption,
% 3.97/1.00                [status(thm)],
% 3.97/1.00                [c_7115,c_37,c_41,c_2384,c_3007,c_5758,c_5903]) ).
% 3.97/1.00  
% 3.97/1.00  cnf(c_15819,plain,
% 3.97/1.00      ( k2_xboole_0(sK7,k1_tarski(sK7)) = sK6 ),
% 3.97/1.00      inference(superposition,[status(thm)],[c_15813,c_7526]) ).
% 3.97/1.00  
% 3.97/1.00  cnf(c_24,plain,
% 3.97/1.00      ( r1_ordinal1(k2_xboole_0(X0,k1_tarski(X0)),X1)
% 3.97/1.00      | ~ r2_hidden(X0,X1)
% 3.97/1.00      | ~ v3_ordinal1(X0)
% 3.97/1.00      | ~ v3_ordinal1(X1) ),
% 3.97/1.00      inference(cnf_transformation,[],[f109]) ).
% 3.97/1.00  
% 3.97/1.00  cnf(c_378,plain,
% 3.97/1.00      ( ~ r2_hidden(X0,X1)
% 3.97/1.00      | r1_ordinal1(k2_xboole_0(X0,k1_tarski(X0)),X1)
% 3.97/1.00      | ~ v3_ordinal1(X1) ),
% 3.97/1.00      inference(global_propositional_subsumption,
% 3.97/1.00                [status(thm)],
% 3.97/1.00                [c_24,c_20]) ).
% 3.97/1.00  
% 3.97/1.00  cnf(c_379,plain,
% 3.97/1.00      ( r1_ordinal1(k2_xboole_0(X0,k1_tarski(X0)),X1)
% 3.97/1.00      | ~ r2_hidden(X0,X1)
% 3.97/1.00      | ~ v3_ordinal1(X1) ),
% 3.97/1.00      inference(renaming,[status(thm)],[c_378]) ).
% 3.97/1.00  
% 3.97/1.00  cnf(c_1341,plain,
% 3.97/1.00      ( r1_ordinal1(k2_xboole_0(X0,k1_tarski(X0)),X1) = iProver_top
% 3.97/1.00      | r2_hidden(X0,X1) != iProver_top
% 3.97/1.00      | v3_ordinal1(X1) != iProver_top ),
% 3.97/1.00      inference(predicate_to_equality,[status(thm)],[c_379]) ).
% 3.97/1.00  
% 3.97/1.00  cnf(c_16082,plain,
% 3.97/1.00      ( r1_ordinal1(sK6,X0) = iProver_top
% 3.97/1.00      | r2_hidden(sK7,X0) != iProver_top
% 3.97/1.00      | v3_ordinal1(X0) != iProver_top ),
% 3.97/1.00      inference(superposition,[status(thm)],[c_15819,c_1341]) ).
% 3.97/1.00  
% 3.97/1.00  cnf(c_17107,plain,
% 3.97/1.00      ( r1_ordinal1(sK6,sK3(X0,sK7)) = iProver_top
% 3.97/1.00      | r2_hidden(sK7,k3_tarski(X0)) != iProver_top
% 3.97/1.00      | v3_ordinal1(sK3(X0,sK7)) != iProver_top ),
% 3.97/1.00      inference(superposition,[status(thm)],[c_1366,c_16082]) ).
% 3.97/1.00  
% 3.97/1.00  cnf(c_17165,plain,
% 3.97/1.00      ( r1_ordinal1(sK6,sK3(sK6,sK7)) = iProver_top
% 3.97/1.00      | r2_hidden(sK7,k3_tarski(sK6)) != iProver_top
% 3.97/1.00      | v3_ordinal1(sK3(sK6,sK7)) != iProver_top ),
% 3.97/1.00      inference(instantiation,[status(thm)],[c_17107]) ).
% 3.97/1.00  
% 3.97/1.00  cnf(c_12205,plain,
% 3.97/1.00      ( ~ r1_ordinal1(sK6,sK3(X0,sK7))
% 3.97/1.00      | r1_tarski(sK6,sK3(X0,sK7))
% 3.97/1.00      | ~ v3_ordinal1(sK3(X0,sK7))
% 3.97/1.00      | ~ v3_ordinal1(sK6) ),
% 3.97/1.00      inference(instantiation,[status(thm)],[c_18]) ).
% 3.97/1.00  
% 3.97/1.00  cnf(c_12221,plain,
% 3.97/1.00      ( r1_ordinal1(sK6,sK3(X0,sK7)) != iProver_top
% 3.97/1.00      | r1_tarski(sK6,sK3(X0,sK7)) = iProver_top
% 3.97/1.00      | v3_ordinal1(sK3(X0,sK7)) != iProver_top
% 3.97/1.00      | v3_ordinal1(sK6) != iProver_top ),
% 3.97/1.00      inference(predicate_to_equality,[status(thm)],[c_12205]) ).
% 3.97/1.00  
% 3.97/1.00  cnf(c_12223,plain,
% 3.97/1.00      ( r1_ordinal1(sK6,sK3(sK6,sK7)) != iProver_top
% 3.97/1.00      | r1_tarski(sK6,sK3(sK6,sK7)) = iProver_top
% 3.97/1.00      | v3_ordinal1(sK3(sK6,sK7)) != iProver_top
% 3.97/1.00      | v3_ordinal1(sK6) != iProver_top ),
% 3.97/1.00      inference(instantiation,[status(thm)],[c_12221]) ).
% 3.97/1.00  
% 3.97/1.00  cnf(c_2258,plain,
% 3.97/1.00      ( ~ r2_hidden(sK3(X0,X1),X0) | ~ r1_tarski(X0,sK3(X0,X1)) ),
% 3.97/1.00      inference(instantiation,[status(thm)],[c_31]) ).
% 3.97/1.00  
% 3.97/1.00  cnf(c_12166,plain,
% 3.97/1.00      ( ~ r2_hidden(sK3(sK6,sK7),sK6) | ~ r1_tarski(sK6,sK3(sK6,sK7)) ),
% 3.97/1.00      inference(instantiation,[status(thm)],[c_2258]) ).
% 3.97/1.00  
% 3.97/1.00  cnf(c_12167,plain,
% 3.97/1.00      ( r2_hidden(sK3(sK6,sK7),sK6) != iProver_top
% 3.97/1.00      | r1_tarski(sK6,sK3(sK6,sK7)) != iProver_top ),
% 3.97/1.00      inference(predicate_to_equality,[status(thm)],[c_12166]) ).
% 3.97/1.00  
% 3.97/1.00  cnf(c_1363,plain,
% 3.97/1.00      ( r2_hidden(X0,X1) != iProver_top
% 3.97/1.00      | r1_tarski(X0,X1) = iProver_top
% 3.97/1.00      | v1_ordinal1(X1) != iProver_top ),
% 3.97/1.00      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 3.97/1.00  
% 3.97/1.00  cnf(c_4370,plain,
% 3.97/1.00      ( r2_hidden(X0,sK7) != iProver_top
% 3.97/1.00      | r1_tarski(X0,k3_tarski(sK6)) = iProver_top
% 3.97/1.00      | v4_ordinal1(sK6) != iProver_top
% 3.97/1.00      | v1_ordinal1(k3_tarski(sK6)) != iProver_top ),
% 3.97/1.00      inference(superposition,[status(thm)],[c_3871,c_1363]) ).
% 3.97/1.00  
% 3.97/1.00  cnf(c_2530,plain,
% 3.97/1.00      ( ~ v3_ordinal1(X0) | v1_ordinal1(k3_tarski(X0)) ),
% 3.97/1.00      inference(resolution,[status(thm)],[c_2431,c_12]) ).
% 3.97/1.00  
% 3.97/1.00  cnf(c_2531,plain,
% 3.97/1.00      ( v3_ordinal1(X0) != iProver_top
% 3.97/1.00      | v1_ordinal1(k3_tarski(X0)) = iProver_top ),
% 3.97/1.00      inference(predicate_to_equality,[status(thm)],[c_2530]) ).
% 3.97/1.00  
% 3.97/1.00  cnf(c_2533,plain,
% 3.97/1.00      ( v3_ordinal1(sK6) != iProver_top
% 3.97/1.00      | v1_ordinal1(k3_tarski(sK6)) = iProver_top ),
% 3.97/1.00      inference(instantiation,[status(thm)],[c_2531]) ).
% 3.97/1.00  
% 3.97/1.00  cnf(c_6231,plain,
% 3.97/1.00      ( v4_ordinal1(sK6) != iProver_top
% 3.97/1.00      | r1_tarski(X0,k3_tarski(sK6)) = iProver_top
% 3.97/1.00      | r2_hidden(X0,sK7) != iProver_top ),
% 3.97/1.00      inference(global_propositional_subsumption,
% 3.97/1.00                [status(thm)],
% 3.97/1.00                [c_4370,c_37,c_2533]) ).
% 3.97/1.00  
% 3.97/1.00  cnf(c_6232,plain,
% 3.97/1.00      ( r2_hidden(X0,sK7) != iProver_top
% 3.97/1.00      | r1_tarski(X0,k3_tarski(sK6)) = iProver_top
% 3.97/1.00      | v4_ordinal1(sK6) != iProver_top ),
% 3.97/1.00      inference(renaming,[status(thm)],[c_6231]) ).
% 3.97/1.00  
% 3.97/1.00  cnf(c_3809,plain,
% 3.97/1.00      ( r2_hidden(sK7,X0) = iProver_top
% 3.97/1.00      | r1_tarski(sK6,X0) != iProver_top
% 3.97/1.00      | v4_ordinal1(sK6) != iProver_top ),
% 3.97/1.00      inference(superposition,[status(thm)],[c_1345,c_1374]) ).
% 3.97/1.00  
% 3.97/1.00  cnf(c_6242,plain,
% 3.97/1.00      ( r2_hidden(sK6,sK7) != iProver_top
% 3.97/1.00      | r2_hidden(sK7,k3_tarski(sK6)) = iProver_top
% 3.97/1.00      | v4_ordinal1(sK6) != iProver_top ),
% 3.97/1.00      inference(superposition,[status(thm)],[c_6232,c_3809]) ).
% 3.97/1.00  
% 3.97/1.00  cnf(c_42,plain,
% 3.97/1.00      ( r2_hidden(sK7,sK6) = iProver_top
% 3.97/1.00      | v4_ordinal1(sK6) != iProver_top ),
% 3.97/1.00      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 3.97/1.00  
% 3.97/1.00  cnf(c_87,plain,
% 3.97/1.00      ( k3_tarski(X0) = X0 | v4_ordinal1(X0) != iProver_top ),
% 3.97/1.00      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 3.97/1.00  
% 3.97/1.00  cnf(c_89,plain,
% 3.97/1.00      ( k3_tarski(sK6) = sK6 | v4_ordinal1(sK6) != iProver_top ),
% 3.97/1.00      inference(instantiation,[status(thm)],[c_87]) ).
% 3.97/1.00  
% 3.97/1.00  cnf(c_630,plain,( X0 = X0 ),theory(equality) ).
% 3.97/1.00  
% 3.97/1.00  cnf(c_3121,plain,
% 3.97/1.00      ( sK7 = sK7 ),
% 3.97/1.00      inference(instantiation,[status(thm)],[c_630]) ).
% 3.97/1.00  
% 3.97/1.00  cnf(c_632,plain,
% 3.97/1.00      ( ~ r2_hidden(X0,X1) | r2_hidden(X2,X3) | X2 != X0 | X3 != X1 ),
% 3.97/1.00      theory(equality) ).
% 3.97/1.00  
% 3.97/1.00  cnf(c_1852,plain,
% 3.97/1.00      ( r2_hidden(X0,X1) | ~ r2_hidden(sK7,sK6) | X1 != sK6 | X0 != sK7 ),
% 3.97/1.00      inference(instantiation,[status(thm)],[c_632]) ).
% 3.97/1.00  
% 3.97/1.00  cnf(c_3120,plain,
% 3.97/1.00      ( r2_hidden(sK7,X0)
% 3.97/1.00      | ~ r2_hidden(sK7,sK6)
% 3.97/1.00      | X0 != sK6
% 3.97/1.00      | sK7 != sK7 ),
% 3.97/1.00      inference(instantiation,[status(thm)],[c_1852]) ).
% 3.97/1.00  
% 3.97/1.00  cnf(c_6343,plain,
% 3.97/1.00      ( r2_hidden(sK7,k3_tarski(sK6))
% 3.97/1.00      | ~ r2_hidden(sK7,sK6)
% 3.97/1.00      | k3_tarski(sK6) != sK6
% 3.97/1.00      | sK7 != sK7 ),
% 3.97/1.00      inference(instantiation,[status(thm)],[c_3120]) ).
% 3.97/1.00  
% 3.97/1.00  cnf(c_6345,plain,
% 3.97/1.00      ( k3_tarski(sK6) != sK6
% 3.97/1.00      | sK7 != sK7
% 3.97/1.00      | r2_hidden(sK7,k3_tarski(sK6)) = iProver_top
% 3.97/1.00      | r2_hidden(sK7,sK6) != iProver_top ),
% 3.97/1.00      inference(predicate_to_equality,[status(thm)],[c_6343]) ).
% 3.97/1.00  
% 3.97/1.00  cnf(c_6436,plain,
% 3.97/1.00      ( r2_hidden(sK7,k3_tarski(sK6)) = iProver_top
% 3.97/1.00      | v4_ordinal1(sK6) != iProver_top ),
% 3.97/1.00      inference(global_propositional_subsumption,
% 3.97/1.00                [status(thm)],
% 3.97/1.00                [c_6242,c_42,c_89,c_3121,c_6345]) ).
% 3.97/1.00  
% 3.97/1.00  cnf(c_3288,plain,
% 3.97/1.00      ( r2_hidden(X0,k3_tarski(X1)) != iProver_top
% 3.97/1.00      | v3_ordinal1(X1) != iProver_top
% 3.97/1.00      | v3_ordinal1(sK3(X1,X0)) = iProver_top ),
% 3.97/1.00      inference(superposition,[status(thm)],[c_1367,c_1357]) ).
% 3.97/1.00  
% 3.97/1.00  cnf(c_10851,plain,
% 3.97/1.00      ( v4_ordinal1(sK6) != iProver_top
% 3.97/1.00      | v3_ordinal1(sK3(sK6,sK7)) = iProver_top
% 3.97/1.00      | v3_ordinal1(sK6) != iProver_top ),
% 3.97/1.00      inference(superposition,[status(thm)],[c_6436,c_3288]) ).
% 3.97/1.00  
% 3.97/1.00  cnf(c_3069,plain,
% 3.97/1.00      ( r2_hidden(sK3(X0,sK7),X0) | ~ r2_hidden(sK7,k3_tarski(X0)) ),
% 3.97/1.00      inference(instantiation,[status(thm)],[c_10]) ).
% 3.97/1.00  
% 3.97/1.00  cnf(c_3074,plain,
% 3.97/1.00      ( r2_hidden(sK3(X0,sK7),X0) = iProver_top
% 3.97/1.00      | r2_hidden(sK7,k3_tarski(X0)) != iProver_top ),
% 3.97/1.00      inference(predicate_to_equality,[status(thm)],[c_3069]) ).
% 3.97/1.00  
% 3.97/1.00  cnf(c_3076,plain,
% 3.97/1.00      ( r2_hidden(sK3(sK6,sK7),sK6) = iProver_top
% 3.97/1.00      | r2_hidden(sK7,k3_tarski(sK6)) != iProver_top ),
% 3.97/1.00      inference(instantiation,[status(thm)],[c_3074]) ).
% 3.97/1.00  
% 3.97/1.00  cnf(contradiction,plain,
% 3.97/1.00      ( $false ),
% 3.97/1.00      inference(minisat,
% 3.97/1.00                [status(thm)],
% 3.97/1.00                [c_17165,c_13026,c_12223,c_12167,c_10851,c_6436,c_3076,
% 3.97/1.00                 c_92,c_88,c_37]) ).
% 3.97/1.00  
% 3.97/1.00  
% 3.97/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 3.97/1.00  
% 3.97/1.00  ------                               Statistics
% 3.97/1.00  
% 3.97/1.00  ------ Selected
% 3.97/1.00  
% 3.97/1.00  total_time:                             0.462
% 3.97/1.00  
%------------------------------------------------------------------------------
