%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:54:01 EST 2020

% Result     : Theorem 7.52s
% Output     : CNFRefutation 7.52s
% Verified   : 
% Statistics : Number of formulae       :  226 (1115 expanded)
%              Number of clauses        :  134 ( 311 expanded)
%              Number of leaves         :   24 ( 256 expanded)
%              Depth                    :   20
%              Number of atoms          :  788 (5026 expanded)
%              Number of equality atoms :  202 ( 648 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal clause size      :   18 (   3 average)
%              Maximal term depth       :    4 (   1 average)

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

fof(f43,plain,(
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

fof(f44,plain,(
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
    inference(rectify,[],[f43])).

fof(f47,plain,(
    ! [X5,X0] :
      ( ? [X7] :
          ( r2_hidden(X7,X0)
          & r2_hidden(X5,X7) )
     => ( r2_hidden(sK3(X0,X5),X0)
        & r2_hidden(X5,sK3(X0,X5)) ) ) ),
    introduced(choice_axiom,[])).

fof(f46,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( r2_hidden(X4,X0)
          & r2_hidden(X2,X4) )
     => ( r2_hidden(sK2(X0,X1),X0)
        & r2_hidden(X2,sK2(X0,X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f45,plain,(
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

fof(f48,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f44,f47,f46,f45])).

fof(f71,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(X5,sK3(X0,X5))
      | ~ r2_hidden(X5,X1)
      | k3_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f48])).

fof(f119,plain,(
    ! [X0,X5] :
      ( r2_hidden(X5,sK3(X0,X5))
      | ~ r2_hidden(X5,k3_tarski(X0)) ) ),
    inference(equality_resolution,[],[f71])).

fof(f15,axiom,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(X1,X0)
         => v3_ordinal1(X1) )
     => v3_ordinal1(k3_tarski(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0] :
      ( v3_ordinal1(k3_tarski(X0))
      | ? [X1] :
          ( ~ v3_ordinal1(X1)
          & r2_hidden(X1,X0) ) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f55,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ v3_ordinal1(X1)
          & r2_hidden(X1,X0) )
     => ( ~ v3_ordinal1(sK4(X0))
        & r2_hidden(sK4(X0),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f56,plain,(
    ! [X0] :
      ( v3_ordinal1(k3_tarski(X0))
      | ( ~ v3_ordinal1(sK4(X0))
        & r2_hidden(sK4(X0),X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f32,f55])).

fof(f94,plain,(
    ! [X0] :
      ( v3_ordinal1(k3_tarski(X0))
      | r2_hidden(sK4(X0),X0) ) ),
    inference(cnf_transformation,[],[f56])).

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

fof(f37,plain,(
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

fof(f38,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f37])).

fof(f39,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK0(X0,X1),X1)
          & r2_hidden(sK0(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f38,f39])).

fof(f65,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f40])).

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

fof(f35,plain,(
    ? [X0] :
      ( ( v4_ordinal1(X0)
      <~> ! [X1] :
            ( r2_hidden(k1_ordinal1(X1),X0)
            | ~ r2_hidden(X1,X0)
            | ~ v3_ordinal1(X1) ) )
      & v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f36,plain,(
    ? [X0] :
      ( ( v4_ordinal1(X0)
      <~> ! [X1] :
            ( r2_hidden(k1_ordinal1(X1),X0)
            | ~ r2_hidden(X1,X0)
            | ~ v3_ordinal1(X1) ) )
      & v3_ordinal1(X0) ) ),
    inference(flattening,[],[f35])).

fof(f59,plain,(
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
    inference(nnf_transformation,[],[f36])).

fof(f60,plain,(
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
    inference(flattening,[],[f59])).

fof(f61,plain,(
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
    inference(rectify,[],[f60])).

fof(f63,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ r2_hidden(k1_ordinal1(X1),X0)
          & r2_hidden(X1,X0)
          & v3_ordinal1(X1) )
     => ( ~ r2_hidden(k1_ordinal1(sK7),X0)
        & r2_hidden(sK7,X0)
        & v3_ordinal1(sK7) ) ) ),
    introduced(choice_axiom,[])).

fof(f62,plain,
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

fof(f64,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7])],[f61,f63,f62])).

fof(f100,plain,(
    ! [X2] :
      ( r2_hidden(k1_ordinal1(X2),sK6)
      | ~ r2_hidden(X2,sK6)
      | ~ v3_ordinal1(X2)
      | v4_ordinal1(sK6) ) ),
    inference(cnf_transformation,[],[f64])).

fof(f5,axiom,(
    ! [X0] : k1_ordinal1(X0) = k2_xboole_0(X0,k1_tarski(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f78,plain,(
    ! [X0] : k1_ordinal1(X0) = k2_xboole_0(X0,k1_tarski(X0)) ),
    inference(cnf_transformation,[],[f5])).

fof(f114,plain,(
    ! [X2] :
      ( r2_hidden(k2_xboole_0(X2,k1_tarski(X2)),sK6)
      | ~ r2_hidden(X2,sK6)
      | ~ v3_ordinal1(X2)
      | v4_ordinal1(sK6) ) ),
    inference(definition_unfolding,[],[f100,f78])).

fof(f73,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | ~ r2_hidden(X6,X0)
      | ~ r2_hidden(X5,X6)
      | k3_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f48])).

fof(f117,plain,(
    ! [X6,X0,X5] :
      ( r2_hidden(X5,k3_tarski(X0))
      | ~ r2_hidden(X6,X0)
      | ~ r2_hidden(X5,X6) ) ),
    inference(equality_resolution,[],[f73])).

fof(f6,axiom,(
    ! [X0] :
      ( v4_ordinal1(X0)
    <=> k3_tarski(X0) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f49,plain,(
    ! [X0] :
      ( ( v4_ordinal1(X0)
        | k3_tarski(X0) != X0 )
      & ( k3_tarski(X0) = X0
        | ~ v4_ordinal1(X0) ) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f79,plain,(
    ! [X0] :
      ( k3_tarski(X0) = X0
      | ~ v4_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f80,plain,(
    ! [X0] :
      ( v4_ordinal1(X0)
      | k3_tarski(X0) != X0 ) ),
    inference(cnf_transformation,[],[f49])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,k1_ordinal1(X1))
    <=> ( X0 = X1
        | r2_hidden(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f51,plain,(
    ! [X0,X1] :
      ( ( r2_hidden(X0,k1_ordinal1(X1))
        | ( X0 != X1
          & ~ r2_hidden(X0,X1) ) )
      & ( X0 = X1
        | r2_hidden(X0,X1)
        | ~ r2_hidden(X0,k1_ordinal1(X1)) ) ) ),
    inference(nnf_transformation,[],[f9])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ( r2_hidden(X0,k1_ordinal1(X1))
        | ( X0 != X1
          & ~ r2_hidden(X0,X1) ) )
      & ( X0 = X1
        | r2_hidden(X0,X1)
        | ~ r2_hidden(X0,k1_ordinal1(X1)) ) ) ),
    inference(flattening,[],[f51])).

fof(f86,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,k1_ordinal1(X1))
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f52])).

fof(f105,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,k2_xboole_0(X1,k1_tarski(X1)))
      | X0 != X1 ) ),
    inference(definition_unfolding,[],[f86,f78])).

fof(f120,plain,(
    ! [X1] : r2_hidden(X1,k2_xboole_0(X1,k1_tarski(X1))) ),
    inference(equality_resolution,[],[f105])).

fof(f10,axiom,(
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
    inference(ennf_transformation,[],[f10])).

fof(f26,plain,(
    ! [X0,X1] :
      ( v3_ordinal1(X0)
      | ~ r2_hidden(X0,X1)
      | ~ v3_ordinal1(X1) ) ),
    inference(flattening,[],[f25])).

fof(f87,plain,(
    ! [X0,X1] :
      ( v3_ordinal1(X0)
      | ~ r2_hidden(X0,X1)
      | ~ v3_ordinal1(X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f12,axiom,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => v3_ordinal1(k1_ordinal1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0] :
      ( v3_ordinal1(k1_ordinal1(X0))
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f89,plain,(
    ! [X0] :
      ( v3_ordinal1(k1_ordinal1(X0))
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f108,plain,(
    ! [X0] :
      ( v3_ordinal1(k2_xboole_0(X0,k1_tarski(X0)))
      | ~ v3_ordinal1(X0) ) ),
    inference(definition_unfolding,[],[f89,f78])).

fof(f99,plain,(
    v3_ordinal1(sK6) ),
    inference(cnf_transformation,[],[f64])).

fof(f95,plain,(
    ! [X0] :
      ( v3_ordinal1(k3_tarski(X0))
      | ~ v3_ordinal1(sK4(X0)) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f72,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(sK3(X0,X5),X0)
      | ~ r2_hidden(X5,X1)
      | k3_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f48])).

fof(f118,plain,(
    ! [X0,X5] :
      ( r2_hidden(sK3(X0,X5),X0)
      | ~ r2_hidden(X5,k3_tarski(X0)) ) ),
    inference(equality_resolution,[],[f72])).

fof(f17,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f98,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f34])).

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

fof(f50,plain,(
    ! [X0,X1] :
      ( ( ( r1_ordinal1(X0,X1)
          | ~ r1_tarski(X0,X1) )
        & ( r1_tarski(X0,X1)
          | ~ r1_ordinal1(X0,X1) ) )
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(nnf_transformation,[],[f24])).

fof(f81,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r1_ordinal1(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f11,axiom,(
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
    inference(ennf_transformation,[],[f11])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(X1,X0)
          | X0 = X1
          | r2_hidden(X0,X1)
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(flattening,[],[f27])).

fof(f88,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,X0)
      | X0 = X1
      | r2_hidden(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f85,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,k1_ordinal1(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f106,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,k2_xboole_0(X1,k1_tarski(X1)))
      | ~ r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f85,f78])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f41])).

fof(f68,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f42])).

fof(f116,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f68])).

fof(f14,axiom,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ! [X1] :
          ( v3_ordinal1(X1)
         => ( r2_hidden(X0,k1_ordinal1(X1))
          <=> r1_ordinal1(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r2_hidden(X0,k1_ordinal1(X1))
          <=> r1_ordinal1(X0,X1) )
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f54,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( r2_hidden(X0,k1_ordinal1(X1))
              | ~ r1_ordinal1(X0,X1) )
            & ( r1_ordinal1(X0,X1)
              | ~ r2_hidden(X0,k1_ordinal1(X1)) ) )
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(nnf_transformation,[],[f31])).

fof(f92,plain,(
    ! [X0,X1] :
      ( r1_ordinal1(X0,X1)
      | ~ r2_hidden(X0,k1_ordinal1(X1))
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f112,plain,(
    ! [X0,X1] :
      ( r1_ordinal1(X0,X1)
      | ~ r2_hidden(X0,k2_xboole_0(X1,k1_tarski(X1)))
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(definition_unfolding,[],[f92,f78])).

fof(f103,plain,
    ( ~ r2_hidden(k1_ordinal1(sK7),sK6)
    | ~ v4_ordinal1(sK6) ),
    inference(cnf_transformation,[],[f64])).

fof(f113,plain,
    ( ~ r2_hidden(k2_xboole_0(sK7,k1_tarski(sK7)),sK6)
    | ~ v4_ordinal1(sK6) ),
    inference(definition_unfolding,[],[f103,f78])).

fof(f101,plain,
    ( v3_ordinal1(sK7)
    | ~ v4_ordinal1(sK6) ),
    inference(cnf_transformation,[],[f64])).

fof(f102,plain,
    ( r2_hidden(sK7,sK6)
    | ~ v4_ordinal1(sK6) ),
    inference(cnf_transformation,[],[f64])).

fof(f13,axiom,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ! [X1] :
          ( v3_ordinal1(X1)
         => ( r2_hidden(X0,X1)
          <=> r1_ordinal1(k1_ordinal1(X0),X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r2_hidden(X0,X1)
          <=> r1_ordinal1(k1_ordinal1(X0),X1) )
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f53,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( r2_hidden(X0,X1)
              | ~ r1_ordinal1(k1_ordinal1(X0),X1) )
            & ( r1_ordinal1(k1_ordinal1(X0),X1)
              | ~ r2_hidden(X0,X1) ) )
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(nnf_transformation,[],[f30])).

fof(f90,plain,(
    ! [X0,X1] :
      ( r1_ordinal1(k1_ordinal1(X0),X1)
      | ~ r2_hidden(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f110,plain,(
    ! [X0,X1] :
      ( r1_ordinal1(k2_xboole_0(X0,k1_tarski(X0)),X1)
      | ~ r2_hidden(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(definition_unfolding,[],[f90,f78])).

cnf(c_11,plain,
    ( r2_hidden(X0,sK3(X1,X0))
    | ~ r2_hidden(X0,k3_tarski(X1)) ),
    inference(cnf_transformation,[],[f119])).

cnf(c_1823,plain,
    ( r2_hidden(X0,sK3(X1,X0)) = iProver_top
    | r2_hidden(X0,k3_tarski(X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_29,plain,
    ( r2_hidden(sK4(X0),X0)
    | v3_ordinal1(k3_tarski(X0)) ),
    inference(cnf_transformation,[],[f94])).

cnf(c_1807,plain,
    ( r2_hidden(sK4(X0),X0) = iProver_top
    | v3_ordinal1(k3_tarski(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_2,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | ~ r1_tarski(X1,X2) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_1831,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,X2) = iProver_top
    | r1_tarski(X1,X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_4579,plain,
    ( r2_hidden(sK4(X0),X1) = iProver_top
    | r1_tarski(X0,X1) != iProver_top
    | v3_ordinal1(k3_tarski(X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1807,c_1831])).

cnf(c_36,negated_conjecture,
    ( ~ r2_hidden(X0,sK6)
    | r2_hidden(k2_xboole_0(X0,k1_tarski(X0)),sK6)
    | v4_ordinal1(sK6)
    | ~ v3_ordinal1(X0) ),
    inference(cnf_transformation,[],[f114])).

cnf(c_1800,plain,
    ( r2_hidden(X0,sK6) != iProver_top
    | r2_hidden(k2_xboole_0(X0,k1_tarski(X0)),sK6) = iProver_top
    | v4_ordinal1(sK6) = iProver_top
    | v3_ordinal1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_36])).

cnf(c_9,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X2,X0)
    | r2_hidden(X2,k3_tarski(X1)) ),
    inference(cnf_transformation,[],[f117])).

cnf(c_1825,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X2,X0) != iProver_top
    | r2_hidden(X2,k3_tarski(X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_4781,plain,
    ( r2_hidden(X0,k2_xboole_0(X1,k1_tarski(X1))) != iProver_top
    | r2_hidden(X0,k3_tarski(sK6)) = iProver_top
    | r2_hidden(X1,sK6) != iProver_top
    | v4_ordinal1(sK6) = iProver_top
    | v3_ordinal1(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1800,c_1825])).

cnf(c_19690,plain,
    ( r2_hidden(X0,sK6) != iProver_top
    | r2_hidden(sK4(X1),k3_tarski(sK6)) = iProver_top
    | r1_tarski(X1,k2_xboole_0(X0,k1_tarski(X0))) != iProver_top
    | v4_ordinal1(sK6) = iProver_top
    | v3_ordinal1(X0) != iProver_top
    | v3_ordinal1(k3_tarski(X1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_4579,c_4781])).

cnf(c_14,plain,
    ( ~ v4_ordinal1(X0)
    | k3_tarski(X0) = X0 ),
    inference(cnf_transformation,[],[f79])).

cnf(c_96,plain,
    ( ~ v4_ordinal1(sK6)
    | k3_tarski(sK6) = sK6 ),
    inference(instantiation,[status(thm)],[c_14])).

cnf(c_13,plain,
    ( v4_ordinal1(X0)
    | k3_tarski(X0) != X0 ),
    inference(cnf_transformation,[],[f80])).

cnf(c_98,plain,
    ( k3_tarski(X0) != X0
    | v4_ordinal1(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_100,plain,
    ( k3_tarski(sK6) != sK6
    | v4_ordinal1(sK6) = iProver_top ),
    inference(instantiation,[status(thm)],[c_98])).

cnf(c_18,plain,
    ( r2_hidden(X0,k2_xboole_0(X0,k1_tarski(X0))) ),
    inference(cnf_transformation,[],[f120])).

cnf(c_3534,plain,
    ( r2_hidden(X0,k3_tarski(X1))
    | ~ r2_hidden(k2_xboole_0(X0,k1_tarski(X0)),X1) ),
    inference(resolution,[status(thm)],[c_9,c_18])).

cnf(c_13081,plain,
    ( r2_hidden(X0,k3_tarski(sK6))
    | ~ r2_hidden(X0,sK6)
    | v4_ordinal1(sK6)
    | ~ v3_ordinal1(X0) ),
    inference(resolution,[status(thm)],[c_3534,c_36])).

cnf(c_13598,plain,
    ( r2_hidden(X0,k3_tarski(k3_tarski(sK6)))
    | ~ r2_hidden(k2_xboole_0(X0,k1_tarski(X0)),sK6)
    | v4_ordinal1(sK6)
    | ~ v3_ordinal1(k2_xboole_0(X0,k1_tarski(X0))) ),
    inference(resolution,[status(thm)],[c_13081,c_3534])).

cnf(c_14420,plain,
    ( r2_hidden(X0,k3_tarski(k3_tarski(sK6)))
    | ~ r2_hidden(X0,sK6)
    | v4_ordinal1(sK6)
    | ~ v3_ordinal1(X0)
    | ~ v3_ordinal1(k2_xboole_0(X0,k1_tarski(X0))) ),
    inference(resolution,[status(thm)],[c_13598,c_36])).

cnf(c_21,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ v3_ordinal1(X1)
    | v3_ordinal1(X0) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_2706,plain,
    ( v3_ordinal1(X0)
    | ~ v3_ordinal1(k2_xboole_0(X0,k1_tarski(X0))) ),
    inference(resolution,[status(thm)],[c_21,c_18])).

cnf(c_14423,plain,
    ( v4_ordinal1(sK6)
    | ~ r2_hidden(X0,sK6)
    | r2_hidden(X0,k3_tarski(k3_tarski(sK6)))
    | ~ v3_ordinal1(k2_xboole_0(X0,k1_tarski(X0))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_14420,c_2706])).

cnf(c_14424,plain,
    ( r2_hidden(X0,k3_tarski(k3_tarski(sK6)))
    | ~ r2_hidden(X0,sK6)
    | v4_ordinal1(sK6)
    | ~ v3_ordinal1(k2_xboole_0(X0,k1_tarski(X0))) ),
    inference(renaming,[status(thm)],[c_14423])).

cnf(c_23,plain,
    ( ~ v3_ordinal1(X0)
    | v3_ordinal1(k2_xboole_0(X0,k1_tarski(X0))) ),
    inference(cnf_transformation,[],[f108])).

cnf(c_14600,plain,
    ( r2_hidden(X0,k3_tarski(k3_tarski(sK6)))
    | ~ r2_hidden(X0,sK6)
    | v4_ordinal1(sK6)
    | ~ v3_ordinal1(X0) ),
    inference(resolution,[status(thm)],[c_14424,c_23])).

cnf(c_14631,plain,
    ( r2_hidden(X0,k3_tarski(k3_tarski(k3_tarski(sK6))))
    | ~ r2_hidden(k2_xboole_0(X0,k1_tarski(X0)),sK6)
    | v4_ordinal1(sK6)
    | ~ v3_ordinal1(k2_xboole_0(X0,k1_tarski(X0))) ),
    inference(resolution,[status(thm)],[c_14600,c_3534])).

cnf(c_19921,plain,
    ( r2_hidden(X0,k3_tarski(k3_tarski(k3_tarski(sK6))))
    | ~ r2_hidden(X0,sK6)
    | v4_ordinal1(sK6)
    | ~ v3_ordinal1(X0)
    | ~ v3_ordinal1(k2_xboole_0(X0,k1_tarski(X0))) ),
    inference(resolution,[status(thm)],[c_14631,c_36])).

cnf(c_37,negated_conjecture,
    ( v3_ordinal1(sK6) ),
    inference(cnf_transformation,[],[f99])).

cnf(c_99,plain,
    ( v4_ordinal1(sK6)
    | k3_tarski(sK6) != sK6 ),
    inference(instantiation,[status(thm)],[c_13])).

cnf(c_105,plain,
    ( r2_hidden(sK6,sK3(sK6,sK6))
    | ~ r2_hidden(sK6,k3_tarski(sK6)) ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_2708,plain,
    ( ~ v3_ordinal1(X0)
    | v3_ordinal1(sK4(X0))
    | v3_ordinal1(k3_tarski(X0)) ),
    inference(resolution,[status(thm)],[c_21,c_29])).

cnf(c_28,plain,
    ( ~ v3_ordinal1(sK4(X0))
    | v3_ordinal1(k3_tarski(X0)) ),
    inference(cnf_transformation,[],[f95])).

cnf(c_2937,plain,
    ( ~ v3_ordinal1(X0)
    | v3_ordinal1(k3_tarski(X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2708,c_28])).

cnf(c_2940,plain,
    ( v3_ordinal1(k3_tarski(sK6))
    | ~ v3_ordinal1(sK6) ),
    inference(instantiation,[status(thm)],[c_2937])).

cnf(c_10,plain,
    ( ~ r2_hidden(X0,k3_tarski(X1))
    | r2_hidden(sK3(X1,X0),X1) ),
    inference(cnf_transformation,[],[f118])).

cnf(c_32,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r1_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f98])).

cnf(c_2961,plain,
    ( ~ r2_hidden(X0,k3_tarski(X1))
    | ~ r1_tarski(X1,sK3(X1,X0)) ),
    inference(resolution,[status(thm)],[c_10,c_32])).

cnf(c_2967,plain,
    ( ~ r2_hidden(sK6,k3_tarski(sK6))
    | ~ r1_tarski(sK6,sK3(sK6,sK6)) ),
    inference(instantiation,[status(thm)],[c_2961])).

cnf(c_16,plain,
    ( ~ r1_ordinal1(X0,X1)
    | r1_tarski(X0,X1)
    | ~ v3_ordinal1(X1)
    | ~ v3_ordinal1(X0) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_3702,plain,
    ( ~ r1_ordinal1(X0,sK3(X0,X1))
    | r1_tarski(X0,sK3(X0,X1))
    | ~ v3_ordinal1(X0)
    | ~ v3_ordinal1(sK3(X0,X1)) ),
    inference(instantiation,[status(thm)],[c_16])).

cnf(c_3714,plain,
    ( ~ r1_ordinal1(sK6,sK3(sK6,sK6))
    | r1_tarski(sK6,sK3(sK6,sK6))
    | ~ v3_ordinal1(sK3(sK6,sK6))
    | ~ v3_ordinal1(sK6) ),
    inference(instantiation,[status(thm)],[c_3702])).

cnf(c_22,plain,
    ( r2_hidden(X0,X1)
    | r2_hidden(X1,X0)
    | ~ v3_ordinal1(X1)
    | ~ v3_ordinal1(X0)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f88])).

cnf(c_6997,plain,
    ( r2_hidden(X0,k3_tarski(X0))
    | r2_hidden(k3_tarski(X0),X0)
    | v4_ordinal1(X0)
    | ~ v3_ordinal1(X0)
    | ~ v3_ordinal1(k3_tarski(X0)) ),
    inference(resolution,[status(thm)],[c_22,c_13])).

cnf(c_6999,plain,
    ( r2_hidden(k3_tarski(sK6),sK6)
    | r2_hidden(sK6,k3_tarski(sK6))
    | v4_ordinal1(sK6)
    | ~ v3_ordinal1(k3_tarski(sK6))
    | ~ v3_ordinal1(sK6) ),
    inference(instantiation,[status(thm)],[c_6997])).

cnf(c_1813,plain,
    ( X0 = X1
    | r2_hidden(X1,X0) = iProver_top
    | r2_hidden(X0,X1) = iProver_top
    | v3_ordinal1(X1) != iProver_top
    | v3_ordinal1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_1824,plain,
    ( r2_hidden(X0,k3_tarski(X1)) != iProver_top
    | r2_hidden(sK3(X1,X0),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_1814,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | v3_ordinal1(X1) != iProver_top
    | v3_ordinal1(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_3603,plain,
    ( r2_hidden(X0,k3_tarski(X1)) != iProver_top
    | v3_ordinal1(X1) != iProver_top
    | v3_ordinal1(sK3(X1,X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1824,c_1814])).

cnf(c_15776,plain,
    ( k3_tarski(X0) = X1
    | r2_hidden(k3_tarski(X0),X1) = iProver_top
    | v3_ordinal1(X0) != iProver_top
    | v3_ordinal1(X1) != iProver_top
    | v3_ordinal1(sK3(X0,X1)) = iProver_top
    | v3_ordinal1(k3_tarski(X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1813,c_3603])).

cnf(c_16054,plain,
    ( r2_hidden(k3_tarski(X0),X1)
    | ~ v3_ordinal1(X1)
    | ~ v3_ordinal1(X0)
    | v3_ordinal1(sK3(X0,X1))
    | ~ v3_ordinal1(k3_tarski(X0))
    | k3_tarski(X0) = X1 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_15776])).

cnf(c_16056,plain,
    ( r2_hidden(k3_tarski(sK6),sK6)
    | v3_ordinal1(sK3(sK6,sK6))
    | ~ v3_ordinal1(k3_tarski(sK6))
    | ~ v3_ordinal1(sK6)
    | k3_tarski(sK6) = sK6 ),
    inference(instantiation,[status(thm)],[c_16054])).

cnf(c_19,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,k2_xboole_0(X1,k1_tarski(X1))) ),
    inference(cnf_transformation,[],[f106])).

cnf(c_3425,plain,
    ( ~ r2_hidden(sK6,X0)
    | r2_hidden(sK6,k2_xboole_0(X0,k1_tarski(X0))) ),
    inference(instantiation,[status(thm)],[c_19])).

cnf(c_17712,plain,
    ( r2_hidden(sK6,k2_xboole_0(sK3(X0,sK6),k1_tarski(sK3(X0,sK6))))
    | ~ r2_hidden(sK6,sK3(X0,sK6)) ),
    inference(instantiation,[status(thm)],[c_3425])).

cnf(c_17715,plain,
    ( r2_hidden(sK6,k2_xboole_0(sK3(sK6,sK6),k1_tarski(sK3(sK6,sK6))))
    | ~ r2_hidden(sK6,sK3(sK6,sK6)) ),
    inference(instantiation,[status(thm)],[c_17712])).

cnf(c_13585,plain,
    ( ~ r2_hidden(X0,sK6)
    | ~ r1_tarski(k3_tarski(sK6),X0)
    | v4_ordinal1(sK6)
    | ~ v3_ordinal1(X0) ),
    inference(resolution,[status(thm)],[c_13081,c_32])).

cnf(c_5,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f116])).

cnf(c_13880,plain,
    ( ~ r2_hidden(k3_tarski(sK6),sK6)
    | v4_ordinal1(sK6)
    | ~ v3_ordinal1(k3_tarski(sK6)) ),
    inference(resolution,[status(thm)],[c_13585,c_5])).

cnf(c_46,plain,
    ( ~ r2_hidden(sK6,sK6)
    | ~ r1_tarski(sK6,sK6) ),
    inference(instantiation,[status(thm)],[c_32])).

cnf(c_27,plain,
    ( r1_ordinal1(X0,X1)
    | ~ r2_hidden(X0,k2_xboole_0(X1,k1_tarski(X1)))
    | ~ v3_ordinal1(X1)
    | ~ v3_ordinal1(X0) ),
    inference(cnf_transformation,[],[f112])).

cnf(c_61,plain,
    ( r1_ordinal1(sK6,sK6)
    | ~ r2_hidden(sK6,k2_xboole_0(sK6,k1_tarski(sK6)))
    | ~ v3_ordinal1(sK6) ),
    inference(instantiation,[status(thm)],[c_27])).

cnf(c_76,plain,
    ( r2_hidden(sK6,sK6)
    | ~ v3_ordinal1(sK6)
    | sK6 = sK6 ),
    inference(instantiation,[status(thm)],[c_22])).

cnf(c_86,plain,
    ( r2_hidden(sK6,k2_xboole_0(sK6,k1_tarski(sK6))) ),
    inference(instantiation,[status(thm)],[c_18])).

cnf(c_90,plain,
    ( ~ r1_ordinal1(sK6,sK6)
    | r1_tarski(sK6,sK6)
    | ~ v3_ordinal1(sK6) ),
    inference(instantiation,[status(thm)],[c_16])).

cnf(c_1013,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_6813,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(k3_tarski(X2),X3)
    | X1 != X3
    | X0 != k3_tarski(X2) ),
    inference(instantiation,[status(thm)],[c_1013])).

cnf(c_6828,plain,
    ( ~ r2_hidden(k3_tarski(sK6),sK6)
    | r2_hidden(sK6,sK6)
    | sK6 != k3_tarski(sK6)
    | sK6 != sK6 ),
    inference(instantiation,[status(thm)],[c_6813])).

cnf(c_1012,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_16156,plain,
    ( X0 != X1
    | X0 = k3_tarski(X2)
    | k3_tarski(X2) != X1 ),
    inference(instantiation,[status(thm)],[c_1012])).

cnf(c_16157,plain,
    ( k3_tarski(sK6) != sK6
    | sK6 = k3_tarski(sK6)
    | sK6 != sK6 ),
    inference(instantiation,[status(thm)],[c_16156])).

cnf(c_17825,plain,
    ( ~ r2_hidden(k3_tarski(sK6),sK6) ),
    inference(global_propositional_subsumption,[status(thm)],[c_13880,c_37,c_46,c_61,c_76,c_86,c_90,c_96,c_2940,c_6828,c_16157])).

cnf(c_19988,plain,
    ( r1_ordinal1(X0,sK3(X0,X1))
    | ~ r2_hidden(X0,k2_xboole_0(sK3(X0,X1),k1_tarski(sK3(X0,X1))))
    | ~ v3_ordinal1(X0)
    | ~ v3_ordinal1(sK3(X0,X1)) ),
    inference(instantiation,[status(thm)],[c_27])).

cnf(c_19995,plain,
    ( r1_ordinal1(sK6,sK3(sK6,sK6))
    | ~ r2_hidden(sK6,k2_xboole_0(sK3(sK6,sK6),k1_tarski(sK3(sK6,sK6))))
    | ~ v3_ordinal1(sK3(sK6,sK6))
    | ~ v3_ordinal1(sK6) ),
    inference(instantiation,[status(thm)],[c_19988])).

cnf(c_20473,plain,
    ( v4_ordinal1(sK6) ),
    inference(global_propositional_subsumption,[status(thm)],[c_19921,c_37,c_46,c_61,c_76,c_86,c_90,c_96,c_99,c_105,c_2940,c_2967,c_3714,c_6828,c_6999,c_13880,c_16056,c_16157,c_17715,c_19995])).

cnf(c_20620,plain,
    ( v4_ordinal1(sK6) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_19690,c_37,c_46,c_61,c_76,c_86,c_90,c_96,c_99,c_100,c_105,c_2940,c_2967,c_3714,c_6828,c_6999,c_13880,c_16056,c_16157,c_17715,c_19995])).

cnf(c_33,negated_conjecture,
    ( ~ r2_hidden(k2_xboole_0(sK7,k1_tarski(sK7)),sK6)
    | ~ v4_ordinal1(sK6) ),
    inference(cnf_transformation,[],[f113])).

cnf(c_1803,plain,
    ( r2_hidden(k2_xboole_0(sK7,k1_tarski(sK7)),sK6) != iProver_top
    | v4_ordinal1(sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_8728,plain,
    ( k2_xboole_0(sK7,k1_tarski(sK7)) = sK6
    | r2_hidden(sK6,k2_xboole_0(sK7,k1_tarski(sK7))) = iProver_top
    | v4_ordinal1(sK6) != iProver_top
    | v3_ordinal1(k2_xboole_0(sK7,k1_tarski(sK7))) != iProver_top
    | v3_ordinal1(sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_1813,c_1803])).

cnf(c_38,plain,
    ( v3_ordinal1(sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_37])).

cnf(c_35,negated_conjecture,
    ( ~ v4_ordinal1(sK6)
    | v3_ordinal1(sK7) ),
    inference(cnf_transformation,[],[f101])).

cnf(c_42,plain,
    ( v4_ordinal1(sK6) != iProver_top
    | v3_ordinal1(sK7) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_35])).

cnf(c_34,negated_conjecture,
    ( r2_hidden(sK7,sK6)
    | ~ v4_ordinal1(sK6) ),
    inference(cnf_transformation,[],[f102])).

cnf(c_1802,plain,
    ( r2_hidden(sK7,sK6) = iProver_top
    | v4_ordinal1(sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_1804,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_2537,plain,
    ( r1_tarski(sK6,sK7) != iProver_top
    | v4_ordinal1(sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_1802,c_1804])).

cnf(c_3312,plain,
    ( ~ r1_ordinal1(sK6,sK7)
    | r1_tarski(sK6,sK7)
    | ~ v3_ordinal1(sK6)
    | ~ v3_ordinal1(sK7) ),
    inference(instantiation,[status(thm)],[c_16])).

cnf(c_3319,plain,
    ( r1_ordinal1(sK6,sK7) != iProver_top
    | r1_tarski(sK6,sK7) = iProver_top
    | v3_ordinal1(sK6) != iProver_top
    | v3_ordinal1(sK7) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3312])).

cnf(c_5618,plain,
    ( r1_ordinal1(sK6,sK7)
    | ~ r2_hidden(sK6,k2_xboole_0(sK7,k1_tarski(sK7)))
    | ~ v3_ordinal1(sK6)
    | ~ v3_ordinal1(sK7) ),
    inference(instantiation,[status(thm)],[c_27])).

cnf(c_5622,plain,
    ( r1_ordinal1(sK6,sK7) = iProver_top
    | r2_hidden(sK6,k2_xboole_0(sK7,k1_tarski(sK7))) != iProver_top
    | v3_ordinal1(sK6) != iProver_top
    | v3_ordinal1(sK7) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5618])).

cnf(c_5874,plain,
    ( v3_ordinal1(k2_xboole_0(sK7,k1_tarski(sK7)))
    | ~ v3_ordinal1(sK7) ),
    inference(instantiation,[status(thm)],[c_23])).

cnf(c_5875,plain,
    ( v3_ordinal1(k2_xboole_0(sK7,k1_tarski(sK7))) = iProver_top
    | v3_ordinal1(sK7) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5874])).

cnf(c_9262,plain,
    ( k2_xboole_0(sK7,k1_tarski(sK7)) = sK6
    | v4_ordinal1(sK6) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_8728,c_38,c_42,c_2537,c_3319,c_5622,c_5875])).

cnf(c_20626,plain,
    ( k2_xboole_0(sK7,k1_tarski(sK7)) = sK6 ),
    inference(superposition,[status(thm)],[c_20620,c_9262])).

cnf(c_25,plain,
    ( r1_ordinal1(k2_xboole_0(X0,k1_tarski(X0)),X1)
    | ~ r2_hidden(X0,X1)
    | ~ v3_ordinal1(X1)
    | ~ v3_ordinal1(X0) ),
    inference(cnf_transformation,[],[f110])).

cnf(c_221,plain,
    ( ~ v3_ordinal1(X1)
    | ~ r2_hidden(X0,X1)
    | r1_ordinal1(k2_xboole_0(X0,k1_tarski(X0)),X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_25,c_21])).

cnf(c_222,plain,
    ( r1_ordinal1(k2_xboole_0(X0,k1_tarski(X0)),X1)
    | ~ r2_hidden(X0,X1)
    | ~ v3_ordinal1(X1) ),
    inference(renaming,[status(thm)],[c_221])).

cnf(c_1798,plain,
    ( r1_ordinal1(k2_xboole_0(X0,k1_tarski(X0)),X1) = iProver_top
    | r2_hidden(X0,X1) != iProver_top
    | v3_ordinal1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_222])).

cnf(c_20882,plain,
    ( r1_ordinal1(sK6,X0) = iProver_top
    | r2_hidden(sK7,X0) != iProver_top
    | v3_ordinal1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_20626,c_1798])).

cnf(c_25370,plain,
    ( r1_ordinal1(sK6,sK3(X0,sK7)) = iProver_top
    | r2_hidden(sK7,k3_tarski(X0)) != iProver_top
    | v3_ordinal1(sK3(X0,sK7)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1823,c_20882])).

cnf(c_25432,plain,
    ( r1_ordinal1(sK6,sK3(sK6,sK7)) = iProver_top
    | r2_hidden(sK7,k3_tarski(sK6)) != iProver_top
    | v3_ordinal1(sK3(sK6,sK7)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_25370])).

cnf(c_14803,plain,
    ( ~ r1_ordinal1(X0,sK3(X1,sK7))
    | r1_tarski(X0,sK3(X1,sK7))
    | ~ v3_ordinal1(X0)
    | ~ v3_ordinal1(sK3(X1,sK7)) ),
    inference(instantiation,[status(thm)],[c_16])).

cnf(c_14814,plain,
    ( r1_ordinal1(X0,sK3(X1,sK7)) != iProver_top
    | r1_tarski(X0,sK3(X1,sK7)) = iProver_top
    | v3_ordinal1(X0) != iProver_top
    | v3_ordinal1(sK3(X1,sK7)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14803])).

cnf(c_14816,plain,
    ( r1_ordinal1(sK6,sK3(sK6,sK7)) != iProver_top
    | r1_tarski(sK6,sK3(sK6,sK7)) = iProver_top
    | v3_ordinal1(sK3(sK6,sK7)) != iProver_top
    | v3_ordinal1(sK6) != iProver_top ),
    inference(instantiation,[status(thm)],[c_14814])).

cnf(c_4494,plain,
    ( ~ r2_hidden(sK3(X0,X1),X2)
    | ~ v3_ordinal1(X2)
    | v3_ordinal1(sK3(X0,X1)) ),
    inference(instantiation,[status(thm)],[c_21])).

cnf(c_7702,plain,
    ( ~ r2_hidden(sK3(sK6,sK7),sK6)
    | v3_ordinal1(sK3(sK6,sK7))
    | ~ v3_ordinal1(sK6) ),
    inference(instantiation,[status(thm)],[c_4494])).

cnf(c_7703,plain,
    ( r2_hidden(sK3(sK6,sK7),sK6) != iProver_top
    | v3_ordinal1(sK3(sK6,sK7)) = iProver_top
    | v3_ordinal1(sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7702])).

cnf(c_2765,plain,
    ( ~ r2_hidden(sK3(X0,X1),X0)
    | ~ r1_tarski(X0,sK3(X0,X1)) ),
    inference(instantiation,[status(thm)],[c_32])).

cnf(c_7108,plain,
    ( ~ r2_hidden(sK3(sK6,sK7),sK6)
    | ~ r1_tarski(sK6,sK3(sK6,sK7)) ),
    inference(instantiation,[status(thm)],[c_2765])).

cnf(c_7109,plain,
    ( r2_hidden(sK3(sK6,sK7),sK6) != iProver_top
    | r1_tarski(sK6,sK3(sK6,sK7)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7108])).

cnf(c_3433,plain,
    ( r2_hidden(X0,sK7)
    | r2_hidden(sK7,X0)
    | ~ v3_ordinal1(X0)
    | ~ v3_ordinal1(sK7)
    | X0 = sK7 ),
    inference(instantiation,[status(thm)],[c_22])).

cnf(c_6756,plain,
    ( r2_hidden(k3_tarski(X0),sK7)
    | r2_hidden(sK7,k3_tarski(X0))
    | ~ v3_ordinal1(k3_tarski(X0))
    | ~ v3_ordinal1(sK7)
    | k3_tarski(X0) = sK7 ),
    inference(instantiation,[status(thm)],[c_3433])).

cnf(c_6767,plain,
    ( k3_tarski(X0) = sK7
    | r2_hidden(k3_tarski(X0),sK7) = iProver_top
    | r2_hidden(sK7,k3_tarski(X0)) = iProver_top
    | v3_ordinal1(k3_tarski(X0)) != iProver_top
    | v3_ordinal1(sK7) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6756])).

cnf(c_6769,plain,
    ( k3_tarski(sK6) = sK7
    | r2_hidden(k3_tarski(sK6),sK7) = iProver_top
    | r2_hidden(sK7,k3_tarski(sK6)) = iProver_top
    | v3_ordinal1(k3_tarski(sK6)) != iProver_top
    | v3_ordinal1(sK7) != iProver_top ),
    inference(instantiation,[status(thm)],[c_6767])).

cnf(c_1829,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_4780,plain,
    ( r2_hidden(X0,k3_tarski(sK6)) = iProver_top
    | r2_hidden(X0,sK7) != iProver_top
    | v4_ordinal1(sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_1802,c_1825])).

cnf(c_5233,plain,
    ( r2_hidden(X0,sK7) != iProver_top
    | r1_tarski(k3_tarski(sK6),X0) != iProver_top
    | v4_ordinal1(sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_4780,c_1804])).

cnf(c_6071,plain,
    ( r2_hidden(k3_tarski(sK6),sK7) != iProver_top
    | v4_ordinal1(sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_1829,c_5233])).

cnf(c_2314,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(sK7,sK6)
    | X1 != sK6
    | X0 != sK7 ),
    inference(instantiation,[status(thm)],[c_1013])).

cnf(c_3771,plain,
    ( r2_hidden(k3_tarski(X0),X1)
    | ~ r2_hidden(sK7,sK6)
    | X1 != sK6
    | k3_tarski(X0) != sK7 ),
    inference(instantiation,[status(thm)],[c_2314])).

cnf(c_3777,plain,
    ( r2_hidden(k3_tarski(sK6),sK6)
    | ~ r2_hidden(sK7,sK6)
    | k3_tarski(sK6) != sK7
    | sK6 != sK6 ),
    inference(instantiation,[status(thm)],[c_3771])).

cnf(c_2784,plain,
    ( ~ r2_hidden(X0,k3_tarski(sK6))
    | r2_hidden(sK3(sK6,X0),sK6) ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_3404,plain,
    ( r2_hidden(sK3(sK6,sK7),sK6)
    | ~ r2_hidden(sK7,k3_tarski(sK6)) ),
    inference(instantiation,[status(thm)],[c_2784])).

cnf(c_3407,plain,
    ( r2_hidden(sK3(sK6,sK7),sK6) = iProver_top
    | r2_hidden(sK7,k3_tarski(sK6)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3404])).

cnf(c_2939,plain,
    ( v3_ordinal1(X0) != iProver_top
    | v3_ordinal1(k3_tarski(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2937])).

cnf(c_2941,plain,
    ( v3_ordinal1(k3_tarski(sK6)) = iProver_top
    | v3_ordinal1(sK6) != iProver_top ),
    inference(instantiation,[status(thm)],[c_2939])).

cnf(c_300,plain,
    ( v4_ordinal1(X0)
    | k3_tarski(X0) != X0 ),
    inference(prop_impl,[status(thm)],[c_13])).

cnf(c_528,plain,
    ( v3_ordinal1(sK7)
    | k3_tarski(X0) != X0
    | sK6 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_300,c_35])).

cnf(c_529,plain,
    ( v3_ordinal1(sK7)
    | k3_tarski(sK6) != sK6 ),
    inference(unflattening,[status(thm)],[c_528])).

cnf(c_530,plain,
    ( k3_tarski(sK6) != sK6
    | v3_ordinal1(sK7) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_529])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_25432,c_20473,c_17825,c_14816,c_7703,c_7109,c_6769,c_6071,c_3777,c_3407,c_2941,c_530,c_100,c_96,c_90,c_86,c_76,c_61,c_46,c_34,c_38,c_37])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.00/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n013.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 18:31:09 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 7.52/1.48  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.52/1.48  
% 7.52/1.48  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.52/1.48  
% 7.52/1.48  ------  iProver source info
% 7.52/1.48  
% 7.52/1.48  git: date: 2020-06-30 10:37:57 +0100
% 7.52/1.48  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.52/1.48  git: non_committed_changes: false
% 7.52/1.48  git: last_make_outside_of_git: false
% 7.52/1.48  
% 7.52/1.48  ------ 
% 7.52/1.48  ------ Parsing...
% 7.52/1.48  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.52/1.48  
% 7.52/1.48  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e  sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 7.52/1.48  
% 7.52/1.48  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.52/1.48  
% 7.52/1.48  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.52/1.48  ------ Proving...
% 7.52/1.48  ------ Problem Properties 
% 7.52/1.48  
% 7.52/1.48  
% 7.52/1.48  clauses                                 36
% 7.52/1.48  conjectures                             5
% 7.52/1.48  EPR                                     12
% 7.52/1.48  Horn                                    28
% 7.52/1.48  unary                                   5
% 7.52/1.48  binary                                  14
% 7.52/1.48  lits                                    94
% 7.52/1.48  lits eq                                 8
% 7.52/1.48  fd_pure                                 0
% 7.52/1.48  fd_pseudo                               0
% 7.52/1.48  fd_cond                                 0
% 7.52/1.48  fd_pseudo_cond                          6
% 7.52/1.48  AC symbols                              0
% 7.52/1.48  
% 7.52/1.48  ------ Input Options Time Limit: Unbounded
% 7.52/1.48  
% 7.52/1.48  
% 7.52/1.48  ------ 
% 7.52/1.48  Current options:
% 7.52/1.48  ------ 
% 7.52/1.48  
% 7.52/1.48  
% 7.52/1.48  
% 7.52/1.48  
% 7.52/1.48  ------ Proving...
% 7.52/1.48  
% 7.52/1.48  
% 7.52/1.48  % SZS status Theorem for theBenchmark.p
% 7.52/1.48  
% 7.52/1.48  % SZS output start CNFRefutation for theBenchmark.p
% 7.52/1.48  
% 7.52/1.48  fof(f3,axiom,(
% 7.52/1.48    ! [X0,X1] : (k3_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (r2_hidden(X3,X0) & r2_hidden(X2,X3))))),
% 7.52/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.52/1.48  
% 7.52/1.48  fof(f43,plain,(
% 7.52/1.48    ! [X0,X1] : ((k3_tarski(X0) = X1 | ? [X2] : ((! [X3] : (~r2_hidden(X3,X0) | ~r2_hidden(X2,X3)) | ~r2_hidden(X2,X1)) & (? [X3] : (r2_hidden(X3,X0) & r2_hidden(X2,X3)) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ! [X3] : (~r2_hidden(X3,X0) | ~r2_hidden(X2,X3))) & (? [X3] : (r2_hidden(X3,X0) & r2_hidden(X2,X3)) | ~r2_hidden(X2,X1))) | k3_tarski(X0) != X1))),
% 7.52/1.48    inference(nnf_transformation,[],[f3])).
% 7.52/1.48  
% 7.52/1.48  fof(f44,plain,(
% 7.52/1.48    ! [X0,X1] : ((k3_tarski(X0) = X1 | ? [X2] : ((! [X3] : (~r2_hidden(X3,X0) | ~r2_hidden(X2,X3)) | ~r2_hidden(X2,X1)) & (? [X4] : (r2_hidden(X4,X0) & r2_hidden(X2,X4)) | r2_hidden(X2,X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : (~r2_hidden(X6,X0) | ~r2_hidden(X5,X6))) & (? [X7] : (r2_hidden(X7,X0) & r2_hidden(X5,X7)) | ~r2_hidden(X5,X1))) | k3_tarski(X0) != X1))),
% 7.52/1.48    inference(rectify,[],[f43])).
% 7.52/1.48  
% 7.52/1.48  fof(f47,plain,(
% 7.52/1.48    ! [X5,X0] : (? [X7] : (r2_hidden(X7,X0) & r2_hidden(X5,X7)) => (r2_hidden(sK3(X0,X5),X0) & r2_hidden(X5,sK3(X0,X5))))),
% 7.52/1.48    introduced(choice_axiom,[])).
% 7.52/1.48  
% 7.52/1.48  fof(f46,plain,(
% 7.52/1.48    ( ! [X2] : (! [X1,X0] : (? [X4] : (r2_hidden(X4,X0) & r2_hidden(X2,X4)) => (r2_hidden(sK2(X0,X1),X0) & r2_hidden(X2,sK2(X0,X1))))) )),
% 7.52/1.48    introduced(choice_axiom,[])).
% 7.52/1.48  
% 7.52/1.48  fof(f45,plain,(
% 7.52/1.48    ! [X1,X0] : (? [X2] : ((! [X3] : (~r2_hidden(X3,X0) | ~r2_hidden(X2,X3)) | ~r2_hidden(X2,X1)) & (? [X4] : (r2_hidden(X4,X0) & r2_hidden(X2,X4)) | r2_hidden(X2,X1))) => ((! [X3] : (~r2_hidden(X3,X0) | ~r2_hidden(sK1(X0,X1),X3)) | ~r2_hidden(sK1(X0,X1),X1)) & (? [X4] : (r2_hidden(X4,X0) & r2_hidden(sK1(X0,X1),X4)) | r2_hidden(sK1(X0,X1),X1))))),
% 7.52/1.48    introduced(choice_axiom,[])).
% 7.52/1.48  
% 7.52/1.48  fof(f48,plain,(
% 7.52/1.48    ! [X0,X1] : ((k3_tarski(X0) = X1 | ((! [X3] : (~r2_hidden(X3,X0) | ~r2_hidden(sK1(X0,X1),X3)) | ~r2_hidden(sK1(X0,X1),X1)) & ((r2_hidden(sK2(X0,X1),X0) & r2_hidden(sK1(X0,X1),sK2(X0,X1))) | r2_hidden(sK1(X0,X1),X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : (~r2_hidden(X6,X0) | ~r2_hidden(X5,X6))) & ((r2_hidden(sK3(X0,X5),X0) & r2_hidden(X5,sK3(X0,X5))) | ~r2_hidden(X5,X1))) | k3_tarski(X0) != X1))),
% 7.52/1.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f44,f47,f46,f45])).
% 7.52/1.48  
% 7.52/1.48  fof(f71,plain,(
% 7.52/1.48    ( ! [X0,X5,X1] : (r2_hidden(X5,sK3(X0,X5)) | ~r2_hidden(X5,X1) | k3_tarski(X0) != X1) )),
% 7.52/1.48    inference(cnf_transformation,[],[f48])).
% 7.52/1.48  
% 7.52/1.48  fof(f119,plain,(
% 7.52/1.48    ( ! [X0,X5] : (r2_hidden(X5,sK3(X0,X5)) | ~r2_hidden(X5,k3_tarski(X0))) )),
% 7.52/1.48    inference(equality_resolution,[],[f71])).
% 7.52/1.48  
% 7.52/1.48  fof(f15,axiom,(
% 7.52/1.48    ! [X0] : (! [X1] : (r2_hidden(X1,X0) => v3_ordinal1(X1)) => v3_ordinal1(k3_tarski(X0)))),
% 7.52/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.52/1.48  
% 7.52/1.48  fof(f32,plain,(
% 7.52/1.48    ! [X0] : (v3_ordinal1(k3_tarski(X0)) | ? [X1] : (~v3_ordinal1(X1) & r2_hidden(X1,X0)))),
% 7.52/1.48    inference(ennf_transformation,[],[f15])).
% 7.52/1.48  
% 7.52/1.48  fof(f55,plain,(
% 7.52/1.48    ! [X0] : (? [X1] : (~v3_ordinal1(X1) & r2_hidden(X1,X0)) => (~v3_ordinal1(sK4(X0)) & r2_hidden(sK4(X0),X0)))),
% 7.52/1.48    introduced(choice_axiom,[])).
% 7.52/1.48  
% 7.52/1.48  fof(f56,plain,(
% 7.52/1.48    ! [X0] : (v3_ordinal1(k3_tarski(X0)) | (~v3_ordinal1(sK4(X0)) & r2_hidden(sK4(X0),X0)))),
% 7.52/1.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f32,f55])).
% 7.52/1.48  
% 7.52/1.48  fof(f94,plain,(
% 7.52/1.48    ( ! [X0] : (v3_ordinal1(k3_tarski(X0)) | r2_hidden(sK4(X0),X0)) )),
% 7.52/1.48    inference(cnf_transformation,[],[f56])).
% 7.52/1.48  
% 7.52/1.48  fof(f1,axiom,(
% 7.52/1.48    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 7.52/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.52/1.48  
% 7.52/1.48  fof(f20,plain,(
% 7.52/1.48    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 7.52/1.48    inference(ennf_transformation,[],[f1])).
% 7.52/1.48  
% 7.52/1.48  fof(f37,plain,(
% 7.52/1.48    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 7.52/1.48    inference(nnf_transformation,[],[f20])).
% 7.52/1.48  
% 7.52/1.48  fof(f38,plain,(
% 7.52/1.48    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 7.52/1.48    inference(rectify,[],[f37])).
% 7.52/1.48  
% 7.52/1.48  fof(f39,plain,(
% 7.52/1.48    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 7.52/1.48    introduced(choice_axiom,[])).
% 7.52/1.48  
% 7.52/1.48  fof(f40,plain,(
% 7.52/1.48    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 7.52/1.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f38,f39])).
% 7.52/1.48  
% 7.52/1.48  fof(f65,plain,(
% 7.52/1.48    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,X1)) )),
% 7.52/1.48    inference(cnf_transformation,[],[f40])).
% 7.52/1.48  
% 7.52/1.48  fof(f18,conjecture,(
% 7.52/1.48    ! [X0] : (v3_ordinal1(X0) => (v4_ordinal1(X0) <=> ! [X1] : (v3_ordinal1(X1) => (r2_hidden(X1,X0) => r2_hidden(k1_ordinal1(X1),X0)))))),
% 7.52/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.52/1.48  
% 7.52/1.48  fof(f19,negated_conjecture,(
% 7.52/1.48    ~! [X0] : (v3_ordinal1(X0) => (v4_ordinal1(X0) <=> ! [X1] : (v3_ordinal1(X1) => (r2_hidden(X1,X0) => r2_hidden(k1_ordinal1(X1),X0)))))),
% 7.52/1.48    inference(negated_conjecture,[],[f18])).
% 7.52/1.48  
% 7.52/1.48  fof(f35,plain,(
% 7.52/1.48    ? [X0] : ((v4_ordinal1(X0) <~> ! [X1] : ((r2_hidden(k1_ordinal1(X1),X0) | ~r2_hidden(X1,X0)) | ~v3_ordinal1(X1))) & v3_ordinal1(X0))),
% 7.52/1.48    inference(ennf_transformation,[],[f19])).
% 7.52/1.48  
% 7.52/1.48  fof(f36,plain,(
% 7.52/1.48    ? [X0] : ((v4_ordinal1(X0) <~> ! [X1] : (r2_hidden(k1_ordinal1(X1),X0) | ~r2_hidden(X1,X0) | ~v3_ordinal1(X1))) & v3_ordinal1(X0))),
% 7.52/1.48    inference(flattening,[],[f35])).
% 7.52/1.48  
% 7.52/1.48  fof(f59,plain,(
% 7.52/1.48    ? [X0] : (((? [X1] : (~r2_hidden(k1_ordinal1(X1),X0) & r2_hidden(X1,X0) & v3_ordinal1(X1)) | ~v4_ordinal1(X0)) & (! [X1] : (r2_hidden(k1_ordinal1(X1),X0) | ~r2_hidden(X1,X0) | ~v3_ordinal1(X1)) | v4_ordinal1(X0))) & v3_ordinal1(X0))),
% 7.52/1.48    inference(nnf_transformation,[],[f36])).
% 7.52/1.48  
% 7.52/1.48  fof(f60,plain,(
% 7.52/1.48    ? [X0] : ((? [X1] : (~r2_hidden(k1_ordinal1(X1),X0) & r2_hidden(X1,X0) & v3_ordinal1(X1)) | ~v4_ordinal1(X0)) & (! [X1] : (r2_hidden(k1_ordinal1(X1),X0) | ~r2_hidden(X1,X0) | ~v3_ordinal1(X1)) | v4_ordinal1(X0)) & v3_ordinal1(X0))),
% 7.52/1.48    inference(flattening,[],[f59])).
% 7.52/1.48  
% 7.52/1.48  fof(f61,plain,(
% 7.52/1.48    ? [X0] : ((? [X1] : (~r2_hidden(k1_ordinal1(X1),X0) & r2_hidden(X1,X0) & v3_ordinal1(X1)) | ~v4_ordinal1(X0)) & (! [X2] : (r2_hidden(k1_ordinal1(X2),X0) | ~r2_hidden(X2,X0) | ~v3_ordinal1(X2)) | v4_ordinal1(X0)) & v3_ordinal1(X0))),
% 7.52/1.48    inference(rectify,[],[f60])).
% 7.52/1.48  
% 7.52/1.48  fof(f63,plain,(
% 7.52/1.48    ( ! [X0] : (? [X1] : (~r2_hidden(k1_ordinal1(X1),X0) & r2_hidden(X1,X0) & v3_ordinal1(X1)) => (~r2_hidden(k1_ordinal1(sK7),X0) & r2_hidden(sK7,X0) & v3_ordinal1(sK7))) )),
% 7.52/1.48    introduced(choice_axiom,[])).
% 7.52/1.48  
% 7.52/1.48  fof(f62,plain,(
% 7.52/1.48    ? [X0] : ((? [X1] : (~r2_hidden(k1_ordinal1(X1),X0) & r2_hidden(X1,X0) & v3_ordinal1(X1)) | ~v4_ordinal1(X0)) & (! [X2] : (r2_hidden(k1_ordinal1(X2),X0) | ~r2_hidden(X2,X0) | ~v3_ordinal1(X2)) | v4_ordinal1(X0)) & v3_ordinal1(X0)) => ((? [X1] : (~r2_hidden(k1_ordinal1(X1),sK6) & r2_hidden(X1,sK6) & v3_ordinal1(X1)) | ~v4_ordinal1(sK6)) & (! [X2] : (r2_hidden(k1_ordinal1(X2),sK6) | ~r2_hidden(X2,sK6) | ~v3_ordinal1(X2)) | v4_ordinal1(sK6)) & v3_ordinal1(sK6))),
% 7.52/1.48    introduced(choice_axiom,[])).
% 7.52/1.48  
% 7.52/1.48  fof(f64,plain,(
% 7.52/1.48    ((~r2_hidden(k1_ordinal1(sK7),sK6) & r2_hidden(sK7,sK6) & v3_ordinal1(sK7)) | ~v4_ordinal1(sK6)) & (! [X2] : (r2_hidden(k1_ordinal1(X2),sK6) | ~r2_hidden(X2,sK6) | ~v3_ordinal1(X2)) | v4_ordinal1(sK6)) & v3_ordinal1(sK6)),
% 7.52/1.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7])],[f61,f63,f62])).
% 7.52/1.48  
% 7.52/1.48  fof(f100,plain,(
% 7.52/1.48    ( ! [X2] : (r2_hidden(k1_ordinal1(X2),sK6) | ~r2_hidden(X2,sK6) | ~v3_ordinal1(X2) | v4_ordinal1(sK6)) )),
% 7.52/1.48    inference(cnf_transformation,[],[f64])).
% 7.52/1.48  
% 7.52/1.48  fof(f5,axiom,(
% 7.52/1.48    ! [X0] : k1_ordinal1(X0) = k2_xboole_0(X0,k1_tarski(X0))),
% 7.52/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.52/1.48  
% 7.52/1.48  fof(f78,plain,(
% 7.52/1.48    ( ! [X0] : (k1_ordinal1(X0) = k2_xboole_0(X0,k1_tarski(X0))) )),
% 7.52/1.48    inference(cnf_transformation,[],[f5])).
% 7.52/1.48  
% 7.52/1.48  fof(f114,plain,(
% 7.52/1.48    ( ! [X2] : (r2_hidden(k2_xboole_0(X2,k1_tarski(X2)),sK6) | ~r2_hidden(X2,sK6) | ~v3_ordinal1(X2) | v4_ordinal1(sK6)) )),
% 7.52/1.48    inference(definition_unfolding,[],[f100,f78])).
% 7.52/1.48  
% 7.52/1.48  fof(f73,plain,(
% 7.52/1.48    ( ! [X6,X0,X5,X1] : (r2_hidden(X5,X1) | ~r2_hidden(X6,X0) | ~r2_hidden(X5,X6) | k3_tarski(X0) != X1) )),
% 7.52/1.48    inference(cnf_transformation,[],[f48])).
% 7.52/1.48  
% 7.52/1.48  fof(f117,plain,(
% 7.52/1.48    ( ! [X6,X0,X5] : (r2_hidden(X5,k3_tarski(X0)) | ~r2_hidden(X6,X0) | ~r2_hidden(X5,X6)) )),
% 7.52/1.48    inference(equality_resolution,[],[f73])).
% 7.52/1.48  
% 7.52/1.48  fof(f6,axiom,(
% 7.52/1.48    ! [X0] : (v4_ordinal1(X0) <=> k3_tarski(X0) = X0)),
% 7.52/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.52/1.48  
% 7.52/1.48  fof(f49,plain,(
% 7.52/1.48    ! [X0] : ((v4_ordinal1(X0) | k3_tarski(X0) != X0) & (k3_tarski(X0) = X0 | ~v4_ordinal1(X0)))),
% 7.52/1.48    inference(nnf_transformation,[],[f6])).
% 7.52/1.48  
% 7.52/1.48  fof(f79,plain,(
% 7.52/1.48    ( ! [X0] : (k3_tarski(X0) = X0 | ~v4_ordinal1(X0)) )),
% 7.52/1.48    inference(cnf_transformation,[],[f49])).
% 7.52/1.48  
% 7.52/1.48  fof(f80,plain,(
% 7.52/1.48    ( ! [X0] : (v4_ordinal1(X0) | k3_tarski(X0) != X0) )),
% 7.52/1.48    inference(cnf_transformation,[],[f49])).
% 7.52/1.48  
% 7.52/1.48  fof(f9,axiom,(
% 7.52/1.48    ! [X0,X1] : (r2_hidden(X0,k1_ordinal1(X1)) <=> (X0 = X1 | r2_hidden(X0,X1)))),
% 7.52/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.52/1.48  
% 7.52/1.48  fof(f51,plain,(
% 7.52/1.48    ! [X0,X1] : ((r2_hidden(X0,k1_ordinal1(X1)) | (X0 != X1 & ~r2_hidden(X0,X1))) & ((X0 = X1 | r2_hidden(X0,X1)) | ~r2_hidden(X0,k1_ordinal1(X1))))),
% 7.52/1.48    inference(nnf_transformation,[],[f9])).
% 7.52/1.48  
% 7.52/1.48  fof(f52,plain,(
% 7.52/1.48    ! [X0,X1] : ((r2_hidden(X0,k1_ordinal1(X1)) | (X0 != X1 & ~r2_hidden(X0,X1))) & (X0 = X1 | r2_hidden(X0,X1) | ~r2_hidden(X0,k1_ordinal1(X1))))),
% 7.52/1.48    inference(flattening,[],[f51])).
% 7.52/1.48  
% 7.52/1.48  fof(f86,plain,(
% 7.52/1.48    ( ! [X0,X1] : (r2_hidden(X0,k1_ordinal1(X1)) | X0 != X1) )),
% 7.52/1.48    inference(cnf_transformation,[],[f52])).
% 7.52/1.48  
% 7.52/1.48  fof(f105,plain,(
% 7.52/1.48    ( ! [X0,X1] : (r2_hidden(X0,k2_xboole_0(X1,k1_tarski(X1))) | X0 != X1) )),
% 7.52/1.48    inference(definition_unfolding,[],[f86,f78])).
% 7.52/1.48  
% 7.52/1.48  fof(f120,plain,(
% 7.52/1.48    ( ! [X1] : (r2_hidden(X1,k2_xboole_0(X1,k1_tarski(X1)))) )),
% 7.52/1.48    inference(equality_resolution,[],[f105])).
% 7.52/1.48  
% 7.52/1.48  fof(f10,axiom,(
% 7.52/1.48    ! [X0,X1] : (v3_ordinal1(X1) => (r2_hidden(X0,X1) => v3_ordinal1(X0)))),
% 7.52/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.52/1.48  
% 7.52/1.48  fof(f25,plain,(
% 7.52/1.48    ! [X0,X1] : ((v3_ordinal1(X0) | ~r2_hidden(X0,X1)) | ~v3_ordinal1(X1))),
% 7.52/1.48    inference(ennf_transformation,[],[f10])).
% 7.52/1.48  
% 7.52/1.48  fof(f26,plain,(
% 7.52/1.48    ! [X0,X1] : (v3_ordinal1(X0) | ~r2_hidden(X0,X1) | ~v3_ordinal1(X1))),
% 7.52/1.48    inference(flattening,[],[f25])).
% 7.52/1.48  
% 7.52/1.48  fof(f87,plain,(
% 7.52/1.48    ( ! [X0,X1] : (v3_ordinal1(X0) | ~r2_hidden(X0,X1) | ~v3_ordinal1(X1)) )),
% 7.52/1.48    inference(cnf_transformation,[],[f26])).
% 7.52/1.48  
% 7.52/1.48  fof(f12,axiom,(
% 7.52/1.48    ! [X0] : (v3_ordinal1(X0) => v3_ordinal1(k1_ordinal1(X0)))),
% 7.52/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.52/1.48  
% 7.52/1.48  fof(f29,plain,(
% 7.52/1.48    ! [X0] : (v3_ordinal1(k1_ordinal1(X0)) | ~v3_ordinal1(X0))),
% 7.52/1.48    inference(ennf_transformation,[],[f12])).
% 7.52/1.48  
% 7.52/1.48  fof(f89,plain,(
% 7.52/1.48    ( ! [X0] : (v3_ordinal1(k1_ordinal1(X0)) | ~v3_ordinal1(X0)) )),
% 7.52/1.48    inference(cnf_transformation,[],[f29])).
% 7.52/1.48  
% 7.52/1.48  fof(f108,plain,(
% 7.52/1.48    ( ! [X0] : (v3_ordinal1(k2_xboole_0(X0,k1_tarski(X0))) | ~v3_ordinal1(X0)) )),
% 7.52/1.48    inference(definition_unfolding,[],[f89,f78])).
% 7.52/1.48  
% 7.52/1.48  fof(f99,plain,(
% 7.52/1.48    v3_ordinal1(sK6)),
% 7.52/1.48    inference(cnf_transformation,[],[f64])).
% 7.52/1.48  
% 7.52/1.48  fof(f95,plain,(
% 7.52/1.48    ( ! [X0] : (v3_ordinal1(k3_tarski(X0)) | ~v3_ordinal1(sK4(X0))) )),
% 7.52/1.48    inference(cnf_transformation,[],[f56])).
% 7.52/1.48  
% 7.52/1.48  fof(f72,plain,(
% 7.52/1.48    ( ! [X0,X5,X1] : (r2_hidden(sK3(X0,X5),X0) | ~r2_hidden(X5,X1) | k3_tarski(X0) != X1) )),
% 7.52/1.48    inference(cnf_transformation,[],[f48])).
% 7.52/1.48  
% 7.52/1.48  fof(f118,plain,(
% 7.52/1.48    ( ! [X0,X5] : (r2_hidden(sK3(X0,X5),X0) | ~r2_hidden(X5,k3_tarski(X0))) )),
% 7.52/1.48    inference(equality_resolution,[],[f72])).
% 7.52/1.48  
% 7.52/1.48  fof(f17,axiom,(
% 7.52/1.48    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 7.52/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.52/1.48  
% 7.52/1.48  fof(f34,plain,(
% 7.52/1.48    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 7.52/1.48    inference(ennf_transformation,[],[f17])).
% 7.52/1.48  
% 7.52/1.48  fof(f98,plain,(
% 7.52/1.48    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1)) )),
% 7.52/1.48    inference(cnf_transformation,[],[f34])).
% 7.52/1.48  
% 7.52/1.48  fof(f7,axiom,(
% 7.52/1.48    ! [X0,X1] : ((v3_ordinal1(X1) & v3_ordinal1(X0)) => (r1_ordinal1(X0,X1) <=> r1_tarski(X0,X1)))),
% 7.52/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.52/1.48  
% 7.52/1.48  fof(f23,plain,(
% 7.52/1.48    ! [X0,X1] : ((r1_ordinal1(X0,X1) <=> r1_tarski(X0,X1)) | (~v3_ordinal1(X1) | ~v3_ordinal1(X0)))),
% 7.52/1.48    inference(ennf_transformation,[],[f7])).
% 7.52/1.48  
% 7.52/1.48  fof(f24,plain,(
% 7.52/1.48    ! [X0,X1] : ((r1_ordinal1(X0,X1) <=> r1_tarski(X0,X1)) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0))),
% 7.52/1.48    inference(flattening,[],[f23])).
% 7.52/1.48  
% 7.52/1.48  fof(f50,plain,(
% 7.52/1.48    ! [X0,X1] : (((r1_ordinal1(X0,X1) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~r1_ordinal1(X0,X1))) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0))),
% 7.52/1.48    inference(nnf_transformation,[],[f24])).
% 7.52/1.48  
% 7.52/1.48  fof(f81,plain,(
% 7.52/1.48    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r1_ordinal1(X0,X1) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0)) )),
% 7.52/1.48    inference(cnf_transformation,[],[f50])).
% 7.52/1.48  
% 7.52/1.48  fof(f11,axiom,(
% 7.52/1.48    ! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => ~(~r2_hidden(X1,X0) & X0 != X1 & ~r2_hidden(X0,X1))))),
% 7.52/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.52/1.48  
% 7.52/1.48  fof(f27,plain,(
% 7.52/1.48    ! [X0] : (! [X1] : ((r2_hidden(X1,X0) | X0 = X1 | r2_hidden(X0,X1)) | ~v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 7.52/1.48    inference(ennf_transformation,[],[f11])).
% 7.52/1.48  
% 7.52/1.48  fof(f28,plain,(
% 7.52/1.48    ! [X0] : (! [X1] : (r2_hidden(X1,X0) | X0 = X1 | r2_hidden(X0,X1) | ~v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 7.52/1.48    inference(flattening,[],[f27])).
% 7.52/1.48  
% 7.52/1.48  fof(f88,plain,(
% 7.52/1.48    ( ! [X0,X1] : (r2_hidden(X1,X0) | X0 = X1 | r2_hidden(X0,X1) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0)) )),
% 7.52/1.48    inference(cnf_transformation,[],[f28])).
% 7.52/1.48  
% 7.52/1.48  fof(f85,plain,(
% 7.52/1.48    ( ! [X0,X1] : (r2_hidden(X0,k1_ordinal1(X1)) | ~r2_hidden(X0,X1)) )),
% 7.52/1.48    inference(cnf_transformation,[],[f52])).
% 7.52/1.48  
% 7.52/1.48  fof(f106,plain,(
% 7.52/1.48    ( ! [X0,X1] : (r2_hidden(X0,k2_xboole_0(X1,k1_tarski(X1))) | ~r2_hidden(X0,X1)) )),
% 7.52/1.48    inference(definition_unfolding,[],[f85,f78])).
% 7.52/1.48  
% 7.52/1.48  fof(f2,axiom,(
% 7.52/1.48    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 7.52/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.52/1.48  
% 7.52/1.48  fof(f41,plain,(
% 7.52/1.48    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 7.52/1.48    inference(nnf_transformation,[],[f2])).
% 7.52/1.48  
% 7.52/1.48  fof(f42,plain,(
% 7.52/1.48    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 7.52/1.48    inference(flattening,[],[f41])).
% 7.52/1.48  
% 7.52/1.48  fof(f68,plain,(
% 7.52/1.48    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 7.52/1.48    inference(cnf_transformation,[],[f42])).
% 7.52/1.48  
% 7.52/1.48  fof(f116,plain,(
% 7.52/1.48    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 7.52/1.48    inference(equality_resolution,[],[f68])).
% 7.52/1.48  
% 7.52/1.48  fof(f14,axiom,(
% 7.52/1.48    ! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => (r2_hidden(X0,k1_ordinal1(X1)) <=> r1_ordinal1(X0,X1))))),
% 7.52/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.52/1.48  
% 7.52/1.48  fof(f31,plain,(
% 7.52/1.48    ! [X0] : (! [X1] : ((r2_hidden(X0,k1_ordinal1(X1)) <=> r1_ordinal1(X0,X1)) | ~v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 7.52/1.48    inference(ennf_transformation,[],[f14])).
% 7.52/1.48  
% 7.52/1.48  fof(f54,plain,(
% 7.52/1.48    ! [X0] : (! [X1] : (((r2_hidden(X0,k1_ordinal1(X1)) | ~r1_ordinal1(X0,X1)) & (r1_ordinal1(X0,X1) | ~r2_hidden(X0,k1_ordinal1(X1)))) | ~v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 7.52/1.48    inference(nnf_transformation,[],[f31])).
% 7.52/1.48  
% 7.52/1.48  fof(f92,plain,(
% 7.52/1.48    ( ! [X0,X1] : (r1_ordinal1(X0,X1) | ~r2_hidden(X0,k1_ordinal1(X1)) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0)) )),
% 7.52/1.48    inference(cnf_transformation,[],[f54])).
% 7.52/1.48  
% 7.52/1.48  fof(f112,plain,(
% 7.52/1.48    ( ! [X0,X1] : (r1_ordinal1(X0,X1) | ~r2_hidden(X0,k2_xboole_0(X1,k1_tarski(X1))) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0)) )),
% 7.52/1.48    inference(definition_unfolding,[],[f92,f78])).
% 7.52/1.48  
% 7.52/1.48  fof(f103,plain,(
% 7.52/1.48    ~r2_hidden(k1_ordinal1(sK7),sK6) | ~v4_ordinal1(sK6)),
% 7.52/1.48    inference(cnf_transformation,[],[f64])).
% 7.52/1.48  
% 7.52/1.48  fof(f113,plain,(
% 7.52/1.48    ~r2_hidden(k2_xboole_0(sK7,k1_tarski(sK7)),sK6) | ~v4_ordinal1(sK6)),
% 7.52/1.48    inference(definition_unfolding,[],[f103,f78])).
% 7.52/1.48  
% 7.52/1.48  fof(f101,plain,(
% 7.52/1.48    v3_ordinal1(sK7) | ~v4_ordinal1(sK6)),
% 7.52/1.48    inference(cnf_transformation,[],[f64])).
% 7.52/1.48  
% 7.52/1.48  fof(f102,plain,(
% 7.52/1.48    r2_hidden(sK7,sK6) | ~v4_ordinal1(sK6)),
% 7.52/1.48    inference(cnf_transformation,[],[f64])).
% 7.52/1.48  
% 7.52/1.48  fof(f13,axiom,(
% 7.52/1.48    ! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => (r2_hidden(X0,X1) <=> r1_ordinal1(k1_ordinal1(X0),X1))))),
% 7.52/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.52/1.48  
% 7.52/1.48  fof(f30,plain,(
% 7.52/1.48    ! [X0] : (! [X1] : ((r2_hidden(X0,X1) <=> r1_ordinal1(k1_ordinal1(X0),X1)) | ~v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 7.52/1.48    inference(ennf_transformation,[],[f13])).
% 7.52/1.48  
% 7.52/1.48  fof(f53,plain,(
% 7.52/1.48    ! [X0] : (! [X1] : (((r2_hidden(X0,X1) | ~r1_ordinal1(k1_ordinal1(X0),X1)) & (r1_ordinal1(k1_ordinal1(X0),X1) | ~r2_hidden(X0,X1))) | ~v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 7.52/1.48    inference(nnf_transformation,[],[f30])).
% 7.52/1.48  
% 7.52/1.48  fof(f90,plain,(
% 7.52/1.48    ( ! [X0,X1] : (r1_ordinal1(k1_ordinal1(X0),X1) | ~r2_hidden(X0,X1) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0)) )),
% 7.52/1.48    inference(cnf_transformation,[],[f53])).
% 7.52/1.48  
% 7.52/1.48  fof(f110,plain,(
% 7.52/1.48    ( ! [X0,X1] : (r1_ordinal1(k2_xboole_0(X0,k1_tarski(X0)),X1) | ~r2_hidden(X0,X1) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0)) )),
% 7.52/1.48    inference(definition_unfolding,[],[f90,f78])).
% 7.52/1.48  
% 7.52/1.48  cnf(c_11,plain,
% 7.52/1.48      ( r2_hidden(X0,sK3(X1,X0)) | ~ r2_hidden(X0,k3_tarski(X1)) ),
% 7.52/1.48      inference(cnf_transformation,[],[f119]) ).
% 7.52/1.48  
% 7.52/1.48  cnf(c_1823,plain,
% 7.52/1.48      ( r2_hidden(X0,sK3(X1,X0)) = iProver_top
% 7.52/1.48      | r2_hidden(X0,k3_tarski(X1)) != iProver_top ),
% 7.52/1.48      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 7.52/1.48  
% 7.52/1.48  cnf(c_29,plain,
% 7.52/1.48      ( r2_hidden(sK4(X0),X0) | v3_ordinal1(k3_tarski(X0)) ),
% 7.52/1.48      inference(cnf_transformation,[],[f94]) ).
% 7.52/1.48  
% 7.52/1.48  cnf(c_1807,plain,
% 7.52/1.48      ( r2_hidden(sK4(X0),X0) = iProver_top
% 7.52/1.48      | v3_ordinal1(k3_tarski(X0)) = iProver_top ),
% 7.52/1.48      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 7.52/1.48  
% 7.52/1.48  cnf(c_2,plain,
% 7.52/1.48      ( ~ r2_hidden(X0,X1) | r2_hidden(X0,X2) | ~ r1_tarski(X1,X2) ),
% 7.52/1.48      inference(cnf_transformation,[],[f65]) ).
% 7.52/1.48  
% 7.52/1.48  cnf(c_1831,plain,
% 7.52/1.48      ( r2_hidden(X0,X1) != iProver_top
% 7.52/1.48      | r2_hidden(X0,X2) = iProver_top
% 7.52/1.48      | r1_tarski(X1,X2) != iProver_top ),
% 7.52/1.48      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 7.52/1.48  
% 7.52/1.48  cnf(c_4579,plain,
% 7.52/1.48      ( r2_hidden(sK4(X0),X1) = iProver_top
% 7.52/1.48      | r1_tarski(X0,X1) != iProver_top
% 7.52/1.48      | v3_ordinal1(k3_tarski(X0)) = iProver_top ),
% 7.52/1.48      inference(superposition,[status(thm)],[c_1807,c_1831]) ).
% 7.52/1.48  
% 7.52/1.48  cnf(c_36,negated_conjecture,
% 7.52/1.48      ( ~ r2_hidden(X0,sK6)
% 7.52/1.48      | r2_hidden(k2_xboole_0(X0,k1_tarski(X0)),sK6)
% 7.52/1.48      | v4_ordinal1(sK6)
% 7.52/1.48      | ~ v3_ordinal1(X0) ),
% 7.52/1.48      inference(cnf_transformation,[],[f114]) ).
% 7.52/1.48  
% 7.52/1.48  cnf(c_1800,plain,
% 7.52/1.48      ( r2_hidden(X0,sK6) != iProver_top
% 7.52/1.48      | r2_hidden(k2_xboole_0(X0,k1_tarski(X0)),sK6) = iProver_top
% 7.52/1.48      | v4_ordinal1(sK6) = iProver_top
% 7.52/1.48      | v3_ordinal1(X0) != iProver_top ),
% 7.52/1.48      inference(predicate_to_equality,[status(thm)],[c_36]) ).
% 7.52/1.48  
% 7.52/1.48  cnf(c_9,plain,
% 7.52/1.48      ( ~ r2_hidden(X0,X1)
% 7.52/1.48      | ~ r2_hidden(X2,X0)
% 7.52/1.48      | r2_hidden(X2,k3_tarski(X1)) ),
% 7.52/1.48      inference(cnf_transformation,[],[f117]) ).
% 7.52/1.48  
% 7.52/1.48  cnf(c_1825,plain,
% 7.52/1.48      ( r2_hidden(X0,X1) != iProver_top
% 7.52/1.48      | r2_hidden(X2,X0) != iProver_top
% 7.52/1.48      | r2_hidden(X2,k3_tarski(X1)) = iProver_top ),
% 7.52/1.48      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 7.52/1.48  
% 7.52/1.48  cnf(c_4781,plain,
% 7.52/1.48      ( r2_hidden(X0,k2_xboole_0(X1,k1_tarski(X1))) != iProver_top
% 7.52/1.48      | r2_hidden(X0,k3_tarski(sK6)) = iProver_top
% 7.52/1.48      | r2_hidden(X1,sK6) != iProver_top
% 7.52/1.48      | v4_ordinal1(sK6) = iProver_top
% 7.52/1.48      | v3_ordinal1(X1) != iProver_top ),
% 7.52/1.48      inference(superposition,[status(thm)],[c_1800,c_1825]) ).
% 7.52/1.48  
% 7.52/1.48  cnf(c_19690,plain,
% 7.52/1.48      ( r2_hidden(X0,sK6) != iProver_top
% 7.52/1.48      | r2_hidden(sK4(X1),k3_tarski(sK6)) = iProver_top
% 7.52/1.48      | r1_tarski(X1,k2_xboole_0(X0,k1_tarski(X0))) != iProver_top
% 7.52/1.48      | v4_ordinal1(sK6) = iProver_top
% 7.52/1.48      | v3_ordinal1(X0) != iProver_top
% 7.52/1.48      | v3_ordinal1(k3_tarski(X1)) = iProver_top ),
% 7.52/1.48      inference(superposition,[status(thm)],[c_4579,c_4781]) ).
% 7.52/1.48  
% 7.52/1.48  cnf(c_14,plain,
% 7.52/1.48      ( ~ v4_ordinal1(X0) | k3_tarski(X0) = X0 ),
% 7.52/1.48      inference(cnf_transformation,[],[f79]) ).
% 7.52/1.48  
% 7.52/1.48  cnf(c_96,plain,
% 7.52/1.48      ( ~ v4_ordinal1(sK6) | k3_tarski(sK6) = sK6 ),
% 7.52/1.48      inference(instantiation,[status(thm)],[c_14]) ).
% 7.52/1.48  
% 7.52/1.48  cnf(c_13,plain,
% 7.52/1.48      ( v4_ordinal1(X0) | k3_tarski(X0) != X0 ),
% 7.52/1.48      inference(cnf_transformation,[],[f80]) ).
% 7.52/1.48  
% 7.52/1.48  cnf(c_98,plain,
% 7.52/1.48      ( k3_tarski(X0) != X0 | v4_ordinal1(X0) = iProver_top ),
% 7.52/1.48      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 7.52/1.48  
% 7.52/1.48  cnf(c_100,plain,
% 7.52/1.48      ( k3_tarski(sK6) != sK6 | v4_ordinal1(sK6) = iProver_top ),
% 7.52/1.48      inference(instantiation,[status(thm)],[c_98]) ).
% 7.52/1.48  
% 7.52/1.48  cnf(c_18,plain,
% 7.52/1.48      ( r2_hidden(X0,k2_xboole_0(X0,k1_tarski(X0))) ),
% 7.52/1.48      inference(cnf_transformation,[],[f120]) ).
% 7.52/1.48  
% 7.52/1.48  cnf(c_3534,plain,
% 7.52/1.48      ( r2_hidden(X0,k3_tarski(X1))
% 7.52/1.48      | ~ r2_hidden(k2_xboole_0(X0,k1_tarski(X0)),X1) ),
% 7.52/1.48      inference(resolution,[status(thm)],[c_9,c_18]) ).
% 7.52/1.48  
% 7.52/1.48  cnf(c_13081,plain,
% 7.52/1.48      ( r2_hidden(X0,k3_tarski(sK6))
% 7.52/1.48      | ~ r2_hidden(X0,sK6)
% 7.52/1.48      | v4_ordinal1(sK6)
% 7.52/1.48      | ~ v3_ordinal1(X0) ),
% 7.52/1.48      inference(resolution,[status(thm)],[c_3534,c_36]) ).
% 7.52/1.48  
% 7.52/1.48  cnf(c_13598,plain,
% 7.52/1.48      ( r2_hidden(X0,k3_tarski(k3_tarski(sK6)))
% 7.52/1.48      | ~ r2_hidden(k2_xboole_0(X0,k1_tarski(X0)),sK6)
% 7.52/1.48      | v4_ordinal1(sK6)
% 7.52/1.48      | ~ v3_ordinal1(k2_xboole_0(X0,k1_tarski(X0))) ),
% 7.52/1.48      inference(resolution,[status(thm)],[c_13081,c_3534]) ).
% 7.52/1.48  
% 7.52/1.48  cnf(c_14420,plain,
% 7.52/1.48      ( r2_hidden(X0,k3_tarski(k3_tarski(sK6)))
% 7.52/1.48      | ~ r2_hidden(X0,sK6)
% 7.52/1.48      | v4_ordinal1(sK6)
% 7.52/1.48      | ~ v3_ordinal1(X0)
% 7.52/1.48      | ~ v3_ordinal1(k2_xboole_0(X0,k1_tarski(X0))) ),
% 7.52/1.48      inference(resolution,[status(thm)],[c_13598,c_36]) ).
% 7.52/1.48  
% 7.52/1.48  cnf(c_21,plain,
% 7.52/1.48      ( ~ r2_hidden(X0,X1) | ~ v3_ordinal1(X1) | v3_ordinal1(X0) ),
% 7.52/1.48      inference(cnf_transformation,[],[f87]) ).
% 7.52/1.48  
% 7.52/1.48  cnf(c_2706,plain,
% 7.52/1.48      ( v3_ordinal1(X0) | ~ v3_ordinal1(k2_xboole_0(X0,k1_tarski(X0))) ),
% 7.52/1.48      inference(resolution,[status(thm)],[c_21,c_18]) ).
% 7.52/1.48  
% 7.52/1.48  cnf(c_14423,plain,
% 7.52/1.48      ( v4_ordinal1(sK6)
% 7.52/1.48      | ~ r2_hidden(X0,sK6)
% 7.52/1.48      | r2_hidden(X0,k3_tarski(k3_tarski(sK6)))
% 7.52/1.48      | ~ v3_ordinal1(k2_xboole_0(X0,k1_tarski(X0))) ),
% 7.52/1.48      inference(global_propositional_subsumption,
% 7.52/1.48                [status(thm)],
% 7.52/1.48                [c_14420,c_2706]) ).
% 7.52/1.48  
% 7.52/1.48  cnf(c_14424,plain,
% 7.52/1.48      ( r2_hidden(X0,k3_tarski(k3_tarski(sK6)))
% 7.52/1.48      | ~ r2_hidden(X0,sK6)
% 7.52/1.48      | v4_ordinal1(sK6)
% 7.52/1.48      | ~ v3_ordinal1(k2_xboole_0(X0,k1_tarski(X0))) ),
% 7.52/1.48      inference(renaming,[status(thm)],[c_14423]) ).
% 7.52/1.48  
% 7.52/1.48  cnf(c_23,plain,
% 7.52/1.48      ( ~ v3_ordinal1(X0) | v3_ordinal1(k2_xboole_0(X0,k1_tarski(X0))) ),
% 7.52/1.48      inference(cnf_transformation,[],[f108]) ).
% 7.52/1.48  
% 7.52/1.48  cnf(c_14600,plain,
% 7.52/1.48      ( r2_hidden(X0,k3_tarski(k3_tarski(sK6)))
% 7.52/1.48      | ~ r2_hidden(X0,sK6)
% 7.52/1.48      | v4_ordinal1(sK6)
% 7.52/1.48      | ~ v3_ordinal1(X0) ),
% 7.52/1.48      inference(resolution,[status(thm)],[c_14424,c_23]) ).
% 7.52/1.48  
% 7.52/1.48  cnf(c_14631,plain,
% 7.52/1.48      ( r2_hidden(X0,k3_tarski(k3_tarski(k3_tarski(sK6))))
% 7.52/1.48      | ~ r2_hidden(k2_xboole_0(X0,k1_tarski(X0)),sK6)
% 7.52/1.48      | v4_ordinal1(sK6)
% 7.52/1.48      | ~ v3_ordinal1(k2_xboole_0(X0,k1_tarski(X0))) ),
% 7.52/1.48      inference(resolution,[status(thm)],[c_14600,c_3534]) ).
% 7.52/1.48  
% 7.52/1.48  cnf(c_19921,plain,
% 7.52/1.48      ( r2_hidden(X0,k3_tarski(k3_tarski(k3_tarski(sK6))))
% 7.52/1.48      | ~ r2_hidden(X0,sK6)
% 7.52/1.48      | v4_ordinal1(sK6)
% 7.52/1.48      | ~ v3_ordinal1(X0)
% 7.52/1.48      | ~ v3_ordinal1(k2_xboole_0(X0,k1_tarski(X0))) ),
% 7.52/1.48      inference(resolution,[status(thm)],[c_14631,c_36]) ).
% 7.52/1.48  
% 7.52/1.48  cnf(c_37,negated_conjecture,
% 7.52/1.48      ( v3_ordinal1(sK6) ),
% 7.52/1.48      inference(cnf_transformation,[],[f99]) ).
% 7.52/1.48  
% 7.52/1.48  cnf(c_99,plain,
% 7.52/1.48      ( v4_ordinal1(sK6) | k3_tarski(sK6) != sK6 ),
% 7.52/1.48      inference(instantiation,[status(thm)],[c_13]) ).
% 7.52/1.48  
% 7.52/1.48  cnf(c_105,plain,
% 7.52/1.48      ( r2_hidden(sK6,sK3(sK6,sK6)) | ~ r2_hidden(sK6,k3_tarski(sK6)) ),
% 7.52/1.48      inference(instantiation,[status(thm)],[c_11]) ).
% 7.52/1.48  
% 7.52/1.48  cnf(c_2708,plain,
% 7.52/1.48      ( ~ v3_ordinal1(X0)
% 7.52/1.48      | v3_ordinal1(sK4(X0))
% 7.52/1.48      | v3_ordinal1(k3_tarski(X0)) ),
% 7.52/1.48      inference(resolution,[status(thm)],[c_21,c_29]) ).
% 7.52/1.48  
% 7.52/1.48  cnf(c_28,plain,
% 7.52/1.48      ( ~ v3_ordinal1(sK4(X0)) | v3_ordinal1(k3_tarski(X0)) ),
% 7.52/1.48      inference(cnf_transformation,[],[f95]) ).
% 7.52/1.48  
% 7.52/1.48  cnf(c_2937,plain,
% 7.52/1.48      ( ~ v3_ordinal1(X0) | v3_ordinal1(k3_tarski(X0)) ),
% 7.52/1.48      inference(global_propositional_subsumption,
% 7.52/1.48                [status(thm)],
% 7.52/1.48                [c_2708,c_28]) ).
% 7.52/1.48  
% 7.52/1.48  cnf(c_2940,plain,
% 7.52/1.48      ( v3_ordinal1(k3_tarski(sK6)) | ~ v3_ordinal1(sK6) ),
% 7.52/1.48      inference(instantiation,[status(thm)],[c_2937]) ).
% 7.52/1.48  
% 7.52/1.48  cnf(c_10,plain,
% 7.52/1.48      ( ~ r2_hidden(X0,k3_tarski(X1)) | r2_hidden(sK3(X1,X0),X1) ),
% 7.52/1.48      inference(cnf_transformation,[],[f118]) ).
% 7.52/1.48  
% 7.52/1.48  cnf(c_32,plain,
% 7.52/1.48      ( ~ r2_hidden(X0,X1) | ~ r1_tarski(X1,X0) ),
% 7.52/1.48      inference(cnf_transformation,[],[f98]) ).
% 7.52/1.48  
% 7.52/1.48  cnf(c_2961,plain,
% 7.52/1.48      ( ~ r2_hidden(X0,k3_tarski(X1)) | ~ r1_tarski(X1,sK3(X1,X0)) ),
% 7.52/1.48      inference(resolution,[status(thm)],[c_10,c_32]) ).
% 7.52/1.48  
% 7.52/1.48  cnf(c_2967,plain,
% 7.52/1.48      ( ~ r2_hidden(sK6,k3_tarski(sK6)) | ~ r1_tarski(sK6,sK3(sK6,sK6)) ),
% 7.52/1.48      inference(instantiation,[status(thm)],[c_2961]) ).
% 7.52/1.48  
% 7.52/1.48  cnf(c_16,plain,
% 7.52/1.48      ( ~ r1_ordinal1(X0,X1)
% 7.52/1.48      | r1_tarski(X0,X1)
% 7.52/1.48      | ~ v3_ordinal1(X1)
% 7.52/1.48      | ~ v3_ordinal1(X0) ),
% 7.52/1.48      inference(cnf_transformation,[],[f81]) ).
% 7.52/1.48  
% 7.52/1.48  cnf(c_3702,plain,
% 7.52/1.48      ( ~ r1_ordinal1(X0,sK3(X0,X1))
% 7.52/1.48      | r1_tarski(X0,sK3(X0,X1))
% 7.52/1.48      | ~ v3_ordinal1(X0)
% 7.52/1.48      | ~ v3_ordinal1(sK3(X0,X1)) ),
% 7.52/1.48      inference(instantiation,[status(thm)],[c_16]) ).
% 7.52/1.48  
% 7.52/1.48  cnf(c_3714,plain,
% 7.52/1.48      ( ~ r1_ordinal1(sK6,sK3(sK6,sK6))
% 7.52/1.48      | r1_tarski(sK6,sK3(sK6,sK6))
% 7.52/1.48      | ~ v3_ordinal1(sK3(sK6,sK6))
% 7.52/1.48      | ~ v3_ordinal1(sK6) ),
% 7.52/1.48      inference(instantiation,[status(thm)],[c_3702]) ).
% 7.52/1.48  
% 7.52/1.48  cnf(c_22,plain,
% 7.52/1.48      ( r2_hidden(X0,X1)
% 7.52/1.48      | r2_hidden(X1,X0)
% 7.52/1.48      | ~ v3_ordinal1(X1)
% 7.52/1.48      | ~ v3_ordinal1(X0)
% 7.52/1.48      | X1 = X0 ),
% 7.52/1.48      inference(cnf_transformation,[],[f88]) ).
% 7.52/1.48  
% 7.52/1.48  cnf(c_6997,plain,
% 7.52/1.48      ( r2_hidden(X0,k3_tarski(X0))
% 7.52/1.48      | r2_hidden(k3_tarski(X0),X0)
% 7.52/1.48      | v4_ordinal1(X0)
% 7.52/1.48      | ~ v3_ordinal1(X0)
% 7.52/1.48      | ~ v3_ordinal1(k3_tarski(X0)) ),
% 7.52/1.48      inference(resolution,[status(thm)],[c_22,c_13]) ).
% 7.52/1.48  
% 7.52/1.48  cnf(c_6999,plain,
% 7.52/1.48      ( r2_hidden(k3_tarski(sK6),sK6)
% 7.52/1.48      | r2_hidden(sK6,k3_tarski(sK6))
% 7.52/1.48      | v4_ordinal1(sK6)
% 7.52/1.48      | ~ v3_ordinal1(k3_tarski(sK6))
% 7.52/1.48      | ~ v3_ordinal1(sK6) ),
% 7.52/1.48      inference(instantiation,[status(thm)],[c_6997]) ).
% 7.52/1.48  
% 7.52/1.48  cnf(c_1813,plain,
% 7.52/1.48      ( X0 = X1
% 7.52/1.48      | r2_hidden(X1,X0) = iProver_top
% 7.52/1.48      | r2_hidden(X0,X1) = iProver_top
% 7.52/1.48      | v3_ordinal1(X1) != iProver_top
% 7.52/1.48      | v3_ordinal1(X0) != iProver_top ),
% 7.52/1.48      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 7.52/1.48  
% 7.52/1.48  cnf(c_1824,plain,
% 7.52/1.48      ( r2_hidden(X0,k3_tarski(X1)) != iProver_top
% 7.52/1.48      | r2_hidden(sK3(X1,X0),X1) = iProver_top ),
% 7.52/1.48      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 7.52/1.48  
% 7.52/1.48  cnf(c_1814,plain,
% 7.52/1.48      ( r2_hidden(X0,X1) != iProver_top
% 7.52/1.48      | v3_ordinal1(X1) != iProver_top
% 7.52/1.48      | v3_ordinal1(X0) = iProver_top ),
% 7.52/1.48      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 7.52/1.48  
% 7.52/1.48  cnf(c_3603,plain,
% 7.52/1.48      ( r2_hidden(X0,k3_tarski(X1)) != iProver_top
% 7.52/1.48      | v3_ordinal1(X1) != iProver_top
% 7.52/1.48      | v3_ordinal1(sK3(X1,X0)) = iProver_top ),
% 7.52/1.48      inference(superposition,[status(thm)],[c_1824,c_1814]) ).
% 7.52/1.48  
% 7.52/1.48  cnf(c_15776,plain,
% 7.52/1.48      ( k3_tarski(X0) = X1
% 7.52/1.48      | r2_hidden(k3_tarski(X0),X1) = iProver_top
% 7.52/1.48      | v3_ordinal1(X0) != iProver_top
% 7.52/1.48      | v3_ordinal1(X1) != iProver_top
% 7.52/1.48      | v3_ordinal1(sK3(X0,X1)) = iProver_top
% 7.52/1.48      | v3_ordinal1(k3_tarski(X0)) != iProver_top ),
% 7.52/1.48      inference(superposition,[status(thm)],[c_1813,c_3603]) ).
% 7.52/1.48  
% 7.52/1.48  cnf(c_16054,plain,
% 7.52/1.48      ( r2_hidden(k3_tarski(X0),X1)
% 7.52/1.48      | ~ v3_ordinal1(X1)
% 7.52/1.48      | ~ v3_ordinal1(X0)
% 7.52/1.48      | v3_ordinal1(sK3(X0,X1))
% 7.52/1.48      | ~ v3_ordinal1(k3_tarski(X0))
% 7.52/1.48      | k3_tarski(X0) = X1 ),
% 7.52/1.48      inference(predicate_to_equality_rev,[status(thm)],[c_15776]) ).
% 7.52/1.48  
% 7.52/1.48  cnf(c_16056,plain,
% 7.52/1.48      ( r2_hidden(k3_tarski(sK6),sK6)
% 7.52/1.48      | v3_ordinal1(sK3(sK6,sK6))
% 7.52/1.48      | ~ v3_ordinal1(k3_tarski(sK6))
% 7.52/1.48      | ~ v3_ordinal1(sK6)
% 7.52/1.48      | k3_tarski(sK6) = sK6 ),
% 7.52/1.48      inference(instantiation,[status(thm)],[c_16054]) ).
% 7.52/1.48  
% 7.52/1.48  cnf(c_19,plain,
% 7.52/1.48      ( ~ r2_hidden(X0,X1)
% 7.52/1.48      | r2_hidden(X0,k2_xboole_0(X1,k1_tarski(X1))) ),
% 7.52/1.48      inference(cnf_transformation,[],[f106]) ).
% 7.52/1.48  
% 7.52/1.48  cnf(c_3425,plain,
% 7.52/1.48      ( ~ r2_hidden(sK6,X0)
% 7.52/1.48      | r2_hidden(sK6,k2_xboole_0(X0,k1_tarski(X0))) ),
% 7.52/1.48      inference(instantiation,[status(thm)],[c_19]) ).
% 7.52/1.48  
% 7.52/1.48  cnf(c_17712,plain,
% 7.52/1.48      ( r2_hidden(sK6,k2_xboole_0(sK3(X0,sK6),k1_tarski(sK3(X0,sK6))))
% 7.52/1.48      | ~ r2_hidden(sK6,sK3(X0,sK6)) ),
% 7.52/1.48      inference(instantiation,[status(thm)],[c_3425]) ).
% 7.52/1.48  
% 7.52/1.48  cnf(c_17715,plain,
% 7.52/1.48      ( r2_hidden(sK6,k2_xboole_0(sK3(sK6,sK6),k1_tarski(sK3(sK6,sK6))))
% 7.52/1.48      | ~ r2_hidden(sK6,sK3(sK6,sK6)) ),
% 7.52/1.48      inference(instantiation,[status(thm)],[c_17712]) ).
% 7.52/1.48  
% 7.52/1.48  cnf(c_13585,plain,
% 7.52/1.48      ( ~ r2_hidden(X0,sK6)
% 7.52/1.48      | ~ r1_tarski(k3_tarski(sK6),X0)
% 7.52/1.48      | v4_ordinal1(sK6)
% 7.52/1.48      | ~ v3_ordinal1(X0) ),
% 7.52/1.48      inference(resolution,[status(thm)],[c_13081,c_32]) ).
% 7.52/1.48  
% 7.52/1.48  cnf(c_5,plain,
% 7.52/1.48      ( r1_tarski(X0,X0) ),
% 7.52/1.48      inference(cnf_transformation,[],[f116]) ).
% 7.52/1.48  
% 7.52/1.48  cnf(c_13880,plain,
% 7.52/1.48      ( ~ r2_hidden(k3_tarski(sK6),sK6)
% 7.52/1.48      | v4_ordinal1(sK6)
% 7.52/1.48      | ~ v3_ordinal1(k3_tarski(sK6)) ),
% 7.52/1.48      inference(resolution,[status(thm)],[c_13585,c_5]) ).
% 7.52/1.48  
% 7.52/1.48  cnf(c_46,plain,
% 7.52/1.48      ( ~ r2_hidden(sK6,sK6) | ~ r1_tarski(sK6,sK6) ),
% 7.52/1.48      inference(instantiation,[status(thm)],[c_32]) ).
% 7.52/1.48  
% 7.52/1.48  cnf(c_27,plain,
% 7.52/1.48      ( r1_ordinal1(X0,X1)
% 7.52/1.48      | ~ r2_hidden(X0,k2_xboole_0(X1,k1_tarski(X1)))
% 7.52/1.48      | ~ v3_ordinal1(X1)
% 7.52/1.48      | ~ v3_ordinal1(X0) ),
% 7.52/1.48      inference(cnf_transformation,[],[f112]) ).
% 7.52/1.48  
% 7.52/1.48  cnf(c_61,plain,
% 7.52/1.48      ( r1_ordinal1(sK6,sK6)
% 7.52/1.48      | ~ r2_hidden(sK6,k2_xboole_0(sK6,k1_tarski(sK6)))
% 7.52/1.48      | ~ v3_ordinal1(sK6) ),
% 7.52/1.48      inference(instantiation,[status(thm)],[c_27]) ).
% 7.52/1.48  
% 7.52/1.48  cnf(c_76,plain,
% 7.52/1.48      ( r2_hidden(sK6,sK6) | ~ v3_ordinal1(sK6) | sK6 = sK6 ),
% 7.52/1.48      inference(instantiation,[status(thm)],[c_22]) ).
% 7.52/1.48  
% 7.52/1.48  cnf(c_86,plain,
% 7.52/1.48      ( r2_hidden(sK6,k2_xboole_0(sK6,k1_tarski(sK6))) ),
% 7.52/1.48      inference(instantiation,[status(thm)],[c_18]) ).
% 7.52/1.48  
% 7.52/1.48  cnf(c_90,plain,
% 7.52/1.48      ( ~ r1_ordinal1(sK6,sK6)
% 7.52/1.48      | r1_tarski(sK6,sK6)
% 7.52/1.48      | ~ v3_ordinal1(sK6) ),
% 7.52/1.48      inference(instantiation,[status(thm)],[c_16]) ).
% 7.52/1.48  
% 7.52/1.48  cnf(c_1013,plain,
% 7.52/1.48      ( ~ r2_hidden(X0,X1) | r2_hidden(X2,X3) | X2 != X0 | X3 != X1 ),
% 7.52/1.48      theory(equality) ).
% 7.52/1.48  
% 7.52/1.48  cnf(c_6813,plain,
% 7.52/1.48      ( r2_hidden(X0,X1)
% 7.52/1.48      | ~ r2_hidden(k3_tarski(X2),X3)
% 7.52/1.48      | X1 != X3
% 7.52/1.48      | X0 != k3_tarski(X2) ),
% 7.52/1.48      inference(instantiation,[status(thm)],[c_1013]) ).
% 7.52/1.48  
% 7.52/1.48  cnf(c_6828,plain,
% 7.52/1.48      ( ~ r2_hidden(k3_tarski(sK6),sK6)
% 7.52/1.48      | r2_hidden(sK6,sK6)
% 7.52/1.48      | sK6 != k3_tarski(sK6)
% 7.52/1.48      | sK6 != sK6 ),
% 7.52/1.48      inference(instantiation,[status(thm)],[c_6813]) ).
% 7.52/1.48  
% 7.52/1.48  cnf(c_1012,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 7.52/1.48  
% 7.52/1.48  cnf(c_16156,plain,
% 7.52/1.48      ( X0 != X1 | X0 = k3_tarski(X2) | k3_tarski(X2) != X1 ),
% 7.52/1.48      inference(instantiation,[status(thm)],[c_1012]) ).
% 7.52/1.48  
% 7.52/1.48  cnf(c_16157,plain,
% 7.52/1.48      ( k3_tarski(sK6) != sK6 | sK6 = k3_tarski(sK6) | sK6 != sK6 ),
% 7.52/1.48      inference(instantiation,[status(thm)],[c_16156]) ).
% 7.52/1.48  
% 7.52/1.48  cnf(c_17825,plain,
% 7.52/1.48      ( ~ r2_hidden(k3_tarski(sK6),sK6) ),
% 7.52/1.48      inference(global_propositional_subsumption,
% 7.52/1.48                [status(thm)],
% 7.52/1.48                [c_13880,c_37,c_46,c_61,c_76,c_86,c_90,c_96,c_2940,
% 7.52/1.48                 c_6828,c_16157]) ).
% 7.52/1.48  
% 7.52/1.48  cnf(c_19988,plain,
% 7.52/1.48      ( r1_ordinal1(X0,sK3(X0,X1))
% 7.52/1.48      | ~ r2_hidden(X0,k2_xboole_0(sK3(X0,X1),k1_tarski(sK3(X0,X1))))
% 7.52/1.48      | ~ v3_ordinal1(X0)
% 7.52/1.48      | ~ v3_ordinal1(sK3(X0,X1)) ),
% 7.52/1.48      inference(instantiation,[status(thm)],[c_27]) ).
% 7.52/1.48  
% 7.52/1.48  cnf(c_19995,plain,
% 7.52/1.48      ( r1_ordinal1(sK6,sK3(sK6,sK6))
% 7.52/1.48      | ~ r2_hidden(sK6,k2_xboole_0(sK3(sK6,sK6),k1_tarski(sK3(sK6,sK6))))
% 7.52/1.48      | ~ v3_ordinal1(sK3(sK6,sK6))
% 7.52/1.48      | ~ v3_ordinal1(sK6) ),
% 7.52/1.48      inference(instantiation,[status(thm)],[c_19988]) ).
% 7.52/1.48  
% 7.52/1.48  cnf(c_20473,plain,
% 7.52/1.48      ( v4_ordinal1(sK6) ),
% 7.52/1.48      inference(global_propositional_subsumption,
% 7.52/1.48                [status(thm)],
% 7.52/1.48                [c_19921,c_37,c_46,c_61,c_76,c_86,c_90,c_96,c_99,c_105,
% 7.52/1.48                 c_2940,c_2967,c_3714,c_6828,c_6999,c_13880,c_16056,
% 7.52/1.48                 c_16157,c_17715,c_19995]) ).
% 7.52/1.48  
% 7.52/1.48  cnf(c_20620,plain,
% 7.52/1.48      ( v4_ordinal1(sK6) = iProver_top ),
% 7.52/1.48      inference(global_propositional_subsumption,
% 7.52/1.48                [status(thm)],
% 7.52/1.48                [c_19690,c_37,c_46,c_61,c_76,c_86,c_90,c_96,c_99,c_100,
% 7.52/1.48                 c_105,c_2940,c_2967,c_3714,c_6828,c_6999,c_13880,
% 7.52/1.48                 c_16056,c_16157,c_17715,c_19995]) ).
% 7.52/1.48  
% 7.52/1.48  cnf(c_33,negated_conjecture,
% 7.52/1.48      ( ~ r2_hidden(k2_xboole_0(sK7,k1_tarski(sK7)),sK6)
% 7.52/1.48      | ~ v4_ordinal1(sK6) ),
% 7.52/1.48      inference(cnf_transformation,[],[f113]) ).
% 7.52/1.48  
% 7.52/1.48  cnf(c_1803,plain,
% 7.52/1.48      ( r2_hidden(k2_xboole_0(sK7,k1_tarski(sK7)),sK6) != iProver_top
% 7.52/1.48      | v4_ordinal1(sK6) != iProver_top ),
% 7.52/1.48      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 7.52/1.48  
% 7.52/1.48  cnf(c_8728,plain,
% 7.52/1.48      ( k2_xboole_0(sK7,k1_tarski(sK7)) = sK6
% 7.52/1.48      | r2_hidden(sK6,k2_xboole_0(sK7,k1_tarski(sK7))) = iProver_top
% 7.52/1.48      | v4_ordinal1(sK6) != iProver_top
% 7.52/1.48      | v3_ordinal1(k2_xboole_0(sK7,k1_tarski(sK7))) != iProver_top
% 7.52/1.48      | v3_ordinal1(sK6) != iProver_top ),
% 7.52/1.48      inference(superposition,[status(thm)],[c_1813,c_1803]) ).
% 7.52/1.48  
% 7.52/1.48  cnf(c_38,plain,
% 7.52/1.48      ( v3_ordinal1(sK6) = iProver_top ),
% 7.52/1.48      inference(predicate_to_equality,[status(thm)],[c_37]) ).
% 7.52/1.48  
% 7.52/1.48  cnf(c_35,negated_conjecture,
% 7.52/1.48      ( ~ v4_ordinal1(sK6) | v3_ordinal1(sK7) ),
% 7.52/1.48      inference(cnf_transformation,[],[f101]) ).
% 7.52/1.48  
% 7.52/1.48  cnf(c_42,plain,
% 7.52/1.48      ( v4_ordinal1(sK6) != iProver_top
% 7.52/1.48      | v3_ordinal1(sK7) = iProver_top ),
% 7.52/1.48      inference(predicate_to_equality,[status(thm)],[c_35]) ).
% 7.52/1.48  
% 7.52/1.48  cnf(c_34,negated_conjecture,
% 7.52/1.48      ( r2_hidden(sK7,sK6) | ~ v4_ordinal1(sK6) ),
% 7.52/1.48      inference(cnf_transformation,[],[f102]) ).
% 7.52/1.48  
% 7.52/1.48  cnf(c_1802,plain,
% 7.52/1.48      ( r2_hidden(sK7,sK6) = iProver_top
% 7.52/1.48      | v4_ordinal1(sK6) != iProver_top ),
% 7.52/1.48      inference(predicate_to_equality,[status(thm)],[c_34]) ).
% 7.52/1.48  
% 7.52/1.48  cnf(c_1804,plain,
% 7.52/1.48      ( r2_hidden(X0,X1) != iProver_top
% 7.52/1.48      | r1_tarski(X1,X0) != iProver_top ),
% 7.52/1.48      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 7.52/1.48  
% 7.52/1.48  cnf(c_2537,plain,
% 7.52/1.48      ( r1_tarski(sK6,sK7) != iProver_top
% 7.52/1.48      | v4_ordinal1(sK6) != iProver_top ),
% 7.52/1.48      inference(superposition,[status(thm)],[c_1802,c_1804]) ).
% 7.52/1.48  
% 7.52/1.48  cnf(c_3312,plain,
% 7.52/1.48      ( ~ r1_ordinal1(sK6,sK7)
% 7.52/1.48      | r1_tarski(sK6,sK7)
% 7.52/1.48      | ~ v3_ordinal1(sK6)
% 7.52/1.48      | ~ v3_ordinal1(sK7) ),
% 7.52/1.48      inference(instantiation,[status(thm)],[c_16]) ).
% 7.52/1.48  
% 7.52/1.48  cnf(c_3319,plain,
% 7.52/1.48      ( r1_ordinal1(sK6,sK7) != iProver_top
% 7.52/1.48      | r1_tarski(sK6,sK7) = iProver_top
% 7.52/1.48      | v3_ordinal1(sK6) != iProver_top
% 7.52/1.48      | v3_ordinal1(sK7) != iProver_top ),
% 7.52/1.48      inference(predicate_to_equality,[status(thm)],[c_3312]) ).
% 7.52/1.48  
% 7.52/1.48  cnf(c_5618,plain,
% 7.52/1.48      ( r1_ordinal1(sK6,sK7)
% 7.52/1.48      | ~ r2_hidden(sK6,k2_xboole_0(sK7,k1_tarski(sK7)))
% 7.52/1.48      | ~ v3_ordinal1(sK6)
% 7.52/1.48      | ~ v3_ordinal1(sK7) ),
% 7.52/1.48      inference(instantiation,[status(thm)],[c_27]) ).
% 7.52/1.48  
% 7.52/1.48  cnf(c_5622,plain,
% 7.52/1.48      ( r1_ordinal1(sK6,sK7) = iProver_top
% 7.52/1.48      | r2_hidden(sK6,k2_xboole_0(sK7,k1_tarski(sK7))) != iProver_top
% 7.52/1.48      | v3_ordinal1(sK6) != iProver_top
% 7.52/1.48      | v3_ordinal1(sK7) != iProver_top ),
% 7.52/1.48      inference(predicate_to_equality,[status(thm)],[c_5618]) ).
% 7.52/1.48  
% 7.52/1.48  cnf(c_5874,plain,
% 7.52/1.48      ( v3_ordinal1(k2_xboole_0(sK7,k1_tarski(sK7)))
% 7.52/1.48      | ~ v3_ordinal1(sK7) ),
% 7.52/1.48      inference(instantiation,[status(thm)],[c_23]) ).
% 7.52/1.48  
% 7.52/1.48  cnf(c_5875,plain,
% 7.52/1.48      ( v3_ordinal1(k2_xboole_0(sK7,k1_tarski(sK7))) = iProver_top
% 7.52/1.48      | v3_ordinal1(sK7) != iProver_top ),
% 7.52/1.48      inference(predicate_to_equality,[status(thm)],[c_5874]) ).
% 7.52/1.48  
% 7.52/1.48  cnf(c_9262,plain,
% 7.52/1.48      ( k2_xboole_0(sK7,k1_tarski(sK7)) = sK6
% 7.52/1.48      | v4_ordinal1(sK6) != iProver_top ),
% 7.52/1.48      inference(global_propositional_subsumption,
% 7.52/1.48                [status(thm)],
% 7.52/1.48                [c_8728,c_38,c_42,c_2537,c_3319,c_5622,c_5875]) ).
% 7.52/1.48  
% 7.52/1.48  cnf(c_20626,plain,
% 7.52/1.48      ( k2_xboole_0(sK7,k1_tarski(sK7)) = sK6 ),
% 7.52/1.48      inference(superposition,[status(thm)],[c_20620,c_9262]) ).
% 7.52/1.48  
% 7.52/1.48  cnf(c_25,plain,
% 7.52/1.48      ( r1_ordinal1(k2_xboole_0(X0,k1_tarski(X0)),X1)
% 7.52/1.48      | ~ r2_hidden(X0,X1)
% 7.52/1.48      | ~ v3_ordinal1(X1)
% 7.52/1.48      | ~ v3_ordinal1(X0) ),
% 7.52/1.48      inference(cnf_transformation,[],[f110]) ).
% 7.52/1.48  
% 7.52/1.48  cnf(c_221,plain,
% 7.52/1.48      ( ~ v3_ordinal1(X1)
% 7.52/1.48      | ~ r2_hidden(X0,X1)
% 7.52/1.48      | r1_ordinal1(k2_xboole_0(X0,k1_tarski(X0)),X1) ),
% 7.52/1.48      inference(global_propositional_subsumption,
% 7.52/1.48                [status(thm)],
% 7.52/1.48                [c_25,c_21]) ).
% 7.52/1.48  
% 7.52/1.48  cnf(c_222,plain,
% 7.52/1.48      ( r1_ordinal1(k2_xboole_0(X0,k1_tarski(X0)),X1)
% 7.52/1.48      | ~ r2_hidden(X0,X1)
% 7.52/1.48      | ~ v3_ordinal1(X1) ),
% 7.52/1.48      inference(renaming,[status(thm)],[c_221]) ).
% 7.52/1.48  
% 7.52/1.48  cnf(c_1798,plain,
% 7.52/1.48      ( r1_ordinal1(k2_xboole_0(X0,k1_tarski(X0)),X1) = iProver_top
% 7.52/1.48      | r2_hidden(X0,X1) != iProver_top
% 7.52/1.48      | v3_ordinal1(X1) != iProver_top ),
% 7.52/1.48      inference(predicate_to_equality,[status(thm)],[c_222]) ).
% 7.52/1.48  
% 7.52/1.48  cnf(c_20882,plain,
% 7.52/1.48      ( r1_ordinal1(sK6,X0) = iProver_top
% 7.52/1.48      | r2_hidden(sK7,X0) != iProver_top
% 7.52/1.48      | v3_ordinal1(X0) != iProver_top ),
% 7.52/1.48      inference(superposition,[status(thm)],[c_20626,c_1798]) ).
% 7.52/1.48  
% 7.52/1.48  cnf(c_25370,plain,
% 7.52/1.48      ( r1_ordinal1(sK6,sK3(X0,sK7)) = iProver_top
% 7.52/1.48      | r2_hidden(sK7,k3_tarski(X0)) != iProver_top
% 7.52/1.48      | v3_ordinal1(sK3(X0,sK7)) != iProver_top ),
% 7.52/1.48      inference(superposition,[status(thm)],[c_1823,c_20882]) ).
% 7.52/1.48  
% 7.52/1.48  cnf(c_25432,plain,
% 7.52/1.48      ( r1_ordinal1(sK6,sK3(sK6,sK7)) = iProver_top
% 7.52/1.48      | r2_hidden(sK7,k3_tarski(sK6)) != iProver_top
% 7.52/1.48      | v3_ordinal1(sK3(sK6,sK7)) != iProver_top ),
% 7.52/1.48      inference(instantiation,[status(thm)],[c_25370]) ).
% 7.52/1.48  
% 7.52/1.48  cnf(c_14803,plain,
% 7.52/1.48      ( ~ r1_ordinal1(X0,sK3(X1,sK7))
% 7.52/1.48      | r1_tarski(X0,sK3(X1,sK7))
% 7.52/1.48      | ~ v3_ordinal1(X0)
% 7.52/1.48      | ~ v3_ordinal1(sK3(X1,sK7)) ),
% 7.52/1.48      inference(instantiation,[status(thm)],[c_16]) ).
% 7.52/1.48  
% 7.52/1.48  cnf(c_14814,plain,
% 7.52/1.48      ( r1_ordinal1(X0,sK3(X1,sK7)) != iProver_top
% 7.52/1.48      | r1_tarski(X0,sK3(X1,sK7)) = iProver_top
% 7.52/1.48      | v3_ordinal1(X0) != iProver_top
% 7.52/1.48      | v3_ordinal1(sK3(X1,sK7)) != iProver_top ),
% 7.52/1.48      inference(predicate_to_equality,[status(thm)],[c_14803]) ).
% 7.52/1.48  
% 7.52/1.48  cnf(c_14816,plain,
% 7.52/1.48      ( r1_ordinal1(sK6,sK3(sK6,sK7)) != iProver_top
% 7.52/1.48      | r1_tarski(sK6,sK3(sK6,sK7)) = iProver_top
% 7.52/1.48      | v3_ordinal1(sK3(sK6,sK7)) != iProver_top
% 7.52/1.48      | v3_ordinal1(sK6) != iProver_top ),
% 7.52/1.48      inference(instantiation,[status(thm)],[c_14814]) ).
% 7.52/1.48  
% 7.52/1.48  cnf(c_4494,plain,
% 7.52/1.48      ( ~ r2_hidden(sK3(X0,X1),X2)
% 7.52/1.48      | ~ v3_ordinal1(X2)
% 7.52/1.48      | v3_ordinal1(sK3(X0,X1)) ),
% 7.52/1.48      inference(instantiation,[status(thm)],[c_21]) ).
% 7.52/1.48  
% 7.52/1.48  cnf(c_7702,plain,
% 7.52/1.48      ( ~ r2_hidden(sK3(sK6,sK7),sK6)
% 7.52/1.48      | v3_ordinal1(sK3(sK6,sK7))
% 7.52/1.48      | ~ v3_ordinal1(sK6) ),
% 7.52/1.48      inference(instantiation,[status(thm)],[c_4494]) ).
% 7.52/1.48  
% 7.52/1.48  cnf(c_7703,plain,
% 7.52/1.48      ( r2_hidden(sK3(sK6,sK7),sK6) != iProver_top
% 7.52/1.48      | v3_ordinal1(sK3(sK6,sK7)) = iProver_top
% 7.52/1.48      | v3_ordinal1(sK6) != iProver_top ),
% 7.52/1.48      inference(predicate_to_equality,[status(thm)],[c_7702]) ).
% 7.52/1.48  
% 7.52/1.48  cnf(c_2765,plain,
% 7.52/1.48      ( ~ r2_hidden(sK3(X0,X1),X0) | ~ r1_tarski(X0,sK3(X0,X1)) ),
% 7.52/1.48      inference(instantiation,[status(thm)],[c_32]) ).
% 7.52/1.48  
% 7.52/1.48  cnf(c_7108,plain,
% 7.52/1.48      ( ~ r2_hidden(sK3(sK6,sK7),sK6) | ~ r1_tarski(sK6,sK3(sK6,sK7)) ),
% 7.52/1.48      inference(instantiation,[status(thm)],[c_2765]) ).
% 7.52/1.48  
% 7.52/1.48  cnf(c_7109,plain,
% 7.52/1.48      ( r2_hidden(sK3(sK6,sK7),sK6) != iProver_top
% 7.52/1.48      | r1_tarski(sK6,sK3(sK6,sK7)) != iProver_top ),
% 7.52/1.48      inference(predicate_to_equality,[status(thm)],[c_7108]) ).
% 7.52/1.48  
% 7.52/1.48  cnf(c_3433,plain,
% 7.52/1.48      ( r2_hidden(X0,sK7)
% 7.52/1.48      | r2_hidden(sK7,X0)
% 7.52/1.48      | ~ v3_ordinal1(X0)
% 7.52/1.48      | ~ v3_ordinal1(sK7)
% 7.52/1.48      | X0 = sK7 ),
% 7.52/1.48      inference(instantiation,[status(thm)],[c_22]) ).
% 7.52/1.48  
% 7.52/1.48  cnf(c_6756,plain,
% 7.52/1.48      ( r2_hidden(k3_tarski(X0),sK7)
% 7.52/1.48      | r2_hidden(sK7,k3_tarski(X0))
% 7.52/1.48      | ~ v3_ordinal1(k3_tarski(X0))
% 7.52/1.48      | ~ v3_ordinal1(sK7)
% 7.52/1.48      | k3_tarski(X0) = sK7 ),
% 7.52/1.48      inference(instantiation,[status(thm)],[c_3433]) ).
% 7.52/1.48  
% 7.52/1.48  cnf(c_6767,plain,
% 7.52/1.48      ( k3_tarski(X0) = sK7
% 7.52/1.48      | r2_hidden(k3_tarski(X0),sK7) = iProver_top
% 7.52/1.48      | r2_hidden(sK7,k3_tarski(X0)) = iProver_top
% 7.52/1.48      | v3_ordinal1(k3_tarski(X0)) != iProver_top
% 7.52/1.48      | v3_ordinal1(sK7) != iProver_top ),
% 7.52/1.48      inference(predicate_to_equality,[status(thm)],[c_6756]) ).
% 7.52/1.48  
% 7.52/1.48  cnf(c_6769,plain,
% 7.52/1.48      ( k3_tarski(sK6) = sK7
% 7.52/1.48      | r2_hidden(k3_tarski(sK6),sK7) = iProver_top
% 7.52/1.48      | r2_hidden(sK7,k3_tarski(sK6)) = iProver_top
% 7.52/1.48      | v3_ordinal1(k3_tarski(sK6)) != iProver_top
% 7.52/1.48      | v3_ordinal1(sK7) != iProver_top ),
% 7.52/1.48      inference(instantiation,[status(thm)],[c_6767]) ).
% 7.52/1.48  
% 7.52/1.48  cnf(c_1829,plain,
% 7.52/1.48      ( r1_tarski(X0,X0) = iProver_top ),
% 7.52/1.48      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 7.52/1.48  
% 7.52/1.48  cnf(c_4780,plain,
% 7.52/1.48      ( r2_hidden(X0,k3_tarski(sK6)) = iProver_top
% 7.52/1.48      | r2_hidden(X0,sK7) != iProver_top
% 7.52/1.48      | v4_ordinal1(sK6) != iProver_top ),
% 7.52/1.48      inference(superposition,[status(thm)],[c_1802,c_1825]) ).
% 7.52/1.48  
% 7.52/1.48  cnf(c_5233,plain,
% 7.52/1.48      ( r2_hidden(X0,sK7) != iProver_top
% 7.52/1.48      | r1_tarski(k3_tarski(sK6),X0) != iProver_top
% 7.52/1.48      | v4_ordinal1(sK6) != iProver_top ),
% 7.52/1.48      inference(superposition,[status(thm)],[c_4780,c_1804]) ).
% 7.52/1.48  
% 7.52/1.48  cnf(c_6071,plain,
% 7.52/1.48      ( r2_hidden(k3_tarski(sK6),sK7) != iProver_top
% 7.52/1.48      | v4_ordinal1(sK6) != iProver_top ),
% 7.52/1.48      inference(superposition,[status(thm)],[c_1829,c_5233]) ).
% 7.52/1.48  
% 7.52/1.48  cnf(c_2314,plain,
% 7.52/1.48      ( r2_hidden(X0,X1) | ~ r2_hidden(sK7,sK6) | X1 != sK6 | X0 != sK7 ),
% 7.52/1.48      inference(instantiation,[status(thm)],[c_1013]) ).
% 7.52/1.48  
% 7.52/1.48  cnf(c_3771,plain,
% 7.52/1.48      ( r2_hidden(k3_tarski(X0),X1)
% 7.52/1.48      | ~ r2_hidden(sK7,sK6)
% 7.52/1.48      | X1 != sK6
% 7.52/1.48      | k3_tarski(X0) != sK7 ),
% 7.52/1.48      inference(instantiation,[status(thm)],[c_2314]) ).
% 7.52/1.48  
% 7.52/1.48  cnf(c_3777,plain,
% 7.52/1.48      ( r2_hidden(k3_tarski(sK6),sK6)
% 7.52/1.48      | ~ r2_hidden(sK7,sK6)
% 7.52/1.48      | k3_tarski(sK6) != sK7
% 7.52/1.48      | sK6 != sK6 ),
% 7.52/1.48      inference(instantiation,[status(thm)],[c_3771]) ).
% 7.52/1.48  
% 7.52/1.48  cnf(c_2784,plain,
% 7.52/1.48      ( ~ r2_hidden(X0,k3_tarski(sK6)) | r2_hidden(sK3(sK6,X0),sK6) ),
% 7.52/1.48      inference(instantiation,[status(thm)],[c_10]) ).
% 7.52/1.48  
% 7.52/1.48  cnf(c_3404,plain,
% 7.52/1.48      ( r2_hidden(sK3(sK6,sK7),sK6) | ~ r2_hidden(sK7,k3_tarski(sK6)) ),
% 7.52/1.48      inference(instantiation,[status(thm)],[c_2784]) ).
% 7.52/1.48  
% 7.52/1.48  cnf(c_3407,plain,
% 7.52/1.48      ( r2_hidden(sK3(sK6,sK7),sK6) = iProver_top
% 7.52/1.48      | r2_hidden(sK7,k3_tarski(sK6)) != iProver_top ),
% 7.52/1.48      inference(predicate_to_equality,[status(thm)],[c_3404]) ).
% 7.52/1.48  
% 7.52/1.48  cnf(c_2939,plain,
% 7.52/1.48      ( v3_ordinal1(X0) != iProver_top
% 7.52/1.48      | v3_ordinal1(k3_tarski(X0)) = iProver_top ),
% 7.52/1.48      inference(predicate_to_equality,[status(thm)],[c_2937]) ).
% 7.52/1.48  
% 7.52/1.48  cnf(c_2941,plain,
% 7.52/1.48      ( v3_ordinal1(k3_tarski(sK6)) = iProver_top
% 7.52/1.48      | v3_ordinal1(sK6) != iProver_top ),
% 7.52/1.48      inference(instantiation,[status(thm)],[c_2939]) ).
% 7.52/1.48  
% 7.52/1.48  cnf(c_300,plain,
% 7.52/1.48      ( v4_ordinal1(X0) | k3_tarski(X0) != X0 ),
% 7.52/1.48      inference(prop_impl,[status(thm)],[c_13]) ).
% 7.52/1.48  
% 7.52/1.48  cnf(c_528,plain,
% 7.52/1.48      ( v3_ordinal1(sK7) | k3_tarski(X0) != X0 | sK6 != X0 ),
% 7.52/1.48      inference(resolution_lifted,[status(thm)],[c_300,c_35]) ).
% 7.52/1.48  
% 7.52/1.48  cnf(c_529,plain,
% 7.52/1.48      ( v3_ordinal1(sK7) | k3_tarski(sK6) != sK6 ),
% 7.52/1.48      inference(unflattening,[status(thm)],[c_528]) ).
% 7.52/1.48  
% 7.52/1.48  cnf(c_530,plain,
% 7.52/1.48      ( k3_tarski(sK6) != sK6 | v3_ordinal1(sK7) = iProver_top ),
% 7.52/1.48      inference(predicate_to_equality,[status(thm)],[c_529]) ).
% 7.52/1.48  
% 7.52/1.48  cnf(contradiction,plain,
% 7.52/1.48      ( $false ),
% 7.52/1.48      inference(minisat,
% 7.52/1.48                [status(thm)],
% 7.52/1.48                [c_25432,c_20473,c_17825,c_14816,c_7703,c_7109,c_6769,
% 7.52/1.48                 c_6071,c_3777,c_3407,c_2941,c_530,c_100,c_96,c_90,c_86,
% 7.52/1.48                 c_76,c_61,c_46,c_34,c_38,c_37]) ).
% 7.52/1.48  
% 7.52/1.48  
% 7.52/1.48  % SZS output end CNFRefutation for theBenchmark.p
% 7.52/1.48  
% 7.52/1.48  ------                               Statistics
% 7.52/1.48  
% 7.52/1.48  ------ Selected
% 7.52/1.48  
% 7.52/1.48  total_time:                             0.681
% 7.52/1.48  
%------------------------------------------------------------------------------
