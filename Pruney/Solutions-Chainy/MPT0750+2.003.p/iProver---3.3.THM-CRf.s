%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:54:00 EST 2020

% Result     : Theorem 23.83s
% Output     : CNFRefutation 23.83s
% Verified   : 
% Statistics : Number of formulae       :  216 ( 539 expanded)
%              Number of clauses        :  118 ( 167 expanded)
%              Number of leaves         :   26 ( 124 expanded)
%              Depth                    :   18
%              Number of atoms          :  735 (2532 expanded)
%              Number of equality atoms :  126 ( 254 expanded)
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

fof(f77,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | ~ r2_hidden(X6,X0)
      | ~ r2_hidden(X5,X6)
      | k3_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f53])).

fof(f120,plain,(
    ! [X6,X0,X5] :
      ( r2_hidden(X5,k3_tarski(X0))
      | ~ r2_hidden(X6,X0)
      | ~ r2_hidden(X5,X6) ) ),
    inference(equality_resolution,[],[f77])).

fof(f75,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(X5,sK3(X0,X5))
      | ~ r2_hidden(X5,X1)
      | k3_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f53])).

fof(f122,plain,(
    ! [X0,X5] :
      ( r2_hidden(X5,sK3(X0,X5))
      | ~ r2_hidden(X5,k3_tarski(X0)) ) ),
    inference(equality_resolution,[],[f75])).

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

fof(f103,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f13,axiom,(
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
    inference(ennf_transformation,[],[f13])).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(X1,X0)
          | X0 = X1
          | r2_hidden(X0,X1)
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(flattening,[],[f32])).

fof(f94,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,X0)
      | X0 = X1
      | r2_hidden(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f33])).

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

fof(f81,plain,(
    ! [X0] :
      ( v1_ordinal1(X0)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f24])).

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

fof(f84,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | ~ r2_hidden(X1,X0)
      | ~ v1_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f27])).

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

fof(f87,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r1_ordinal1(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( ( v3_ordinal1(X1)
        & v3_ordinal1(X0) )
     => ( r1_ordinal1(X1,X0)
        | r1_ordinal1(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1] :
      ( r1_ordinal1(X1,X0)
      | r1_ordinal1(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f26,plain,(
    ! [X0,X1] :
      ( r1_ordinal1(X1,X0)
      | r1_ordinal1(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(flattening,[],[f25])).

fof(f82,plain,(
    ! [X0,X1] :
      ( r1_ordinal1(X1,X0)
      | r1_ordinal1(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f26])).

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
    inference(nnf_transformation,[],[f41])).

fof(f64,plain,(
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
    inference(flattening,[],[f63])).

fof(f65,plain,(
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
    inference(rectify,[],[f64])).

fof(f67,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ r2_hidden(k1_ordinal1(X1),X0)
          & r2_hidden(X1,X0)
          & v3_ordinal1(X1) )
     => ( ~ r2_hidden(k1_ordinal1(sK7),X0)
        & r2_hidden(sK7,X0)
        & v3_ordinal1(sK7) ) ) ),
    introduced(choice_axiom,[])).

fof(f66,plain,
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

fof(f68,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7])],[f65,f67,f66])).

fof(f108,plain,
    ( ~ r2_hidden(k1_ordinal1(sK7),sK6)
    | ~ v4_ordinal1(sK6) ),
    inference(cnf_transformation,[],[f68])).

fof(f6,axiom,(
    ! [X0] : k1_ordinal1(X0) = k2_xboole_0(X0,k1_tarski(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f83,plain,(
    ! [X0] : k1_ordinal1(X0) = k2_xboole_0(X0,k1_tarski(X0)) ),
    inference(cnf_transformation,[],[f6])).

fof(f116,plain,
    ( ~ r2_hidden(k2_xboole_0(sK7,k1_tarski(sK7)),sK6)
    | ~ v4_ordinal1(sK6) ),
    inference(definition_unfolding,[],[f108,f83])).

fof(f14,axiom,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => v3_ordinal1(k1_ordinal1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0] :
      ( v3_ordinal1(k1_ordinal1(X0))
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f95,plain,(
    ! [X0] :
      ( v3_ordinal1(k1_ordinal1(X0))
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f113,plain,(
    ! [X0] :
      ( v3_ordinal1(k2_xboole_0(X0,k1_tarski(X0)))
      | ~ v3_ordinal1(X0) ) ),
    inference(definition_unfolding,[],[f95,f83])).

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

fof(f69,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,k1_ordinal1(X1))
    <=> ( X0 = X1
        | r2_hidden(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f56,plain,(
    ! [X0,X1] :
      ( ( r2_hidden(X0,k1_ordinal1(X1))
        | ( X0 != X1
          & ~ r2_hidden(X0,X1) ) )
      & ( X0 = X1
        | r2_hidden(X0,X1)
        | ~ r2_hidden(X0,k1_ordinal1(X1)) ) ) ),
    inference(nnf_transformation,[],[f11])).

fof(f57,plain,(
    ! [X0,X1] :
      ( ( r2_hidden(X0,k1_ordinal1(X1))
        | ( X0 != X1
          & ~ r2_hidden(X0,X1) ) )
      & ( X0 = X1
        | r2_hidden(X0,X1)
        | ~ r2_hidden(X0,k1_ordinal1(X1)) ) ) ),
    inference(flattening,[],[f56])).

fof(f91,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,k1_ordinal1(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f111,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,k2_xboole_0(X1,k1_tarski(X1)))
      | ~ r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f91,f83])).

fof(f105,plain,(
    ! [X2] :
      ( r2_hidden(k1_ordinal1(X2),sK6)
      | ~ r2_hidden(X2,sK6)
      | ~ v3_ordinal1(X2)
      | v4_ordinal1(sK6) ) ),
    inference(cnf_transformation,[],[f68])).

fof(f117,plain,(
    ! [X2] :
      ( r2_hidden(k2_xboole_0(X2,k1_tarski(X2)),sK6)
      | ~ r2_hidden(X2,sK6)
      | ~ v3_ordinal1(X2)
      | v4_ordinal1(sK6) ) ),
    inference(definition_unfolding,[],[f105,f83])).

fof(f104,plain,(
    v3_ordinal1(sK6) ),
    inference(cnf_transformation,[],[f68])).

fof(f12,axiom,(
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
    inference(ennf_transformation,[],[f12])).

fof(f31,plain,(
    ! [X0,X1] :
      ( v3_ordinal1(X0)
      | ~ r2_hidden(X0,X1)
      | ~ v3_ordinal1(X1) ) ),
    inference(flattening,[],[f30])).

fof(f93,plain,(
    ! [X0,X1] :
      ( v3_ordinal1(X0)
      | ~ r2_hidden(X0,X1)
      | ~ v3_ordinal1(X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f16,axiom,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(X1,X0)
         => v3_ordinal1(X1) )
     => v3_ordinal1(k3_tarski(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0] :
      ( v3_ordinal1(k3_tarski(X0))
      | ? [X1] :
          ( ~ v3_ordinal1(X1)
          & r2_hidden(X1,X0) ) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f59,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ v3_ordinal1(X1)
          & r2_hidden(X1,X0) )
     => ( ~ v3_ordinal1(sK4(X0))
        & r2_hidden(sK4(X0),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f60,plain,(
    ! [X0] :
      ( v3_ordinal1(k3_tarski(X0))
      | ( ~ v3_ordinal1(sK4(X0))
        & r2_hidden(sK4(X0),X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f36,f59])).

fof(f98,plain,(
    ! [X0] :
      ( v3_ordinal1(k3_tarski(X0))
      | r2_hidden(sK4(X0),X0) ) ),
    inference(cnf_transformation,[],[f60])).

fof(f99,plain,(
    ! [X0] :
      ( v3_ordinal1(k3_tarski(X0))
      | ~ v3_ordinal1(sK4(X0)) ) ),
    inference(cnf_transformation,[],[f60])).

fof(f70,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK0(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f45])).

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

fof(f86,plain,(
    ! [X0] :
      ( v4_ordinal1(X0)
      | k3_tarski(X0) != X0 ) ),
    inference(cnf_transformation,[],[f54])).

fof(f76,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(sK3(X0,X5),X0)
      | ~ r2_hidden(X5,X1)
      | k3_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f53])).

fof(f121,plain,(
    ! [X0,X5] :
      ( r2_hidden(sK3(X0,X5),X0)
      | ~ r2_hidden(X5,k3_tarski(X0)) ) ),
    inference(equality_resolution,[],[f76])).

fof(f92,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,k1_ordinal1(X1))
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f57])).

fof(f110,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,k2_xboole_0(X1,k1_tarski(X1)))
      | X0 != X1 ) ),
    inference(definition_unfolding,[],[f92,f83])).

fof(f123,plain,(
    ! [X1] : r2_hidden(X1,k2_xboole_0(X1,k1_tarski(X1))) ),
    inference(equality_resolution,[],[f110])).

fof(f71,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK0(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f90,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | r2_hidden(X0,X1)
      | ~ r2_hidden(X0,k1_ordinal1(X1)) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f112,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | r2_hidden(X0,X1)
      | ~ r2_hidden(X0,k2_xboole_0(X1,k1_tarski(X1))) ) ),
    inference(definition_unfolding,[],[f90,f83])).

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

fof(f72,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f47])).

fof(f119,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f72])).

fof(f85,plain,(
    ! [X0] :
      ( k3_tarski(X0) = X0
      | ~ v4_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f107,plain,
    ( r2_hidden(sK7,sK6)
    | ~ v4_ordinal1(sK6) ),
    inference(cnf_transformation,[],[f68])).

fof(f106,plain,
    ( v3_ordinal1(sK7)
    | ~ v4_ordinal1(sK6) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_9,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X2,X0)
    | r2_hidden(X2,k3_tarski(X1)) ),
    inference(cnf_transformation,[],[f120])).

cnf(c_2147,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(sK7,X0)
    | r2_hidden(sK7,k3_tarski(X1)) ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_12305,plain,
    ( ~ r2_hidden(sK3(X0,sK7),X1)
    | ~ r2_hidden(sK7,sK3(X0,sK7))
    | r2_hidden(sK7,k3_tarski(X1)) ),
    inference(instantiation,[status(thm)],[c_2147])).

cnf(c_24584,plain,
    ( ~ r2_hidden(sK3(X0,sK7),sK7)
    | ~ r2_hidden(sK7,sK3(X0,sK7))
    | r2_hidden(sK7,k3_tarski(sK7)) ),
    inference(instantiation,[status(thm)],[c_12305])).

cnf(c_85037,plain,
    ( ~ r2_hidden(sK3(k2_xboole_0(sK7,k1_tarski(sK7)),sK7),sK7)
    | ~ r2_hidden(sK7,sK3(k2_xboole_0(sK7,k1_tarski(sK7)),sK7))
    | r2_hidden(sK7,k3_tarski(sK7)) ),
    inference(instantiation,[status(thm)],[c_24584])).

cnf(c_11,plain,
    ( r2_hidden(X0,sK3(X1,X0))
    | ~ r2_hidden(X0,k3_tarski(X1)) ),
    inference(cnf_transformation,[],[f122])).

cnf(c_2160,plain,
    ( r2_hidden(sK7,sK3(X0,sK7))
    | ~ r2_hidden(sK7,k3_tarski(X0)) ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_81604,plain,
    ( r2_hidden(sK7,sK3(sK7,sK7))
    | ~ r2_hidden(sK7,k3_tarski(sK7)) ),
    inference(instantiation,[status(thm)],[c_2160])).

cnf(c_33,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r1_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f103])).

cnf(c_2152,plain,
    ( ~ r2_hidden(sK7,X0)
    | ~ r1_tarski(X0,sK7) ),
    inference(instantiation,[status(thm)],[c_33])).

cnf(c_10171,plain,
    ( ~ r2_hidden(sK7,sK3(X0,sK7))
    | ~ r1_tarski(sK3(X0,sK7),sK7) ),
    inference(instantiation,[status(thm)],[c_2152])).

cnf(c_75458,plain,
    ( ~ r2_hidden(sK7,sK3(sK7,sK7))
    | ~ r1_tarski(sK3(sK7,sK7),sK7) ),
    inference(instantiation,[status(thm)],[c_10171])).

cnf(c_57736,plain,
    ( ~ r2_hidden(sK3(X0,sK7),k2_xboole_0(sK7,k1_tarski(sK7)))
    | ~ r2_hidden(sK7,sK3(X0,sK7))
    | r2_hidden(sK7,k3_tarski(k2_xboole_0(sK7,k1_tarski(sK7)))) ),
    inference(instantiation,[status(thm)],[c_12305])).

cnf(c_57742,plain,
    ( ~ r2_hidden(sK3(sK6,sK7),k2_xboole_0(sK7,k1_tarski(sK7)))
    | ~ r2_hidden(sK7,sK3(sK6,sK7))
    | r2_hidden(sK7,k3_tarski(k2_xboole_0(sK7,k1_tarski(sK7)))) ),
    inference(instantiation,[status(thm)],[c_57736])).

cnf(c_24,plain,
    ( r2_hidden(X0,X1)
    | r2_hidden(X1,X0)
    | ~ v3_ordinal1(X0)
    | ~ v3_ordinal1(X1)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f94])).

cnf(c_1836,plain,
    ( X0 = X1
    | r2_hidden(X1,X0) = iProver_top
    | r2_hidden(X0,X1) = iProver_top
    | v3_ordinal1(X1) != iProver_top
    | v3_ordinal1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_12,plain,
    ( ~ v3_ordinal1(X0)
    | v1_ordinal1(X0) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_14,plain,
    ( ~ r2_hidden(X0,X1)
    | r1_tarski(X0,X1)
    | ~ v1_ordinal1(X1) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_485,plain,
    ( ~ r2_hidden(X0,X1)
    | r1_tarski(X0,X1)
    | ~ v3_ordinal1(X2)
    | X1 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_14])).

cnf(c_486,plain,
    ( ~ r2_hidden(X0,X1)
    | r1_tarski(X0,X1)
    | ~ v3_ordinal1(X1) ),
    inference(unflattening,[status(thm)],[c_485])).

cnf(c_1821,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r1_tarski(X0,X1) = iProver_top
    | v3_ordinal1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_486])).

cnf(c_4298,plain,
    ( X0 = X1
    | r2_hidden(X1,X0) = iProver_top
    | r1_tarski(X0,X1) = iProver_top
    | v3_ordinal1(X1) != iProver_top
    | v3_ordinal1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1836,c_1821])).

cnf(c_18,plain,
    ( ~ r1_ordinal1(X0,X1)
    | r1_tarski(X0,X1)
    | ~ v3_ordinal1(X0)
    | ~ v3_ordinal1(X1) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_87,plain,
    ( r1_ordinal1(X0,X1) != iProver_top
    | r1_tarski(X0,X1) = iProver_top
    | v3_ordinal1(X0) != iProver_top
    | v3_ordinal1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_487,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r1_tarski(X0,X1) = iProver_top
    | v3_ordinal1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_486])).

cnf(c_1040,plain,
    ( ~ r1_ordinal1(X0,X1)
    | r1_ordinal1(X2,X1)
    | X2 != X0 ),
    theory(equality)).

cnf(c_6099,plain,
    ( ~ r1_ordinal1(X0,X1)
    | r1_ordinal1(X2,X1)
    | r2_hidden(X2,X0)
    | r2_hidden(X0,X2)
    | ~ v3_ordinal1(X0)
    | ~ v3_ordinal1(X2) ),
    inference(resolution,[status(thm)],[c_24,c_1040])).

cnf(c_13,plain,
    ( r1_ordinal1(X0,X1)
    | r1_ordinal1(X1,X0)
    | ~ v3_ordinal1(X0)
    | ~ v3_ordinal1(X1) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_4391,plain,
    ( r1_ordinal1(X0,X0)
    | ~ v3_ordinal1(X0) ),
    inference(factoring,[status(thm)],[c_13])).

cnf(c_19309,plain,
    ( r1_ordinal1(X0,X1)
    | r2_hidden(X0,X1)
    | r2_hidden(X1,X0)
    | ~ v3_ordinal1(X0)
    | ~ v3_ordinal1(X1) ),
    inference(resolution,[status(thm)],[c_6099,c_4391])).

cnf(c_19310,plain,
    ( r1_ordinal1(X0,X1) = iProver_top
    | r2_hidden(X0,X1) = iProver_top
    | r2_hidden(X1,X0) = iProver_top
    | v3_ordinal1(X0) != iProver_top
    | v3_ordinal1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19309])).

cnf(c_42061,plain,
    ( r2_hidden(X1,X0) = iProver_top
    | r1_tarski(X0,X1) = iProver_top
    | v3_ordinal1(X1) != iProver_top
    | v3_ordinal1(X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4298,c_87,c_487,c_19310])).

cnf(c_42062,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r1_tarski(X1,X0) = iProver_top
    | v3_ordinal1(X1) != iProver_top
    | v3_ordinal1(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_42061])).

cnf(c_34,negated_conjecture,
    ( ~ r2_hidden(k2_xboole_0(sK7,k1_tarski(sK7)),sK6)
    | ~ v4_ordinal1(sK6) ),
    inference(cnf_transformation,[],[f116])).

cnf(c_1826,plain,
    ( r2_hidden(k2_xboole_0(sK7,k1_tarski(sK7)),sK6) != iProver_top
    | v4_ordinal1(sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_42083,plain,
    ( r1_tarski(sK6,k2_xboole_0(sK7,k1_tarski(sK7))) = iProver_top
    | v4_ordinal1(sK6) != iProver_top
    | v3_ordinal1(k2_xboole_0(sK7,k1_tarski(sK7))) != iProver_top
    | v3_ordinal1(sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_42062,c_1826])).

cnf(c_42146,plain,
    ( r1_tarski(sK6,k2_xboole_0(sK7,k1_tarski(sK7)))
    | ~ v4_ordinal1(sK6)
    | ~ v3_ordinal1(k2_xboole_0(sK7,k1_tarski(sK7)))
    | ~ v3_ordinal1(sK6) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_42083])).

cnf(c_3402,plain,
    ( r2_hidden(sK7,sK3(k2_xboole_0(X0,k1_tarski(X0)),sK7))
    | ~ r2_hidden(sK7,k3_tarski(k2_xboole_0(X0,k1_tarski(X0)))) ),
    inference(instantiation,[status(thm)],[c_2160])).

cnf(c_28296,plain,
    ( r2_hidden(sK7,sK3(k2_xboole_0(sK7,k1_tarski(sK7)),sK7))
    | ~ r2_hidden(sK7,k3_tarski(k2_xboole_0(sK7,k1_tarski(sK7)))) ),
    inference(instantiation,[status(thm)],[c_3402])).

cnf(c_1038,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_2150,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(sK7,X2)
    | X1 != X2
    | X0 != sK7 ),
    inference(instantiation,[status(thm)],[c_1038])).

cnf(c_3504,plain,
    ( ~ r2_hidden(sK7,X0)
    | r2_hidden(sK7,X1)
    | X1 != X0
    | sK7 != sK7 ),
    inference(instantiation,[status(thm)],[c_2150])).

cnf(c_6203,plain,
    ( ~ r2_hidden(sK7,X0)
    | r2_hidden(sK7,sK7)
    | sK7 != X0
    | sK7 != sK7 ),
    inference(instantiation,[status(thm)],[c_3504])).

cnf(c_26829,plain,
    ( ~ r2_hidden(sK7,sK3(k2_xboole_0(sK7,k1_tarski(sK7)),sK7))
    | r2_hidden(sK7,sK7)
    | sK7 != sK3(k2_xboole_0(sK7,k1_tarski(sK7)),sK7)
    | sK7 != sK7 ),
    inference(instantiation,[status(thm)],[c_6203])).

cnf(c_25,plain,
    ( ~ v3_ordinal1(X0)
    | v3_ordinal1(k2_xboole_0(X0,k1_tarski(X0))) ),
    inference(cnf_transformation,[],[f113])).

cnf(c_13242,plain,
    ( v3_ordinal1(k2_xboole_0(sK7,k1_tarski(sK7)))
    | ~ v3_ordinal1(sK7) ),
    inference(instantiation,[status(thm)],[c_25])).

cnf(c_2,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | ~ r1_tarski(X1,X2) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_5701,plain,
    ( ~ r2_hidden(sK3(X0,sK7),X0)
    | r2_hidden(sK3(X0,sK7),X1)
    | ~ r1_tarski(X0,X1) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_12372,plain,
    ( ~ r2_hidden(sK3(X0,sK7),X0)
    | r2_hidden(sK3(X0,sK7),k2_xboole_0(sK7,k1_tarski(sK7)))
    | ~ r1_tarski(X0,k2_xboole_0(sK7,k1_tarski(sK7))) ),
    inference(instantiation,[status(thm)],[c_5701])).

cnf(c_12375,plain,
    ( r2_hidden(sK3(sK6,sK7),k2_xboole_0(sK7,k1_tarski(sK7)))
    | ~ r2_hidden(sK3(sK6,sK7),sK6)
    | ~ r1_tarski(sK6,k2_xboole_0(sK7,k1_tarski(sK7))) ),
    inference(instantiation,[status(thm)],[c_12372])).

cnf(c_21,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,k2_xboole_0(X1,k1_tarski(X1))) ),
    inference(cnf_transformation,[],[f111])).

cnf(c_2854,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r1_tarski(k2_xboole_0(X1,k1_tarski(X1)),X0) ),
    inference(resolution,[status(thm)],[c_21,c_33])).

cnf(c_37,negated_conjecture,
    ( ~ r2_hidden(X0,sK6)
    | r2_hidden(k2_xboole_0(X0,k1_tarski(X0)),sK6)
    | v4_ordinal1(sK6)
    | ~ v3_ordinal1(X0) ),
    inference(cnf_transformation,[],[f117])).

cnf(c_3069,plain,
    ( ~ r2_hidden(X0,sK6)
    | r1_tarski(k2_xboole_0(X0,k1_tarski(X0)),sK6)
    | v4_ordinal1(sK6)
    | ~ v3_ordinal1(X0)
    | ~ v3_ordinal1(sK6) ),
    inference(resolution,[status(thm)],[c_486,c_37])).

cnf(c_38,negated_conjecture,
    ( v3_ordinal1(sK6) ),
    inference(cnf_transformation,[],[f104])).

cnf(c_1823,plain,
    ( r2_hidden(X0,sK6) != iProver_top
    | r2_hidden(k2_xboole_0(X0,k1_tarski(X0)),sK6) = iProver_top
    | v4_ordinal1(sK6) = iProver_top
    | v3_ordinal1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_37])).

cnf(c_2064,plain,
    ( r2_hidden(X0,sK6) != iProver_top
    | r1_tarski(k2_xboole_0(X0,k1_tarski(X0)),sK6) = iProver_top
    | v4_ordinal1(sK6) = iProver_top
    | v3_ordinal1(X0) != iProver_top
    | v3_ordinal1(sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_1823,c_1821])).

cnf(c_2065,plain,
    ( ~ r2_hidden(X0,sK6)
    | r1_tarski(k2_xboole_0(X0,k1_tarski(X0)),sK6)
    | v4_ordinal1(sK6)
    | ~ v3_ordinal1(X0)
    | ~ v3_ordinal1(sK6) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_2064])).

cnf(c_3330,plain,
    ( ~ v3_ordinal1(X0)
    | v4_ordinal1(sK6)
    | r1_tarski(k2_xboole_0(X0,k1_tarski(X0)),sK6)
    | ~ r2_hidden(X0,sK6) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3069,c_38,c_2065])).

cnf(c_3331,plain,
    ( ~ r2_hidden(X0,sK6)
    | r1_tarski(k2_xboole_0(X0,k1_tarski(X0)),sK6)
    | v4_ordinal1(sK6)
    | ~ v3_ordinal1(X0) ),
    inference(renaming,[status(thm)],[c_3330])).

cnf(c_10332,plain,
    ( ~ r2_hidden(X0,sK6)
    | ~ r2_hidden(sK6,X0)
    | v4_ordinal1(sK6)
    | ~ v3_ordinal1(X0) ),
    inference(resolution,[status(thm)],[c_2854,c_3331])).

cnf(c_23,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ v3_ordinal1(X1)
    | v3_ordinal1(X0) ),
    inference(cnf_transformation,[],[f93])).

cnf(c_29,plain,
    ( r2_hidden(sK4(X0),X0)
    | v3_ordinal1(k3_tarski(X0)) ),
    inference(cnf_transformation,[],[f98])).

cnf(c_2487,plain,
    ( ~ v3_ordinal1(X0)
    | v3_ordinal1(sK4(X0))
    | v3_ordinal1(k3_tarski(X0)) ),
    inference(resolution,[status(thm)],[c_23,c_29])).

cnf(c_28,plain,
    ( ~ v3_ordinal1(sK4(X0))
    | v3_ordinal1(k3_tarski(X0)) ),
    inference(cnf_transformation,[],[f99])).

cnf(c_2642,plain,
    ( ~ v3_ordinal1(X0)
    | v3_ordinal1(k3_tarski(X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2487,c_28])).

cnf(c_2645,plain,
    ( v3_ordinal1(k3_tarski(sK6))
    | ~ v3_ordinal1(sK6) ),
    inference(instantiation,[status(thm)],[c_2642])).

cnf(c_1,plain,
    ( r2_hidden(sK0(X0,X1),X0)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_3360,plain,
    ( r2_hidden(sK0(sK6,k3_tarski(X0)),sK6)
    | r1_tarski(sK6,k3_tarski(X0)) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_3367,plain,
    ( r2_hidden(sK0(sK6,k3_tarski(sK6)),sK6)
    | r1_tarski(sK6,k3_tarski(sK6)) ),
    inference(instantiation,[status(thm)],[c_3360])).

cnf(c_3432,plain,
    ( ~ r2_hidden(k3_tarski(X0),X1)
    | ~ r1_tarski(X1,k3_tarski(X0)) ),
    inference(instantiation,[status(thm)],[c_33])).

cnf(c_3434,plain,
    ( ~ r2_hidden(k3_tarski(sK6),sK6)
    | ~ r1_tarski(sK6,k3_tarski(sK6)) ),
    inference(instantiation,[status(thm)],[c_3432])).

cnf(c_15,plain,
    ( v4_ordinal1(X0)
    | k3_tarski(X0) != X0 ),
    inference(cnf_transformation,[],[f86])).

cnf(c_6092,plain,
    ( r2_hidden(X0,k3_tarski(X0))
    | r2_hidden(k3_tarski(X0),X0)
    | v4_ordinal1(X0)
    | ~ v3_ordinal1(X0)
    | ~ v3_ordinal1(k3_tarski(X0)) ),
    inference(resolution,[status(thm)],[c_24,c_15])).

cnf(c_6094,plain,
    ( r2_hidden(k3_tarski(sK6),sK6)
    | r2_hidden(sK6,k3_tarski(sK6))
    | v4_ordinal1(sK6)
    | ~ v3_ordinal1(k3_tarski(sK6))
    | ~ v3_ordinal1(sK6) ),
    inference(instantiation,[status(thm)],[c_6092])).

cnf(c_8827,plain,
    ( ~ r2_hidden(sK0(sK6,k3_tarski(X0)),X1)
    | ~ v3_ordinal1(X1)
    | v3_ordinal1(sK0(sK6,k3_tarski(X0))) ),
    inference(instantiation,[status(thm)],[c_23])).

cnf(c_8829,plain,
    ( ~ r2_hidden(sK0(sK6,k3_tarski(sK6)),sK6)
    | v3_ordinal1(sK0(sK6,k3_tarski(sK6)))
    | ~ v3_ordinal1(sK6) ),
    inference(instantiation,[status(thm)],[c_8827])).

cnf(c_10,plain,
    ( ~ r2_hidden(X0,k3_tarski(X1))
    | r2_hidden(sK3(X1,X0),X1) ),
    inference(cnf_transformation,[],[f121])).

cnf(c_1847,plain,
    ( r2_hidden(X0,k3_tarski(X1)) != iProver_top
    | r2_hidden(sK3(X1,X0),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_3037,plain,
    ( r2_hidden(X0,k3_tarski(X1)) != iProver_top
    | r1_tarski(sK3(X1,X0),X1) = iProver_top
    | v3_ordinal1(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1847,c_1821])).

cnf(c_1846,plain,
    ( r2_hidden(X0,sK3(X1,X0)) = iProver_top
    | r2_hidden(X0,k3_tarski(X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_1827,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_2828,plain,
    ( r2_hidden(X0,k3_tarski(X1)) != iProver_top
    | r1_tarski(sK3(X1,X0),X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1846,c_1827])).

cnf(c_9218,plain,
    ( r2_hidden(X0,k3_tarski(X0)) != iProver_top
    | v3_ordinal1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_3037,c_2828])).

cnf(c_9222,plain,
    ( ~ r2_hidden(X0,k3_tarski(X0))
    | ~ v3_ordinal1(X0) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_9218])).

cnf(c_9224,plain,
    ( ~ r2_hidden(sK6,k3_tarski(sK6))
    | ~ v3_ordinal1(sK6) ),
    inference(instantiation,[status(thm)],[c_9222])).

cnf(c_20,plain,
    ( r2_hidden(X0,k2_xboole_0(X0,k1_tarski(X0))) ),
    inference(cnf_transformation,[],[f123])).

cnf(c_4365,plain,
    ( r2_hidden(X0,k3_tarski(X1))
    | ~ r2_hidden(k2_xboole_0(X0,k1_tarski(X0)),X1) ),
    inference(resolution,[status(thm)],[c_9,c_20])).

cnf(c_10356,plain,
    ( r2_hidden(X0,k3_tarski(sK6))
    | ~ r2_hidden(X0,sK6)
    | v4_ordinal1(sK6)
    | ~ v3_ordinal1(X0) ),
    inference(resolution,[status(thm)],[c_4365,c_37])).

cnf(c_0,plain,
    ( ~ r2_hidden(sK0(X0,X1),X1)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_10664,plain,
    ( ~ r2_hidden(sK0(X0,k3_tarski(sK6)),sK6)
    | r1_tarski(X0,k3_tarski(sK6))
    | v4_ordinal1(sK6)
    | ~ v3_ordinal1(sK0(X0,k3_tarski(sK6))) ),
    inference(resolution,[status(thm)],[c_10356,c_0])).

cnf(c_10666,plain,
    ( ~ r2_hidden(sK0(sK6,k3_tarski(sK6)),sK6)
    | r1_tarski(sK6,k3_tarski(sK6))
    | v4_ordinal1(sK6)
    | ~ v3_ordinal1(sK0(sK6,k3_tarski(sK6))) ),
    inference(instantiation,[status(thm)],[c_10664])).

cnf(c_10847,plain,
    ( v4_ordinal1(sK6) ),
    inference(global_propositional_subsumption,[status(thm)],[c_10332,c_38,c_2645,c_3367,c_3434,c_6094,c_8829,c_9224,c_10666])).

cnf(c_22,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k2_xboole_0(X1,k1_tarski(X1)))
    | X1 = X0 ),
    inference(cnf_transformation,[],[f112])).

cnf(c_2448,plain,
    ( ~ r2_hidden(X0,k2_xboole_0(sK7,k1_tarski(sK7)))
    | r2_hidden(X0,sK7)
    | sK7 = X0 ),
    inference(instantiation,[status(thm)],[c_22])).

cnf(c_6533,plain,
    ( ~ r2_hidden(sK3(k2_xboole_0(sK7,k1_tarski(sK7)),sK7),k2_xboole_0(sK7,k1_tarski(sK7)))
    | r2_hidden(sK3(k2_xboole_0(sK7,k1_tarski(sK7)),sK7),sK7)
    | sK7 = sK3(k2_xboole_0(sK7,k1_tarski(sK7)),sK7) ),
    inference(instantiation,[status(thm)],[c_2448])).

cnf(c_2161,plain,
    ( r2_hidden(sK3(X0,sK7),X0)
    | ~ r2_hidden(sK7,k3_tarski(X0)) ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_3401,plain,
    ( r2_hidden(sK3(k2_xboole_0(X0,k1_tarski(X0)),sK7),k2_xboole_0(X0,k1_tarski(X0)))
    | ~ r2_hidden(sK7,k3_tarski(k2_xboole_0(X0,k1_tarski(X0)))) ),
    inference(instantiation,[status(thm)],[c_2161])).

cnf(c_6532,plain,
    ( r2_hidden(sK3(k2_xboole_0(sK7,k1_tarski(sK7)),sK7),k2_xboole_0(sK7,k1_tarski(sK7)))
    | ~ r2_hidden(sK7,k3_tarski(k2_xboole_0(sK7,k1_tarski(sK7)))) ),
    inference(instantiation,[status(thm)],[c_3401])).

cnf(c_3152,plain,
    ( ~ r2_hidden(X0,sK7)
    | r1_tarski(X0,sK7)
    | ~ v3_ordinal1(sK7) ),
    inference(instantiation,[status(thm)],[c_486])).

cnf(c_5751,plain,
    ( ~ r2_hidden(sK3(sK7,sK7),sK7)
    | r1_tarski(sK3(sK7,sK7),sK7)
    | ~ v3_ordinal1(sK7) ),
    inference(instantiation,[status(thm)],[c_3152])).

cnf(c_5750,plain,
    ( r2_hidden(sK3(sK7,sK7),sK7)
    | ~ r2_hidden(sK7,k3_tarski(sK7)) ),
    inference(instantiation,[status(thm)],[c_2161])).

cnf(c_2107,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(sK7,sK6)
    | X1 != sK6
    | X0 != sK7 ),
    inference(instantiation,[status(thm)],[c_1038])).

cnf(c_2221,plain,
    ( r2_hidden(sK7,X0)
    | ~ r2_hidden(sK7,sK6)
    | X0 != sK6
    | sK7 != sK7 ),
    inference(instantiation,[status(thm)],[c_2107])).

cnf(c_3388,plain,
    ( r2_hidden(sK7,k3_tarski(X0))
    | ~ r2_hidden(sK7,sK6)
    | k3_tarski(X0) != sK6
    | sK7 != sK7 ),
    inference(instantiation,[status(thm)],[c_2221])).

cnf(c_3390,plain,
    ( r2_hidden(sK7,k3_tarski(sK6))
    | ~ r2_hidden(sK7,sK6)
    | k3_tarski(sK6) != sK6
    | sK7 != sK7 ),
    inference(instantiation,[status(thm)],[c_3388])).

cnf(c_5,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f119])).

cnf(c_3164,plain,
    ( r1_tarski(sK7,sK7) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_3163,plain,
    ( ~ r2_hidden(sK7,sK7)
    | ~ r1_tarski(sK7,sK7) ),
    inference(instantiation,[status(thm)],[c_2152])).

cnf(c_1036,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_2222,plain,
    ( sK7 = sK7 ),
    inference(instantiation,[status(thm)],[c_1036])).

cnf(c_2171,plain,
    ( r2_hidden(sK7,sK3(sK6,sK7))
    | ~ r2_hidden(sK7,k3_tarski(sK6)) ),
    inference(instantiation,[status(thm)],[c_2160])).

cnf(c_2167,plain,
    ( r2_hidden(sK3(sK6,sK7),sK6)
    | ~ r2_hidden(sK7,k3_tarski(sK6)) ),
    inference(instantiation,[status(thm)],[c_2161])).

cnf(c_16,plain,
    ( ~ v4_ordinal1(X0)
    | k3_tarski(X0) = X0 ),
    inference(cnf_transformation,[],[f85])).

cnf(c_94,plain,
    ( ~ v4_ordinal1(sK6)
    | k3_tarski(sK6) = sK6 ),
    inference(instantiation,[status(thm)],[c_16])).

cnf(c_35,negated_conjecture,
    ( r2_hidden(sK7,sK6)
    | ~ v4_ordinal1(sK6) ),
    inference(cnf_transformation,[],[f107])).

cnf(c_36,negated_conjecture,
    ( ~ v4_ordinal1(sK6)
    | v3_ordinal1(sK7) ),
    inference(cnf_transformation,[],[f106])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_85037,c_81604,c_75458,c_57742,c_42146,c_28296,c_26829,c_13242,c_12375,c_10847,c_6533,c_6532,c_5751,c_5750,c_3390,c_3164,c_3163,c_2222,c_2171,c_2167,c_94,c_35,c_36,c_38])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n023.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 17:06:20 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running in FOF mode
% 23.83/3.51  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 23.83/3.51  
% 23.83/3.51  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 23.83/3.51  
% 23.83/3.51  ------  iProver source info
% 23.83/3.51  
% 23.83/3.51  git: date: 2020-06-30 10:37:57 +0100
% 23.83/3.51  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 23.83/3.51  git: non_committed_changes: false
% 23.83/3.51  git: last_make_outside_of_git: false
% 23.83/3.51  
% 23.83/3.51  ------ 
% 23.83/3.51  ------ Parsing...
% 23.83/3.51  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 23.83/3.51  
% 23.83/3.51  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 23.83/3.51  
% 23.83/3.51  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 23.83/3.51  
% 23.83/3.51  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 23.83/3.51  ------ Proving...
% 23.83/3.51  ------ Problem Properties 
% 23.83/3.51  
% 23.83/3.51  
% 23.83/3.51  clauses                                 36
% 23.83/3.51  conjectures                             5
% 23.83/3.51  EPR                                     13
% 23.83/3.51  Horn                                    27
% 23.83/3.51  unary                                   5
% 23.83/3.51  binary                                  14
% 23.83/3.51  lits                                    93
% 23.83/3.51  lits eq                                 8
% 23.83/3.51  fd_pure                                 0
% 23.83/3.51  fd_pseudo                               0
% 23.83/3.51  fd_cond                                 0
% 23.83/3.51  fd_pseudo_cond                          6
% 23.83/3.51  AC symbols                              0
% 23.83/3.51  
% 23.83/3.51  ------ Input Options Time Limit: Unbounded
% 23.83/3.51  
% 23.83/3.51  
% 23.83/3.51  ------ 
% 23.83/3.51  Current options:
% 23.83/3.51  ------ 
% 23.83/3.51  
% 23.83/3.51  
% 23.83/3.51  
% 23.83/3.51  
% 23.83/3.51  ------ Proving...
% 23.83/3.51  
% 23.83/3.51  
% 23.83/3.51  % SZS status Theorem for theBenchmark.p
% 23.83/3.51  
% 23.83/3.51  % SZS output start CNFRefutation for theBenchmark.p
% 23.83/3.51  
% 23.83/3.51  fof(f3,axiom,(
% 23.83/3.51    ! [X0,X1] : (k3_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (r2_hidden(X3,X0) & r2_hidden(X2,X3))))),
% 23.83/3.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.83/3.51  
% 23.83/3.51  fof(f48,plain,(
% 23.83/3.51    ! [X0,X1] : ((k3_tarski(X0) = X1 | ? [X2] : ((! [X3] : (~r2_hidden(X3,X0) | ~r2_hidden(X2,X3)) | ~r2_hidden(X2,X1)) & (? [X3] : (r2_hidden(X3,X0) & r2_hidden(X2,X3)) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ! [X3] : (~r2_hidden(X3,X0) | ~r2_hidden(X2,X3))) & (? [X3] : (r2_hidden(X3,X0) & r2_hidden(X2,X3)) | ~r2_hidden(X2,X1))) | k3_tarski(X0) != X1))),
% 23.83/3.51    inference(nnf_transformation,[],[f3])).
% 23.83/3.51  
% 23.83/3.51  fof(f49,plain,(
% 23.83/3.51    ! [X0,X1] : ((k3_tarski(X0) = X1 | ? [X2] : ((! [X3] : (~r2_hidden(X3,X0) | ~r2_hidden(X2,X3)) | ~r2_hidden(X2,X1)) & (? [X4] : (r2_hidden(X4,X0) & r2_hidden(X2,X4)) | r2_hidden(X2,X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : (~r2_hidden(X6,X0) | ~r2_hidden(X5,X6))) & (? [X7] : (r2_hidden(X7,X0) & r2_hidden(X5,X7)) | ~r2_hidden(X5,X1))) | k3_tarski(X0) != X1))),
% 23.83/3.51    inference(rectify,[],[f48])).
% 23.83/3.51  
% 23.83/3.51  fof(f52,plain,(
% 23.83/3.51    ! [X5,X0] : (? [X7] : (r2_hidden(X7,X0) & r2_hidden(X5,X7)) => (r2_hidden(sK3(X0,X5),X0) & r2_hidden(X5,sK3(X0,X5))))),
% 23.83/3.51    introduced(choice_axiom,[])).
% 23.83/3.51  
% 23.83/3.51  fof(f51,plain,(
% 23.83/3.51    ( ! [X2] : (! [X1,X0] : (? [X4] : (r2_hidden(X4,X0) & r2_hidden(X2,X4)) => (r2_hidden(sK2(X0,X1),X0) & r2_hidden(X2,sK2(X0,X1))))) )),
% 23.83/3.51    introduced(choice_axiom,[])).
% 23.83/3.51  
% 23.83/3.51  fof(f50,plain,(
% 23.83/3.51    ! [X1,X0] : (? [X2] : ((! [X3] : (~r2_hidden(X3,X0) | ~r2_hidden(X2,X3)) | ~r2_hidden(X2,X1)) & (? [X4] : (r2_hidden(X4,X0) & r2_hidden(X2,X4)) | r2_hidden(X2,X1))) => ((! [X3] : (~r2_hidden(X3,X0) | ~r2_hidden(sK1(X0,X1),X3)) | ~r2_hidden(sK1(X0,X1),X1)) & (? [X4] : (r2_hidden(X4,X0) & r2_hidden(sK1(X0,X1),X4)) | r2_hidden(sK1(X0,X1),X1))))),
% 23.83/3.51    introduced(choice_axiom,[])).
% 23.83/3.51  
% 23.83/3.51  fof(f53,plain,(
% 23.83/3.51    ! [X0,X1] : ((k3_tarski(X0) = X1 | ((! [X3] : (~r2_hidden(X3,X0) | ~r2_hidden(sK1(X0,X1),X3)) | ~r2_hidden(sK1(X0,X1),X1)) & ((r2_hidden(sK2(X0,X1),X0) & r2_hidden(sK1(X0,X1),sK2(X0,X1))) | r2_hidden(sK1(X0,X1),X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : (~r2_hidden(X6,X0) | ~r2_hidden(X5,X6))) & ((r2_hidden(sK3(X0,X5),X0) & r2_hidden(X5,sK3(X0,X5))) | ~r2_hidden(X5,X1))) | k3_tarski(X0) != X1))),
% 23.83/3.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f49,f52,f51,f50])).
% 23.83/3.51  
% 23.83/3.51  fof(f77,plain,(
% 23.83/3.51    ( ! [X6,X0,X5,X1] : (r2_hidden(X5,X1) | ~r2_hidden(X6,X0) | ~r2_hidden(X5,X6) | k3_tarski(X0) != X1) )),
% 23.83/3.51    inference(cnf_transformation,[],[f53])).
% 23.83/3.51  
% 23.83/3.51  fof(f120,plain,(
% 23.83/3.51    ( ! [X6,X0,X5] : (r2_hidden(X5,k3_tarski(X0)) | ~r2_hidden(X6,X0) | ~r2_hidden(X5,X6)) )),
% 23.83/3.51    inference(equality_resolution,[],[f77])).
% 23.83/3.51  
% 23.83/3.51  fof(f75,plain,(
% 23.83/3.51    ( ! [X0,X5,X1] : (r2_hidden(X5,sK3(X0,X5)) | ~r2_hidden(X5,X1) | k3_tarski(X0) != X1) )),
% 23.83/3.51    inference(cnf_transformation,[],[f53])).
% 23.83/3.51  
% 23.83/3.51  fof(f122,plain,(
% 23.83/3.51    ( ! [X0,X5] : (r2_hidden(X5,sK3(X0,X5)) | ~r2_hidden(X5,k3_tarski(X0))) )),
% 23.83/3.51    inference(equality_resolution,[],[f75])).
% 23.83/3.51  
% 23.83/3.51  fof(f18,axiom,(
% 23.83/3.51    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 23.83/3.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.83/3.51  
% 23.83/3.51  fof(f39,plain,(
% 23.83/3.51    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 23.83/3.51    inference(ennf_transformation,[],[f18])).
% 23.83/3.51  
% 23.83/3.51  fof(f103,plain,(
% 23.83/3.51    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1)) )),
% 23.83/3.51    inference(cnf_transformation,[],[f39])).
% 23.83/3.51  
% 23.83/3.51  fof(f13,axiom,(
% 23.83/3.51    ! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => ~(~r2_hidden(X1,X0) & X0 != X1 & ~r2_hidden(X0,X1))))),
% 23.83/3.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.83/3.51  
% 23.83/3.51  fof(f32,plain,(
% 23.83/3.51    ! [X0] : (! [X1] : ((r2_hidden(X1,X0) | X0 = X1 | r2_hidden(X0,X1)) | ~v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 23.83/3.51    inference(ennf_transformation,[],[f13])).
% 23.83/3.51  
% 23.83/3.51  fof(f33,plain,(
% 23.83/3.51    ! [X0] : (! [X1] : (r2_hidden(X1,X0) | X0 = X1 | r2_hidden(X0,X1) | ~v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 23.83/3.51    inference(flattening,[],[f32])).
% 23.83/3.51  
% 23.83/3.51  fof(f94,plain,(
% 23.83/3.51    ( ! [X0,X1] : (r2_hidden(X1,X0) | X0 = X1 | r2_hidden(X0,X1) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0)) )),
% 23.83/3.51    inference(cnf_transformation,[],[f33])).
% 23.83/3.51  
% 23.83/3.51  fof(f4,axiom,(
% 23.83/3.51    ! [X0] : (v3_ordinal1(X0) => (v2_ordinal1(X0) & v1_ordinal1(X0)))),
% 23.83/3.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.83/3.51  
% 23.83/3.51  fof(f22,plain,(
% 23.83/3.51    ! [X0] : (v3_ordinal1(X0) => v1_ordinal1(X0))),
% 23.83/3.51    inference(pure_predicate_removal,[],[f4])).
% 23.83/3.51  
% 23.83/3.51  fof(f24,plain,(
% 23.83/3.51    ! [X0] : (v1_ordinal1(X0) | ~v3_ordinal1(X0))),
% 23.83/3.51    inference(ennf_transformation,[],[f22])).
% 23.83/3.51  
% 23.83/3.51  fof(f81,plain,(
% 23.83/3.51    ( ! [X0] : (v1_ordinal1(X0) | ~v3_ordinal1(X0)) )),
% 23.83/3.51    inference(cnf_transformation,[],[f24])).
% 23.83/3.51  
% 23.83/3.51  fof(f7,axiom,(
% 23.83/3.51    ! [X0] : (v1_ordinal1(X0) <=> ! [X1] : (r2_hidden(X1,X0) => r1_tarski(X1,X0)))),
% 23.83/3.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.83/3.51  
% 23.83/3.51  fof(f21,plain,(
% 23.83/3.51    ! [X0] : (v1_ordinal1(X0) => ! [X1] : (r2_hidden(X1,X0) => r1_tarski(X1,X0)))),
% 23.83/3.51    inference(unused_predicate_definition_removal,[],[f7])).
% 23.83/3.51  
% 23.83/3.51  fof(f27,plain,(
% 23.83/3.51    ! [X0] : (! [X1] : (r1_tarski(X1,X0) | ~r2_hidden(X1,X0)) | ~v1_ordinal1(X0))),
% 23.83/3.51    inference(ennf_transformation,[],[f21])).
% 23.83/3.51  
% 23.83/3.51  fof(f84,plain,(
% 23.83/3.51    ( ! [X0,X1] : (r1_tarski(X1,X0) | ~r2_hidden(X1,X0) | ~v1_ordinal1(X0)) )),
% 23.83/3.51    inference(cnf_transformation,[],[f27])).
% 23.83/3.51  
% 23.83/3.51  fof(f9,axiom,(
% 23.83/3.51    ! [X0,X1] : ((v3_ordinal1(X1) & v3_ordinal1(X0)) => (r1_ordinal1(X0,X1) <=> r1_tarski(X0,X1)))),
% 23.83/3.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.83/3.51  
% 23.83/3.51  fof(f28,plain,(
% 23.83/3.51    ! [X0,X1] : ((r1_ordinal1(X0,X1) <=> r1_tarski(X0,X1)) | (~v3_ordinal1(X1) | ~v3_ordinal1(X0)))),
% 23.83/3.51    inference(ennf_transformation,[],[f9])).
% 23.83/3.51  
% 23.83/3.51  fof(f29,plain,(
% 23.83/3.51    ! [X0,X1] : ((r1_ordinal1(X0,X1) <=> r1_tarski(X0,X1)) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0))),
% 23.83/3.51    inference(flattening,[],[f28])).
% 23.83/3.51  
% 23.83/3.51  fof(f55,plain,(
% 23.83/3.51    ! [X0,X1] : (((r1_ordinal1(X0,X1) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~r1_ordinal1(X0,X1))) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0))),
% 23.83/3.51    inference(nnf_transformation,[],[f29])).
% 23.83/3.51  
% 23.83/3.51  fof(f87,plain,(
% 23.83/3.51    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r1_ordinal1(X0,X1) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0)) )),
% 23.83/3.51    inference(cnf_transformation,[],[f55])).
% 23.83/3.51  
% 23.83/3.51  fof(f5,axiom,(
% 23.83/3.51    ! [X0,X1] : ((v3_ordinal1(X1) & v3_ordinal1(X0)) => (r1_ordinal1(X1,X0) | r1_ordinal1(X0,X1)))),
% 23.83/3.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.83/3.51  
% 23.83/3.51  fof(f25,plain,(
% 23.83/3.51    ! [X0,X1] : ((r1_ordinal1(X1,X0) | r1_ordinal1(X0,X1)) | (~v3_ordinal1(X1) | ~v3_ordinal1(X0)))),
% 23.83/3.51    inference(ennf_transformation,[],[f5])).
% 23.83/3.51  
% 23.83/3.51  fof(f26,plain,(
% 23.83/3.51    ! [X0,X1] : (r1_ordinal1(X1,X0) | r1_ordinal1(X0,X1) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0))),
% 23.83/3.51    inference(flattening,[],[f25])).
% 23.83/3.51  
% 23.83/3.51  fof(f82,plain,(
% 23.83/3.51    ( ! [X0,X1] : (r1_ordinal1(X1,X0) | r1_ordinal1(X0,X1) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0)) )),
% 23.83/3.51    inference(cnf_transformation,[],[f26])).
% 23.83/3.51  
% 23.83/3.51  fof(f19,conjecture,(
% 23.83/3.51    ! [X0] : (v3_ordinal1(X0) => (v4_ordinal1(X0) <=> ! [X1] : (v3_ordinal1(X1) => (r2_hidden(X1,X0) => r2_hidden(k1_ordinal1(X1),X0)))))),
% 23.83/3.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.83/3.51  
% 23.83/3.51  fof(f20,negated_conjecture,(
% 23.83/3.51    ~! [X0] : (v3_ordinal1(X0) => (v4_ordinal1(X0) <=> ! [X1] : (v3_ordinal1(X1) => (r2_hidden(X1,X0) => r2_hidden(k1_ordinal1(X1),X0)))))),
% 23.83/3.51    inference(negated_conjecture,[],[f19])).
% 23.83/3.51  
% 23.83/3.51  fof(f40,plain,(
% 23.83/3.51    ? [X0] : ((v4_ordinal1(X0) <~> ! [X1] : ((r2_hidden(k1_ordinal1(X1),X0) | ~r2_hidden(X1,X0)) | ~v3_ordinal1(X1))) & v3_ordinal1(X0))),
% 23.83/3.51    inference(ennf_transformation,[],[f20])).
% 23.83/3.51  
% 23.83/3.51  fof(f41,plain,(
% 23.83/3.51    ? [X0] : ((v4_ordinal1(X0) <~> ! [X1] : (r2_hidden(k1_ordinal1(X1),X0) | ~r2_hidden(X1,X0) | ~v3_ordinal1(X1))) & v3_ordinal1(X0))),
% 23.83/3.51    inference(flattening,[],[f40])).
% 23.83/3.51  
% 23.83/3.51  fof(f63,plain,(
% 23.83/3.51    ? [X0] : (((? [X1] : (~r2_hidden(k1_ordinal1(X1),X0) & r2_hidden(X1,X0) & v3_ordinal1(X1)) | ~v4_ordinal1(X0)) & (! [X1] : (r2_hidden(k1_ordinal1(X1),X0) | ~r2_hidden(X1,X0) | ~v3_ordinal1(X1)) | v4_ordinal1(X0))) & v3_ordinal1(X0))),
% 23.83/3.51    inference(nnf_transformation,[],[f41])).
% 23.83/3.51  
% 23.83/3.51  fof(f64,plain,(
% 23.83/3.51    ? [X0] : ((? [X1] : (~r2_hidden(k1_ordinal1(X1),X0) & r2_hidden(X1,X0) & v3_ordinal1(X1)) | ~v4_ordinal1(X0)) & (! [X1] : (r2_hidden(k1_ordinal1(X1),X0) | ~r2_hidden(X1,X0) | ~v3_ordinal1(X1)) | v4_ordinal1(X0)) & v3_ordinal1(X0))),
% 23.83/3.51    inference(flattening,[],[f63])).
% 23.83/3.51  
% 23.83/3.51  fof(f65,plain,(
% 23.83/3.51    ? [X0] : ((? [X1] : (~r2_hidden(k1_ordinal1(X1),X0) & r2_hidden(X1,X0) & v3_ordinal1(X1)) | ~v4_ordinal1(X0)) & (! [X2] : (r2_hidden(k1_ordinal1(X2),X0) | ~r2_hidden(X2,X0) | ~v3_ordinal1(X2)) | v4_ordinal1(X0)) & v3_ordinal1(X0))),
% 23.83/3.51    inference(rectify,[],[f64])).
% 23.83/3.51  
% 23.83/3.51  fof(f67,plain,(
% 23.83/3.51    ( ! [X0] : (? [X1] : (~r2_hidden(k1_ordinal1(X1),X0) & r2_hidden(X1,X0) & v3_ordinal1(X1)) => (~r2_hidden(k1_ordinal1(sK7),X0) & r2_hidden(sK7,X0) & v3_ordinal1(sK7))) )),
% 23.83/3.51    introduced(choice_axiom,[])).
% 23.83/3.51  
% 23.83/3.51  fof(f66,plain,(
% 23.83/3.51    ? [X0] : ((? [X1] : (~r2_hidden(k1_ordinal1(X1),X0) & r2_hidden(X1,X0) & v3_ordinal1(X1)) | ~v4_ordinal1(X0)) & (! [X2] : (r2_hidden(k1_ordinal1(X2),X0) | ~r2_hidden(X2,X0) | ~v3_ordinal1(X2)) | v4_ordinal1(X0)) & v3_ordinal1(X0)) => ((? [X1] : (~r2_hidden(k1_ordinal1(X1),sK6) & r2_hidden(X1,sK6) & v3_ordinal1(X1)) | ~v4_ordinal1(sK6)) & (! [X2] : (r2_hidden(k1_ordinal1(X2),sK6) | ~r2_hidden(X2,sK6) | ~v3_ordinal1(X2)) | v4_ordinal1(sK6)) & v3_ordinal1(sK6))),
% 23.83/3.51    introduced(choice_axiom,[])).
% 23.83/3.51  
% 23.83/3.51  fof(f68,plain,(
% 23.83/3.51    ((~r2_hidden(k1_ordinal1(sK7),sK6) & r2_hidden(sK7,sK6) & v3_ordinal1(sK7)) | ~v4_ordinal1(sK6)) & (! [X2] : (r2_hidden(k1_ordinal1(X2),sK6) | ~r2_hidden(X2,sK6) | ~v3_ordinal1(X2)) | v4_ordinal1(sK6)) & v3_ordinal1(sK6)),
% 23.83/3.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7])],[f65,f67,f66])).
% 23.83/3.51  
% 23.83/3.51  fof(f108,plain,(
% 23.83/3.51    ~r2_hidden(k1_ordinal1(sK7),sK6) | ~v4_ordinal1(sK6)),
% 23.83/3.51    inference(cnf_transformation,[],[f68])).
% 23.83/3.51  
% 23.83/3.51  fof(f6,axiom,(
% 23.83/3.51    ! [X0] : k1_ordinal1(X0) = k2_xboole_0(X0,k1_tarski(X0))),
% 23.83/3.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.83/3.51  
% 23.83/3.51  fof(f83,plain,(
% 23.83/3.51    ( ! [X0] : (k1_ordinal1(X0) = k2_xboole_0(X0,k1_tarski(X0))) )),
% 23.83/3.51    inference(cnf_transformation,[],[f6])).
% 23.83/3.51  
% 23.83/3.51  fof(f116,plain,(
% 23.83/3.51    ~r2_hidden(k2_xboole_0(sK7,k1_tarski(sK7)),sK6) | ~v4_ordinal1(sK6)),
% 23.83/3.51    inference(definition_unfolding,[],[f108,f83])).
% 23.83/3.51  
% 23.83/3.51  fof(f14,axiom,(
% 23.83/3.51    ! [X0] : (v3_ordinal1(X0) => v3_ordinal1(k1_ordinal1(X0)))),
% 23.83/3.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.83/3.51  
% 23.83/3.51  fof(f34,plain,(
% 23.83/3.51    ! [X0] : (v3_ordinal1(k1_ordinal1(X0)) | ~v3_ordinal1(X0))),
% 23.83/3.51    inference(ennf_transformation,[],[f14])).
% 23.83/3.51  
% 23.83/3.51  fof(f95,plain,(
% 23.83/3.51    ( ! [X0] : (v3_ordinal1(k1_ordinal1(X0)) | ~v3_ordinal1(X0)) )),
% 23.83/3.51    inference(cnf_transformation,[],[f34])).
% 23.83/3.51  
% 23.83/3.51  fof(f113,plain,(
% 23.83/3.51    ( ! [X0] : (v3_ordinal1(k2_xboole_0(X0,k1_tarski(X0))) | ~v3_ordinal1(X0)) )),
% 23.83/3.51    inference(definition_unfolding,[],[f95,f83])).
% 23.83/3.51  
% 23.83/3.51  fof(f1,axiom,(
% 23.83/3.51    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 23.83/3.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.83/3.51  
% 23.83/3.51  fof(f23,plain,(
% 23.83/3.51    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 23.83/3.51    inference(ennf_transformation,[],[f1])).
% 23.83/3.51  
% 23.83/3.51  fof(f42,plain,(
% 23.83/3.51    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 23.83/3.51    inference(nnf_transformation,[],[f23])).
% 23.83/3.51  
% 23.83/3.51  fof(f43,plain,(
% 23.83/3.51    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 23.83/3.51    inference(rectify,[],[f42])).
% 23.83/3.51  
% 23.83/3.51  fof(f44,plain,(
% 23.83/3.51    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 23.83/3.51    introduced(choice_axiom,[])).
% 23.83/3.51  
% 23.83/3.51  fof(f45,plain,(
% 23.83/3.51    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 23.83/3.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f43,f44])).
% 23.83/3.51  
% 23.83/3.51  fof(f69,plain,(
% 23.83/3.51    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,X1)) )),
% 23.83/3.51    inference(cnf_transformation,[],[f45])).
% 23.83/3.51  
% 23.83/3.51  fof(f11,axiom,(
% 23.83/3.51    ! [X0,X1] : (r2_hidden(X0,k1_ordinal1(X1)) <=> (X0 = X1 | r2_hidden(X0,X1)))),
% 23.83/3.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.83/3.51  
% 23.83/3.51  fof(f56,plain,(
% 23.83/3.51    ! [X0,X1] : ((r2_hidden(X0,k1_ordinal1(X1)) | (X0 != X1 & ~r2_hidden(X0,X1))) & ((X0 = X1 | r2_hidden(X0,X1)) | ~r2_hidden(X0,k1_ordinal1(X1))))),
% 23.83/3.51    inference(nnf_transformation,[],[f11])).
% 23.83/3.51  
% 23.83/3.51  fof(f57,plain,(
% 23.83/3.51    ! [X0,X1] : ((r2_hidden(X0,k1_ordinal1(X1)) | (X0 != X1 & ~r2_hidden(X0,X1))) & (X0 = X1 | r2_hidden(X0,X1) | ~r2_hidden(X0,k1_ordinal1(X1))))),
% 23.83/3.51    inference(flattening,[],[f56])).
% 23.83/3.51  
% 23.83/3.51  fof(f91,plain,(
% 23.83/3.51    ( ! [X0,X1] : (r2_hidden(X0,k1_ordinal1(X1)) | ~r2_hidden(X0,X1)) )),
% 23.83/3.51    inference(cnf_transformation,[],[f57])).
% 23.83/3.51  
% 23.83/3.51  fof(f111,plain,(
% 23.83/3.51    ( ! [X0,X1] : (r2_hidden(X0,k2_xboole_0(X1,k1_tarski(X1))) | ~r2_hidden(X0,X1)) )),
% 23.83/3.51    inference(definition_unfolding,[],[f91,f83])).
% 23.83/3.51  
% 23.83/3.51  fof(f105,plain,(
% 23.83/3.51    ( ! [X2] : (r2_hidden(k1_ordinal1(X2),sK6) | ~r2_hidden(X2,sK6) | ~v3_ordinal1(X2) | v4_ordinal1(sK6)) )),
% 23.83/3.51    inference(cnf_transformation,[],[f68])).
% 23.83/3.51  
% 23.83/3.51  fof(f117,plain,(
% 23.83/3.51    ( ! [X2] : (r2_hidden(k2_xboole_0(X2,k1_tarski(X2)),sK6) | ~r2_hidden(X2,sK6) | ~v3_ordinal1(X2) | v4_ordinal1(sK6)) )),
% 23.83/3.51    inference(definition_unfolding,[],[f105,f83])).
% 23.83/3.51  
% 23.83/3.51  fof(f104,plain,(
% 23.83/3.51    v3_ordinal1(sK6)),
% 23.83/3.51    inference(cnf_transformation,[],[f68])).
% 23.83/3.51  
% 23.83/3.51  fof(f12,axiom,(
% 23.83/3.51    ! [X0,X1] : (v3_ordinal1(X1) => (r2_hidden(X0,X1) => v3_ordinal1(X0)))),
% 23.83/3.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.83/3.51  
% 23.83/3.51  fof(f30,plain,(
% 23.83/3.51    ! [X0,X1] : ((v3_ordinal1(X0) | ~r2_hidden(X0,X1)) | ~v3_ordinal1(X1))),
% 23.83/3.51    inference(ennf_transformation,[],[f12])).
% 23.83/3.51  
% 23.83/3.51  fof(f31,plain,(
% 23.83/3.51    ! [X0,X1] : (v3_ordinal1(X0) | ~r2_hidden(X0,X1) | ~v3_ordinal1(X1))),
% 23.83/3.51    inference(flattening,[],[f30])).
% 23.83/3.51  
% 23.83/3.51  fof(f93,plain,(
% 23.83/3.51    ( ! [X0,X1] : (v3_ordinal1(X0) | ~r2_hidden(X0,X1) | ~v3_ordinal1(X1)) )),
% 23.83/3.51    inference(cnf_transformation,[],[f31])).
% 23.83/3.51  
% 23.83/3.51  fof(f16,axiom,(
% 23.83/3.51    ! [X0] : (! [X1] : (r2_hidden(X1,X0) => v3_ordinal1(X1)) => v3_ordinal1(k3_tarski(X0)))),
% 23.83/3.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.83/3.51  
% 23.83/3.51  fof(f36,plain,(
% 23.83/3.51    ! [X0] : (v3_ordinal1(k3_tarski(X0)) | ? [X1] : (~v3_ordinal1(X1) & r2_hidden(X1,X0)))),
% 23.83/3.51    inference(ennf_transformation,[],[f16])).
% 23.83/3.51  
% 23.83/3.51  fof(f59,plain,(
% 23.83/3.51    ! [X0] : (? [X1] : (~v3_ordinal1(X1) & r2_hidden(X1,X0)) => (~v3_ordinal1(sK4(X0)) & r2_hidden(sK4(X0),X0)))),
% 23.83/3.51    introduced(choice_axiom,[])).
% 23.83/3.51  
% 23.83/3.51  fof(f60,plain,(
% 23.83/3.51    ! [X0] : (v3_ordinal1(k3_tarski(X0)) | (~v3_ordinal1(sK4(X0)) & r2_hidden(sK4(X0),X0)))),
% 23.83/3.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f36,f59])).
% 23.83/3.51  
% 23.83/3.51  fof(f98,plain,(
% 23.83/3.51    ( ! [X0] : (v3_ordinal1(k3_tarski(X0)) | r2_hidden(sK4(X0),X0)) )),
% 23.83/3.51    inference(cnf_transformation,[],[f60])).
% 23.83/3.51  
% 23.83/3.51  fof(f99,plain,(
% 23.83/3.51    ( ! [X0] : (v3_ordinal1(k3_tarski(X0)) | ~v3_ordinal1(sK4(X0))) )),
% 23.83/3.51    inference(cnf_transformation,[],[f60])).
% 23.83/3.51  
% 23.83/3.51  fof(f70,plain,(
% 23.83/3.51    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK0(X0,X1),X0)) )),
% 23.83/3.51    inference(cnf_transformation,[],[f45])).
% 23.83/3.51  
% 23.83/3.51  fof(f8,axiom,(
% 23.83/3.51    ! [X0] : (v4_ordinal1(X0) <=> k3_tarski(X0) = X0)),
% 23.83/3.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.83/3.51  
% 23.83/3.51  fof(f54,plain,(
% 23.83/3.51    ! [X0] : ((v4_ordinal1(X0) | k3_tarski(X0) != X0) & (k3_tarski(X0) = X0 | ~v4_ordinal1(X0)))),
% 23.83/3.51    inference(nnf_transformation,[],[f8])).
% 23.83/3.51  
% 23.83/3.51  fof(f86,plain,(
% 23.83/3.51    ( ! [X0] : (v4_ordinal1(X0) | k3_tarski(X0) != X0) )),
% 23.83/3.51    inference(cnf_transformation,[],[f54])).
% 23.83/3.51  
% 23.83/3.51  fof(f76,plain,(
% 23.83/3.51    ( ! [X0,X5,X1] : (r2_hidden(sK3(X0,X5),X0) | ~r2_hidden(X5,X1) | k3_tarski(X0) != X1) )),
% 23.83/3.51    inference(cnf_transformation,[],[f53])).
% 23.83/3.51  
% 23.83/3.51  fof(f121,plain,(
% 23.83/3.51    ( ! [X0,X5] : (r2_hidden(sK3(X0,X5),X0) | ~r2_hidden(X5,k3_tarski(X0))) )),
% 23.83/3.51    inference(equality_resolution,[],[f76])).
% 23.83/3.51  
% 23.83/3.51  fof(f92,plain,(
% 23.83/3.51    ( ! [X0,X1] : (r2_hidden(X0,k1_ordinal1(X1)) | X0 != X1) )),
% 23.83/3.51    inference(cnf_transformation,[],[f57])).
% 23.83/3.51  
% 23.83/3.51  fof(f110,plain,(
% 23.83/3.51    ( ! [X0,X1] : (r2_hidden(X0,k2_xboole_0(X1,k1_tarski(X1))) | X0 != X1) )),
% 23.83/3.51    inference(definition_unfolding,[],[f92,f83])).
% 23.83/3.51  
% 23.83/3.51  fof(f123,plain,(
% 23.83/3.51    ( ! [X1] : (r2_hidden(X1,k2_xboole_0(X1,k1_tarski(X1)))) )),
% 23.83/3.51    inference(equality_resolution,[],[f110])).
% 23.83/3.51  
% 23.83/3.51  fof(f71,plain,(
% 23.83/3.51    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r2_hidden(sK0(X0,X1),X1)) )),
% 23.83/3.51    inference(cnf_transformation,[],[f45])).
% 23.83/3.51  
% 23.83/3.51  fof(f90,plain,(
% 23.83/3.51    ( ! [X0,X1] : (X0 = X1 | r2_hidden(X0,X1) | ~r2_hidden(X0,k1_ordinal1(X1))) )),
% 23.83/3.51    inference(cnf_transformation,[],[f57])).
% 23.83/3.51  
% 23.83/3.51  fof(f112,plain,(
% 23.83/3.51    ( ! [X0,X1] : (X0 = X1 | r2_hidden(X0,X1) | ~r2_hidden(X0,k2_xboole_0(X1,k1_tarski(X1)))) )),
% 23.83/3.51    inference(definition_unfolding,[],[f90,f83])).
% 23.83/3.51  
% 23.83/3.51  fof(f2,axiom,(
% 23.83/3.51    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 23.83/3.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.83/3.51  
% 23.83/3.51  fof(f46,plain,(
% 23.83/3.51    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 23.83/3.51    inference(nnf_transformation,[],[f2])).
% 23.83/3.51  
% 23.83/3.51  fof(f47,plain,(
% 23.83/3.51    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 23.83/3.51    inference(flattening,[],[f46])).
% 23.83/3.51  
% 23.83/3.51  fof(f72,plain,(
% 23.83/3.51    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 23.83/3.51    inference(cnf_transformation,[],[f47])).
% 23.83/3.51  
% 23.83/3.51  fof(f119,plain,(
% 23.83/3.51    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 23.83/3.51    inference(equality_resolution,[],[f72])).
% 23.83/3.51  
% 23.83/3.51  fof(f85,plain,(
% 23.83/3.51    ( ! [X0] : (k3_tarski(X0) = X0 | ~v4_ordinal1(X0)) )),
% 23.83/3.51    inference(cnf_transformation,[],[f54])).
% 23.83/3.51  
% 23.83/3.51  fof(f107,plain,(
% 23.83/3.51    r2_hidden(sK7,sK6) | ~v4_ordinal1(sK6)),
% 23.83/3.51    inference(cnf_transformation,[],[f68])).
% 23.83/3.51  
% 23.83/3.51  fof(f106,plain,(
% 23.83/3.51    v3_ordinal1(sK7) | ~v4_ordinal1(sK6)),
% 23.83/3.51    inference(cnf_transformation,[],[f68])).
% 23.83/3.51  
% 23.83/3.51  cnf(c_9,plain,
% 23.83/3.51      ( ~ r2_hidden(X0,X1)
% 23.83/3.51      | ~ r2_hidden(X2,X0)
% 23.83/3.51      | r2_hidden(X2,k3_tarski(X1)) ),
% 23.83/3.51      inference(cnf_transformation,[],[f120]) ).
% 23.83/3.51  
% 23.83/3.51  cnf(c_2147,plain,
% 23.83/3.51      ( ~ r2_hidden(X0,X1)
% 23.83/3.51      | ~ r2_hidden(sK7,X0)
% 23.83/3.51      | r2_hidden(sK7,k3_tarski(X1)) ),
% 23.83/3.51      inference(instantiation,[status(thm)],[c_9]) ).
% 23.83/3.51  
% 23.83/3.51  cnf(c_12305,plain,
% 23.83/3.51      ( ~ r2_hidden(sK3(X0,sK7),X1)
% 23.83/3.51      | ~ r2_hidden(sK7,sK3(X0,sK7))
% 23.83/3.51      | r2_hidden(sK7,k3_tarski(X1)) ),
% 23.83/3.51      inference(instantiation,[status(thm)],[c_2147]) ).
% 23.83/3.51  
% 23.83/3.51  cnf(c_24584,plain,
% 23.83/3.51      ( ~ r2_hidden(sK3(X0,sK7),sK7)
% 23.83/3.51      | ~ r2_hidden(sK7,sK3(X0,sK7))
% 23.83/3.51      | r2_hidden(sK7,k3_tarski(sK7)) ),
% 23.83/3.51      inference(instantiation,[status(thm)],[c_12305]) ).
% 23.83/3.51  
% 23.83/3.51  cnf(c_85037,plain,
% 23.83/3.51      ( ~ r2_hidden(sK3(k2_xboole_0(sK7,k1_tarski(sK7)),sK7),sK7)
% 23.83/3.51      | ~ r2_hidden(sK7,sK3(k2_xboole_0(sK7,k1_tarski(sK7)),sK7))
% 23.83/3.51      | r2_hidden(sK7,k3_tarski(sK7)) ),
% 23.83/3.51      inference(instantiation,[status(thm)],[c_24584]) ).
% 23.83/3.51  
% 23.83/3.51  cnf(c_11,plain,
% 23.83/3.51      ( r2_hidden(X0,sK3(X1,X0)) | ~ r2_hidden(X0,k3_tarski(X1)) ),
% 23.83/3.51      inference(cnf_transformation,[],[f122]) ).
% 23.83/3.51  
% 23.83/3.51  cnf(c_2160,plain,
% 23.83/3.51      ( r2_hidden(sK7,sK3(X0,sK7)) | ~ r2_hidden(sK7,k3_tarski(X0)) ),
% 23.83/3.51      inference(instantiation,[status(thm)],[c_11]) ).
% 23.83/3.51  
% 23.83/3.51  cnf(c_81604,plain,
% 23.83/3.51      ( r2_hidden(sK7,sK3(sK7,sK7)) | ~ r2_hidden(sK7,k3_tarski(sK7)) ),
% 23.83/3.51      inference(instantiation,[status(thm)],[c_2160]) ).
% 23.83/3.51  
% 23.83/3.51  cnf(c_33,plain,
% 23.83/3.51      ( ~ r2_hidden(X0,X1) | ~ r1_tarski(X1,X0) ),
% 23.83/3.51      inference(cnf_transformation,[],[f103]) ).
% 23.83/3.51  
% 23.83/3.51  cnf(c_2152,plain,
% 23.83/3.51      ( ~ r2_hidden(sK7,X0) | ~ r1_tarski(X0,sK7) ),
% 23.83/3.51      inference(instantiation,[status(thm)],[c_33]) ).
% 23.83/3.51  
% 23.83/3.51  cnf(c_10171,plain,
% 23.83/3.51      ( ~ r2_hidden(sK7,sK3(X0,sK7)) | ~ r1_tarski(sK3(X0,sK7),sK7) ),
% 23.83/3.51      inference(instantiation,[status(thm)],[c_2152]) ).
% 23.83/3.51  
% 23.83/3.51  cnf(c_75458,plain,
% 23.83/3.51      ( ~ r2_hidden(sK7,sK3(sK7,sK7)) | ~ r1_tarski(sK3(sK7,sK7),sK7) ),
% 23.83/3.51      inference(instantiation,[status(thm)],[c_10171]) ).
% 23.83/3.51  
% 23.83/3.51  cnf(c_57736,plain,
% 23.83/3.51      ( ~ r2_hidden(sK3(X0,sK7),k2_xboole_0(sK7,k1_tarski(sK7)))
% 23.83/3.51      | ~ r2_hidden(sK7,sK3(X0,sK7))
% 23.83/3.51      | r2_hidden(sK7,k3_tarski(k2_xboole_0(sK7,k1_tarski(sK7)))) ),
% 23.83/3.51      inference(instantiation,[status(thm)],[c_12305]) ).
% 23.83/3.51  
% 23.83/3.51  cnf(c_57742,plain,
% 23.83/3.51      ( ~ r2_hidden(sK3(sK6,sK7),k2_xboole_0(sK7,k1_tarski(sK7)))
% 23.83/3.51      | ~ r2_hidden(sK7,sK3(sK6,sK7))
% 23.83/3.51      | r2_hidden(sK7,k3_tarski(k2_xboole_0(sK7,k1_tarski(sK7)))) ),
% 23.83/3.51      inference(instantiation,[status(thm)],[c_57736]) ).
% 23.83/3.51  
% 23.83/3.51  cnf(c_24,plain,
% 23.83/3.51      ( r2_hidden(X0,X1)
% 23.83/3.51      | r2_hidden(X1,X0)
% 23.83/3.51      | ~ v3_ordinal1(X0)
% 23.83/3.51      | ~ v3_ordinal1(X1)
% 23.83/3.51      | X1 = X0 ),
% 23.83/3.51      inference(cnf_transformation,[],[f94]) ).
% 23.83/3.51  
% 23.83/3.51  cnf(c_1836,plain,
% 23.83/3.51      ( X0 = X1
% 23.83/3.51      | r2_hidden(X1,X0) = iProver_top
% 23.83/3.51      | r2_hidden(X0,X1) = iProver_top
% 23.83/3.51      | v3_ordinal1(X1) != iProver_top
% 23.83/3.51      | v3_ordinal1(X0) != iProver_top ),
% 23.83/3.51      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 23.83/3.51  
% 23.83/3.51  cnf(c_12,plain,
% 23.83/3.51      ( ~ v3_ordinal1(X0) | v1_ordinal1(X0) ),
% 23.83/3.51      inference(cnf_transformation,[],[f81]) ).
% 23.83/3.51  
% 23.83/3.51  cnf(c_14,plain,
% 23.83/3.51      ( ~ r2_hidden(X0,X1) | r1_tarski(X0,X1) | ~ v1_ordinal1(X1) ),
% 23.83/3.51      inference(cnf_transformation,[],[f84]) ).
% 23.83/3.51  
% 23.83/3.51  cnf(c_485,plain,
% 23.83/3.51      ( ~ r2_hidden(X0,X1)
% 23.83/3.51      | r1_tarski(X0,X1)
% 23.83/3.51      | ~ v3_ordinal1(X2)
% 23.83/3.51      | X1 != X2 ),
% 23.83/3.51      inference(resolution_lifted,[status(thm)],[c_12,c_14]) ).
% 23.83/3.51  
% 23.83/3.51  cnf(c_486,plain,
% 23.83/3.51      ( ~ r2_hidden(X0,X1) | r1_tarski(X0,X1) | ~ v3_ordinal1(X1) ),
% 23.83/3.51      inference(unflattening,[status(thm)],[c_485]) ).
% 23.83/3.51  
% 23.83/3.51  cnf(c_1821,plain,
% 23.83/3.51      ( r2_hidden(X0,X1) != iProver_top
% 23.83/3.51      | r1_tarski(X0,X1) = iProver_top
% 23.83/3.51      | v3_ordinal1(X1) != iProver_top ),
% 23.83/3.51      inference(predicate_to_equality,[status(thm)],[c_486]) ).
% 23.83/3.51  
% 23.83/3.51  cnf(c_4298,plain,
% 23.83/3.51      ( X0 = X1
% 23.83/3.51      | r2_hidden(X1,X0) = iProver_top
% 23.83/3.51      | r1_tarski(X0,X1) = iProver_top
% 23.83/3.51      | v3_ordinal1(X1) != iProver_top
% 23.83/3.51      | v3_ordinal1(X0) != iProver_top ),
% 23.83/3.51      inference(superposition,[status(thm)],[c_1836,c_1821]) ).
% 23.83/3.51  
% 23.83/3.51  cnf(c_18,plain,
% 23.83/3.51      ( ~ r1_ordinal1(X0,X1)
% 23.83/3.51      | r1_tarski(X0,X1)
% 23.83/3.51      | ~ v3_ordinal1(X0)
% 23.83/3.51      | ~ v3_ordinal1(X1) ),
% 23.83/3.51      inference(cnf_transformation,[],[f87]) ).
% 23.83/3.51  
% 23.83/3.51  cnf(c_87,plain,
% 23.83/3.51      ( r1_ordinal1(X0,X1) != iProver_top
% 23.83/3.51      | r1_tarski(X0,X1) = iProver_top
% 23.83/3.51      | v3_ordinal1(X0) != iProver_top
% 23.83/3.51      | v3_ordinal1(X1) != iProver_top ),
% 23.83/3.51      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 23.83/3.51  
% 23.83/3.51  cnf(c_487,plain,
% 23.83/3.51      ( r2_hidden(X0,X1) != iProver_top
% 23.83/3.51      | r1_tarski(X0,X1) = iProver_top
% 23.83/3.51      | v3_ordinal1(X1) != iProver_top ),
% 23.83/3.51      inference(predicate_to_equality,[status(thm)],[c_486]) ).
% 23.83/3.51  
% 23.83/3.51  cnf(c_1040,plain,
% 23.83/3.51      ( ~ r1_ordinal1(X0,X1) | r1_ordinal1(X2,X1) | X2 != X0 ),
% 23.83/3.51      theory(equality) ).
% 23.83/3.51  
% 23.83/3.51  cnf(c_6099,plain,
% 23.83/3.51      ( ~ r1_ordinal1(X0,X1)
% 23.83/3.51      | r1_ordinal1(X2,X1)
% 23.83/3.51      | r2_hidden(X2,X0)
% 23.83/3.51      | r2_hidden(X0,X2)
% 23.83/3.51      | ~ v3_ordinal1(X0)
% 23.83/3.51      | ~ v3_ordinal1(X2) ),
% 23.83/3.51      inference(resolution,[status(thm)],[c_24,c_1040]) ).
% 23.83/3.51  
% 23.83/3.51  cnf(c_13,plain,
% 23.83/3.51      ( r1_ordinal1(X0,X1)
% 23.83/3.51      | r1_ordinal1(X1,X0)
% 23.83/3.51      | ~ v3_ordinal1(X0)
% 23.83/3.51      | ~ v3_ordinal1(X1) ),
% 23.83/3.51      inference(cnf_transformation,[],[f82]) ).
% 23.83/3.51  
% 23.83/3.51  cnf(c_4391,plain,
% 23.83/3.51      ( r1_ordinal1(X0,X0) | ~ v3_ordinal1(X0) ),
% 23.83/3.51      inference(factoring,[status(thm)],[c_13]) ).
% 23.83/3.51  
% 23.83/3.51  cnf(c_19309,plain,
% 23.83/3.51      ( r1_ordinal1(X0,X1)
% 23.83/3.51      | r2_hidden(X0,X1)
% 23.83/3.51      | r2_hidden(X1,X0)
% 23.83/3.51      | ~ v3_ordinal1(X0)
% 23.83/3.51      | ~ v3_ordinal1(X1) ),
% 23.83/3.51      inference(resolution,[status(thm)],[c_6099,c_4391]) ).
% 23.83/3.51  
% 23.83/3.51  cnf(c_19310,plain,
% 23.83/3.51      ( r1_ordinal1(X0,X1) = iProver_top
% 23.83/3.51      | r2_hidden(X0,X1) = iProver_top
% 23.83/3.51      | r2_hidden(X1,X0) = iProver_top
% 23.83/3.51      | v3_ordinal1(X0) != iProver_top
% 23.83/3.51      | v3_ordinal1(X1) != iProver_top ),
% 23.83/3.51      inference(predicate_to_equality,[status(thm)],[c_19309]) ).
% 23.83/3.51  
% 23.83/3.51  cnf(c_42061,plain,
% 23.83/3.51      ( r2_hidden(X1,X0) = iProver_top
% 23.83/3.51      | r1_tarski(X0,X1) = iProver_top
% 23.83/3.51      | v3_ordinal1(X1) != iProver_top
% 23.83/3.51      | v3_ordinal1(X0) != iProver_top ),
% 23.83/3.51      inference(global_propositional_subsumption,
% 23.83/3.51                [status(thm)],
% 23.83/3.51                [c_4298,c_87,c_487,c_19310]) ).
% 23.83/3.51  
% 23.83/3.51  cnf(c_42062,plain,
% 23.83/3.51      ( r2_hidden(X0,X1) = iProver_top
% 23.83/3.51      | r1_tarski(X1,X0) = iProver_top
% 23.83/3.51      | v3_ordinal1(X1) != iProver_top
% 23.83/3.51      | v3_ordinal1(X0) != iProver_top ),
% 23.83/3.51      inference(renaming,[status(thm)],[c_42061]) ).
% 23.83/3.51  
% 23.83/3.51  cnf(c_34,negated_conjecture,
% 23.83/3.51      ( ~ r2_hidden(k2_xboole_0(sK7,k1_tarski(sK7)),sK6)
% 23.83/3.51      | ~ v4_ordinal1(sK6) ),
% 23.83/3.51      inference(cnf_transformation,[],[f116]) ).
% 23.83/3.51  
% 23.83/3.51  cnf(c_1826,plain,
% 23.83/3.51      ( r2_hidden(k2_xboole_0(sK7,k1_tarski(sK7)),sK6) != iProver_top
% 23.83/3.51      | v4_ordinal1(sK6) != iProver_top ),
% 23.83/3.51      inference(predicate_to_equality,[status(thm)],[c_34]) ).
% 23.83/3.51  
% 23.83/3.51  cnf(c_42083,plain,
% 23.83/3.51      ( r1_tarski(sK6,k2_xboole_0(sK7,k1_tarski(sK7))) = iProver_top
% 23.83/3.51      | v4_ordinal1(sK6) != iProver_top
% 23.83/3.51      | v3_ordinal1(k2_xboole_0(sK7,k1_tarski(sK7))) != iProver_top
% 23.83/3.51      | v3_ordinal1(sK6) != iProver_top ),
% 23.83/3.51      inference(superposition,[status(thm)],[c_42062,c_1826]) ).
% 23.83/3.51  
% 23.83/3.51  cnf(c_42146,plain,
% 23.83/3.51      ( r1_tarski(sK6,k2_xboole_0(sK7,k1_tarski(sK7)))
% 23.83/3.51      | ~ v4_ordinal1(sK6)
% 23.83/3.51      | ~ v3_ordinal1(k2_xboole_0(sK7,k1_tarski(sK7)))
% 23.83/3.51      | ~ v3_ordinal1(sK6) ),
% 23.83/3.51      inference(predicate_to_equality_rev,[status(thm)],[c_42083]) ).
% 23.83/3.51  
% 23.83/3.51  cnf(c_3402,plain,
% 23.83/3.51      ( r2_hidden(sK7,sK3(k2_xboole_0(X0,k1_tarski(X0)),sK7))
% 23.83/3.51      | ~ r2_hidden(sK7,k3_tarski(k2_xboole_0(X0,k1_tarski(X0)))) ),
% 23.83/3.51      inference(instantiation,[status(thm)],[c_2160]) ).
% 23.83/3.51  
% 23.83/3.51  cnf(c_28296,plain,
% 23.83/3.51      ( r2_hidden(sK7,sK3(k2_xboole_0(sK7,k1_tarski(sK7)),sK7))
% 23.83/3.51      | ~ r2_hidden(sK7,k3_tarski(k2_xboole_0(sK7,k1_tarski(sK7)))) ),
% 23.83/3.51      inference(instantiation,[status(thm)],[c_3402]) ).
% 23.83/3.51  
% 23.83/3.51  cnf(c_1038,plain,
% 23.83/3.51      ( ~ r2_hidden(X0,X1) | r2_hidden(X2,X3) | X2 != X0 | X3 != X1 ),
% 23.83/3.51      theory(equality) ).
% 23.83/3.51  
% 23.83/3.51  cnf(c_2150,plain,
% 23.83/3.51      ( r2_hidden(X0,X1) | ~ r2_hidden(sK7,X2) | X1 != X2 | X0 != sK7 ),
% 23.83/3.51      inference(instantiation,[status(thm)],[c_1038]) ).
% 23.83/3.51  
% 23.83/3.51  cnf(c_3504,plain,
% 23.83/3.51      ( ~ r2_hidden(sK7,X0) | r2_hidden(sK7,X1) | X1 != X0 | sK7 != sK7 ),
% 23.83/3.51      inference(instantiation,[status(thm)],[c_2150]) ).
% 23.83/3.51  
% 23.83/3.51  cnf(c_6203,plain,
% 23.83/3.51      ( ~ r2_hidden(sK7,X0)
% 23.83/3.51      | r2_hidden(sK7,sK7)
% 23.83/3.51      | sK7 != X0
% 23.83/3.51      | sK7 != sK7 ),
% 23.83/3.51      inference(instantiation,[status(thm)],[c_3504]) ).
% 23.83/3.51  
% 23.83/3.51  cnf(c_26829,plain,
% 23.83/3.51      ( ~ r2_hidden(sK7,sK3(k2_xboole_0(sK7,k1_tarski(sK7)),sK7))
% 23.83/3.51      | r2_hidden(sK7,sK7)
% 23.83/3.51      | sK7 != sK3(k2_xboole_0(sK7,k1_tarski(sK7)),sK7)
% 23.83/3.51      | sK7 != sK7 ),
% 23.83/3.51      inference(instantiation,[status(thm)],[c_6203]) ).
% 23.83/3.51  
% 23.83/3.51  cnf(c_25,plain,
% 23.83/3.51      ( ~ v3_ordinal1(X0) | v3_ordinal1(k2_xboole_0(X0,k1_tarski(X0))) ),
% 23.83/3.51      inference(cnf_transformation,[],[f113]) ).
% 23.83/3.51  
% 23.83/3.51  cnf(c_13242,plain,
% 23.83/3.51      ( v3_ordinal1(k2_xboole_0(sK7,k1_tarski(sK7)))
% 23.83/3.51      | ~ v3_ordinal1(sK7) ),
% 23.83/3.51      inference(instantiation,[status(thm)],[c_25]) ).
% 23.83/3.51  
% 23.83/3.51  cnf(c_2,plain,
% 23.83/3.51      ( ~ r2_hidden(X0,X1) | r2_hidden(X0,X2) | ~ r1_tarski(X1,X2) ),
% 23.83/3.51      inference(cnf_transformation,[],[f69]) ).
% 23.83/3.51  
% 23.83/3.51  cnf(c_5701,plain,
% 23.83/3.51      ( ~ r2_hidden(sK3(X0,sK7),X0)
% 23.83/3.51      | r2_hidden(sK3(X0,sK7),X1)
% 23.83/3.51      | ~ r1_tarski(X0,X1) ),
% 23.83/3.51      inference(instantiation,[status(thm)],[c_2]) ).
% 23.83/3.51  
% 23.83/3.51  cnf(c_12372,plain,
% 23.83/3.51      ( ~ r2_hidden(sK3(X0,sK7),X0)
% 23.83/3.51      | r2_hidden(sK3(X0,sK7),k2_xboole_0(sK7,k1_tarski(sK7)))
% 23.83/3.51      | ~ r1_tarski(X0,k2_xboole_0(sK7,k1_tarski(sK7))) ),
% 23.83/3.51      inference(instantiation,[status(thm)],[c_5701]) ).
% 23.83/3.51  
% 23.83/3.51  cnf(c_12375,plain,
% 23.83/3.51      ( r2_hidden(sK3(sK6,sK7),k2_xboole_0(sK7,k1_tarski(sK7)))
% 23.83/3.51      | ~ r2_hidden(sK3(sK6,sK7),sK6)
% 23.83/3.51      | ~ r1_tarski(sK6,k2_xboole_0(sK7,k1_tarski(sK7))) ),
% 23.83/3.51      inference(instantiation,[status(thm)],[c_12372]) ).
% 23.83/3.51  
% 23.83/3.51  cnf(c_21,plain,
% 23.83/3.51      ( ~ r2_hidden(X0,X1)
% 23.83/3.51      | r2_hidden(X0,k2_xboole_0(X1,k1_tarski(X1))) ),
% 23.83/3.51      inference(cnf_transformation,[],[f111]) ).
% 23.83/3.51  
% 23.83/3.51  cnf(c_2854,plain,
% 23.83/3.51      ( ~ r2_hidden(X0,X1)
% 23.83/3.51      | ~ r1_tarski(k2_xboole_0(X1,k1_tarski(X1)),X0) ),
% 23.83/3.51      inference(resolution,[status(thm)],[c_21,c_33]) ).
% 23.83/3.51  
% 23.83/3.51  cnf(c_37,negated_conjecture,
% 23.83/3.51      ( ~ r2_hidden(X0,sK6)
% 23.83/3.51      | r2_hidden(k2_xboole_0(X0,k1_tarski(X0)),sK6)
% 23.83/3.51      | v4_ordinal1(sK6)
% 23.83/3.51      | ~ v3_ordinal1(X0) ),
% 23.83/3.51      inference(cnf_transformation,[],[f117]) ).
% 23.83/3.51  
% 23.83/3.51  cnf(c_3069,plain,
% 23.83/3.51      ( ~ r2_hidden(X0,sK6)
% 23.83/3.51      | r1_tarski(k2_xboole_0(X0,k1_tarski(X0)),sK6)
% 23.83/3.51      | v4_ordinal1(sK6)
% 23.83/3.51      | ~ v3_ordinal1(X0)
% 23.83/3.51      | ~ v3_ordinal1(sK6) ),
% 23.83/3.51      inference(resolution,[status(thm)],[c_486,c_37]) ).
% 23.83/3.51  
% 23.83/3.51  cnf(c_38,negated_conjecture,
% 23.83/3.51      ( v3_ordinal1(sK6) ),
% 23.83/3.51      inference(cnf_transformation,[],[f104]) ).
% 23.83/3.51  
% 23.83/3.51  cnf(c_1823,plain,
% 23.83/3.51      ( r2_hidden(X0,sK6) != iProver_top
% 23.83/3.51      | r2_hidden(k2_xboole_0(X0,k1_tarski(X0)),sK6) = iProver_top
% 23.83/3.51      | v4_ordinal1(sK6) = iProver_top
% 23.83/3.51      | v3_ordinal1(X0) != iProver_top ),
% 23.83/3.51      inference(predicate_to_equality,[status(thm)],[c_37]) ).
% 23.83/3.51  
% 23.83/3.51  cnf(c_2064,plain,
% 23.83/3.51      ( r2_hidden(X0,sK6) != iProver_top
% 23.83/3.51      | r1_tarski(k2_xboole_0(X0,k1_tarski(X0)),sK6) = iProver_top
% 23.83/3.51      | v4_ordinal1(sK6) = iProver_top
% 23.83/3.51      | v3_ordinal1(X0) != iProver_top
% 23.83/3.51      | v3_ordinal1(sK6) != iProver_top ),
% 23.83/3.51      inference(superposition,[status(thm)],[c_1823,c_1821]) ).
% 23.83/3.51  
% 23.83/3.51  cnf(c_2065,plain,
% 23.83/3.51      ( ~ r2_hidden(X0,sK6)
% 23.83/3.51      | r1_tarski(k2_xboole_0(X0,k1_tarski(X0)),sK6)
% 23.83/3.51      | v4_ordinal1(sK6)
% 23.83/3.51      | ~ v3_ordinal1(X0)
% 23.83/3.51      | ~ v3_ordinal1(sK6) ),
% 23.83/3.51      inference(predicate_to_equality_rev,[status(thm)],[c_2064]) ).
% 23.83/3.51  
% 23.83/3.51  cnf(c_3330,plain,
% 23.83/3.51      ( ~ v3_ordinal1(X0)
% 23.83/3.51      | v4_ordinal1(sK6)
% 23.83/3.51      | r1_tarski(k2_xboole_0(X0,k1_tarski(X0)),sK6)
% 23.83/3.51      | ~ r2_hidden(X0,sK6) ),
% 23.83/3.51      inference(global_propositional_subsumption,
% 23.83/3.51                [status(thm)],
% 23.83/3.51                [c_3069,c_38,c_2065]) ).
% 23.83/3.51  
% 23.83/3.51  cnf(c_3331,plain,
% 23.83/3.51      ( ~ r2_hidden(X0,sK6)
% 23.83/3.51      | r1_tarski(k2_xboole_0(X0,k1_tarski(X0)),sK6)
% 23.83/3.51      | v4_ordinal1(sK6)
% 23.83/3.51      | ~ v3_ordinal1(X0) ),
% 23.83/3.51      inference(renaming,[status(thm)],[c_3330]) ).
% 23.83/3.51  
% 23.83/3.51  cnf(c_10332,plain,
% 23.83/3.51      ( ~ r2_hidden(X0,sK6)
% 23.83/3.51      | ~ r2_hidden(sK6,X0)
% 23.83/3.51      | v4_ordinal1(sK6)
% 23.83/3.51      | ~ v3_ordinal1(X0) ),
% 23.83/3.51      inference(resolution,[status(thm)],[c_2854,c_3331]) ).
% 23.83/3.51  
% 23.83/3.51  cnf(c_23,plain,
% 23.83/3.51      ( ~ r2_hidden(X0,X1) | ~ v3_ordinal1(X1) | v3_ordinal1(X0) ),
% 23.83/3.51      inference(cnf_transformation,[],[f93]) ).
% 23.83/3.51  
% 23.83/3.51  cnf(c_29,plain,
% 23.83/3.51      ( r2_hidden(sK4(X0),X0) | v3_ordinal1(k3_tarski(X0)) ),
% 23.83/3.51      inference(cnf_transformation,[],[f98]) ).
% 23.83/3.51  
% 23.83/3.51  cnf(c_2487,plain,
% 23.83/3.51      ( ~ v3_ordinal1(X0)
% 23.83/3.51      | v3_ordinal1(sK4(X0))
% 23.83/3.51      | v3_ordinal1(k3_tarski(X0)) ),
% 23.83/3.51      inference(resolution,[status(thm)],[c_23,c_29]) ).
% 23.83/3.51  
% 23.83/3.51  cnf(c_28,plain,
% 23.83/3.51      ( ~ v3_ordinal1(sK4(X0)) | v3_ordinal1(k3_tarski(X0)) ),
% 23.83/3.51      inference(cnf_transformation,[],[f99]) ).
% 23.83/3.51  
% 23.83/3.51  cnf(c_2642,plain,
% 23.83/3.51      ( ~ v3_ordinal1(X0) | v3_ordinal1(k3_tarski(X0)) ),
% 23.83/3.51      inference(global_propositional_subsumption,
% 23.83/3.51                [status(thm)],
% 23.83/3.51                [c_2487,c_28]) ).
% 23.83/3.51  
% 23.83/3.51  cnf(c_2645,plain,
% 23.83/3.51      ( v3_ordinal1(k3_tarski(sK6)) | ~ v3_ordinal1(sK6) ),
% 23.83/3.51      inference(instantiation,[status(thm)],[c_2642]) ).
% 23.83/3.51  
% 23.83/3.51  cnf(c_1,plain,
% 23.83/3.51      ( r2_hidden(sK0(X0,X1),X0) | r1_tarski(X0,X1) ),
% 23.83/3.51      inference(cnf_transformation,[],[f70]) ).
% 23.83/3.51  
% 23.83/3.51  cnf(c_3360,plain,
% 23.83/3.51      ( r2_hidden(sK0(sK6,k3_tarski(X0)),sK6)
% 23.83/3.51      | r1_tarski(sK6,k3_tarski(X0)) ),
% 23.83/3.51      inference(instantiation,[status(thm)],[c_1]) ).
% 23.83/3.51  
% 23.83/3.51  cnf(c_3367,plain,
% 23.83/3.51      ( r2_hidden(sK0(sK6,k3_tarski(sK6)),sK6)
% 23.83/3.51      | r1_tarski(sK6,k3_tarski(sK6)) ),
% 23.83/3.51      inference(instantiation,[status(thm)],[c_3360]) ).
% 23.83/3.51  
% 23.83/3.51  cnf(c_3432,plain,
% 23.83/3.51      ( ~ r2_hidden(k3_tarski(X0),X1) | ~ r1_tarski(X1,k3_tarski(X0)) ),
% 23.83/3.51      inference(instantiation,[status(thm)],[c_33]) ).
% 23.83/3.51  
% 23.83/3.51  cnf(c_3434,plain,
% 23.83/3.51      ( ~ r2_hidden(k3_tarski(sK6),sK6)
% 23.83/3.51      | ~ r1_tarski(sK6,k3_tarski(sK6)) ),
% 23.83/3.51      inference(instantiation,[status(thm)],[c_3432]) ).
% 23.83/3.51  
% 23.83/3.51  cnf(c_15,plain,
% 23.83/3.51      ( v4_ordinal1(X0) | k3_tarski(X0) != X0 ),
% 23.83/3.51      inference(cnf_transformation,[],[f86]) ).
% 23.83/3.51  
% 23.83/3.51  cnf(c_6092,plain,
% 23.83/3.51      ( r2_hidden(X0,k3_tarski(X0))
% 23.83/3.51      | r2_hidden(k3_tarski(X0),X0)
% 23.83/3.51      | v4_ordinal1(X0)
% 23.83/3.51      | ~ v3_ordinal1(X0)
% 23.83/3.51      | ~ v3_ordinal1(k3_tarski(X0)) ),
% 23.83/3.51      inference(resolution,[status(thm)],[c_24,c_15]) ).
% 23.83/3.51  
% 23.83/3.51  cnf(c_6094,plain,
% 23.83/3.51      ( r2_hidden(k3_tarski(sK6),sK6)
% 23.83/3.51      | r2_hidden(sK6,k3_tarski(sK6))
% 23.83/3.51      | v4_ordinal1(sK6)
% 23.83/3.51      | ~ v3_ordinal1(k3_tarski(sK6))
% 23.83/3.51      | ~ v3_ordinal1(sK6) ),
% 23.83/3.51      inference(instantiation,[status(thm)],[c_6092]) ).
% 23.83/3.51  
% 23.83/3.51  cnf(c_8827,plain,
% 23.83/3.51      ( ~ r2_hidden(sK0(sK6,k3_tarski(X0)),X1)
% 23.83/3.51      | ~ v3_ordinal1(X1)
% 23.83/3.51      | v3_ordinal1(sK0(sK6,k3_tarski(X0))) ),
% 23.83/3.51      inference(instantiation,[status(thm)],[c_23]) ).
% 23.83/3.51  
% 23.83/3.51  cnf(c_8829,plain,
% 23.83/3.51      ( ~ r2_hidden(sK0(sK6,k3_tarski(sK6)),sK6)
% 23.83/3.51      | v3_ordinal1(sK0(sK6,k3_tarski(sK6)))
% 23.83/3.51      | ~ v3_ordinal1(sK6) ),
% 23.83/3.51      inference(instantiation,[status(thm)],[c_8827]) ).
% 23.83/3.51  
% 23.83/3.51  cnf(c_10,plain,
% 23.83/3.51      ( ~ r2_hidden(X0,k3_tarski(X1)) | r2_hidden(sK3(X1,X0),X1) ),
% 23.83/3.51      inference(cnf_transformation,[],[f121]) ).
% 23.83/3.51  
% 23.83/3.51  cnf(c_1847,plain,
% 23.83/3.51      ( r2_hidden(X0,k3_tarski(X1)) != iProver_top
% 23.83/3.51      | r2_hidden(sK3(X1,X0),X1) = iProver_top ),
% 23.83/3.51      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 23.83/3.51  
% 23.83/3.51  cnf(c_3037,plain,
% 23.83/3.51      ( r2_hidden(X0,k3_tarski(X1)) != iProver_top
% 23.83/3.51      | r1_tarski(sK3(X1,X0),X1) = iProver_top
% 23.83/3.51      | v3_ordinal1(X1) != iProver_top ),
% 23.83/3.51      inference(superposition,[status(thm)],[c_1847,c_1821]) ).
% 23.83/3.51  
% 23.83/3.51  cnf(c_1846,plain,
% 23.83/3.51      ( r2_hidden(X0,sK3(X1,X0)) = iProver_top
% 23.83/3.51      | r2_hidden(X0,k3_tarski(X1)) != iProver_top ),
% 23.83/3.51      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 23.83/3.51  
% 23.83/3.51  cnf(c_1827,plain,
% 23.83/3.51      ( r2_hidden(X0,X1) != iProver_top
% 23.83/3.51      | r1_tarski(X1,X0) != iProver_top ),
% 23.83/3.51      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 23.83/3.51  
% 23.83/3.51  cnf(c_2828,plain,
% 23.83/3.51      ( r2_hidden(X0,k3_tarski(X1)) != iProver_top
% 23.83/3.51      | r1_tarski(sK3(X1,X0),X0) != iProver_top ),
% 23.83/3.51      inference(superposition,[status(thm)],[c_1846,c_1827]) ).
% 23.83/3.51  
% 23.83/3.51  cnf(c_9218,plain,
% 23.83/3.51      ( r2_hidden(X0,k3_tarski(X0)) != iProver_top
% 23.83/3.51      | v3_ordinal1(X0) != iProver_top ),
% 23.83/3.51      inference(superposition,[status(thm)],[c_3037,c_2828]) ).
% 23.83/3.51  
% 23.83/3.51  cnf(c_9222,plain,
% 23.83/3.51      ( ~ r2_hidden(X0,k3_tarski(X0)) | ~ v3_ordinal1(X0) ),
% 23.83/3.51      inference(predicate_to_equality_rev,[status(thm)],[c_9218]) ).
% 23.83/3.51  
% 23.83/3.51  cnf(c_9224,plain,
% 23.83/3.51      ( ~ r2_hidden(sK6,k3_tarski(sK6)) | ~ v3_ordinal1(sK6) ),
% 23.83/3.51      inference(instantiation,[status(thm)],[c_9222]) ).
% 23.83/3.51  
% 23.83/3.51  cnf(c_20,plain,
% 23.83/3.51      ( r2_hidden(X0,k2_xboole_0(X0,k1_tarski(X0))) ),
% 23.83/3.51      inference(cnf_transformation,[],[f123]) ).
% 23.83/3.51  
% 23.83/3.51  cnf(c_4365,plain,
% 23.83/3.51      ( r2_hidden(X0,k3_tarski(X1))
% 23.83/3.51      | ~ r2_hidden(k2_xboole_0(X0,k1_tarski(X0)),X1) ),
% 23.83/3.51      inference(resolution,[status(thm)],[c_9,c_20]) ).
% 23.83/3.51  
% 23.83/3.51  cnf(c_10356,plain,
% 23.83/3.51      ( r2_hidden(X0,k3_tarski(sK6))
% 23.83/3.51      | ~ r2_hidden(X0,sK6)
% 23.83/3.51      | v4_ordinal1(sK6)
% 23.83/3.51      | ~ v3_ordinal1(X0) ),
% 23.83/3.51      inference(resolution,[status(thm)],[c_4365,c_37]) ).
% 23.83/3.51  
% 23.83/3.51  cnf(c_0,plain,
% 23.83/3.51      ( ~ r2_hidden(sK0(X0,X1),X1) | r1_tarski(X0,X1) ),
% 23.83/3.51      inference(cnf_transformation,[],[f71]) ).
% 23.83/3.51  
% 23.83/3.51  cnf(c_10664,plain,
% 23.83/3.51      ( ~ r2_hidden(sK0(X0,k3_tarski(sK6)),sK6)
% 23.83/3.51      | r1_tarski(X0,k3_tarski(sK6))
% 23.83/3.51      | v4_ordinal1(sK6)
% 23.83/3.51      | ~ v3_ordinal1(sK0(X0,k3_tarski(sK6))) ),
% 23.83/3.51      inference(resolution,[status(thm)],[c_10356,c_0]) ).
% 23.83/3.51  
% 23.83/3.51  cnf(c_10666,plain,
% 23.83/3.51      ( ~ r2_hidden(sK0(sK6,k3_tarski(sK6)),sK6)
% 23.83/3.51      | r1_tarski(sK6,k3_tarski(sK6))
% 23.83/3.51      | v4_ordinal1(sK6)
% 23.83/3.51      | ~ v3_ordinal1(sK0(sK6,k3_tarski(sK6))) ),
% 23.83/3.51      inference(instantiation,[status(thm)],[c_10664]) ).
% 23.83/3.51  
% 23.83/3.51  cnf(c_10847,plain,
% 23.83/3.51      ( v4_ordinal1(sK6) ),
% 23.83/3.51      inference(global_propositional_subsumption,
% 23.83/3.51                [status(thm)],
% 23.83/3.51                [c_10332,c_38,c_2645,c_3367,c_3434,c_6094,c_8829,c_9224,
% 23.83/3.51                 c_10666]) ).
% 23.83/3.51  
% 23.83/3.51  cnf(c_22,plain,
% 23.83/3.51      ( r2_hidden(X0,X1)
% 23.83/3.51      | ~ r2_hidden(X0,k2_xboole_0(X1,k1_tarski(X1)))
% 23.83/3.51      | X1 = X0 ),
% 23.83/3.51      inference(cnf_transformation,[],[f112]) ).
% 23.83/3.51  
% 23.83/3.51  cnf(c_2448,plain,
% 23.83/3.51      ( ~ r2_hidden(X0,k2_xboole_0(sK7,k1_tarski(sK7)))
% 23.83/3.51      | r2_hidden(X0,sK7)
% 23.83/3.51      | sK7 = X0 ),
% 23.83/3.51      inference(instantiation,[status(thm)],[c_22]) ).
% 23.83/3.51  
% 23.83/3.51  cnf(c_6533,plain,
% 23.83/3.51      ( ~ r2_hidden(sK3(k2_xboole_0(sK7,k1_tarski(sK7)),sK7),k2_xboole_0(sK7,k1_tarski(sK7)))
% 23.83/3.51      | r2_hidden(sK3(k2_xboole_0(sK7,k1_tarski(sK7)),sK7),sK7)
% 23.83/3.51      | sK7 = sK3(k2_xboole_0(sK7,k1_tarski(sK7)),sK7) ),
% 23.83/3.51      inference(instantiation,[status(thm)],[c_2448]) ).
% 23.83/3.51  
% 23.83/3.51  cnf(c_2161,plain,
% 23.83/3.51      ( r2_hidden(sK3(X0,sK7),X0) | ~ r2_hidden(sK7,k3_tarski(X0)) ),
% 23.83/3.51      inference(instantiation,[status(thm)],[c_10]) ).
% 23.83/3.51  
% 23.83/3.51  cnf(c_3401,plain,
% 23.83/3.51      ( r2_hidden(sK3(k2_xboole_0(X0,k1_tarski(X0)),sK7),k2_xboole_0(X0,k1_tarski(X0)))
% 23.83/3.51      | ~ r2_hidden(sK7,k3_tarski(k2_xboole_0(X0,k1_tarski(X0)))) ),
% 23.83/3.51      inference(instantiation,[status(thm)],[c_2161]) ).
% 23.83/3.51  
% 23.83/3.51  cnf(c_6532,plain,
% 23.83/3.51      ( r2_hidden(sK3(k2_xboole_0(sK7,k1_tarski(sK7)),sK7),k2_xboole_0(sK7,k1_tarski(sK7)))
% 23.83/3.51      | ~ r2_hidden(sK7,k3_tarski(k2_xboole_0(sK7,k1_tarski(sK7)))) ),
% 23.83/3.51      inference(instantiation,[status(thm)],[c_3401]) ).
% 23.83/3.51  
% 23.83/3.51  cnf(c_3152,plain,
% 23.83/3.51      ( ~ r2_hidden(X0,sK7) | r1_tarski(X0,sK7) | ~ v3_ordinal1(sK7) ),
% 23.83/3.51      inference(instantiation,[status(thm)],[c_486]) ).
% 23.83/3.51  
% 23.83/3.51  cnf(c_5751,plain,
% 23.83/3.51      ( ~ r2_hidden(sK3(sK7,sK7),sK7)
% 23.83/3.51      | r1_tarski(sK3(sK7,sK7),sK7)
% 23.83/3.51      | ~ v3_ordinal1(sK7) ),
% 23.83/3.51      inference(instantiation,[status(thm)],[c_3152]) ).
% 23.83/3.51  
% 23.83/3.51  cnf(c_5750,plain,
% 23.83/3.51      ( r2_hidden(sK3(sK7,sK7),sK7) | ~ r2_hidden(sK7,k3_tarski(sK7)) ),
% 23.83/3.51      inference(instantiation,[status(thm)],[c_2161]) ).
% 23.83/3.51  
% 23.83/3.51  cnf(c_2107,plain,
% 23.83/3.51      ( r2_hidden(X0,X1) | ~ r2_hidden(sK7,sK6) | X1 != sK6 | X0 != sK7 ),
% 23.83/3.51      inference(instantiation,[status(thm)],[c_1038]) ).
% 23.83/3.51  
% 23.83/3.51  cnf(c_2221,plain,
% 23.83/3.51      ( r2_hidden(sK7,X0)
% 23.83/3.51      | ~ r2_hidden(sK7,sK6)
% 23.83/3.51      | X0 != sK6
% 23.83/3.51      | sK7 != sK7 ),
% 23.83/3.51      inference(instantiation,[status(thm)],[c_2107]) ).
% 23.83/3.51  
% 23.83/3.51  cnf(c_3388,plain,
% 23.83/3.51      ( r2_hidden(sK7,k3_tarski(X0))
% 23.83/3.51      | ~ r2_hidden(sK7,sK6)
% 23.83/3.51      | k3_tarski(X0) != sK6
% 23.83/3.51      | sK7 != sK7 ),
% 23.83/3.51      inference(instantiation,[status(thm)],[c_2221]) ).
% 23.83/3.51  
% 23.83/3.51  cnf(c_3390,plain,
% 23.83/3.51      ( r2_hidden(sK7,k3_tarski(sK6))
% 23.83/3.51      | ~ r2_hidden(sK7,sK6)
% 23.83/3.51      | k3_tarski(sK6) != sK6
% 23.83/3.51      | sK7 != sK7 ),
% 23.83/3.51      inference(instantiation,[status(thm)],[c_3388]) ).
% 23.83/3.51  
% 23.83/3.51  cnf(c_5,plain,
% 23.83/3.51      ( r1_tarski(X0,X0) ),
% 23.83/3.51      inference(cnf_transformation,[],[f119]) ).
% 23.83/3.51  
% 23.83/3.51  cnf(c_3164,plain,
% 23.83/3.51      ( r1_tarski(sK7,sK7) ),
% 23.83/3.51      inference(instantiation,[status(thm)],[c_5]) ).
% 23.83/3.51  
% 23.83/3.51  cnf(c_3163,plain,
% 23.83/3.51      ( ~ r2_hidden(sK7,sK7) | ~ r1_tarski(sK7,sK7) ),
% 23.83/3.51      inference(instantiation,[status(thm)],[c_2152]) ).
% 23.83/3.51  
% 23.83/3.51  cnf(c_1036,plain,( X0 = X0 ),theory(equality) ).
% 23.83/3.51  
% 23.83/3.51  cnf(c_2222,plain,
% 23.83/3.51      ( sK7 = sK7 ),
% 23.83/3.51      inference(instantiation,[status(thm)],[c_1036]) ).
% 23.83/3.51  
% 23.83/3.51  cnf(c_2171,plain,
% 23.83/3.51      ( r2_hidden(sK7,sK3(sK6,sK7)) | ~ r2_hidden(sK7,k3_tarski(sK6)) ),
% 23.83/3.51      inference(instantiation,[status(thm)],[c_2160]) ).
% 23.83/3.51  
% 23.83/3.51  cnf(c_2167,plain,
% 23.83/3.51      ( r2_hidden(sK3(sK6,sK7),sK6) | ~ r2_hidden(sK7,k3_tarski(sK6)) ),
% 23.83/3.51      inference(instantiation,[status(thm)],[c_2161]) ).
% 23.83/3.51  
% 23.83/3.51  cnf(c_16,plain,
% 23.83/3.51      ( ~ v4_ordinal1(X0) | k3_tarski(X0) = X0 ),
% 23.83/3.51      inference(cnf_transformation,[],[f85]) ).
% 23.83/3.51  
% 23.83/3.51  cnf(c_94,plain,
% 23.83/3.51      ( ~ v4_ordinal1(sK6) | k3_tarski(sK6) = sK6 ),
% 23.83/3.51      inference(instantiation,[status(thm)],[c_16]) ).
% 23.83/3.51  
% 23.83/3.51  cnf(c_35,negated_conjecture,
% 23.83/3.51      ( r2_hidden(sK7,sK6) | ~ v4_ordinal1(sK6) ),
% 23.83/3.51      inference(cnf_transformation,[],[f107]) ).
% 23.83/3.51  
% 23.83/3.51  cnf(c_36,negated_conjecture,
% 23.83/3.51      ( ~ v4_ordinal1(sK6) | v3_ordinal1(sK7) ),
% 23.83/3.51      inference(cnf_transformation,[],[f106]) ).
% 23.83/3.51  
% 23.83/3.51  cnf(contradiction,plain,
% 23.83/3.51      ( $false ),
% 23.83/3.51      inference(minisat,
% 23.83/3.51                [status(thm)],
% 23.83/3.51                [c_85037,c_81604,c_75458,c_57742,c_42146,c_28296,c_26829,
% 23.83/3.51                 c_13242,c_12375,c_10847,c_6533,c_6532,c_5751,c_5750,
% 23.83/3.51                 c_3390,c_3164,c_3163,c_2222,c_2171,c_2167,c_94,c_35,
% 23.83/3.51                 c_36,c_38]) ).
% 23.83/3.51  
% 23.83/3.51  
% 23.83/3.51  % SZS output end CNFRefutation for theBenchmark.p
% 23.83/3.51  
% 23.83/3.51  ------                               Statistics
% 23.83/3.51  
% 23.83/3.51  ------ Selected
% 23.83/3.51  
% 23.83/3.51  total_time:                             2.914
% 23.83/3.51  
%------------------------------------------------------------------------------
