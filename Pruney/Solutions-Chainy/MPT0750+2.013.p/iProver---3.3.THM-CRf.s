%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:54:02 EST 2020

% Result     : Theorem 15.84s
% Output     : CNFRefutation 15.84s
% Verified   : 
% Statistics : Number of formulae       :  242 (2475 expanded)
%              Number of clauses        :  159 ( 671 expanded)
%              Number of leaves         :   22 ( 584 expanded)
%              Depth                    :   30
%              Number of atoms          :  820 (11901 expanded)
%              Number of equality atoms :  282 (1517 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal clause size      :   18 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2,axiom,(
    ! [X0,X1] :
      ( k3_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] :
              ( r2_hidden(X3,X0)
              & r2_hidden(X2,X3) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
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
    inference(nnf_transformation,[],[f2])).

fof(f34,plain,(
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
    inference(rectify,[],[f33])).

fof(f37,plain,(
    ! [X5,X0] :
      ( ? [X7] :
          ( r2_hidden(X7,X0)
          & r2_hidden(X5,X7) )
     => ( r2_hidden(sK3(X0,X5),X0)
        & r2_hidden(X5,sK3(X0,X5)) ) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( r2_hidden(X4,X0)
          & r2_hidden(X2,X4) )
     => ( r2_hidden(sK2(X0,X1),X0)
        & r2_hidden(X2,sK2(X0,X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,(
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

fof(f38,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f34,f37,f36,f35])).

fof(f57,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(X5,sK3(X0,X5))
      | ~ r2_hidden(X5,X1)
      | k3_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f38])).

fof(f97,plain,(
    ! [X0,X5] :
      ( r2_hidden(X5,sK3(X0,X5))
      | ~ r2_hidden(X5,k3_tarski(X0)) ) ),
    inference(equality_resolution,[],[f57])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,k1_ordinal1(X1))
    <=> ( X0 = X1
        | r2_hidden(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X0,X1] :
      ( ( r2_hidden(X0,k1_ordinal1(X1))
        | ( X0 != X1
          & ~ r2_hidden(X0,X1) ) )
      & ( X0 = X1
        | r2_hidden(X0,X1)
        | ~ r2_hidden(X0,k1_ordinal1(X1)) ) ) ),
    inference(nnf_transformation,[],[f9])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ( r2_hidden(X0,k1_ordinal1(X1))
        | ( X0 != X1
          & ~ r2_hidden(X0,X1) ) )
      & ( X0 = X1
        | r2_hidden(X0,X1)
        | ~ r2_hidden(X0,k1_ordinal1(X1)) ) ) ),
    inference(flattening,[],[f45])).

fof(f74,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,k1_ordinal1(X1))
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f46])).

fof(f3,axiom,(
    ! [X0] : k1_ordinal1(X0) = k2_xboole_0(X0,k1_tarski(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f63,plain,(
    ! [X0] : k1_ordinal1(X0) = k2_xboole_0(X0,k1_tarski(X0)) ),
    inference(cnf_transformation,[],[f3])).

fof(f87,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,k2_xboole_0(X1,k1_tarski(X1)))
      | X0 != X1 ) ),
    inference(definition_unfolding,[],[f74,f63])).

fof(f98,plain,(
    ! [X1] : r2_hidden(X1,k2_xboole_0(X1,k1_tarski(X1))) ),
    inference(equality_resolution,[],[f87])).

fof(f15,conjecture,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ( v4_ordinal1(X0)
      <=> ! [X1] :
            ( v3_ordinal1(X1)
           => ( r2_hidden(X1,X0)
             => r2_hidden(k1_ordinal1(X1),X0) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,negated_conjecture,(
    ~ ! [X0] :
        ( v3_ordinal1(X0)
       => ( v4_ordinal1(X0)
        <=> ! [X1] :
              ( v3_ordinal1(X1)
             => ( r2_hidden(X1,X0)
               => r2_hidden(k1_ordinal1(X1),X0) ) ) ) ) ),
    inference(negated_conjecture,[],[f15])).

fof(f27,plain,(
    ? [X0] :
      ( ( v4_ordinal1(X0)
      <~> ! [X1] :
            ( r2_hidden(k1_ordinal1(X1),X0)
            | ~ r2_hidden(X1,X0)
            | ~ v3_ordinal1(X1) ) )
      & v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f28,plain,(
    ? [X0] :
      ( ( v4_ordinal1(X0)
      <~> ! [X1] :
            ( r2_hidden(k1_ordinal1(X1),X0)
            | ~ r2_hidden(X1,X0)
            | ~ v3_ordinal1(X1) ) )
      & v3_ordinal1(X0) ) ),
    inference(flattening,[],[f27])).

fof(f48,plain,(
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
    inference(nnf_transformation,[],[f28])).

fof(f49,plain,(
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
    inference(flattening,[],[f48])).

fof(f50,plain,(
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
    inference(rectify,[],[f49])).

fof(f52,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ r2_hidden(k1_ordinal1(X1),X0)
          & r2_hidden(X1,X0)
          & v3_ordinal1(X1) )
     => ( ~ r2_hidden(k1_ordinal1(sK6),X0)
        & r2_hidden(sK6,X0)
        & v3_ordinal1(sK6) ) ) ),
    introduced(choice_axiom,[])).

fof(f51,plain,
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
            ( ~ r2_hidden(k1_ordinal1(X1),sK5)
            & r2_hidden(X1,sK5)
            & v3_ordinal1(X1) )
        | ~ v4_ordinal1(sK5) )
      & ( ! [X2] :
            ( r2_hidden(k1_ordinal1(X2),sK5)
            | ~ r2_hidden(X2,sK5)
            | ~ v3_ordinal1(X2) )
        | v4_ordinal1(sK5) )
      & v3_ordinal1(sK5) ) ),
    introduced(choice_axiom,[])).

fof(f53,plain,
    ( ( ( ~ r2_hidden(k1_ordinal1(sK6),sK5)
        & r2_hidden(sK6,sK5)
        & v3_ordinal1(sK6) )
      | ~ v4_ordinal1(sK5) )
    & ( ! [X2] :
          ( r2_hidden(k1_ordinal1(X2),sK5)
          | ~ r2_hidden(X2,sK5)
          | ~ v3_ordinal1(X2) )
      | v4_ordinal1(sK5) )
    & v3_ordinal1(sK5) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6])],[f50,f52,f51])).

fof(f82,plain,(
    ! [X2] :
      ( r2_hidden(k1_ordinal1(X2),sK5)
      | ~ r2_hidden(X2,sK5)
      | ~ v3_ordinal1(X2)
      | v4_ordinal1(sK5) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f94,plain,(
    ! [X2] :
      ( r2_hidden(k2_xboole_0(X2,k1_tarski(X2)),sK5)
      | ~ r2_hidden(X2,sK5)
      | ~ v3_ordinal1(X2)
      | v4_ordinal1(sK5) ) ),
    inference(definition_unfolding,[],[f82,f63])).

fof(f59,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | ~ r2_hidden(X6,X0)
      | ~ r2_hidden(X5,X6)
      | k3_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f38])).

fof(f95,plain,(
    ! [X6,X0,X5] :
      ( r2_hidden(X5,k3_tarski(X0))
      | ~ r2_hidden(X6,X0)
      | ~ r2_hidden(X5,X6) ) ),
    inference(equality_resolution,[],[f59])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ( v3_ordinal1(X1)
        & v3_ordinal1(X0) )
     => ( r1_ordinal1(X0,X1)
      <=> r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1] :
      ( ( r1_ordinal1(X0,X1)
      <=> r1_tarski(X0,X1) )
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( r1_ordinal1(X0,X1)
      <=> r1_tarski(X0,X1) )
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(flattening,[],[f18])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( ( r1_ordinal1(X0,X1)
          | ~ r1_tarski(X0,X1) )
        & ( r1_tarski(X0,X1)
          | ~ r1_ordinal1(X0,X1) ) )
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f66,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r1_ordinal1(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f13,axiom,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ! [X1] :
          ( v3_ordinal1(X1)
         => ( r2_hidden(X0,X1)
          <=> r1_ordinal1(k1_ordinal1(X0),X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r2_hidden(X0,X1)
          <=> r1_ordinal1(k1_ordinal1(X0),X1) )
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f47,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( r2_hidden(X0,X1)
              | ~ r1_ordinal1(k1_ordinal1(X0),X1) )
            & ( r1_ordinal1(k1_ordinal1(X0),X1)
              | ~ r2_hidden(X0,X1) ) )
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(nnf_transformation,[],[f25])).

fof(f78,plain,(
    ! [X0,X1] :
      ( r1_ordinal1(k1_ordinal1(X0),X1)
      | ~ r2_hidden(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f92,plain,(
    ! [X0,X1] :
      ( r1_ordinal1(k2_xboole_0(X0,k1_tarski(X0)),X1)
      | ~ r2_hidden(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(definition_unfolding,[],[f78,f63])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( v3_ordinal1(X1)
     => ( r2_hidden(X0,X1)
       => v3_ordinal1(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] :
      ( v3_ordinal1(X0)
      | ~ r2_hidden(X0,X1)
      | ~ v3_ordinal1(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f21,plain,(
    ! [X0,X1] :
      ( v3_ordinal1(X0)
      | ~ r2_hidden(X0,X1)
      | ~ v3_ordinal1(X1) ) ),
    inference(flattening,[],[f20])).

fof(f75,plain,(
    ! [X0,X1] :
      ( v3_ordinal1(X0)
      | ~ r2_hidden(X0,X1)
      | ~ v3_ordinal1(X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f12,axiom,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => v3_ordinal1(k1_ordinal1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0] :
      ( v3_ordinal1(k1_ordinal1(X0))
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f77,plain,(
    ! [X0] :
      ( v3_ordinal1(k1_ordinal1(X0))
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f90,plain,(
    ! [X0] :
      ( v3_ordinal1(k2_xboole_0(X0,k1_tarski(X0)))
      | ~ v3_ordinal1(X0) ) ),
    inference(definition_unfolding,[],[f77,f63])).

fof(f14,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f80,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f5,axiom,(
    ! [X0] :
      ( v4_ordinal1(X0)
    <=> k3_tarski(X0) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0] :
      ( ( v4_ordinal1(X0)
        | k3_tarski(X0) != X0 )
      & ( k3_tarski(X0) = X0
        | ~ v4_ordinal1(X0) ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f64,plain,(
    ! [X0] :
      ( k3_tarski(X0) = X0
      | ~ v4_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f65,plain,(
    ! [X0] :
      ( v4_ordinal1(X0)
      | k3_tarski(X0) != X0 ) ),
    inference(cnf_transformation,[],[f39])).

fof(f73,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,k1_ordinal1(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f88,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,k2_xboole_0(X1,k1_tarski(X1)))
      | ~ r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f73,f63])).

fof(f61,plain,(
    ! [X0,X1] :
      ( k3_tarski(X0) = X1
      | r2_hidden(sK2(X0,X1),X0)
      | r2_hidden(sK1(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f81,plain,(
    v3_ordinal1(sK5) ),
    inference(cnf_transformation,[],[f53])).

fof(f60,plain,(
    ! [X0,X1] :
      ( k3_tarski(X0) = X1
      | r2_hidden(sK1(X0,X1),sK2(X0,X1))
      | r2_hidden(sK1(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f17])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f29])).

fof(f31,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK0(X0,X1),X1)
          & r2_hidden(sK0(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f30,f31])).

fof(f54,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f62,plain,(
    ! [X0,X3,X1] :
      ( k3_tarski(X0) = X1
      | ~ r2_hidden(X3,X0)
      | ~ r2_hidden(sK1(X0,X1),X3)
      | ~ r2_hidden(sK1(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f11,axiom,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ! [X1] :
          ( v3_ordinal1(X1)
         => ~ ( ~ r2_hidden(X1,X0)
              & X0 != X1
              & ~ r2_hidden(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(X1,X0)
          | X0 = X1
          | r2_hidden(X0,X1)
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(X1,X0)
          | X0 = X1
          | r2_hidden(X0,X1)
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(flattening,[],[f22])).

fof(f76,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,X0)
      | X0 = X1
      | r2_hidden(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f85,plain,
    ( ~ r2_hidden(k1_ordinal1(sK6),sK5)
    | ~ v4_ordinal1(sK5) ),
    inference(cnf_transformation,[],[f53])).

fof(f93,plain,
    ( ~ r2_hidden(k2_xboole_0(sK6,k1_tarski(sK6)),sK5)
    | ~ v4_ordinal1(sK5) ),
    inference(definition_unfolding,[],[f85,f63])).

fof(f72,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | r2_hidden(X0,X1)
      | ~ r2_hidden(X0,k1_ordinal1(X1)) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f89,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | r2_hidden(X0,X1)
      | ~ r2_hidden(X0,k2_xboole_0(X1,k1_tarski(X1))) ) ),
    inference(definition_unfolding,[],[f72,f63])).

fof(f83,plain,
    ( v3_ordinal1(sK6)
    | ~ v4_ordinal1(sK5) ),
    inference(cnf_transformation,[],[f53])).

fof(f84,plain,
    ( r2_hidden(sK6,sK5)
    | ~ v4_ordinal1(sK5) ),
    inference(cnf_transformation,[],[f53])).

fof(f58,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(sK3(X0,X5),X0)
      | ~ r2_hidden(X5,X1)
      | k3_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f38])).

fof(f96,plain,(
    ! [X0,X5] :
      ( r2_hidden(sK3(X0,X5),X0)
      | ~ r2_hidden(X5,k3_tarski(X0)) ) ),
    inference(equality_resolution,[],[f58])).

fof(f55,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK0(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f56,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK0(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_8,plain,
    ( r2_hidden(X0,sK3(X1,X0))
    | ~ r2_hidden(X0,k3_tarski(X1)) ),
    inference(cnf_transformation,[],[f97])).

cnf(c_1885,plain,
    ( r2_hidden(X0,sK3(X1,X0)) = iProver_top
    | r2_hidden(X0,k3_tarski(X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_17,plain,
    ( r2_hidden(X0,k2_xboole_0(X0,k1_tarski(X0))) ),
    inference(cnf_transformation,[],[f98])).

cnf(c_1879,plain,
    ( r2_hidden(X0,k2_xboole_0(X0,k1_tarski(X0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_29,negated_conjecture,
    ( ~ r2_hidden(X0,sK5)
    | r2_hidden(k2_xboole_0(X0,k1_tarski(X0)),sK5)
    | ~ v3_ordinal1(X0)
    | v4_ordinal1(sK5) ),
    inference(cnf_transformation,[],[f94])).

cnf(c_1869,plain,
    ( r2_hidden(X0,sK5) != iProver_top
    | r2_hidden(k2_xboole_0(X0,k1_tarski(X0)),sK5) = iProver_top
    | v3_ordinal1(X0) != iProver_top
    | v4_ordinal1(sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_6,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X2,X0)
    | r2_hidden(X2,k3_tarski(X1)) ),
    inference(cnf_transformation,[],[f95])).

cnf(c_1887,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X2,X0) != iProver_top
    | r2_hidden(X2,k3_tarski(X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_5182,plain,
    ( r2_hidden(X0,k2_xboole_0(X1,k1_tarski(X1))) != iProver_top
    | r2_hidden(X0,k3_tarski(sK5)) = iProver_top
    | r2_hidden(X1,sK5) != iProver_top
    | v3_ordinal1(X1) != iProver_top
    | v4_ordinal1(sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_1869,c_1887])).

cnf(c_5944,plain,
    ( r2_hidden(X0,k3_tarski(sK5)) = iProver_top
    | r2_hidden(X0,sK5) != iProver_top
    | v3_ordinal1(X0) != iProver_top
    | v4_ordinal1(sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_1879,c_5182])).

cnf(c_12,plain,
    ( ~ r1_ordinal1(X0,X1)
    | r1_tarski(X0,X1)
    | ~ v3_ordinal1(X1)
    | ~ v3_ordinal1(X0) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_24,plain,
    ( r1_ordinal1(k2_xboole_0(X0,k1_tarski(X0)),X1)
    | ~ r2_hidden(X0,X1)
    | ~ v3_ordinal1(X1)
    | ~ v3_ordinal1(X0) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_20,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ v3_ordinal1(X1)
    | v3_ordinal1(X0) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_177,plain,
    ( ~ v3_ordinal1(X1)
    | ~ r2_hidden(X0,X1)
    | r1_ordinal1(k2_xboole_0(X0,k1_tarski(X0)),X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_24,c_20])).

cnf(c_178,plain,
    ( r1_ordinal1(k2_xboole_0(X0,k1_tarski(X0)),X1)
    | ~ r2_hidden(X0,X1)
    | ~ v3_ordinal1(X1) ),
    inference(renaming,[status(thm)],[c_177])).

cnf(c_428,plain,
    ( ~ r2_hidden(X0,X1)
    | r1_tarski(X2,X3)
    | ~ v3_ordinal1(X3)
    | ~ v3_ordinal1(X2)
    | ~ v3_ordinal1(X1)
    | X1 != X3
    | k2_xboole_0(X0,k1_tarski(X0)) != X2 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_178])).

cnf(c_429,plain,
    ( ~ r2_hidden(X0,X1)
    | r1_tarski(k2_xboole_0(X0,k1_tarski(X0)),X1)
    | ~ v3_ordinal1(X1)
    | ~ v3_ordinal1(k2_xboole_0(X0,k1_tarski(X0))) ),
    inference(unflattening,[status(thm)],[c_428])).

cnf(c_22,plain,
    ( ~ v3_ordinal1(X0)
    | v3_ordinal1(k2_xboole_0(X0,k1_tarski(X0))) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_433,plain,
    ( ~ v3_ordinal1(X1)
    | r1_tarski(k2_xboole_0(X0,k1_tarski(X0)),X1)
    | ~ r2_hidden(X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_429,c_22,c_20])).

cnf(c_434,plain,
    ( ~ r2_hidden(X0,X1)
    | r1_tarski(k2_xboole_0(X0,k1_tarski(X0)),X1)
    | ~ v3_ordinal1(X1) ),
    inference(renaming,[status(thm)],[c_433])).

cnf(c_1866,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r1_tarski(k2_xboole_0(X0,k1_tarski(X0)),X1) = iProver_top
    | v3_ordinal1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_434])).

cnf(c_25,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r1_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_1873,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_2603,plain,
    ( r1_tarski(k2_xboole_0(X0,k1_tarski(X0)),X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1879,c_1873])).

cnf(c_3201,plain,
    ( r2_hidden(X0,X0) != iProver_top
    | v3_ordinal1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1866,c_2603])).

cnf(c_10964,plain,
    ( r2_hidden(k3_tarski(sK5),sK5) != iProver_top
    | v3_ordinal1(k3_tarski(sK5)) != iProver_top
    | v4_ordinal1(sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_5944,c_3201])).

cnf(c_10,plain,
    ( ~ v4_ordinal1(X0)
    | k3_tarski(X0) = X0 ),
    inference(cnf_transformation,[],[f64])).

cnf(c_78,plain,
    ( ~ v4_ordinal1(sK5)
    | k3_tarski(sK5) = sK5 ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_9,plain,
    ( v4_ordinal1(X0)
    | k3_tarski(X0) != X0 ),
    inference(cnf_transformation,[],[f65])).

cnf(c_80,plain,
    ( k3_tarski(X0) != X0
    | v4_ordinal1(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_82,plain,
    ( k3_tarski(sK5) != sK5
    | v4_ordinal1(sK5) = iProver_top ),
    inference(instantiation,[status(thm)],[c_80])).

cnf(c_18,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,k2_xboole_0(X1,k1_tarski(X1))) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_3509,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,k3_tarski(X2))
    | ~ r2_hidden(k2_xboole_0(X1,k1_tarski(X1)),X2) ),
    inference(resolution,[status(thm)],[c_6,c_18])).

cnf(c_3505,plain,
    ( r2_hidden(X0,k3_tarski(X1))
    | ~ r2_hidden(k2_xboole_0(X0,k1_tarski(X0)),X1) ),
    inference(resolution,[status(thm)],[c_6,c_17])).

cnf(c_9528,plain,
    ( r2_hidden(X0,k3_tarski(sK5))
    | ~ r2_hidden(X0,sK5)
    | ~ v3_ordinal1(X0)
    | v4_ordinal1(sK5) ),
    inference(resolution,[status(thm)],[c_3505,c_29])).

cnf(c_17185,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,k3_tarski(k3_tarski(sK5)))
    | ~ r2_hidden(k2_xboole_0(X1,k1_tarski(X1)),sK5)
    | ~ v3_ordinal1(k2_xboole_0(X1,k1_tarski(X1)))
    | v4_ordinal1(sK5) ),
    inference(resolution,[status(thm)],[c_3509,c_9528])).

cnf(c_18321,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,k3_tarski(k3_tarski(sK5)))
    | ~ r2_hidden(X1,sK5)
    | ~ v3_ordinal1(X1)
    | ~ v3_ordinal1(k2_xboole_0(X1,k1_tarski(X1)))
    | v4_ordinal1(sK5) ),
    inference(resolution,[status(thm)],[c_17185,c_29])).

cnf(c_10959,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,k3_tarski(k3_tarski(sK5))) = iProver_top
    | r2_hidden(X1,sK5) != iProver_top
    | v3_ordinal1(X1) != iProver_top
    | v4_ordinal1(sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_5944,c_1887])).

cnf(c_11060,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,k3_tarski(k3_tarski(sK5)))
    | ~ r2_hidden(X1,sK5)
    | ~ v3_ordinal1(X1)
    | v4_ordinal1(sK5) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_10959])).

cnf(c_18453,plain,
    ( ~ v3_ordinal1(X1)
    | ~ r2_hidden(X1,sK5)
    | r2_hidden(X0,k3_tarski(k3_tarski(sK5)))
    | ~ r2_hidden(X0,X1)
    | v4_ordinal1(sK5) ),
    inference(global_propositional_subsumption,[status(thm)],[c_18321,c_11060])).

cnf(c_18454,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,k3_tarski(k3_tarski(sK5)))
    | ~ r2_hidden(X1,sK5)
    | ~ v3_ordinal1(X1)
    | v4_ordinal1(sK5) ),
    inference(renaming,[status(thm)],[c_18453])).

cnf(c_4,plain,
    ( r2_hidden(sK2(X0,X1),X0)
    | r2_hidden(sK1(X0,X1),X1)
    | k3_tarski(X0) = X1 ),
    inference(cnf_transformation,[],[f61])).

cnf(c_3857,plain,
    ( r2_hidden(sK2(X0,X0),X0)
    | r2_hidden(sK1(X0,X0),X0)
    | v4_ordinal1(X0) ),
    inference(resolution,[status(thm)],[c_4,c_9])).

cnf(c_18501,plain,
    ( ~ r2_hidden(X0,sK2(sK5,sK5))
    | r2_hidden(X0,k3_tarski(k3_tarski(sK5)))
    | r2_hidden(sK1(sK5,sK5),sK5)
    | ~ v3_ordinal1(sK2(sK5,sK5))
    | v4_ordinal1(sK5) ),
    inference(resolution,[status(thm)],[c_18454,c_3857])).

cnf(c_30,negated_conjecture,
    ( v3_ordinal1(sK5) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_81,plain,
    ( v4_ordinal1(sK5)
    | k3_tarski(sK5) != sK5 ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_5,plain,
    ( r2_hidden(sK1(X0,X1),X1)
    | r2_hidden(sK1(X0,X1),sK2(X0,X1))
    | k3_tarski(X0) = X1 ),
    inference(cnf_transformation,[],[f60])).

cnf(c_93,plain,
    ( r2_hidden(sK1(sK5,sK5),sK2(sK5,sK5))
    | r2_hidden(sK1(sK5,sK5),sK5)
    | k3_tarski(sK5) = sK5 ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_2469,plain,
    ( r2_hidden(sK1(X0,X1),k2_xboole_0(sK2(X0,X1),k1_tarski(sK2(X0,X1))))
    | ~ r2_hidden(sK1(X0,X1),sK2(X0,X1)) ),
    inference(instantiation,[status(thm)],[c_18])).

cnf(c_2481,plain,
    ( r2_hidden(sK1(sK5,sK5),k2_xboole_0(sK2(sK5,sK5),k1_tarski(sK2(sK5,sK5))))
    | ~ r2_hidden(sK1(sK5,sK5),sK2(sK5,sK5)) ),
    inference(instantiation,[status(thm)],[c_2469])).

cnf(c_2518,plain,
    ( ~ r2_hidden(sK2(X0,sK5),X0)
    | r1_tarski(k2_xboole_0(sK2(X0,sK5),k1_tarski(sK2(X0,sK5))),X0)
    | ~ v3_ordinal1(X0) ),
    inference(instantiation,[status(thm)],[c_434])).

cnf(c_2538,plain,
    ( ~ r2_hidden(sK2(sK5,sK5),sK5)
    | r1_tarski(k2_xboole_0(sK2(sK5,sK5),k1_tarski(sK2(sK5,sK5))),sK5)
    | ~ v3_ordinal1(sK5) ),
    inference(instantiation,[status(thm)],[c_2518])).

cnf(c_3859,plain,
    ( r2_hidden(sK2(sK5,sK5),sK5)
    | r2_hidden(sK1(sK5,sK5),sK5)
    | v4_ordinal1(sK5) ),
    inference(instantiation,[status(thm)],[c_3857])).

cnf(c_2,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | ~ r1_tarski(X1,X2) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_7110,plain,
    ( ~ r2_hidden(sK1(X0,X1),X2)
    | r2_hidden(sK1(X0,X1),X3)
    | ~ r1_tarski(X2,X3) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_14931,plain,
    ( r2_hidden(sK1(X0,X1),X2)
    | ~ r2_hidden(sK1(X0,X1),k2_xboole_0(sK2(X0,X1),k1_tarski(sK2(X0,X1))))
    | ~ r1_tarski(k2_xboole_0(sK2(X0,X1),k1_tarski(sK2(X0,X1))),X2) ),
    inference(instantiation,[status(thm)],[c_7110])).

cnf(c_14933,plain,
    ( ~ r2_hidden(sK1(sK5,sK5),k2_xboole_0(sK2(sK5,sK5),k1_tarski(sK2(sK5,sK5))))
    | r2_hidden(sK1(sK5,sK5),sK5)
    | ~ r1_tarski(k2_xboole_0(sK2(sK5,sK5),k1_tarski(sK2(sK5,sK5))),sK5) ),
    inference(instantiation,[status(thm)],[c_14931])).

cnf(c_18701,plain,
    ( r2_hidden(sK1(sK5,sK5),sK5)
    | v4_ordinal1(sK5) ),
    inference(global_propositional_subsumption,[status(thm)],[c_18501,c_30,c_81,c_93,c_2481,c_2538,c_3859,c_14933])).

cnf(c_2429,plain,
    ( r2_hidden(k2_xboole_0(sK1(X0,sK5),k1_tarski(sK1(X0,sK5))),sK5)
    | ~ r2_hidden(sK1(X0,sK5),sK5)
    | ~ v3_ordinal1(sK1(X0,sK5))
    | v4_ordinal1(sK5) ),
    inference(instantiation,[status(thm)],[c_29])).

cnf(c_2433,plain,
    ( r2_hidden(k2_xboole_0(sK1(sK5,sK5),k1_tarski(sK1(sK5,sK5))),sK5)
    | ~ r2_hidden(sK1(sK5,sK5),sK5)
    | ~ v3_ordinal1(sK1(sK5,sK5))
    | v4_ordinal1(sK5) ),
    inference(instantiation,[status(thm)],[c_2429])).

cnf(c_3738,plain,
    ( ~ r2_hidden(sK1(X0,X1),X2)
    | ~ v3_ordinal1(X2)
    | v3_ordinal1(sK1(X0,X1)) ),
    inference(instantiation,[status(thm)],[c_20])).

cnf(c_3740,plain,
    ( ~ r2_hidden(sK1(sK5,sK5),sK5)
    | v3_ordinal1(sK1(sK5,sK5))
    | ~ v3_ordinal1(sK5) ),
    inference(instantiation,[status(thm)],[c_3738])).

cnf(c_3,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(sK1(X1,X2),X0)
    | ~ r2_hidden(sK1(X1,X2),X2)
    | k3_tarski(X1) = X2 ),
    inference(cnf_transformation,[],[f62])).

cnf(c_4420,plain,
    ( ~ r2_hidden(k2_xboole_0(sK1(X0,sK5),k1_tarski(sK1(X0,sK5))),sK5)
    | ~ r2_hidden(sK1(sK5,X1),X1)
    | ~ r2_hidden(sK1(sK5,X1),k2_xboole_0(sK1(X0,sK5),k1_tarski(sK1(X0,sK5))))
    | k3_tarski(sK5) = X1 ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_4450,plain,
    ( ~ r2_hidden(k2_xboole_0(sK1(sK5,sK5),k1_tarski(sK1(sK5,sK5))),sK5)
    | ~ r2_hidden(sK1(sK5,sK5),k2_xboole_0(sK1(sK5,sK5),k1_tarski(sK1(sK5,sK5))))
    | ~ r2_hidden(sK1(sK5,sK5),sK5)
    | k3_tarski(sK5) = sK5 ),
    inference(instantiation,[status(thm)],[c_4420])).

cnf(c_13762,plain,
    ( r2_hidden(sK1(X0,X1),k2_xboole_0(sK1(X0,X1),k1_tarski(sK1(X0,X1)))) ),
    inference(instantiation,[status(thm)],[c_17])).

cnf(c_13768,plain,
    ( r2_hidden(sK1(sK5,sK5),k2_xboole_0(sK1(sK5,sK5),k1_tarski(sK1(sK5,sK5)))) ),
    inference(instantiation,[status(thm)],[c_13762])).

cnf(c_18705,plain,
    ( v4_ordinal1(sK5) ),
    inference(global_propositional_subsumption,[status(thm)],[c_18701,c_30,c_81,c_2433,c_3740,c_4450,c_13768])).

cnf(c_18981,plain,
    ( v4_ordinal1(sK5) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_10964,c_30,c_78,c_81,c_82,c_2433,c_3740,c_4450,c_13768,c_18701])).

cnf(c_21,plain,
    ( r2_hidden(X0,X1)
    | r2_hidden(X1,X0)
    | ~ v3_ordinal1(X1)
    | ~ v3_ordinal1(X0)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f76])).

cnf(c_1875,plain,
    ( X0 = X1
    | r2_hidden(X1,X0) = iProver_top
    | r2_hidden(X0,X1) = iProver_top
    | v3_ordinal1(X1) != iProver_top
    | v3_ordinal1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_26,negated_conjecture,
    ( ~ r2_hidden(k2_xboole_0(sK6,k1_tarski(sK6)),sK5)
    | ~ v4_ordinal1(sK5) ),
    inference(cnf_transformation,[],[f93])).

cnf(c_1872,plain,
    ( r2_hidden(k2_xboole_0(sK6,k1_tarski(sK6)),sK5) != iProver_top
    | v4_ordinal1(sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_4829,plain,
    ( k2_xboole_0(sK6,k1_tarski(sK6)) = sK5
    | r2_hidden(sK5,k2_xboole_0(sK6,k1_tarski(sK6))) = iProver_top
    | v3_ordinal1(k2_xboole_0(sK6,k1_tarski(sK6))) != iProver_top
    | v3_ordinal1(sK5) != iProver_top
    | v4_ordinal1(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_1875,c_1872])).

cnf(c_31,plain,
    ( v3_ordinal1(sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_6039,plain,
    ( v3_ordinal1(k2_xboole_0(sK6,k1_tarski(sK6))) != iProver_top
    | r2_hidden(sK5,k2_xboole_0(sK6,k1_tarski(sK6))) = iProver_top
    | k2_xboole_0(sK6,k1_tarski(sK6)) = sK5
    | v4_ordinal1(sK5) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4829,c_31])).

cnf(c_6040,plain,
    ( k2_xboole_0(sK6,k1_tarski(sK6)) = sK5
    | r2_hidden(sK5,k2_xboole_0(sK6,k1_tarski(sK6))) = iProver_top
    | v3_ordinal1(k2_xboole_0(sK6,k1_tarski(sK6))) != iProver_top
    | v4_ordinal1(sK5) != iProver_top ),
    inference(renaming,[status(thm)],[c_6039])).

cnf(c_19,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k2_xboole_0(X1,k1_tarski(X1)))
    | X1 = X0 ),
    inference(cnf_transformation,[],[f89])).

cnf(c_1877,plain,
    ( X0 = X1
    | r2_hidden(X1,X0) = iProver_top
    | r2_hidden(X1,k2_xboole_0(X0,k1_tarski(X0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_6052,plain,
    ( k2_xboole_0(sK6,k1_tarski(sK6)) = sK5
    | sK5 = sK6
    | r2_hidden(sK5,sK6) = iProver_top
    | v3_ordinal1(k2_xboole_0(sK6,k1_tarski(sK6))) != iProver_top
    | v4_ordinal1(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_6040,c_1877])).

cnf(c_28,negated_conjecture,
    ( v3_ordinal1(sK6)
    | ~ v4_ordinal1(sK5) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_35,plain,
    ( v3_ordinal1(sK6) = iProver_top
    | v4_ordinal1(sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_1874,plain,
    ( v3_ordinal1(X0) != iProver_top
    | v3_ordinal1(k2_xboole_0(X0,k1_tarski(X0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_6050,plain,
    ( k2_xboole_0(sK6,k1_tarski(sK6)) = sK5
    | r1_tarski(k2_xboole_0(sK6,k1_tarski(sK6)),sK5) != iProver_top
    | v3_ordinal1(k2_xboole_0(sK6,k1_tarski(sK6))) != iProver_top
    | v4_ordinal1(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_6040,c_1873])).

cnf(c_27,negated_conjecture,
    ( r2_hidden(sK6,sK5)
    | ~ v4_ordinal1(sK5) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_36,plain,
    ( r2_hidden(sK6,sK5) = iProver_top
    | v4_ordinal1(sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_60,plain,
    ( r2_hidden(X0,k2_xboole_0(X0,k1_tarski(X0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_62,plain,
    ( r2_hidden(sK5,k2_xboole_0(sK5,k1_tarski(sK5))) = iProver_top ),
    inference(instantiation,[status(thm)],[c_60])).

cnf(c_683,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X2,X3)
    | ~ v3_ordinal1(X3)
    | X3 != X0
    | k2_xboole_0(X2,k1_tarski(X2)) != X1 ),
    inference(resolution_lifted,[status(thm)],[c_25,c_434])).

cnf(c_684,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X1,k2_xboole_0(X0,k1_tarski(X0)))
    | ~ v3_ordinal1(X1) ),
    inference(unflattening,[status(thm)],[c_683])).

cnf(c_685,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X1,k2_xboole_0(X0,k1_tarski(X0))) != iProver_top
    | v3_ordinal1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_684])).

cnf(c_687,plain,
    ( r2_hidden(sK5,k2_xboole_0(sK5,k1_tarski(sK5))) != iProver_top
    | r2_hidden(sK5,sK5) != iProver_top
    | v3_ordinal1(sK5) != iProver_top ),
    inference(instantiation,[status(thm)],[c_685])).

cnf(c_2209,plain,
    ( ~ r2_hidden(sK6,sK5)
    | r1_tarski(k2_xboole_0(sK6,k1_tarski(sK6)),sK5)
    | ~ v3_ordinal1(sK5) ),
    inference(instantiation,[status(thm)],[c_434])).

cnf(c_2210,plain,
    ( r2_hidden(sK6,sK5) != iProver_top
    | r1_tarski(k2_xboole_0(sK6,k1_tarski(sK6)),sK5) = iProver_top
    | v3_ordinal1(sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2209])).

cnf(c_1891,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,X2) = iProver_top
    | r1_tarski(X1,X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_6048,plain,
    ( k2_xboole_0(sK6,k1_tarski(sK6)) = sK5
    | r2_hidden(sK5,X0) = iProver_top
    | r1_tarski(k2_xboole_0(sK6,k1_tarski(sK6)),X0) != iProver_top
    | v3_ordinal1(k2_xboole_0(sK6,k1_tarski(sK6))) != iProver_top
    | v4_ordinal1(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_6040,c_1891])).

cnf(c_6095,plain,
    ( k2_xboole_0(sK6,k1_tarski(sK6)) = sK5
    | r2_hidden(sK5,sK5) = iProver_top
    | r1_tarski(k2_xboole_0(sK6,k1_tarski(sK6)),sK5) != iProver_top
    | v3_ordinal1(k2_xboole_0(sK6,k1_tarski(sK6))) != iProver_top
    | v4_ordinal1(sK5) != iProver_top ),
    inference(instantiation,[status(thm)],[c_6048])).

cnf(c_9938,plain,
    ( k2_xboole_0(sK6,k1_tarski(sK6)) = sK5
    | v3_ordinal1(k2_xboole_0(sK6,k1_tarski(sK6))) != iProver_top
    | v4_ordinal1(sK5) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6050,c_31,c_36,c_62,c_687,c_2210,c_6095])).

cnf(c_9945,plain,
    ( k2_xboole_0(sK6,k1_tarski(sK6)) = sK5
    | v3_ordinal1(sK6) != iProver_top
    | v4_ordinal1(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_1874,c_9938])).

cnf(c_11281,plain,
    ( k2_xboole_0(sK6,k1_tarski(sK6)) = sK5
    | v4_ordinal1(sK5) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6052,c_35,c_9945])).

cnf(c_18987,plain,
    ( k2_xboole_0(sK6,k1_tarski(sK6)) = sK5 ),
    inference(superposition,[status(thm)],[c_18981,c_11281])).

cnf(c_20297,plain,
    ( r2_hidden(sK6,X0) != iProver_top
    | r1_tarski(sK5,X0) = iProver_top
    | v3_ordinal1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_18987,c_1866])).

cnf(c_71164,plain,
    ( r2_hidden(sK6,k3_tarski(X0)) != iProver_top
    | r1_tarski(sK5,sK3(X0,sK6)) = iProver_top
    | v3_ordinal1(sK3(X0,sK6)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1885,c_20297])).

cnf(c_71265,plain,
    ( r2_hidden(sK6,k3_tarski(sK5)) != iProver_top
    | r1_tarski(sK5,sK3(sK5,sK6)) = iProver_top
    | v3_ordinal1(sK3(sK5,sK6)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_71164])).

cnf(c_1883,plain,
    ( k3_tarski(X0) = X0
    | v4_ordinal1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_18986,plain,
    ( k3_tarski(sK5) = sK5 ),
    inference(superposition,[status(thm)],[c_18981,c_1883])).

cnf(c_1871,plain,
    ( r2_hidden(sK6,sK5) = iProver_top
    | v4_ordinal1(sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_5181,plain,
    ( r2_hidden(X0,k3_tarski(sK5)) = iProver_top
    | r2_hidden(X0,sK6) != iProver_top
    | v4_ordinal1(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_1871,c_1887])).

cnf(c_19199,plain,
    ( r2_hidden(X0,sK5) = iProver_top
    | r2_hidden(X0,sK6) != iProver_top
    | v4_ordinal1(sK5) != iProver_top ),
    inference(demodulation,[status(thm)],[c_18986,c_5181])).

cnf(c_19827,plain,
    ( r2_hidden(X0,sK6) != iProver_top
    | r2_hidden(X0,sK5) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_19199,c_30,c_78,c_81,c_82,c_2433,c_3740,c_4450,c_13768,c_18701])).

cnf(c_19828,plain,
    ( r2_hidden(X0,sK5) = iProver_top
    | r2_hidden(X0,sK6) != iProver_top ),
    inference(renaming,[status(thm)],[c_19827])).

cnf(c_19840,plain,
    ( sK6 = X0
    | r2_hidden(X0,sK5) = iProver_top
    | r2_hidden(sK6,X0) = iProver_top
    | v3_ordinal1(X0) != iProver_top
    | v3_ordinal1(sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_1875,c_19828])).

cnf(c_249,plain,
    ( v4_ordinal1(X0)
    | k3_tarski(X0) != X0 ),
    inference(prop_impl,[status(thm)],[c_9])).

cnf(c_510,plain,
    ( v3_ordinal1(sK6)
    | k3_tarski(X0) != X0
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_249,c_28])).

cnf(c_511,plain,
    ( v3_ordinal1(sK6)
    | k3_tarski(sK5) != sK5 ),
    inference(unflattening,[status(thm)],[c_510])).

cnf(c_512,plain,
    ( k3_tarski(sK5) != sK5
    | v3_ordinal1(sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_511])).

cnf(c_34000,plain,
    ( v3_ordinal1(X0) != iProver_top
    | r2_hidden(sK6,X0) = iProver_top
    | r2_hidden(X0,sK5) = iProver_top
    | sK6 = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_19840,c_30,c_78,c_81,c_512,c_2433,c_3740,c_4450,c_13768,c_18701])).

cnf(c_34001,plain,
    ( sK6 = X0
    | r2_hidden(X0,sK5) = iProver_top
    | r2_hidden(sK6,X0) = iProver_top
    | v3_ordinal1(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_34000])).

cnf(c_7,plain,
    ( ~ r2_hidden(X0,k3_tarski(X1))
    | r2_hidden(sK3(X1,X0),X1) ),
    inference(cnf_transformation,[],[f96])).

cnf(c_1886,plain,
    ( r2_hidden(X0,k3_tarski(X1)) != iProver_top
    | r2_hidden(sK3(X1,X0),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_1876,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | v3_ordinal1(X1) != iProver_top
    | v3_ordinal1(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_3779,plain,
    ( r2_hidden(X0,k3_tarski(X1)) != iProver_top
    | v3_ordinal1(X1) != iProver_top
    | v3_ordinal1(sK3(X1,X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1886,c_1876])).

cnf(c_34014,plain,
    ( k3_tarski(X0) = sK6
    | r2_hidden(k3_tarski(X0),sK5) = iProver_top
    | v3_ordinal1(X0) != iProver_top
    | v3_ordinal1(sK3(X0,sK6)) = iProver_top
    | v3_ordinal1(k3_tarski(X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_34001,c_3779])).

cnf(c_34235,plain,
    ( k3_tarski(sK5) = sK6
    | r2_hidden(k3_tarski(sK5),sK5) = iProver_top
    | v3_ordinal1(sK3(sK5,sK6)) = iProver_top
    | v3_ordinal1(k3_tarski(sK5)) != iProver_top
    | v3_ordinal1(sK5) != iProver_top ),
    inference(instantiation,[status(thm)],[c_34014])).

cnf(c_20171,plain,
    ( ~ r2_hidden(sK3(X0,sK6),X0)
    | ~ r1_tarski(X0,sK3(X0,sK6)) ),
    inference(instantiation,[status(thm)],[c_25])).

cnf(c_20172,plain,
    ( r2_hidden(sK3(X0,sK6),X0) != iProver_top
    | r1_tarski(X0,sK3(X0,sK6)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20171])).

cnf(c_20174,plain,
    ( r2_hidden(sK3(sK5,sK6),sK5) != iProver_top
    | r1_tarski(sK5,sK3(sK5,sK6)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_20172])).

cnf(c_1216,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_19987,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(k3_tarski(sK5),X2)
    | X1 != X2
    | X0 != k3_tarski(sK5) ),
    inference(instantiation,[status(thm)],[c_1216])).

cnf(c_20011,plain,
    ( X0 != X1
    | X2 != k3_tarski(sK5)
    | r2_hidden(X2,X0) = iProver_top
    | r2_hidden(k3_tarski(sK5),X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19987])).

cnf(c_20013,plain,
    ( sK5 != k3_tarski(sK5)
    | sK5 != sK5
    | r2_hidden(k3_tarski(sK5),sK5) != iProver_top
    | r2_hidden(sK5,sK5) = iProver_top ),
    inference(instantiation,[status(thm)],[c_20011])).

cnf(c_20012,plain,
    ( ~ r2_hidden(k3_tarski(sK5),sK5)
    | r2_hidden(sK5,sK5)
    | sK5 != k3_tarski(sK5)
    | sK5 != sK5 ),
    inference(instantiation,[status(thm)],[c_19987])).

cnf(c_1214,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_1213,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_3846,plain,
    ( X0 != X1
    | X1 = X0 ),
    inference(resolution,[status(thm)],[c_1214,c_1213])).

cnf(c_19006,plain,
    ( ~ v4_ordinal1(X0)
    | X0 = k3_tarski(X0) ),
    inference(resolution,[status(thm)],[c_10,c_3846])).

cnf(c_19008,plain,
    ( ~ v4_ordinal1(sK5)
    | sK5 = k3_tarski(sK5) ),
    inference(instantiation,[status(thm)],[c_19006])).

cnf(c_1,plain,
    ( r2_hidden(sK0(X0,X1),X0)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_1892,plain,
    ( r2_hidden(sK0(X0,X1),X0) = iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_0,plain,
    ( ~ r2_hidden(sK0(X0,X1),X1)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_1893,plain,
    ( r2_hidden(sK0(X0,X1),X1) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_3464,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1892,c_1893])).

cnf(c_5663,plain,
    ( r2_hidden(X0,sK6) != iProver_top
    | r1_tarski(k3_tarski(sK5),X0) != iProver_top
    | v4_ordinal1(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_5181,c_1873])).

cnf(c_6323,plain,
    ( r2_hidden(k3_tarski(sK5),sK6) != iProver_top
    | v4_ordinal1(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_3464,c_5663])).

cnf(c_16504,plain,
    ( k3_tarski(sK5) = sK6
    | r2_hidden(sK6,k3_tarski(sK5)) = iProver_top
    | v3_ordinal1(k3_tarski(sK5)) != iProver_top
    | v3_ordinal1(sK6) != iProver_top
    | v4_ordinal1(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_1875,c_6323])).

cnf(c_1218,plain,
    ( ~ v3_ordinal1(X0)
    | v3_ordinal1(X1)
    | X1 != X0 ),
    theory(equality)).

cnf(c_6828,plain,
    ( ~ v3_ordinal1(X0)
    | v3_ordinal1(k3_tarski(X1))
    | k3_tarski(X1) != X0 ),
    inference(instantiation,[status(thm)],[c_1218])).

cnf(c_6829,plain,
    ( k3_tarski(X0) != X1
    | v3_ordinal1(X1) != iProver_top
    | v3_ordinal1(k3_tarski(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6828])).

cnf(c_6831,plain,
    ( k3_tarski(sK5) != sK5
    | v3_ordinal1(k3_tarski(sK5)) = iProver_top
    | v3_ordinal1(sK5) != iProver_top ),
    inference(instantiation,[status(thm)],[c_6829])).

cnf(c_2261,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(sK6,sK5)
    | X1 != sK5
    | X0 != sK6 ),
    inference(instantiation,[status(thm)],[c_1216])).

cnf(c_3246,plain,
    ( r2_hidden(k3_tarski(sK5),X0)
    | ~ r2_hidden(sK6,sK5)
    | X0 != sK5
    | k3_tarski(sK5) != sK6 ),
    inference(instantiation,[status(thm)],[c_2261])).

cnf(c_3250,plain,
    ( r2_hidden(k3_tarski(sK5),sK5)
    | ~ r2_hidden(sK6,sK5)
    | k3_tarski(sK5) != sK6
    | sK5 != sK5 ),
    inference(instantiation,[status(thm)],[c_3246])).

cnf(c_3128,plain,
    ( r2_hidden(sK3(X0,sK6),X0)
    | ~ r2_hidden(sK6,k3_tarski(X0)) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_3133,plain,
    ( r2_hidden(sK3(X0,sK6),X0) = iProver_top
    | r2_hidden(sK6,k3_tarski(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3128])).

cnf(c_3135,plain,
    ( r2_hidden(sK3(sK5,sK6),sK5) = iProver_top
    | r2_hidden(sK6,k3_tarski(sK5)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_3133])).

cnf(c_686,plain,
    ( ~ r2_hidden(sK5,k2_xboole_0(sK5,k1_tarski(sK5)))
    | ~ r2_hidden(sK5,sK5)
    | ~ v3_ordinal1(sK5) ),
    inference(instantiation,[status(thm)],[c_684])).

cnf(c_61,plain,
    ( r2_hidden(sK5,k2_xboole_0(sK5,k1_tarski(sK5))) ),
    inference(instantiation,[status(thm)],[c_17])).

cnf(c_51,plain,
    ( r2_hidden(sK5,sK5)
    | ~ v3_ordinal1(sK5)
    | sK5 = sK5 ),
    inference(instantiation,[status(thm)],[c_21])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_71265,c_34235,c_20174,c_20013,c_20012,c_19008,c_18705,c_16504,c_6831,c_3250,c_3135,c_687,c_686,c_512,c_82,c_78,c_62,c_61,c_51,c_27,c_31,c_30])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 13:55:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 15.84/2.48  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 15.84/2.48  
% 15.84/2.48  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 15.84/2.48  
% 15.84/2.48  ------  iProver source info
% 15.84/2.48  
% 15.84/2.48  git: date: 2020-06-30 10:37:57 +0100
% 15.84/2.48  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 15.84/2.48  git: non_committed_changes: false
% 15.84/2.48  git: last_make_outside_of_git: false
% 15.84/2.48  
% 15.84/2.48  ------ 
% 15.84/2.48  ------ Parsing...
% 15.84/2.48  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 15.84/2.48  
% 15.84/2.48  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 15.84/2.48  
% 15.84/2.48  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 15.84/2.48  
% 15.84/2.48  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 15.84/2.48  ------ Proving...
% 15.84/2.48  ------ Problem Properties 
% 15.84/2.48  
% 15.84/2.48  
% 15.84/2.48  clauses                                 28
% 15.84/2.48  conjectures                             5
% 15.84/2.48  EPR                                     7
% 15.84/2.48  Horn                                    22
% 15.84/2.48  unary                                   2
% 15.84/2.48  binary                                  14
% 15.84/2.48  lits                                    71
% 15.84/2.48  lits eq                                 7
% 15.84/2.49  fd_pure                                 0
% 15.84/2.49  fd_pseudo                               0
% 15.84/2.49  fd_cond                                 0
% 15.84/2.49  fd_pseudo_cond                          5
% 15.84/2.49  AC symbols                              0
% 15.84/2.49  
% 15.84/2.49  ------ Input Options Time Limit: Unbounded
% 15.84/2.49  
% 15.84/2.49  
% 15.84/2.49  ------ 
% 15.84/2.49  Current options:
% 15.84/2.49  ------ 
% 15.84/2.49  
% 15.84/2.49  
% 15.84/2.49  
% 15.84/2.49  
% 15.84/2.49  ------ Proving...
% 15.84/2.49  
% 15.84/2.49  
% 15.84/2.49  % SZS status Theorem for theBenchmark.p
% 15.84/2.49  
% 15.84/2.49  % SZS output start CNFRefutation for theBenchmark.p
% 15.84/2.49  
% 15.84/2.49  fof(f2,axiom,(
% 15.84/2.49    ! [X0,X1] : (k3_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (r2_hidden(X3,X0) & r2_hidden(X2,X3))))),
% 15.84/2.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.84/2.49  
% 15.84/2.49  fof(f33,plain,(
% 15.84/2.49    ! [X0,X1] : ((k3_tarski(X0) = X1 | ? [X2] : ((! [X3] : (~r2_hidden(X3,X0) | ~r2_hidden(X2,X3)) | ~r2_hidden(X2,X1)) & (? [X3] : (r2_hidden(X3,X0) & r2_hidden(X2,X3)) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ! [X3] : (~r2_hidden(X3,X0) | ~r2_hidden(X2,X3))) & (? [X3] : (r2_hidden(X3,X0) & r2_hidden(X2,X3)) | ~r2_hidden(X2,X1))) | k3_tarski(X0) != X1))),
% 15.84/2.49    inference(nnf_transformation,[],[f2])).
% 15.84/2.49  
% 15.84/2.49  fof(f34,plain,(
% 15.84/2.49    ! [X0,X1] : ((k3_tarski(X0) = X1 | ? [X2] : ((! [X3] : (~r2_hidden(X3,X0) | ~r2_hidden(X2,X3)) | ~r2_hidden(X2,X1)) & (? [X4] : (r2_hidden(X4,X0) & r2_hidden(X2,X4)) | r2_hidden(X2,X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : (~r2_hidden(X6,X0) | ~r2_hidden(X5,X6))) & (? [X7] : (r2_hidden(X7,X0) & r2_hidden(X5,X7)) | ~r2_hidden(X5,X1))) | k3_tarski(X0) != X1))),
% 15.84/2.49    inference(rectify,[],[f33])).
% 15.84/2.49  
% 15.84/2.49  fof(f37,plain,(
% 15.84/2.49    ! [X5,X0] : (? [X7] : (r2_hidden(X7,X0) & r2_hidden(X5,X7)) => (r2_hidden(sK3(X0,X5),X0) & r2_hidden(X5,sK3(X0,X5))))),
% 15.84/2.49    introduced(choice_axiom,[])).
% 15.84/2.49  
% 15.84/2.49  fof(f36,plain,(
% 15.84/2.49    ( ! [X2] : (! [X1,X0] : (? [X4] : (r2_hidden(X4,X0) & r2_hidden(X2,X4)) => (r2_hidden(sK2(X0,X1),X0) & r2_hidden(X2,sK2(X0,X1))))) )),
% 15.84/2.49    introduced(choice_axiom,[])).
% 15.84/2.49  
% 15.84/2.49  fof(f35,plain,(
% 15.84/2.49    ! [X1,X0] : (? [X2] : ((! [X3] : (~r2_hidden(X3,X0) | ~r2_hidden(X2,X3)) | ~r2_hidden(X2,X1)) & (? [X4] : (r2_hidden(X4,X0) & r2_hidden(X2,X4)) | r2_hidden(X2,X1))) => ((! [X3] : (~r2_hidden(X3,X0) | ~r2_hidden(sK1(X0,X1),X3)) | ~r2_hidden(sK1(X0,X1),X1)) & (? [X4] : (r2_hidden(X4,X0) & r2_hidden(sK1(X0,X1),X4)) | r2_hidden(sK1(X0,X1),X1))))),
% 15.84/2.49    introduced(choice_axiom,[])).
% 15.84/2.49  
% 15.84/2.49  fof(f38,plain,(
% 15.84/2.49    ! [X0,X1] : ((k3_tarski(X0) = X1 | ((! [X3] : (~r2_hidden(X3,X0) | ~r2_hidden(sK1(X0,X1),X3)) | ~r2_hidden(sK1(X0,X1),X1)) & ((r2_hidden(sK2(X0,X1),X0) & r2_hidden(sK1(X0,X1),sK2(X0,X1))) | r2_hidden(sK1(X0,X1),X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : (~r2_hidden(X6,X0) | ~r2_hidden(X5,X6))) & ((r2_hidden(sK3(X0,X5),X0) & r2_hidden(X5,sK3(X0,X5))) | ~r2_hidden(X5,X1))) | k3_tarski(X0) != X1))),
% 15.84/2.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f34,f37,f36,f35])).
% 15.84/2.49  
% 15.84/2.49  fof(f57,plain,(
% 15.84/2.49    ( ! [X0,X5,X1] : (r2_hidden(X5,sK3(X0,X5)) | ~r2_hidden(X5,X1) | k3_tarski(X0) != X1) )),
% 15.84/2.49    inference(cnf_transformation,[],[f38])).
% 15.84/2.49  
% 15.84/2.49  fof(f97,plain,(
% 15.84/2.49    ( ! [X0,X5] : (r2_hidden(X5,sK3(X0,X5)) | ~r2_hidden(X5,k3_tarski(X0))) )),
% 15.84/2.49    inference(equality_resolution,[],[f57])).
% 15.84/2.49  
% 15.84/2.49  fof(f9,axiom,(
% 15.84/2.49    ! [X0,X1] : (r2_hidden(X0,k1_ordinal1(X1)) <=> (X0 = X1 | r2_hidden(X0,X1)))),
% 15.84/2.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.84/2.49  
% 15.84/2.49  fof(f45,plain,(
% 15.84/2.49    ! [X0,X1] : ((r2_hidden(X0,k1_ordinal1(X1)) | (X0 != X1 & ~r2_hidden(X0,X1))) & ((X0 = X1 | r2_hidden(X0,X1)) | ~r2_hidden(X0,k1_ordinal1(X1))))),
% 15.84/2.49    inference(nnf_transformation,[],[f9])).
% 15.84/2.49  
% 15.84/2.49  fof(f46,plain,(
% 15.84/2.49    ! [X0,X1] : ((r2_hidden(X0,k1_ordinal1(X1)) | (X0 != X1 & ~r2_hidden(X0,X1))) & (X0 = X1 | r2_hidden(X0,X1) | ~r2_hidden(X0,k1_ordinal1(X1))))),
% 15.84/2.49    inference(flattening,[],[f45])).
% 15.84/2.49  
% 15.84/2.49  fof(f74,plain,(
% 15.84/2.49    ( ! [X0,X1] : (r2_hidden(X0,k1_ordinal1(X1)) | X0 != X1) )),
% 15.84/2.49    inference(cnf_transformation,[],[f46])).
% 15.84/2.49  
% 15.84/2.49  fof(f3,axiom,(
% 15.84/2.49    ! [X0] : k1_ordinal1(X0) = k2_xboole_0(X0,k1_tarski(X0))),
% 15.84/2.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.84/2.49  
% 15.84/2.49  fof(f63,plain,(
% 15.84/2.49    ( ! [X0] : (k1_ordinal1(X0) = k2_xboole_0(X0,k1_tarski(X0))) )),
% 15.84/2.49    inference(cnf_transformation,[],[f3])).
% 15.84/2.49  
% 15.84/2.49  fof(f87,plain,(
% 15.84/2.49    ( ! [X0,X1] : (r2_hidden(X0,k2_xboole_0(X1,k1_tarski(X1))) | X0 != X1) )),
% 15.84/2.49    inference(definition_unfolding,[],[f74,f63])).
% 15.84/2.49  
% 15.84/2.49  fof(f98,plain,(
% 15.84/2.49    ( ! [X1] : (r2_hidden(X1,k2_xboole_0(X1,k1_tarski(X1)))) )),
% 15.84/2.49    inference(equality_resolution,[],[f87])).
% 15.84/2.49  
% 15.84/2.49  fof(f15,conjecture,(
% 15.84/2.49    ! [X0] : (v3_ordinal1(X0) => (v4_ordinal1(X0) <=> ! [X1] : (v3_ordinal1(X1) => (r2_hidden(X1,X0) => r2_hidden(k1_ordinal1(X1),X0)))))),
% 15.84/2.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.84/2.49  
% 15.84/2.49  fof(f16,negated_conjecture,(
% 15.84/2.49    ~! [X0] : (v3_ordinal1(X0) => (v4_ordinal1(X0) <=> ! [X1] : (v3_ordinal1(X1) => (r2_hidden(X1,X0) => r2_hidden(k1_ordinal1(X1),X0)))))),
% 15.84/2.49    inference(negated_conjecture,[],[f15])).
% 15.84/2.49  
% 15.84/2.49  fof(f27,plain,(
% 15.84/2.49    ? [X0] : ((v4_ordinal1(X0) <~> ! [X1] : ((r2_hidden(k1_ordinal1(X1),X0) | ~r2_hidden(X1,X0)) | ~v3_ordinal1(X1))) & v3_ordinal1(X0))),
% 15.84/2.49    inference(ennf_transformation,[],[f16])).
% 15.84/2.49  
% 15.84/2.49  fof(f28,plain,(
% 15.84/2.49    ? [X0] : ((v4_ordinal1(X0) <~> ! [X1] : (r2_hidden(k1_ordinal1(X1),X0) | ~r2_hidden(X1,X0) | ~v3_ordinal1(X1))) & v3_ordinal1(X0))),
% 15.84/2.49    inference(flattening,[],[f27])).
% 15.84/2.49  
% 15.84/2.49  fof(f48,plain,(
% 15.84/2.49    ? [X0] : (((? [X1] : (~r2_hidden(k1_ordinal1(X1),X0) & r2_hidden(X1,X0) & v3_ordinal1(X1)) | ~v4_ordinal1(X0)) & (! [X1] : (r2_hidden(k1_ordinal1(X1),X0) | ~r2_hidden(X1,X0) | ~v3_ordinal1(X1)) | v4_ordinal1(X0))) & v3_ordinal1(X0))),
% 15.84/2.49    inference(nnf_transformation,[],[f28])).
% 15.84/2.49  
% 15.84/2.49  fof(f49,plain,(
% 15.84/2.49    ? [X0] : ((? [X1] : (~r2_hidden(k1_ordinal1(X1),X0) & r2_hidden(X1,X0) & v3_ordinal1(X1)) | ~v4_ordinal1(X0)) & (! [X1] : (r2_hidden(k1_ordinal1(X1),X0) | ~r2_hidden(X1,X0) | ~v3_ordinal1(X1)) | v4_ordinal1(X0)) & v3_ordinal1(X0))),
% 15.84/2.49    inference(flattening,[],[f48])).
% 15.84/2.49  
% 15.84/2.49  fof(f50,plain,(
% 15.84/2.49    ? [X0] : ((? [X1] : (~r2_hidden(k1_ordinal1(X1),X0) & r2_hidden(X1,X0) & v3_ordinal1(X1)) | ~v4_ordinal1(X0)) & (! [X2] : (r2_hidden(k1_ordinal1(X2),X0) | ~r2_hidden(X2,X0) | ~v3_ordinal1(X2)) | v4_ordinal1(X0)) & v3_ordinal1(X0))),
% 15.84/2.49    inference(rectify,[],[f49])).
% 15.84/2.49  
% 15.84/2.49  fof(f52,plain,(
% 15.84/2.49    ( ! [X0] : (? [X1] : (~r2_hidden(k1_ordinal1(X1),X0) & r2_hidden(X1,X0) & v3_ordinal1(X1)) => (~r2_hidden(k1_ordinal1(sK6),X0) & r2_hidden(sK6,X0) & v3_ordinal1(sK6))) )),
% 15.84/2.49    introduced(choice_axiom,[])).
% 15.84/2.49  
% 15.84/2.49  fof(f51,plain,(
% 15.84/2.49    ? [X0] : ((? [X1] : (~r2_hidden(k1_ordinal1(X1),X0) & r2_hidden(X1,X0) & v3_ordinal1(X1)) | ~v4_ordinal1(X0)) & (! [X2] : (r2_hidden(k1_ordinal1(X2),X0) | ~r2_hidden(X2,X0) | ~v3_ordinal1(X2)) | v4_ordinal1(X0)) & v3_ordinal1(X0)) => ((? [X1] : (~r2_hidden(k1_ordinal1(X1),sK5) & r2_hidden(X1,sK5) & v3_ordinal1(X1)) | ~v4_ordinal1(sK5)) & (! [X2] : (r2_hidden(k1_ordinal1(X2),sK5) | ~r2_hidden(X2,sK5) | ~v3_ordinal1(X2)) | v4_ordinal1(sK5)) & v3_ordinal1(sK5))),
% 15.84/2.49    introduced(choice_axiom,[])).
% 15.84/2.49  
% 15.84/2.49  fof(f53,plain,(
% 15.84/2.49    ((~r2_hidden(k1_ordinal1(sK6),sK5) & r2_hidden(sK6,sK5) & v3_ordinal1(sK6)) | ~v4_ordinal1(sK5)) & (! [X2] : (r2_hidden(k1_ordinal1(X2),sK5) | ~r2_hidden(X2,sK5) | ~v3_ordinal1(X2)) | v4_ordinal1(sK5)) & v3_ordinal1(sK5)),
% 15.84/2.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6])],[f50,f52,f51])).
% 15.84/2.49  
% 15.84/2.49  fof(f82,plain,(
% 15.84/2.49    ( ! [X2] : (r2_hidden(k1_ordinal1(X2),sK5) | ~r2_hidden(X2,sK5) | ~v3_ordinal1(X2) | v4_ordinal1(sK5)) )),
% 15.84/2.49    inference(cnf_transformation,[],[f53])).
% 15.84/2.49  
% 15.84/2.49  fof(f94,plain,(
% 15.84/2.49    ( ! [X2] : (r2_hidden(k2_xboole_0(X2,k1_tarski(X2)),sK5) | ~r2_hidden(X2,sK5) | ~v3_ordinal1(X2) | v4_ordinal1(sK5)) )),
% 15.84/2.49    inference(definition_unfolding,[],[f82,f63])).
% 15.84/2.49  
% 15.84/2.49  fof(f59,plain,(
% 15.84/2.49    ( ! [X6,X0,X5,X1] : (r2_hidden(X5,X1) | ~r2_hidden(X6,X0) | ~r2_hidden(X5,X6) | k3_tarski(X0) != X1) )),
% 15.84/2.49    inference(cnf_transformation,[],[f38])).
% 15.84/2.49  
% 15.84/2.49  fof(f95,plain,(
% 15.84/2.49    ( ! [X6,X0,X5] : (r2_hidden(X5,k3_tarski(X0)) | ~r2_hidden(X6,X0) | ~r2_hidden(X5,X6)) )),
% 15.84/2.49    inference(equality_resolution,[],[f59])).
% 15.84/2.49  
% 15.84/2.49  fof(f6,axiom,(
% 15.84/2.49    ! [X0,X1] : ((v3_ordinal1(X1) & v3_ordinal1(X0)) => (r1_ordinal1(X0,X1) <=> r1_tarski(X0,X1)))),
% 15.84/2.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.84/2.49  
% 15.84/2.49  fof(f18,plain,(
% 15.84/2.49    ! [X0,X1] : ((r1_ordinal1(X0,X1) <=> r1_tarski(X0,X1)) | (~v3_ordinal1(X1) | ~v3_ordinal1(X0)))),
% 15.84/2.49    inference(ennf_transformation,[],[f6])).
% 15.84/2.49  
% 15.84/2.49  fof(f19,plain,(
% 15.84/2.49    ! [X0,X1] : ((r1_ordinal1(X0,X1) <=> r1_tarski(X0,X1)) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0))),
% 15.84/2.49    inference(flattening,[],[f18])).
% 15.84/2.49  
% 15.84/2.49  fof(f40,plain,(
% 15.84/2.49    ! [X0,X1] : (((r1_ordinal1(X0,X1) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~r1_ordinal1(X0,X1))) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0))),
% 15.84/2.49    inference(nnf_transformation,[],[f19])).
% 15.84/2.49  
% 15.84/2.49  fof(f66,plain,(
% 15.84/2.49    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r1_ordinal1(X0,X1) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0)) )),
% 15.84/2.49    inference(cnf_transformation,[],[f40])).
% 15.84/2.49  
% 15.84/2.49  fof(f13,axiom,(
% 15.84/2.49    ! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => (r2_hidden(X0,X1) <=> r1_ordinal1(k1_ordinal1(X0),X1))))),
% 15.84/2.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.84/2.49  
% 15.84/2.49  fof(f25,plain,(
% 15.84/2.49    ! [X0] : (! [X1] : ((r2_hidden(X0,X1) <=> r1_ordinal1(k1_ordinal1(X0),X1)) | ~v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 15.84/2.49    inference(ennf_transformation,[],[f13])).
% 15.84/2.49  
% 15.84/2.49  fof(f47,plain,(
% 15.84/2.49    ! [X0] : (! [X1] : (((r2_hidden(X0,X1) | ~r1_ordinal1(k1_ordinal1(X0),X1)) & (r1_ordinal1(k1_ordinal1(X0),X1) | ~r2_hidden(X0,X1))) | ~v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 15.84/2.49    inference(nnf_transformation,[],[f25])).
% 15.84/2.49  
% 15.84/2.49  fof(f78,plain,(
% 15.84/2.49    ( ! [X0,X1] : (r1_ordinal1(k1_ordinal1(X0),X1) | ~r2_hidden(X0,X1) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0)) )),
% 15.84/2.49    inference(cnf_transformation,[],[f47])).
% 15.84/2.49  
% 15.84/2.49  fof(f92,plain,(
% 15.84/2.49    ( ! [X0,X1] : (r1_ordinal1(k2_xboole_0(X0,k1_tarski(X0)),X1) | ~r2_hidden(X0,X1) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0)) )),
% 15.84/2.49    inference(definition_unfolding,[],[f78,f63])).
% 15.84/2.49  
% 15.84/2.49  fof(f10,axiom,(
% 15.84/2.49    ! [X0,X1] : (v3_ordinal1(X1) => (r2_hidden(X0,X1) => v3_ordinal1(X0)))),
% 15.84/2.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.84/2.49  
% 15.84/2.49  fof(f20,plain,(
% 15.84/2.49    ! [X0,X1] : ((v3_ordinal1(X0) | ~r2_hidden(X0,X1)) | ~v3_ordinal1(X1))),
% 15.84/2.49    inference(ennf_transformation,[],[f10])).
% 15.84/2.49  
% 15.84/2.49  fof(f21,plain,(
% 15.84/2.49    ! [X0,X1] : (v3_ordinal1(X0) | ~r2_hidden(X0,X1) | ~v3_ordinal1(X1))),
% 15.84/2.49    inference(flattening,[],[f20])).
% 15.84/2.49  
% 15.84/2.49  fof(f75,plain,(
% 15.84/2.49    ( ! [X0,X1] : (v3_ordinal1(X0) | ~r2_hidden(X0,X1) | ~v3_ordinal1(X1)) )),
% 15.84/2.49    inference(cnf_transformation,[],[f21])).
% 15.84/2.49  
% 15.84/2.49  fof(f12,axiom,(
% 15.84/2.49    ! [X0] : (v3_ordinal1(X0) => v3_ordinal1(k1_ordinal1(X0)))),
% 15.84/2.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.84/2.49  
% 15.84/2.49  fof(f24,plain,(
% 15.84/2.49    ! [X0] : (v3_ordinal1(k1_ordinal1(X0)) | ~v3_ordinal1(X0))),
% 15.84/2.49    inference(ennf_transformation,[],[f12])).
% 15.84/2.49  
% 15.84/2.49  fof(f77,plain,(
% 15.84/2.49    ( ! [X0] : (v3_ordinal1(k1_ordinal1(X0)) | ~v3_ordinal1(X0)) )),
% 15.84/2.49    inference(cnf_transformation,[],[f24])).
% 15.84/2.49  
% 15.84/2.49  fof(f90,plain,(
% 15.84/2.49    ( ! [X0] : (v3_ordinal1(k2_xboole_0(X0,k1_tarski(X0))) | ~v3_ordinal1(X0)) )),
% 15.84/2.49    inference(definition_unfolding,[],[f77,f63])).
% 15.84/2.49  
% 15.84/2.49  fof(f14,axiom,(
% 15.84/2.49    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 15.84/2.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.84/2.49  
% 15.84/2.49  fof(f26,plain,(
% 15.84/2.49    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 15.84/2.49    inference(ennf_transformation,[],[f14])).
% 15.84/2.49  
% 15.84/2.49  fof(f80,plain,(
% 15.84/2.49    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1)) )),
% 15.84/2.49    inference(cnf_transformation,[],[f26])).
% 15.84/2.49  
% 15.84/2.49  fof(f5,axiom,(
% 15.84/2.49    ! [X0] : (v4_ordinal1(X0) <=> k3_tarski(X0) = X0)),
% 15.84/2.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.84/2.49  
% 15.84/2.49  fof(f39,plain,(
% 15.84/2.49    ! [X0] : ((v4_ordinal1(X0) | k3_tarski(X0) != X0) & (k3_tarski(X0) = X0 | ~v4_ordinal1(X0)))),
% 15.84/2.49    inference(nnf_transformation,[],[f5])).
% 15.84/2.49  
% 15.84/2.49  fof(f64,plain,(
% 15.84/2.49    ( ! [X0] : (k3_tarski(X0) = X0 | ~v4_ordinal1(X0)) )),
% 15.84/2.49    inference(cnf_transformation,[],[f39])).
% 15.84/2.49  
% 15.84/2.49  fof(f65,plain,(
% 15.84/2.49    ( ! [X0] : (v4_ordinal1(X0) | k3_tarski(X0) != X0) )),
% 15.84/2.49    inference(cnf_transformation,[],[f39])).
% 15.84/2.49  
% 15.84/2.49  fof(f73,plain,(
% 15.84/2.49    ( ! [X0,X1] : (r2_hidden(X0,k1_ordinal1(X1)) | ~r2_hidden(X0,X1)) )),
% 15.84/2.49    inference(cnf_transformation,[],[f46])).
% 15.84/2.49  
% 15.84/2.49  fof(f88,plain,(
% 15.84/2.49    ( ! [X0,X1] : (r2_hidden(X0,k2_xboole_0(X1,k1_tarski(X1))) | ~r2_hidden(X0,X1)) )),
% 15.84/2.49    inference(definition_unfolding,[],[f73,f63])).
% 15.84/2.49  
% 15.84/2.49  fof(f61,plain,(
% 15.84/2.49    ( ! [X0,X1] : (k3_tarski(X0) = X1 | r2_hidden(sK2(X0,X1),X0) | r2_hidden(sK1(X0,X1),X1)) )),
% 15.84/2.49    inference(cnf_transformation,[],[f38])).
% 15.84/2.49  
% 15.84/2.49  fof(f81,plain,(
% 15.84/2.49    v3_ordinal1(sK5)),
% 15.84/2.49    inference(cnf_transformation,[],[f53])).
% 15.84/2.49  
% 15.84/2.49  fof(f60,plain,(
% 15.84/2.49    ( ! [X0,X1] : (k3_tarski(X0) = X1 | r2_hidden(sK1(X0,X1),sK2(X0,X1)) | r2_hidden(sK1(X0,X1),X1)) )),
% 15.84/2.49    inference(cnf_transformation,[],[f38])).
% 15.84/2.49  
% 15.84/2.49  fof(f1,axiom,(
% 15.84/2.49    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 15.84/2.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.84/2.49  
% 15.84/2.49  fof(f17,plain,(
% 15.84/2.49    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 15.84/2.49    inference(ennf_transformation,[],[f1])).
% 15.84/2.49  
% 15.84/2.49  fof(f29,plain,(
% 15.84/2.49    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 15.84/2.49    inference(nnf_transformation,[],[f17])).
% 15.84/2.49  
% 15.84/2.49  fof(f30,plain,(
% 15.84/2.49    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 15.84/2.49    inference(rectify,[],[f29])).
% 15.84/2.49  
% 15.84/2.49  fof(f31,plain,(
% 15.84/2.49    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 15.84/2.49    introduced(choice_axiom,[])).
% 15.84/2.49  
% 15.84/2.49  fof(f32,plain,(
% 15.84/2.49    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 15.84/2.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f30,f31])).
% 15.84/2.49  
% 15.84/2.49  fof(f54,plain,(
% 15.84/2.49    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,X1)) )),
% 15.84/2.49    inference(cnf_transformation,[],[f32])).
% 15.84/2.49  
% 15.84/2.49  fof(f62,plain,(
% 15.84/2.49    ( ! [X0,X3,X1] : (k3_tarski(X0) = X1 | ~r2_hidden(X3,X0) | ~r2_hidden(sK1(X0,X1),X3) | ~r2_hidden(sK1(X0,X1),X1)) )),
% 15.84/2.49    inference(cnf_transformation,[],[f38])).
% 15.84/2.49  
% 15.84/2.49  fof(f11,axiom,(
% 15.84/2.49    ! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => ~(~r2_hidden(X1,X0) & X0 != X1 & ~r2_hidden(X0,X1))))),
% 15.84/2.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.84/2.49  
% 15.84/2.49  fof(f22,plain,(
% 15.84/2.49    ! [X0] : (! [X1] : ((r2_hidden(X1,X0) | X0 = X1 | r2_hidden(X0,X1)) | ~v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 15.84/2.49    inference(ennf_transformation,[],[f11])).
% 15.84/2.49  
% 15.84/2.49  fof(f23,plain,(
% 15.84/2.49    ! [X0] : (! [X1] : (r2_hidden(X1,X0) | X0 = X1 | r2_hidden(X0,X1) | ~v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 15.84/2.49    inference(flattening,[],[f22])).
% 15.84/2.49  
% 15.84/2.49  fof(f76,plain,(
% 15.84/2.49    ( ! [X0,X1] : (r2_hidden(X1,X0) | X0 = X1 | r2_hidden(X0,X1) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0)) )),
% 15.84/2.49    inference(cnf_transformation,[],[f23])).
% 15.84/2.49  
% 15.84/2.49  fof(f85,plain,(
% 15.84/2.49    ~r2_hidden(k1_ordinal1(sK6),sK5) | ~v4_ordinal1(sK5)),
% 15.84/2.49    inference(cnf_transformation,[],[f53])).
% 15.84/2.49  
% 15.84/2.49  fof(f93,plain,(
% 15.84/2.49    ~r2_hidden(k2_xboole_0(sK6,k1_tarski(sK6)),sK5) | ~v4_ordinal1(sK5)),
% 15.84/2.49    inference(definition_unfolding,[],[f85,f63])).
% 15.84/2.49  
% 15.84/2.49  fof(f72,plain,(
% 15.84/2.49    ( ! [X0,X1] : (X0 = X1 | r2_hidden(X0,X1) | ~r2_hidden(X0,k1_ordinal1(X1))) )),
% 15.84/2.49    inference(cnf_transformation,[],[f46])).
% 15.84/2.49  
% 15.84/2.49  fof(f89,plain,(
% 15.84/2.49    ( ! [X0,X1] : (X0 = X1 | r2_hidden(X0,X1) | ~r2_hidden(X0,k2_xboole_0(X1,k1_tarski(X1)))) )),
% 15.84/2.49    inference(definition_unfolding,[],[f72,f63])).
% 15.84/2.49  
% 15.84/2.49  fof(f83,plain,(
% 15.84/2.49    v3_ordinal1(sK6) | ~v4_ordinal1(sK5)),
% 15.84/2.49    inference(cnf_transformation,[],[f53])).
% 15.84/2.49  
% 15.84/2.49  fof(f84,plain,(
% 15.84/2.49    r2_hidden(sK6,sK5) | ~v4_ordinal1(sK5)),
% 15.84/2.49    inference(cnf_transformation,[],[f53])).
% 15.84/2.49  
% 15.84/2.49  fof(f58,plain,(
% 15.84/2.49    ( ! [X0,X5,X1] : (r2_hidden(sK3(X0,X5),X0) | ~r2_hidden(X5,X1) | k3_tarski(X0) != X1) )),
% 15.84/2.49    inference(cnf_transformation,[],[f38])).
% 15.84/2.49  
% 15.84/2.49  fof(f96,plain,(
% 15.84/2.49    ( ! [X0,X5] : (r2_hidden(sK3(X0,X5),X0) | ~r2_hidden(X5,k3_tarski(X0))) )),
% 15.84/2.49    inference(equality_resolution,[],[f58])).
% 15.84/2.49  
% 15.84/2.49  fof(f55,plain,(
% 15.84/2.49    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK0(X0,X1),X0)) )),
% 15.84/2.49    inference(cnf_transformation,[],[f32])).
% 15.84/2.49  
% 15.84/2.49  fof(f56,plain,(
% 15.84/2.49    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r2_hidden(sK0(X0,X1),X1)) )),
% 15.84/2.49    inference(cnf_transformation,[],[f32])).
% 15.84/2.49  
% 15.84/2.49  cnf(c_8,plain,
% 15.84/2.49      ( r2_hidden(X0,sK3(X1,X0)) | ~ r2_hidden(X0,k3_tarski(X1)) ),
% 15.84/2.49      inference(cnf_transformation,[],[f97]) ).
% 15.84/2.49  
% 15.84/2.49  cnf(c_1885,plain,
% 15.84/2.49      ( r2_hidden(X0,sK3(X1,X0)) = iProver_top
% 15.84/2.49      | r2_hidden(X0,k3_tarski(X1)) != iProver_top ),
% 15.84/2.49      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 15.84/2.49  
% 15.84/2.49  cnf(c_17,plain,
% 15.84/2.49      ( r2_hidden(X0,k2_xboole_0(X0,k1_tarski(X0))) ),
% 15.84/2.49      inference(cnf_transformation,[],[f98]) ).
% 15.84/2.49  
% 15.84/2.49  cnf(c_1879,plain,
% 15.84/2.49      ( r2_hidden(X0,k2_xboole_0(X0,k1_tarski(X0))) = iProver_top ),
% 15.84/2.49      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 15.84/2.49  
% 15.84/2.49  cnf(c_29,negated_conjecture,
% 15.84/2.49      ( ~ r2_hidden(X0,sK5)
% 15.84/2.49      | r2_hidden(k2_xboole_0(X0,k1_tarski(X0)),sK5)
% 15.84/2.49      | ~ v3_ordinal1(X0)
% 15.84/2.49      | v4_ordinal1(sK5) ),
% 15.84/2.49      inference(cnf_transformation,[],[f94]) ).
% 15.84/2.49  
% 15.84/2.49  cnf(c_1869,plain,
% 15.84/2.49      ( r2_hidden(X0,sK5) != iProver_top
% 15.84/2.49      | r2_hidden(k2_xboole_0(X0,k1_tarski(X0)),sK5) = iProver_top
% 15.84/2.49      | v3_ordinal1(X0) != iProver_top
% 15.84/2.49      | v4_ordinal1(sK5) = iProver_top ),
% 15.84/2.49      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 15.84/2.49  
% 15.84/2.49  cnf(c_6,plain,
% 15.84/2.49      ( ~ r2_hidden(X0,X1)
% 15.84/2.49      | ~ r2_hidden(X2,X0)
% 15.84/2.49      | r2_hidden(X2,k3_tarski(X1)) ),
% 15.84/2.49      inference(cnf_transformation,[],[f95]) ).
% 15.84/2.49  
% 15.84/2.49  cnf(c_1887,plain,
% 15.84/2.49      ( r2_hidden(X0,X1) != iProver_top
% 15.84/2.49      | r2_hidden(X2,X0) != iProver_top
% 15.84/2.49      | r2_hidden(X2,k3_tarski(X1)) = iProver_top ),
% 15.84/2.49      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 15.84/2.49  
% 15.84/2.49  cnf(c_5182,plain,
% 15.84/2.49      ( r2_hidden(X0,k2_xboole_0(X1,k1_tarski(X1))) != iProver_top
% 15.84/2.49      | r2_hidden(X0,k3_tarski(sK5)) = iProver_top
% 15.84/2.49      | r2_hidden(X1,sK5) != iProver_top
% 15.84/2.49      | v3_ordinal1(X1) != iProver_top
% 15.84/2.49      | v4_ordinal1(sK5) = iProver_top ),
% 15.84/2.49      inference(superposition,[status(thm)],[c_1869,c_1887]) ).
% 15.84/2.49  
% 15.84/2.49  cnf(c_5944,plain,
% 15.84/2.49      ( r2_hidden(X0,k3_tarski(sK5)) = iProver_top
% 15.84/2.49      | r2_hidden(X0,sK5) != iProver_top
% 15.84/2.49      | v3_ordinal1(X0) != iProver_top
% 15.84/2.49      | v4_ordinal1(sK5) = iProver_top ),
% 15.84/2.49      inference(superposition,[status(thm)],[c_1879,c_5182]) ).
% 15.84/2.49  
% 15.84/2.49  cnf(c_12,plain,
% 15.84/2.49      ( ~ r1_ordinal1(X0,X1)
% 15.84/2.49      | r1_tarski(X0,X1)
% 15.84/2.49      | ~ v3_ordinal1(X1)
% 15.84/2.49      | ~ v3_ordinal1(X0) ),
% 15.84/2.49      inference(cnf_transformation,[],[f66]) ).
% 15.84/2.49  
% 15.84/2.49  cnf(c_24,plain,
% 15.84/2.49      ( r1_ordinal1(k2_xboole_0(X0,k1_tarski(X0)),X1)
% 15.84/2.49      | ~ r2_hidden(X0,X1)
% 15.84/2.49      | ~ v3_ordinal1(X1)
% 15.84/2.49      | ~ v3_ordinal1(X0) ),
% 15.84/2.49      inference(cnf_transformation,[],[f92]) ).
% 15.84/2.49  
% 15.84/2.49  cnf(c_20,plain,
% 15.84/2.49      ( ~ r2_hidden(X0,X1) | ~ v3_ordinal1(X1) | v3_ordinal1(X0) ),
% 15.84/2.49      inference(cnf_transformation,[],[f75]) ).
% 15.84/2.49  
% 15.84/2.49  cnf(c_177,plain,
% 15.84/2.49      ( ~ v3_ordinal1(X1)
% 15.84/2.49      | ~ r2_hidden(X0,X1)
% 15.84/2.49      | r1_ordinal1(k2_xboole_0(X0,k1_tarski(X0)),X1) ),
% 15.84/2.49      inference(global_propositional_subsumption,
% 15.84/2.49                [status(thm)],
% 15.84/2.49                [c_24,c_20]) ).
% 15.84/2.49  
% 15.84/2.49  cnf(c_178,plain,
% 15.84/2.49      ( r1_ordinal1(k2_xboole_0(X0,k1_tarski(X0)),X1)
% 15.84/2.49      | ~ r2_hidden(X0,X1)
% 15.84/2.49      | ~ v3_ordinal1(X1) ),
% 15.84/2.49      inference(renaming,[status(thm)],[c_177]) ).
% 15.84/2.49  
% 15.84/2.49  cnf(c_428,plain,
% 15.84/2.49      ( ~ r2_hidden(X0,X1)
% 15.84/2.49      | r1_tarski(X2,X3)
% 15.84/2.49      | ~ v3_ordinal1(X3)
% 15.84/2.49      | ~ v3_ordinal1(X2)
% 15.84/2.49      | ~ v3_ordinal1(X1)
% 15.84/2.49      | X1 != X3
% 15.84/2.49      | k2_xboole_0(X0,k1_tarski(X0)) != X2 ),
% 15.84/2.49      inference(resolution_lifted,[status(thm)],[c_12,c_178]) ).
% 15.84/2.49  
% 15.84/2.49  cnf(c_429,plain,
% 15.84/2.49      ( ~ r2_hidden(X0,X1)
% 15.84/2.49      | r1_tarski(k2_xboole_0(X0,k1_tarski(X0)),X1)
% 15.84/2.49      | ~ v3_ordinal1(X1)
% 15.84/2.49      | ~ v3_ordinal1(k2_xboole_0(X0,k1_tarski(X0))) ),
% 15.84/2.49      inference(unflattening,[status(thm)],[c_428]) ).
% 15.84/2.49  
% 15.84/2.49  cnf(c_22,plain,
% 15.84/2.49      ( ~ v3_ordinal1(X0) | v3_ordinal1(k2_xboole_0(X0,k1_tarski(X0))) ),
% 15.84/2.49      inference(cnf_transformation,[],[f90]) ).
% 15.84/2.49  
% 15.84/2.49  cnf(c_433,plain,
% 15.84/2.49      ( ~ v3_ordinal1(X1)
% 15.84/2.49      | r1_tarski(k2_xboole_0(X0,k1_tarski(X0)),X1)
% 15.84/2.49      | ~ r2_hidden(X0,X1) ),
% 15.84/2.49      inference(global_propositional_subsumption,
% 15.84/2.49                [status(thm)],
% 15.84/2.49                [c_429,c_22,c_20]) ).
% 15.84/2.49  
% 15.84/2.49  cnf(c_434,plain,
% 15.84/2.49      ( ~ r2_hidden(X0,X1)
% 15.84/2.49      | r1_tarski(k2_xboole_0(X0,k1_tarski(X0)),X1)
% 15.84/2.49      | ~ v3_ordinal1(X1) ),
% 15.84/2.49      inference(renaming,[status(thm)],[c_433]) ).
% 15.84/2.49  
% 15.84/2.49  cnf(c_1866,plain,
% 15.84/2.49      ( r2_hidden(X0,X1) != iProver_top
% 15.84/2.49      | r1_tarski(k2_xboole_0(X0,k1_tarski(X0)),X1) = iProver_top
% 15.84/2.49      | v3_ordinal1(X1) != iProver_top ),
% 15.84/2.49      inference(predicate_to_equality,[status(thm)],[c_434]) ).
% 15.84/2.49  
% 15.84/2.49  cnf(c_25,plain,
% 15.84/2.49      ( ~ r2_hidden(X0,X1) | ~ r1_tarski(X1,X0) ),
% 15.84/2.49      inference(cnf_transformation,[],[f80]) ).
% 15.84/2.49  
% 15.84/2.49  cnf(c_1873,plain,
% 15.84/2.49      ( r2_hidden(X0,X1) != iProver_top
% 15.84/2.49      | r1_tarski(X1,X0) != iProver_top ),
% 15.84/2.49      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 15.84/2.49  
% 15.84/2.49  cnf(c_2603,plain,
% 15.84/2.49      ( r1_tarski(k2_xboole_0(X0,k1_tarski(X0)),X0) != iProver_top ),
% 15.84/2.49      inference(superposition,[status(thm)],[c_1879,c_1873]) ).
% 15.84/2.49  
% 15.84/2.49  cnf(c_3201,plain,
% 15.84/2.49      ( r2_hidden(X0,X0) != iProver_top
% 15.84/2.49      | v3_ordinal1(X0) != iProver_top ),
% 15.84/2.49      inference(superposition,[status(thm)],[c_1866,c_2603]) ).
% 15.84/2.49  
% 15.84/2.49  cnf(c_10964,plain,
% 15.84/2.49      ( r2_hidden(k3_tarski(sK5),sK5) != iProver_top
% 15.84/2.49      | v3_ordinal1(k3_tarski(sK5)) != iProver_top
% 15.84/2.49      | v4_ordinal1(sK5) = iProver_top ),
% 15.84/2.49      inference(superposition,[status(thm)],[c_5944,c_3201]) ).
% 15.84/2.49  
% 15.84/2.49  cnf(c_10,plain,
% 15.84/2.49      ( ~ v4_ordinal1(X0) | k3_tarski(X0) = X0 ),
% 15.84/2.49      inference(cnf_transformation,[],[f64]) ).
% 15.84/2.49  
% 15.84/2.49  cnf(c_78,plain,
% 15.84/2.49      ( ~ v4_ordinal1(sK5) | k3_tarski(sK5) = sK5 ),
% 15.84/2.49      inference(instantiation,[status(thm)],[c_10]) ).
% 15.84/2.49  
% 15.84/2.49  cnf(c_9,plain,
% 15.84/2.49      ( v4_ordinal1(X0) | k3_tarski(X0) != X0 ),
% 15.84/2.49      inference(cnf_transformation,[],[f65]) ).
% 15.84/2.49  
% 15.84/2.49  cnf(c_80,plain,
% 15.84/2.49      ( k3_tarski(X0) != X0 | v4_ordinal1(X0) = iProver_top ),
% 15.84/2.49      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 15.84/2.49  
% 15.84/2.49  cnf(c_82,plain,
% 15.84/2.49      ( k3_tarski(sK5) != sK5 | v4_ordinal1(sK5) = iProver_top ),
% 15.84/2.49      inference(instantiation,[status(thm)],[c_80]) ).
% 15.84/2.49  
% 15.84/2.49  cnf(c_18,plain,
% 15.84/2.49      ( ~ r2_hidden(X0,X1)
% 15.84/2.49      | r2_hidden(X0,k2_xboole_0(X1,k1_tarski(X1))) ),
% 15.84/2.49      inference(cnf_transformation,[],[f88]) ).
% 15.84/2.49  
% 15.84/2.49  cnf(c_3509,plain,
% 15.84/2.49      ( ~ r2_hidden(X0,X1)
% 15.84/2.49      | r2_hidden(X0,k3_tarski(X2))
% 15.84/2.49      | ~ r2_hidden(k2_xboole_0(X1,k1_tarski(X1)),X2) ),
% 15.84/2.49      inference(resolution,[status(thm)],[c_6,c_18]) ).
% 15.84/2.49  
% 15.84/2.49  cnf(c_3505,plain,
% 15.84/2.49      ( r2_hidden(X0,k3_tarski(X1))
% 15.84/2.49      | ~ r2_hidden(k2_xboole_0(X0,k1_tarski(X0)),X1) ),
% 15.84/2.49      inference(resolution,[status(thm)],[c_6,c_17]) ).
% 15.84/2.49  
% 15.84/2.49  cnf(c_9528,plain,
% 15.84/2.49      ( r2_hidden(X0,k3_tarski(sK5))
% 15.84/2.49      | ~ r2_hidden(X0,sK5)
% 15.84/2.49      | ~ v3_ordinal1(X0)
% 15.84/2.49      | v4_ordinal1(sK5) ),
% 15.84/2.49      inference(resolution,[status(thm)],[c_3505,c_29]) ).
% 15.84/2.49  
% 15.84/2.49  cnf(c_17185,plain,
% 15.84/2.49      ( ~ r2_hidden(X0,X1)
% 15.84/2.49      | r2_hidden(X0,k3_tarski(k3_tarski(sK5)))
% 15.84/2.49      | ~ r2_hidden(k2_xboole_0(X1,k1_tarski(X1)),sK5)
% 15.84/2.49      | ~ v3_ordinal1(k2_xboole_0(X1,k1_tarski(X1)))
% 15.84/2.49      | v4_ordinal1(sK5) ),
% 15.84/2.49      inference(resolution,[status(thm)],[c_3509,c_9528]) ).
% 15.84/2.49  
% 15.84/2.49  cnf(c_18321,plain,
% 15.84/2.49      ( ~ r2_hidden(X0,X1)
% 15.84/2.49      | r2_hidden(X0,k3_tarski(k3_tarski(sK5)))
% 15.84/2.49      | ~ r2_hidden(X1,sK5)
% 15.84/2.49      | ~ v3_ordinal1(X1)
% 15.84/2.49      | ~ v3_ordinal1(k2_xboole_0(X1,k1_tarski(X1)))
% 15.84/2.49      | v4_ordinal1(sK5) ),
% 15.84/2.49      inference(resolution,[status(thm)],[c_17185,c_29]) ).
% 15.84/2.49  
% 15.84/2.49  cnf(c_10959,plain,
% 15.84/2.49      ( r2_hidden(X0,X1) != iProver_top
% 15.84/2.49      | r2_hidden(X0,k3_tarski(k3_tarski(sK5))) = iProver_top
% 15.84/2.49      | r2_hidden(X1,sK5) != iProver_top
% 15.84/2.49      | v3_ordinal1(X1) != iProver_top
% 15.84/2.49      | v4_ordinal1(sK5) = iProver_top ),
% 15.84/2.49      inference(superposition,[status(thm)],[c_5944,c_1887]) ).
% 15.84/2.49  
% 15.84/2.49  cnf(c_11060,plain,
% 15.84/2.49      ( ~ r2_hidden(X0,X1)
% 15.84/2.49      | r2_hidden(X0,k3_tarski(k3_tarski(sK5)))
% 15.84/2.49      | ~ r2_hidden(X1,sK5)
% 15.84/2.49      | ~ v3_ordinal1(X1)
% 15.84/2.49      | v4_ordinal1(sK5) ),
% 15.84/2.49      inference(predicate_to_equality_rev,[status(thm)],[c_10959]) ).
% 15.84/2.49  
% 15.84/2.49  cnf(c_18453,plain,
% 15.84/2.49      ( ~ v3_ordinal1(X1)
% 15.84/2.49      | ~ r2_hidden(X1,sK5)
% 15.84/2.49      | r2_hidden(X0,k3_tarski(k3_tarski(sK5)))
% 15.84/2.49      | ~ r2_hidden(X0,X1)
% 15.84/2.49      | v4_ordinal1(sK5) ),
% 15.84/2.49      inference(global_propositional_subsumption,
% 15.84/2.49                [status(thm)],
% 15.84/2.49                [c_18321,c_11060]) ).
% 15.84/2.49  
% 15.84/2.49  cnf(c_18454,plain,
% 15.84/2.49      ( ~ r2_hidden(X0,X1)
% 15.84/2.49      | r2_hidden(X0,k3_tarski(k3_tarski(sK5)))
% 15.84/2.49      | ~ r2_hidden(X1,sK5)
% 15.84/2.49      | ~ v3_ordinal1(X1)
% 15.84/2.49      | v4_ordinal1(sK5) ),
% 15.84/2.49      inference(renaming,[status(thm)],[c_18453]) ).
% 15.84/2.49  
% 15.84/2.49  cnf(c_4,plain,
% 15.84/2.49      ( r2_hidden(sK2(X0,X1),X0)
% 15.84/2.49      | r2_hidden(sK1(X0,X1),X1)
% 15.84/2.49      | k3_tarski(X0) = X1 ),
% 15.84/2.49      inference(cnf_transformation,[],[f61]) ).
% 15.84/2.49  
% 15.84/2.49  cnf(c_3857,plain,
% 15.84/2.49      ( r2_hidden(sK2(X0,X0),X0)
% 15.84/2.49      | r2_hidden(sK1(X0,X0),X0)
% 15.84/2.49      | v4_ordinal1(X0) ),
% 15.84/2.49      inference(resolution,[status(thm)],[c_4,c_9]) ).
% 15.84/2.49  
% 15.84/2.49  cnf(c_18501,plain,
% 15.84/2.49      ( ~ r2_hidden(X0,sK2(sK5,sK5))
% 15.84/2.49      | r2_hidden(X0,k3_tarski(k3_tarski(sK5)))
% 15.84/2.49      | r2_hidden(sK1(sK5,sK5),sK5)
% 15.84/2.49      | ~ v3_ordinal1(sK2(sK5,sK5))
% 15.84/2.49      | v4_ordinal1(sK5) ),
% 15.84/2.49      inference(resolution,[status(thm)],[c_18454,c_3857]) ).
% 15.84/2.49  
% 15.84/2.49  cnf(c_30,negated_conjecture,
% 15.84/2.49      ( v3_ordinal1(sK5) ),
% 15.84/2.49      inference(cnf_transformation,[],[f81]) ).
% 15.84/2.49  
% 15.84/2.49  cnf(c_81,plain,
% 15.84/2.49      ( v4_ordinal1(sK5) | k3_tarski(sK5) != sK5 ),
% 15.84/2.49      inference(instantiation,[status(thm)],[c_9]) ).
% 15.84/2.49  
% 15.84/2.49  cnf(c_5,plain,
% 15.84/2.49      ( r2_hidden(sK1(X0,X1),X1)
% 15.84/2.49      | r2_hidden(sK1(X0,X1),sK2(X0,X1))
% 15.84/2.49      | k3_tarski(X0) = X1 ),
% 15.84/2.49      inference(cnf_transformation,[],[f60]) ).
% 15.84/2.49  
% 15.84/2.49  cnf(c_93,plain,
% 15.84/2.49      ( r2_hidden(sK1(sK5,sK5),sK2(sK5,sK5))
% 15.84/2.49      | r2_hidden(sK1(sK5,sK5),sK5)
% 15.84/2.49      | k3_tarski(sK5) = sK5 ),
% 15.84/2.49      inference(instantiation,[status(thm)],[c_5]) ).
% 15.84/2.49  
% 15.84/2.49  cnf(c_2469,plain,
% 15.84/2.49      ( r2_hidden(sK1(X0,X1),k2_xboole_0(sK2(X0,X1),k1_tarski(sK2(X0,X1))))
% 15.84/2.49      | ~ r2_hidden(sK1(X0,X1),sK2(X0,X1)) ),
% 15.84/2.49      inference(instantiation,[status(thm)],[c_18]) ).
% 15.84/2.49  
% 15.84/2.49  cnf(c_2481,plain,
% 15.84/2.49      ( r2_hidden(sK1(sK5,sK5),k2_xboole_0(sK2(sK5,sK5),k1_tarski(sK2(sK5,sK5))))
% 15.84/2.49      | ~ r2_hidden(sK1(sK5,sK5),sK2(sK5,sK5)) ),
% 15.84/2.49      inference(instantiation,[status(thm)],[c_2469]) ).
% 15.84/2.49  
% 15.84/2.49  cnf(c_2518,plain,
% 15.84/2.49      ( ~ r2_hidden(sK2(X0,sK5),X0)
% 15.84/2.49      | r1_tarski(k2_xboole_0(sK2(X0,sK5),k1_tarski(sK2(X0,sK5))),X0)
% 15.84/2.49      | ~ v3_ordinal1(X0) ),
% 15.84/2.49      inference(instantiation,[status(thm)],[c_434]) ).
% 15.84/2.49  
% 15.84/2.49  cnf(c_2538,plain,
% 15.84/2.49      ( ~ r2_hidden(sK2(sK5,sK5),sK5)
% 15.84/2.49      | r1_tarski(k2_xboole_0(sK2(sK5,sK5),k1_tarski(sK2(sK5,sK5))),sK5)
% 15.84/2.49      | ~ v3_ordinal1(sK5) ),
% 15.84/2.49      inference(instantiation,[status(thm)],[c_2518]) ).
% 15.84/2.49  
% 15.84/2.49  cnf(c_3859,plain,
% 15.84/2.49      ( r2_hidden(sK2(sK5,sK5),sK5)
% 15.84/2.49      | r2_hidden(sK1(sK5,sK5),sK5)
% 15.84/2.49      | v4_ordinal1(sK5) ),
% 15.84/2.49      inference(instantiation,[status(thm)],[c_3857]) ).
% 15.84/2.49  
% 15.84/2.49  cnf(c_2,plain,
% 15.84/2.49      ( ~ r2_hidden(X0,X1) | r2_hidden(X0,X2) | ~ r1_tarski(X1,X2) ),
% 15.84/2.49      inference(cnf_transformation,[],[f54]) ).
% 15.84/2.49  
% 15.84/2.49  cnf(c_7110,plain,
% 15.84/2.49      ( ~ r2_hidden(sK1(X0,X1),X2)
% 15.84/2.49      | r2_hidden(sK1(X0,X1),X3)
% 15.84/2.49      | ~ r1_tarski(X2,X3) ),
% 15.84/2.49      inference(instantiation,[status(thm)],[c_2]) ).
% 15.84/2.49  
% 15.84/2.49  cnf(c_14931,plain,
% 15.84/2.49      ( r2_hidden(sK1(X0,X1),X2)
% 15.84/2.49      | ~ r2_hidden(sK1(X0,X1),k2_xboole_0(sK2(X0,X1),k1_tarski(sK2(X0,X1))))
% 15.84/2.49      | ~ r1_tarski(k2_xboole_0(sK2(X0,X1),k1_tarski(sK2(X0,X1))),X2) ),
% 15.84/2.49      inference(instantiation,[status(thm)],[c_7110]) ).
% 15.84/2.49  
% 15.84/2.49  cnf(c_14933,plain,
% 15.84/2.49      ( ~ r2_hidden(sK1(sK5,sK5),k2_xboole_0(sK2(sK5,sK5),k1_tarski(sK2(sK5,sK5))))
% 15.84/2.49      | r2_hidden(sK1(sK5,sK5),sK5)
% 15.84/2.49      | ~ r1_tarski(k2_xboole_0(sK2(sK5,sK5),k1_tarski(sK2(sK5,sK5))),sK5) ),
% 15.84/2.49      inference(instantiation,[status(thm)],[c_14931]) ).
% 15.84/2.49  
% 15.84/2.49  cnf(c_18701,plain,
% 15.84/2.49      ( r2_hidden(sK1(sK5,sK5),sK5) | v4_ordinal1(sK5) ),
% 15.84/2.49      inference(global_propositional_subsumption,
% 15.84/2.49                [status(thm)],
% 15.84/2.49                [c_18501,c_30,c_81,c_93,c_2481,c_2538,c_3859,c_14933]) ).
% 15.84/2.49  
% 15.84/2.49  cnf(c_2429,plain,
% 15.84/2.49      ( r2_hidden(k2_xboole_0(sK1(X0,sK5),k1_tarski(sK1(X0,sK5))),sK5)
% 15.84/2.49      | ~ r2_hidden(sK1(X0,sK5),sK5)
% 15.84/2.49      | ~ v3_ordinal1(sK1(X0,sK5))
% 15.84/2.49      | v4_ordinal1(sK5) ),
% 15.84/2.49      inference(instantiation,[status(thm)],[c_29]) ).
% 15.84/2.49  
% 15.84/2.49  cnf(c_2433,plain,
% 15.84/2.49      ( r2_hidden(k2_xboole_0(sK1(sK5,sK5),k1_tarski(sK1(sK5,sK5))),sK5)
% 15.84/2.49      | ~ r2_hidden(sK1(sK5,sK5),sK5)
% 15.84/2.49      | ~ v3_ordinal1(sK1(sK5,sK5))
% 15.84/2.49      | v4_ordinal1(sK5) ),
% 15.84/2.49      inference(instantiation,[status(thm)],[c_2429]) ).
% 15.84/2.49  
% 15.84/2.49  cnf(c_3738,plain,
% 15.84/2.49      ( ~ r2_hidden(sK1(X0,X1),X2)
% 15.84/2.49      | ~ v3_ordinal1(X2)
% 15.84/2.49      | v3_ordinal1(sK1(X0,X1)) ),
% 15.84/2.49      inference(instantiation,[status(thm)],[c_20]) ).
% 15.84/2.49  
% 15.84/2.49  cnf(c_3740,plain,
% 15.84/2.49      ( ~ r2_hidden(sK1(sK5,sK5),sK5)
% 15.84/2.49      | v3_ordinal1(sK1(sK5,sK5))
% 15.84/2.49      | ~ v3_ordinal1(sK5) ),
% 15.84/2.49      inference(instantiation,[status(thm)],[c_3738]) ).
% 15.84/2.49  
% 15.84/2.49  cnf(c_3,plain,
% 15.84/2.49      ( ~ r2_hidden(X0,X1)
% 15.84/2.49      | ~ r2_hidden(sK1(X1,X2),X0)
% 15.84/2.49      | ~ r2_hidden(sK1(X1,X2),X2)
% 15.84/2.49      | k3_tarski(X1) = X2 ),
% 15.84/2.49      inference(cnf_transformation,[],[f62]) ).
% 15.84/2.49  
% 15.84/2.49  cnf(c_4420,plain,
% 15.84/2.49      ( ~ r2_hidden(k2_xboole_0(sK1(X0,sK5),k1_tarski(sK1(X0,sK5))),sK5)
% 15.84/2.49      | ~ r2_hidden(sK1(sK5,X1),X1)
% 15.84/2.49      | ~ r2_hidden(sK1(sK5,X1),k2_xboole_0(sK1(X0,sK5),k1_tarski(sK1(X0,sK5))))
% 15.84/2.49      | k3_tarski(sK5) = X1 ),
% 15.84/2.49      inference(instantiation,[status(thm)],[c_3]) ).
% 15.84/2.49  
% 15.84/2.49  cnf(c_4450,plain,
% 15.84/2.49      ( ~ r2_hidden(k2_xboole_0(sK1(sK5,sK5),k1_tarski(sK1(sK5,sK5))),sK5)
% 15.84/2.49      | ~ r2_hidden(sK1(sK5,sK5),k2_xboole_0(sK1(sK5,sK5),k1_tarski(sK1(sK5,sK5))))
% 15.84/2.49      | ~ r2_hidden(sK1(sK5,sK5),sK5)
% 15.84/2.49      | k3_tarski(sK5) = sK5 ),
% 15.84/2.49      inference(instantiation,[status(thm)],[c_4420]) ).
% 15.84/2.49  
% 15.84/2.49  cnf(c_13762,plain,
% 15.84/2.49      ( r2_hidden(sK1(X0,X1),k2_xboole_0(sK1(X0,X1),k1_tarski(sK1(X0,X1)))) ),
% 15.84/2.49      inference(instantiation,[status(thm)],[c_17]) ).
% 15.84/2.49  
% 15.84/2.49  cnf(c_13768,plain,
% 15.84/2.49      ( r2_hidden(sK1(sK5,sK5),k2_xboole_0(sK1(sK5,sK5),k1_tarski(sK1(sK5,sK5)))) ),
% 15.84/2.49      inference(instantiation,[status(thm)],[c_13762]) ).
% 15.84/2.49  
% 15.84/2.49  cnf(c_18705,plain,
% 15.84/2.49      ( v4_ordinal1(sK5) ),
% 15.84/2.49      inference(global_propositional_subsumption,
% 15.84/2.49                [status(thm)],
% 15.84/2.49                [c_18701,c_30,c_81,c_2433,c_3740,c_4450,c_13768]) ).
% 15.84/2.49  
% 15.84/2.49  cnf(c_18981,plain,
% 15.84/2.49      ( v4_ordinal1(sK5) = iProver_top ),
% 15.84/2.49      inference(global_propositional_subsumption,
% 15.84/2.49                [status(thm)],
% 15.84/2.49                [c_10964,c_30,c_78,c_81,c_82,c_2433,c_3740,c_4450,
% 15.84/2.49                 c_13768,c_18701]) ).
% 15.84/2.49  
% 15.84/2.49  cnf(c_21,plain,
% 15.84/2.49      ( r2_hidden(X0,X1)
% 15.84/2.49      | r2_hidden(X1,X0)
% 15.84/2.49      | ~ v3_ordinal1(X1)
% 15.84/2.49      | ~ v3_ordinal1(X0)
% 15.84/2.49      | X1 = X0 ),
% 15.84/2.49      inference(cnf_transformation,[],[f76]) ).
% 15.84/2.49  
% 15.84/2.49  cnf(c_1875,plain,
% 15.84/2.49      ( X0 = X1
% 15.84/2.49      | r2_hidden(X1,X0) = iProver_top
% 15.84/2.49      | r2_hidden(X0,X1) = iProver_top
% 15.84/2.49      | v3_ordinal1(X1) != iProver_top
% 15.84/2.49      | v3_ordinal1(X0) != iProver_top ),
% 15.84/2.49      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 15.84/2.49  
% 15.84/2.49  cnf(c_26,negated_conjecture,
% 15.84/2.49      ( ~ r2_hidden(k2_xboole_0(sK6,k1_tarski(sK6)),sK5)
% 15.84/2.49      | ~ v4_ordinal1(sK5) ),
% 15.84/2.49      inference(cnf_transformation,[],[f93]) ).
% 15.84/2.49  
% 15.84/2.49  cnf(c_1872,plain,
% 15.84/2.49      ( r2_hidden(k2_xboole_0(sK6,k1_tarski(sK6)),sK5) != iProver_top
% 15.84/2.49      | v4_ordinal1(sK5) != iProver_top ),
% 15.84/2.49      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 15.84/2.49  
% 15.84/2.49  cnf(c_4829,plain,
% 15.84/2.49      ( k2_xboole_0(sK6,k1_tarski(sK6)) = sK5
% 15.84/2.49      | r2_hidden(sK5,k2_xboole_0(sK6,k1_tarski(sK6))) = iProver_top
% 15.84/2.49      | v3_ordinal1(k2_xboole_0(sK6,k1_tarski(sK6))) != iProver_top
% 15.84/2.49      | v3_ordinal1(sK5) != iProver_top
% 15.84/2.49      | v4_ordinal1(sK5) != iProver_top ),
% 15.84/2.49      inference(superposition,[status(thm)],[c_1875,c_1872]) ).
% 15.84/2.49  
% 15.84/2.49  cnf(c_31,plain,
% 15.84/2.49      ( v3_ordinal1(sK5) = iProver_top ),
% 15.84/2.49      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 15.84/2.49  
% 15.84/2.49  cnf(c_6039,plain,
% 15.84/2.49      ( v3_ordinal1(k2_xboole_0(sK6,k1_tarski(sK6))) != iProver_top
% 15.84/2.49      | r2_hidden(sK5,k2_xboole_0(sK6,k1_tarski(sK6))) = iProver_top
% 15.84/2.49      | k2_xboole_0(sK6,k1_tarski(sK6)) = sK5
% 15.84/2.49      | v4_ordinal1(sK5) != iProver_top ),
% 15.84/2.49      inference(global_propositional_subsumption,
% 15.84/2.49                [status(thm)],
% 15.84/2.49                [c_4829,c_31]) ).
% 15.84/2.49  
% 15.84/2.49  cnf(c_6040,plain,
% 15.84/2.49      ( k2_xboole_0(sK6,k1_tarski(sK6)) = sK5
% 15.84/2.49      | r2_hidden(sK5,k2_xboole_0(sK6,k1_tarski(sK6))) = iProver_top
% 15.84/2.49      | v3_ordinal1(k2_xboole_0(sK6,k1_tarski(sK6))) != iProver_top
% 15.84/2.49      | v4_ordinal1(sK5) != iProver_top ),
% 15.84/2.49      inference(renaming,[status(thm)],[c_6039]) ).
% 15.84/2.49  
% 15.84/2.49  cnf(c_19,plain,
% 15.84/2.49      ( r2_hidden(X0,X1)
% 15.84/2.49      | ~ r2_hidden(X0,k2_xboole_0(X1,k1_tarski(X1)))
% 15.84/2.49      | X1 = X0 ),
% 15.84/2.49      inference(cnf_transformation,[],[f89]) ).
% 15.84/2.49  
% 15.84/2.49  cnf(c_1877,plain,
% 15.84/2.49      ( X0 = X1
% 15.84/2.49      | r2_hidden(X1,X0) = iProver_top
% 15.84/2.49      | r2_hidden(X1,k2_xboole_0(X0,k1_tarski(X0))) != iProver_top ),
% 15.84/2.49      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 15.84/2.49  
% 15.84/2.49  cnf(c_6052,plain,
% 15.84/2.49      ( k2_xboole_0(sK6,k1_tarski(sK6)) = sK5
% 15.84/2.49      | sK5 = sK6
% 15.84/2.49      | r2_hidden(sK5,sK6) = iProver_top
% 15.84/2.49      | v3_ordinal1(k2_xboole_0(sK6,k1_tarski(sK6))) != iProver_top
% 15.84/2.49      | v4_ordinal1(sK5) != iProver_top ),
% 15.84/2.49      inference(superposition,[status(thm)],[c_6040,c_1877]) ).
% 15.84/2.49  
% 15.84/2.49  cnf(c_28,negated_conjecture,
% 15.84/2.49      ( v3_ordinal1(sK6) | ~ v4_ordinal1(sK5) ),
% 15.84/2.49      inference(cnf_transformation,[],[f83]) ).
% 15.84/2.49  
% 15.84/2.49  cnf(c_35,plain,
% 15.84/2.49      ( v3_ordinal1(sK6) = iProver_top
% 15.84/2.49      | v4_ordinal1(sK5) != iProver_top ),
% 15.84/2.49      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 15.84/2.49  
% 15.84/2.49  cnf(c_1874,plain,
% 15.84/2.49      ( v3_ordinal1(X0) != iProver_top
% 15.84/2.49      | v3_ordinal1(k2_xboole_0(X0,k1_tarski(X0))) = iProver_top ),
% 15.84/2.49      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 15.84/2.49  
% 15.84/2.49  cnf(c_6050,plain,
% 15.84/2.49      ( k2_xboole_0(sK6,k1_tarski(sK6)) = sK5
% 15.84/2.49      | r1_tarski(k2_xboole_0(sK6,k1_tarski(sK6)),sK5) != iProver_top
% 15.84/2.49      | v3_ordinal1(k2_xboole_0(sK6,k1_tarski(sK6))) != iProver_top
% 15.84/2.49      | v4_ordinal1(sK5) != iProver_top ),
% 15.84/2.49      inference(superposition,[status(thm)],[c_6040,c_1873]) ).
% 15.84/2.49  
% 15.84/2.49  cnf(c_27,negated_conjecture,
% 15.84/2.49      ( r2_hidden(sK6,sK5) | ~ v4_ordinal1(sK5) ),
% 15.84/2.49      inference(cnf_transformation,[],[f84]) ).
% 15.84/2.49  
% 15.84/2.49  cnf(c_36,plain,
% 15.84/2.49      ( r2_hidden(sK6,sK5) = iProver_top
% 15.84/2.49      | v4_ordinal1(sK5) != iProver_top ),
% 15.84/2.49      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 15.84/2.49  
% 15.84/2.49  cnf(c_60,plain,
% 15.84/2.49      ( r2_hidden(X0,k2_xboole_0(X0,k1_tarski(X0))) = iProver_top ),
% 15.84/2.49      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 15.84/2.49  
% 15.84/2.49  cnf(c_62,plain,
% 15.84/2.49      ( r2_hidden(sK5,k2_xboole_0(sK5,k1_tarski(sK5))) = iProver_top ),
% 15.84/2.49      inference(instantiation,[status(thm)],[c_60]) ).
% 15.84/2.49  
% 15.84/2.49  cnf(c_683,plain,
% 15.84/2.49      ( ~ r2_hidden(X0,X1)
% 15.84/2.49      | ~ r2_hidden(X2,X3)
% 15.84/2.49      | ~ v3_ordinal1(X3)
% 15.84/2.49      | X3 != X0
% 15.84/2.49      | k2_xboole_0(X2,k1_tarski(X2)) != X1 ),
% 15.84/2.49      inference(resolution_lifted,[status(thm)],[c_25,c_434]) ).
% 15.84/2.49  
% 15.84/2.49  cnf(c_684,plain,
% 15.84/2.49      ( ~ r2_hidden(X0,X1)
% 15.84/2.49      | ~ r2_hidden(X1,k2_xboole_0(X0,k1_tarski(X0)))
% 15.84/2.49      | ~ v3_ordinal1(X1) ),
% 15.84/2.49      inference(unflattening,[status(thm)],[c_683]) ).
% 15.84/2.49  
% 15.84/2.49  cnf(c_685,plain,
% 15.84/2.49      ( r2_hidden(X0,X1) != iProver_top
% 15.84/2.49      | r2_hidden(X1,k2_xboole_0(X0,k1_tarski(X0))) != iProver_top
% 15.84/2.49      | v3_ordinal1(X1) != iProver_top ),
% 15.84/2.49      inference(predicate_to_equality,[status(thm)],[c_684]) ).
% 15.84/2.49  
% 15.84/2.49  cnf(c_687,plain,
% 15.84/2.49      ( r2_hidden(sK5,k2_xboole_0(sK5,k1_tarski(sK5))) != iProver_top
% 15.84/2.49      | r2_hidden(sK5,sK5) != iProver_top
% 15.84/2.49      | v3_ordinal1(sK5) != iProver_top ),
% 15.84/2.49      inference(instantiation,[status(thm)],[c_685]) ).
% 15.84/2.49  
% 15.84/2.49  cnf(c_2209,plain,
% 15.84/2.49      ( ~ r2_hidden(sK6,sK5)
% 15.84/2.49      | r1_tarski(k2_xboole_0(sK6,k1_tarski(sK6)),sK5)
% 15.84/2.49      | ~ v3_ordinal1(sK5) ),
% 15.84/2.49      inference(instantiation,[status(thm)],[c_434]) ).
% 15.84/2.49  
% 15.84/2.49  cnf(c_2210,plain,
% 15.84/2.49      ( r2_hidden(sK6,sK5) != iProver_top
% 15.84/2.49      | r1_tarski(k2_xboole_0(sK6,k1_tarski(sK6)),sK5) = iProver_top
% 15.84/2.49      | v3_ordinal1(sK5) != iProver_top ),
% 15.84/2.49      inference(predicate_to_equality,[status(thm)],[c_2209]) ).
% 15.84/2.49  
% 15.84/2.49  cnf(c_1891,plain,
% 15.84/2.49      ( r2_hidden(X0,X1) != iProver_top
% 15.84/2.49      | r2_hidden(X0,X2) = iProver_top
% 15.84/2.49      | r1_tarski(X1,X2) != iProver_top ),
% 15.84/2.49      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 15.84/2.49  
% 15.84/2.49  cnf(c_6048,plain,
% 15.84/2.49      ( k2_xboole_0(sK6,k1_tarski(sK6)) = sK5
% 15.84/2.49      | r2_hidden(sK5,X0) = iProver_top
% 15.84/2.49      | r1_tarski(k2_xboole_0(sK6,k1_tarski(sK6)),X0) != iProver_top
% 15.84/2.49      | v3_ordinal1(k2_xboole_0(sK6,k1_tarski(sK6))) != iProver_top
% 15.84/2.49      | v4_ordinal1(sK5) != iProver_top ),
% 15.84/2.49      inference(superposition,[status(thm)],[c_6040,c_1891]) ).
% 15.84/2.49  
% 15.84/2.49  cnf(c_6095,plain,
% 15.84/2.49      ( k2_xboole_0(sK6,k1_tarski(sK6)) = sK5
% 15.84/2.49      | r2_hidden(sK5,sK5) = iProver_top
% 15.84/2.49      | r1_tarski(k2_xboole_0(sK6,k1_tarski(sK6)),sK5) != iProver_top
% 15.84/2.49      | v3_ordinal1(k2_xboole_0(sK6,k1_tarski(sK6))) != iProver_top
% 15.84/2.49      | v4_ordinal1(sK5) != iProver_top ),
% 15.84/2.49      inference(instantiation,[status(thm)],[c_6048]) ).
% 15.84/2.49  
% 15.84/2.49  cnf(c_9938,plain,
% 15.84/2.49      ( k2_xboole_0(sK6,k1_tarski(sK6)) = sK5
% 15.84/2.49      | v3_ordinal1(k2_xboole_0(sK6,k1_tarski(sK6))) != iProver_top
% 15.84/2.49      | v4_ordinal1(sK5) != iProver_top ),
% 15.84/2.49      inference(global_propositional_subsumption,
% 15.84/2.49                [status(thm)],
% 15.84/2.49                [c_6050,c_31,c_36,c_62,c_687,c_2210,c_6095]) ).
% 15.84/2.49  
% 15.84/2.49  cnf(c_9945,plain,
% 15.84/2.49      ( k2_xboole_0(sK6,k1_tarski(sK6)) = sK5
% 15.84/2.49      | v3_ordinal1(sK6) != iProver_top
% 15.84/2.49      | v4_ordinal1(sK5) != iProver_top ),
% 15.84/2.49      inference(superposition,[status(thm)],[c_1874,c_9938]) ).
% 15.84/2.49  
% 15.84/2.49  cnf(c_11281,plain,
% 15.84/2.49      ( k2_xboole_0(sK6,k1_tarski(sK6)) = sK5
% 15.84/2.49      | v4_ordinal1(sK5) != iProver_top ),
% 15.84/2.49      inference(global_propositional_subsumption,
% 15.84/2.49                [status(thm)],
% 15.84/2.49                [c_6052,c_35,c_9945]) ).
% 15.84/2.49  
% 15.84/2.49  cnf(c_18987,plain,
% 15.84/2.49      ( k2_xboole_0(sK6,k1_tarski(sK6)) = sK5 ),
% 15.84/2.49      inference(superposition,[status(thm)],[c_18981,c_11281]) ).
% 15.84/2.49  
% 15.84/2.49  cnf(c_20297,plain,
% 15.84/2.49      ( r2_hidden(sK6,X0) != iProver_top
% 15.84/2.49      | r1_tarski(sK5,X0) = iProver_top
% 15.84/2.49      | v3_ordinal1(X0) != iProver_top ),
% 15.84/2.49      inference(superposition,[status(thm)],[c_18987,c_1866]) ).
% 15.84/2.49  
% 15.84/2.49  cnf(c_71164,plain,
% 15.84/2.49      ( r2_hidden(sK6,k3_tarski(X0)) != iProver_top
% 15.84/2.49      | r1_tarski(sK5,sK3(X0,sK6)) = iProver_top
% 15.84/2.49      | v3_ordinal1(sK3(X0,sK6)) != iProver_top ),
% 15.84/2.49      inference(superposition,[status(thm)],[c_1885,c_20297]) ).
% 15.84/2.49  
% 15.84/2.49  cnf(c_71265,plain,
% 15.84/2.49      ( r2_hidden(sK6,k3_tarski(sK5)) != iProver_top
% 15.84/2.49      | r1_tarski(sK5,sK3(sK5,sK6)) = iProver_top
% 15.84/2.49      | v3_ordinal1(sK3(sK5,sK6)) != iProver_top ),
% 15.84/2.49      inference(instantiation,[status(thm)],[c_71164]) ).
% 15.84/2.49  
% 15.84/2.49  cnf(c_1883,plain,
% 15.84/2.49      ( k3_tarski(X0) = X0 | v4_ordinal1(X0) != iProver_top ),
% 15.84/2.49      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 15.84/2.49  
% 15.84/2.49  cnf(c_18986,plain,
% 15.84/2.49      ( k3_tarski(sK5) = sK5 ),
% 15.84/2.49      inference(superposition,[status(thm)],[c_18981,c_1883]) ).
% 15.84/2.49  
% 15.84/2.49  cnf(c_1871,plain,
% 15.84/2.49      ( r2_hidden(sK6,sK5) = iProver_top
% 15.84/2.49      | v4_ordinal1(sK5) != iProver_top ),
% 15.84/2.49      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 15.84/2.49  
% 15.84/2.49  cnf(c_5181,plain,
% 15.84/2.49      ( r2_hidden(X0,k3_tarski(sK5)) = iProver_top
% 15.84/2.49      | r2_hidden(X0,sK6) != iProver_top
% 15.84/2.49      | v4_ordinal1(sK5) != iProver_top ),
% 15.84/2.49      inference(superposition,[status(thm)],[c_1871,c_1887]) ).
% 15.84/2.49  
% 15.84/2.49  cnf(c_19199,plain,
% 15.84/2.49      ( r2_hidden(X0,sK5) = iProver_top
% 15.84/2.49      | r2_hidden(X0,sK6) != iProver_top
% 15.84/2.49      | v4_ordinal1(sK5) != iProver_top ),
% 15.84/2.49      inference(demodulation,[status(thm)],[c_18986,c_5181]) ).
% 15.84/2.49  
% 15.84/2.49  cnf(c_19827,plain,
% 15.84/2.49      ( r2_hidden(X0,sK6) != iProver_top
% 15.84/2.49      | r2_hidden(X0,sK5) = iProver_top ),
% 15.84/2.49      inference(global_propositional_subsumption,
% 15.84/2.49                [status(thm)],
% 15.84/2.49                [c_19199,c_30,c_78,c_81,c_82,c_2433,c_3740,c_4450,
% 15.84/2.49                 c_13768,c_18701]) ).
% 15.84/2.49  
% 15.84/2.49  cnf(c_19828,plain,
% 15.84/2.49      ( r2_hidden(X0,sK5) = iProver_top
% 15.84/2.49      | r2_hidden(X0,sK6) != iProver_top ),
% 15.84/2.49      inference(renaming,[status(thm)],[c_19827]) ).
% 15.84/2.49  
% 15.84/2.49  cnf(c_19840,plain,
% 15.84/2.49      ( sK6 = X0
% 15.84/2.49      | r2_hidden(X0,sK5) = iProver_top
% 15.84/2.49      | r2_hidden(sK6,X0) = iProver_top
% 15.84/2.49      | v3_ordinal1(X0) != iProver_top
% 15.84/2.49      | v3_ordinal1(sK6) != iProver_top ),
% 15.84/2.49      inference(superposition,[status(thm)],[c_1875,c_19828]) ).
% 15.84/2.49  
% 15.84/2.49  cnf(c_249,plain,
% 15.84/2.49      ( v4_ordinal1(X0) | k3_tarski(X0) != X0 ),
% 15.84/2.49      inference(prop_impl,[status(thm)],[c_9]) ).
% 15.84/2.49  
% 15.84/2.49  cnf(c_510,plain,
% 15.84/2.49      ( v3_ordinal1(sK6) | k3_tarski(X0) != X0 | sK5 != X0 ),
% 15.84/2.49      inference(resolution_lifted,[status(thm)],[c_249,c_28]) ).
% 15.84/2.49  
% 15.84/2.49  cnf(c_511,plain,
% 15.84/2.49      ( v3_ordinal1(sK6) | k3_tarski(sK5) != sK5 ),
% 15.84/2.49      inference(unflattening,[status(thm)],[c_510]) ).
% 15.84/2.49  
% 15.84/2.49  cnf(c_512,plain,
% 15.84/2.49      ( k3_tarski(sK5) != sK5 | v3_ordinal1(sK6) = iProver_top ),
% 15.84/2.49      inference(predicate_to_equality,[status(thm)],[c_511]) ).
% 15.84/2.49  
% 15.84/2.49  cnf(c_34000,plain,
% 15.84/2.49      ( v3_ordinal1(X0) != iProver_top
% 15.84/2.49      | r2_hidden(sK6,X0) = iProver_top
% 15.84/2.49      | r2_hidden(X0,sK5) = iProver_top
% 15.84/2.49      | sK6 = X0 ),
% 15.84/2.49      inference(global_propositional_subsumption,
% 15.84/2.49                [status(thm)],
% 15.84/2.49                [c_19840,c_30,c_78,c_81,c_512,c_2433,c_3740,c_4450,
% 15.84/2.49                 c_13768,c_18701]) ).
% 15.84/2.49  
% 15.84/2.49  cnf(c_34001,plain,
% 15.84/2.49      ( sK6 = X0
% 15.84/2.49      | r2_hidden(X0,sK5) = iProver_top
% 15.84/2.49      | r2_hidden(sK6,X0) = iProver_top
% 15.84/2.49      | v3_ordinal1(X0) != iProver_top ),
% 15.84/2.49      inference(renaming,[status(thm)],[c_34000]) ).
% 15.84/2.49  
% 15.84/2.49  cnf(c_7,plain,
% 15.84/2.49      ( ~ r2_hidden(X0,k3_tarski(X1)) | r2_hidden(sK3(X1,X0),X1) ),
% 15.84/2.49      inference(cnf_transformation,[],[f96]) ).
% 15.84/2.49  
% 15.84/2.49  cnf(c_1886,plain,
% 15.84/2.49      ( r2_hidden(X0,k3_tarski(X1)) != iProver_top
% 15.84/2.49      | r2_hidden(sK3(X1,X0),X1) = iProver_top ),
% 15.84/2.49      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 15.84/2.49  
% 15.84/2.49  cnf(c_1876,plain,
% 15.84/2.49      ( r2_hidden(X0,X1) != iProver_top
% 15.84/2.49      | v3_ordinal1(X1) != iProver_top
% 15.84/2.49      | v3_ordinal1(X0) = iProver_top ),
% 15.84/2.49      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 15.84/2.49  
% 15.84/2.49  cnf(c_3779,plain,
% 15.84/2.49      ( r2_hidden(X0,k3_tarski(X1)) != iProver_top
% 15.84/2.49      | v3_ordinal1(X1) != iProver_top
% 15.84/2.49      | v3_ordinal1(sK3(X1,X0)) = iProver_top ),
% 15.84/2.49      inference(superposition,[status(thm)],[c_1886,c_1876]) ).
% 15.84/2.49  
% 15.84/2.49  cnf(c_34014,plain,
% 15.84/2.49      ( k3_tarski(X0) = sK6
% 15.84/2.49      | r2_hidden(k3_tarski(X0),sK5) = iProver_top
% 15.84/2.49      | v3_ordinal1(X0) != iProver_top
% 15.84/2.49      | v3_ordinal1(sK3(X0,sK6)) = iProver_top
% 15.84/2.49      | v3_ordinal1(k3_tarski(X0)) != iProver_top ),
% 15.84/2.49      inference(superposition,[status(thm)],[c_34001,c_3779]) ).
% 15.84/2.49  
% 15.84/2.49  cnf(c_34235,plain,
% 15.84/2.49      ( k3_tarski(sK5) = sK6
% 15.84/2.49      | r2_hidden(k3_tarski(sK5),sK5) = iProver_top
% 15.84/2.49      | v3_ordinal1(sK3(sK5,sK6)) = iProver_top
% 15.84/2.49      | v3_ordinal1(k3_tarski(sK5)) != iProver_top
% 15.84/2.49      | v3_ordinal1(sK5) != iProver_top ),
% 15.84/2.49      inference(instantiation,[status(thm)],[c_34014]) ).
% 15.84/2.49  
% 15.84/2.49  cnf(c_20171,plain,
% 15.84/2.49      ( ~ r2_hidden(sK3(X0,sK6),X0) | ~ r1_tarski(X0,sK3(X0,sK6)) ),
% 15.84/2.49      inference(instantiation,[status(thm)],[c_25]) ).
% 15.84/2.49  
% 15.84/2.49  cnf(c_20172,plain,
% 15.84/2.49      ( r2_hidden(sK3(X0,sK6),X0) != iProver_top
% 15.84/2.49      | r1_tarski(X0,sK3(X0,sK6)) != iProver_top ),
% 15.84/2.49      inference(predicate_to_equality,[status(thm)],[c_20171]) ).
% 15.84/2.49  
% 15.84/2.49  cnf(c_20174,plain,
% 15.84/2.49      ( r2_hidden(sK3(sK5,sK6),sK5) != iProver_top
% 15.84/2.49      | r1_tarski(sK5,sK3(sK5,sK6)) != iProver_top ),
% 15.84/2.49      inference(instantiation,[status(thm)],[c_20172]) ).
% 15.84/2.49  
% 15.84/2.49  cnf(c_1216,plain,
% 15.84/2.49      ( ~ r2_hidden(X0,X1) | r2_hidden(X2,X3) | X2 != X0 | X3 != X1 ),
% 15.84/2.49      theory(equality) ).
% 15.84/2.49  
% 15.84/2.49  cnf(c_19987,plain,
% 15.84/2.49      ( r2_hidden(X0,X1)
% 15.84/2.49      | ~ r2_hidden(k3_tarski(sK5),X2)
% 15.84/2.49      | X1 != X2
% 15.84/2.49      | X0 != k3_tarski(sK5) ),
% 15.84/2.49      inference(instantiation,[status(thm)],[c_1216]) ).
% 15.84/2.49  
% 15.84/2.49  cnf(c_20011,plain,
% 15.84/2.49      ( X0 != X1
% 15.84/2.49      | X2 != k3_tarski(sK5)
% 15.84/2.49      | r2_hidden(X2,X0) = iProver_top
% 15.84/2.49      | r2_hidden(k3_tarski(sK5),X1) != iProver_top ),
% 15.84/2.49      inference(predicate_to_equality,[status(thm)],[c_19987]) ).
% 15.84/2.49  
% 15.84/2.49  cnf(c_20013,plain,
% 15.84/2.49      ( sK5 != k3_tarski(sK5)
% 15.84/2.49      | sK5 != sK5
% 15.84/2.49      | r2_hidden(k3_tarski(sK5),sK5) != iProver_top
% 15.84/2.49      | r2_hidden(sK5,sK5) = iProver_top ),
% 15.84/2.49      inference(instantiation,[status(thm)],[c_20011]) ).
% 15.84/2.49  
% 15.84/2.49  cnf(c_20012,plain,
% 15.84/2.49      ( ~ r2_hidden(k3_tarski(sK5),sK5)
% 15.84/2.49      | r2_hidden(sK5,sK5)
% 15.84/2.49      | sK5 != k3_tarski(sK5)
% 15.84/2.49      | sK5 != sK5 ),
% 15.84/2.49      inference(instantiation,[status(thm)],[c_19987]) ).
% 15.84/2.49  
% 15.84/2.49  cnf(c_1214,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 15.84/2.49  
% 15.84/2.49  cnf(c_1213,plain,( X0 = X0 ),theory(equality) ).
% 15.84/2.49  
% 15.84/2.49  cnf(c_3846,plain,
% 15.84/2.49      ( X0 != X1 | X1 = X0 ),
% 15.84/2.49      inference(resolution,[status(thm)],[c_1214,c_1213]) ).
% 15.84/2.49  
% 15.84/2.49  cnf(c_19006,plain,
% 15.84/2.49      ( ~ v4_ordinal1(X0) | X0 = k3_tarski(X0) ),
% 15.84/2.49      inference(resolution,[status(thm)],[c_10,c_3846]) ).
% 15.84/2.49  
% 15.84/2.49  cnf(c_19008,plain,
% 15.84/2.49      ( ~ v4_ordinal1(sK5) | sK5 = k3_tarski(sK5) ),
% 15.84/2.49      inference(instantiation,[status(thm)],[c_19006]) ).
% 15.84/2.49  
% 15.84/2.49  cnf(c_1,plain,
% 15.84/2.49      ( r2_hidden(sK0(X0,X1),X0) | r1_tarski(X0,X1) ),
% 15.84/2.49      inference(cnf_transformation,[],[f55]) ).
% 15.84/2.49  
% 15.84/2.49  cnf(c_1892,plain,
% 15.84/2.49      ( r2_hidden(sK0(X0,X1),X0) = iProver_top
% 15.84/2.49      | r1_tarski(X0,X1) = iProver_top ),
% 15.84/2.49      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 15.84/2.49  
% 15.84/2.49  cnf(c_0,plain,
% 15.84/2.49      ( ~ r2_hidden(sK0(X0,X1),X1) | r1_tarski(X0,X1) ),
% 15.84/2.49      inference(cnf_transformation,[],[f56]) ).
% 15.84/2.49  
% 15.84/2.49  cnf(c_1893,plain,
% 15.84/2.49      ( r2_hidden(sK0(X0,X1),X1) != iProver_top
% 15.84/2.49      | r1_tarski(X0,X1) = iProver_top ),
% 15.84/2.49      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 15.84/2.49  
% 15.84/2.49  cnf(c_3464,plain,
% 15.84/2.49      ( r1_tarski(X0,X0) = iProver_top ),
% 15.84/2.49      inference(superposition,[status(thm)],[c_1892,c_1893]) ).
% 15.84/2.49  
% 15.84/2.49  cnf(c_5663,plain,
% 15.84/2.49      ( r2_hidden(X0,sK6) != iProver_top
% 15.84/2.49      | r1_tarski(k3_tarski(sK5),X0) != iProver_top
% 15.84/2.49      | v4_ordinal1(sK5) != iProver_top ),
% 15.84/2.49      inference(superposition,[status(thm)],[c_5181,c_1873]) ).
% 15.84/2.49  
% 15.84/2.49  cnf(c_6323,plain,
% 15.84/2.49      ( r2_hidden(k3_tarski(sK5),sK6) != iProver_top
% 15.84/2.49      | v4_ordinal1(sK5) != iProver_top ),
% 15.84/2.49      inference(superposition,[status(thm)],[c_3464,c_5663]) ).
% 15.84/2.49  
% 15.84/2.49  cnf(c_16504,plain,
% 15.84/2.49      ( k3_tarski(sK5) = sK6
% 15.84/2.49      | r2_hidden(sK6,k3_tarski(sK5)) = iProver_top
% 15.84/2.49      | v3_ordinal1(k3_tarski(sK5)) != iProver_top
% 15.84/2.49      | v3_ordinal1(sK6) != iProver_top
% 15.84/2.49      | v4_ordinal1(sK5) != iProver_top ),
% 15.84/2.49      inference(superposition,[status(thm)],[c_1875,c_6323]) ).
% 15.84/2.49  
% 15.84/2.49  cnf(c_1218,plain,
% 15.84/2.49      ( ~ v3_ordinal1(X0) | v3_ordinal1(X1) | X1 != X0 ),
% 15.84/2.49      theory(equality) ).
% 15.84/2.49  
% 15.84/2.49  cnf(c_6828,plain,
% 15.84/2.49      ( ~ v3_ordinal1(X0)
% 15.84/2.49      | v3_ordinal1(k3_tarski(X1))
% 15.84/2.49      | k3_tarski(X1) != X0 ),
% 15.84/2.49      inference(instantiation,[status(thm)],[c_1218]) ).
% 15.84/2.49  
% 15.84/2.49  cnf(c_6829,plain,
% 15.84/2.49      ( k3_tarski(X0) != X1
% 15.84/2.49      | v3_ordinal1(X1) != iProver_top
% 15.84/2.49      | v3_ordinal1(k3_tarski(X0)) = iProver_top ),
% 15.84/2.49      inference(predicate_to_equality,[status(thm)],[c_6828]) ).
% 15.84/2.49  
% 15.84/2.49  cnf(c_6831,plain,
% 15.84/2.49      ( k3_tarski(sK5) != sK5
% 15.84/2.49      | v3_ordinal1(k3_tarski(sK5)) = iProver_top
% 15.84/2.49      | v3_ordinal1(sK5) != iProver_top ),
% 15.84/2.49      inference(instantiation,[status(thm)],[c_6829]) ).
% 15.84/2.49  
% 15.84/2.49  cnf(c_2261,plain,
% 15.84/2.49      ( r2_hidden(X0,X1) | ~ r2_hidden(sK6,sK5) | X1 != sK5 | X0 != sK6 ),
% 15.84/2.49      inference(instantiation,[status(thm)],[c_1216]) ).
% 15.84/2.49  
% 15.84/2.49  cnf(c_3246,plain,
% 15.84/2.49      ( r2_hidden(k3_tarski(sK5),X0)
% 15.84/2.49      | ~ r2_hidden(sK6,sK5)
% 15.84/2.49      | X0 != sK5
% 15.84/2.49      | k3_tarski(sK5) != sK6 ),
% 15.84/2.49      inference(instantiation,[status(thm)],[c_2261]) ).
% 15.84/2.49  
% 15.84/2.49  cnf(c_3250,plain,
% 15.84/2.49      ( r2_hidden(k3_tarski(sK5),sK5)
% 15.84/2.49      | ~ r2_hidden(sK6,sK5)
% 15.84/2.49      | k3_tarski(sK5) != sK6
% 15.84/2.49      | sK5 != sK5 ),
% 15.84/2.49      inference(instantiation,[status(thm)],[c_3246]) ).
% 15.84/2.49  
% 15.84/2.49  cnf(c_3128,plain,
% 15.84/2.49      ( r2_hidden(sK3(X0,sK6),X0) | ~ r2_hidden(sK6,k3_tarski(X0)) ),
% 15.84/2.49      inference(instantiation,[status(thm)],[c_7]) ).
% 15.84/2.49  
% 15.84/2.49  cnf(c_3133,plain,
% 15.84/2.49      ( r2_hidden(sK3(X0,sK6),X0) = iProver_top
% 15.84/2.49      | r2_hidden(sK6,k3_tarski(X0)) != iProver_top ),
% 15.84/2.49      inference(predicate_to_equality,[status(thm)],[c_3128]) ).
% 15.84/2.49  
% 15.84/2.49  cnf(c_3135,plain,
% 15.84/2.49      ( r2_hidden(sK3(sK5,sK6),sK5) = iProver_top
% 15.84/2.49      | r2_hidden(sK6,k3_tarski(sK5)) != iProver_top ),
% 15.84/2.49      inference(instantiation,[status(thm)],[c_3133]) ).
% 15.84/2.49  
% 15.84/2.49  cnf(c_686,plain,
% 15.84/2.49      ( ~ r2_hidden(sK5,k2_xboole_0(sK5,k1_tarski(sK5)))
% 15.84/2.49      | ~ r2_hidden(sK5,sK5)
% 15.84/2.49      | ~ v3_ordinal1(sK5) ),
% 15.84/2.49      inference(instantiation,[status(thm)],[c_684]) ).
% 15.84/2.49  
% 15.84/2.49  cnf(c_61,plain,
% 15.84/2.49      ( r2_hidden(sK5,k2_xboole_0(sK5,k1_tarski(sK5))) ),
% 15.84/2.49      inference(instantiation,[status(thm)],[c_17]) ).
% 15.84/2.49  
% 15.84/2.49  cnf(c_51,plain,
% 15.84/2.49      ( r2_hidden(sK5,sK5) | ~ v3_ordinal1(sK5) | sK5 = sK5 ),
% 15.84/2.49      inference(instantiation,[status(thm)],[c_21]) ).
% 15.84/2.49  
% 15.84/2.49  cnf(contradiction,plain,
% 15.84/2.49      ( $false ),
% 15.84/2.49      inference(minisat,
% 15.84/2.49                [status(thm)],
% 15.84/2.49                [c_71265,c_34235,c_20174,c_20013,c_20012,c_19008,c_18705,
% 15.84/2.49                 c_16504,c_6831,c_3250,c_3135,c_687,c_686,c_512,c_82,
% 15.84/2.49                 c_78,c_62,c_61,c_51,c_27,c_31,c_30]) ).
% 15.84/2.49  
% 15.84/2.49  
% 15.84/2.49  % SZS output end CNFRefutation for theBenchmark.p
% 15.84/2.49  
% 15.84/2.49  ------                               Statistics
% 15.84/2.49  
% 15.84/2.49  ------ Selected
% 15.84/2.49  
% 15.84/2.49  total_time:                             1.904
% 15.84/2.49  
%------------------------------------------------------------------------------
