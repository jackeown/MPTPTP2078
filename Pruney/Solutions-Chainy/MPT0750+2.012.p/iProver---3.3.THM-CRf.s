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
% DateTime   : Thu Dec  3 11:54:02 EST 2020

% Result     : Theorem 3.86s
% Output     : CNFRefutation 3.86s
% Verified   : 
% Statistics : Number of formulae       :  204 (2289 expanded)
%              Number of clauses        :  111 ( 628 expanded)
%              Number of leaves         :   23 ( 547 expanded)
%              Depth                    :   29
%              Number of atoms          :  695 (11006 expanded)
%              Number of equality atoms :  211 (1538 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal clause size      :   18 (   3 average)
%              Maximal term depth       :    5 (   1 average)

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
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

fof(f36,plain,(
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
    inference(rectify,[],[f35])).

fof(f39,plain,(
    ! [X5,X0] :
      ( ? [X7] :
          ( r2_hidden(X7,X0)
          & r2_hidden(X5,X7) )
     => ( r2_hidden(sK2(X0,X5),X0)
        & r2_hidden(X5,sK2(X0,X5)) ) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( r2_hidden(X4,X0)
          & r2_hidden(X2,X4) )
     => ( r2_hidden(sK1(X0,X1),X0)
        & r2_hidden(X2,sK1(X0,X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,(
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
              | ~ r2_hidden(sK0(X0,X1),X3) )
          | ~ r2_hidden(sK0(X0,X1),X1) )
        & ( ? [X4] :
              ( r2_hidden(X4,X0)
              & r2_hidden(sK0(X0,X1),X4) )
          | r2_hidden(sK0(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( k3_tarski(X0) = X1
        | ( ( ! [X3] :
                ( ~ r2_hidden(X3,X0)
                | ~ r2_hidden(sK0(X0,X1),X3) )
            | ~ r2_hidden(sK0(X0,X1),X1) )
          & ( ( r2_hidden(sK1(X0,X1),X0)
              & r2_hidden(sK0(X0,X1),sK1(X0,X1)) )
            | r2_hidden(sK0(X0,X1),X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] :
                  ( ~ r2_hidden(X6,X0)
                  | ~ r2_hidden(X5,X6) ) )
            & ( ( r2_hidden(sK2(X0,X5),X0)
                & r2_hidden(X5,sK2(X0,X5)) )
              | ~ r2_hidden(X5,X1) ) )
        | k3_tarski(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f36,f39,f38,f37])).

fof(f64,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(sK2(X0,X5),X0)
      | ~ r2_hidden(X5,X1)
      | k3_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f40])).

fof(f111,plain,(
    ! [X0,X5] :
      ( r2_hidden(sK2(X0,X5),X0)
      | ~ r2_hidden(X5,k3_tarski(X0)) ) ),
    inference(equality_resolution,[],[f64])).

fof(f17,conjecture,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ( v4_ordinal1(X0)
      <=> ! [X1] :
            ( v3_ordinal1(X1)
           => ( r2_hidden(X1,X0)
             => r2_hidden(k1_ordinal1(X1),X0) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,negated_conjecture,(
    ~ ! [X0] :
        ( v3_ordinal1(X0)
       => ( v4_ordinal1(X0)
        <=> ! [X1] :
              ( v3_ordinal1(X1)
             => ( r2_hidden(X1,X0)
               => r2_hidden(k1_ordinal1(X1),X0) ) ) ) ) ),
    inference(negated_conjecture,[],[f17])).

fof(f31,plain,(
    ? [X0] :
      ( ( v4_ordinal1(X0)
      <~> ! [X1] :
            ( r2_hidden(k1_ordinal1(X1),X0)
            | ~ r2_hidden(X1,X0)
            | ~ v3_ordinal1(X1) ) )
      & v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f32,plain,(
    ? [X0] :
      ( ( v4_ordinal1(X0)
      <~> ! [X1] :
            ( r2_hidden(k1_ordinal1(X1),X0)
            | ~ r2_hidden(X1,X0)
            | ~ v3_ordinal1(X1) ) )
      & v3_ordinal1(X0) ) ),
    inference(flattening,[],[f31])).

fof(f54,plain,(
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
    inference(nnf_transformation,[],[f32])).

fof(f55,plain,(
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
    inference(flattening,[],[f54])).

fof(f56,plain,(
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
    inference(rectify,[],[f55])).

fof(f58,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ r2_hidden(k1_ordinal1(X1),X0)
          & r2_hidden(X1,X0)
          & v3_ordinal1(X1) )
     => ( ~ r2_hidden(k1_ordinal1(sK7),X0)
        & r2_hidden(sK7,X0)
        & v3_ordinal1(sK7) ) ) ),
    introduced(choice_axiom,[])).

fof(f57,plain,
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

fof(f59,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7])],[f56,f58,f57])).

fof(f94,plain,(
    ! [X2] :
      ( r2_hidden(k1_ordinal1(X2),sK6)
      | ~ r2_hidden(X2,sK6)
      | ~ v3_ordinal1(X2)
      | v4_ordinal1(sK6) ) ),
    inference(cnf_transformation,[],[f59])).

fof(f3,axiom,(
    ! [X0] : k1_ordinal1(X0) = k2_xboole_0(X0,k1_tarski(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f69,plain,(
    ! [X0] : k1_ordinal1(X0) = k2_xboole_0(X0,k1_tarski(X0)) ),
    inference(cnf_transformation,[],[f3])).

fof(f107,plain,(
    ! [X2] :
      ( r2_hidden(k2_xboole_0(X2,k1_tarski(X2)),sK6)
      | ~ r2_hidden(X2,sK6)
      | ~ v3_ordinal1(X2)
      | v4_ordinal1(sK6) ) ),
    inference(definition_unfolding,[],[f94,f69])).

fof(f96,plain,
    ( r2_hidden(sK7,sK6)
    | ~ v4_ordinal1(sK6) ),
    inference(cnf_transformation,[],[f59])).

fof(f65,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | ~ r2_hidden(X6,X0)
      | ~ r2_hidden(X5,X6)
      | k3_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f40])).

fof(f110,plain,(
    ! [X6,X0,X5] :
      ( r2_hidden(X5,k3_tarski(X0))
      | ~ r2_hidden(X6,X0)
      | ~ r2_hidden(X5,X6) ) ),
    inference(equality_resolution,[],[f65])).

fof(f93,plain,(
    v3_ordinal1(sK6) ),
    inference(cnf_transformation,[],[f59])).

fof(f63,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(X5,sK2(X0,X5))
      | ~ r2_hidden(X5,X1)
      | k3_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f40])).

fof(f112,plain,(
    ! [X0,X5] :
      ( r2_hidden(X5,sK2(X0,X5))
      | ~ r2_hidden(X5,k3_tarski(X0)) ) ),
    inference(equality_resolution,[],[f63])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,k1_ordinal1(X1))
    <=> ( X0 = X1
        | r2_hidden(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f47,plain,(
    ! [X0,X1] :
      ( ( r2_hidden(X0,k1_ordinal1(X1))
        | ( X0 != X1
          & ~ r2_hidden(X0,X1) ) )
      & ( X0 = X1
        | r2_hidden(X0,X1)
        | ~ r2_hidden(X0,k1_ordinal1(X1)) ) ) ),
    inference(nnf_transformation,[],[f8])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ( r2_hidden(X0,k1_ordinal1(X1))
        | ( X0 != X1
          & ~ r2_hidden(X0,X1) ) )
      & ( X0 = X1
        | r2_hidden(X0,X1)
        | ~ r2_hidden(X0,k1_ordinal1(X1)) ) ) ),
    inference(flattening,[],[f47])).

fof(f79,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,k1_ordinal1(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f100,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,k2_xboole_0(X1,k1_tarski(X1)))
      | ~ r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f79,f69])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( v3_ordinal1(X1)
     => ( r2_hidden(X0,X1)
       => v3_ordinal1(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] :
      ( v3_ordinal1(X0)
      | ~ r2_hidden(X0,X1)
      | ~ v3_ordinal1(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f22,plain,(
    ! [X0,X1] :
      ( v3_ordinal1(X0)
      | ~ r2_hidden(X0,X1)
      | ~ v3_ordinal1(X1) ) ),
    inference(flattening,[],[f21])).

fof(f82,plain,(
    ! [X0,X1] :
      ( v3_ordinal1(X0)
      | ~ r2_hidden(X0,X1)
      | ~ v3_ordinal1(X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f14,axiom,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(X1,X0)
         => v3_ordinal1(X1) )
     => v3_ordinal1(k3_tarski(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0] :
      ( v3_ordinal1(k3_tarski(X0))
      | ? [X1] :
          ( ~ v3_ordinal1(X1)
          & r2_hidden(X1,X0) ) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f50,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ v3_ordinal1(X1)
          & r2_hidden(X1,X0) )
     => ( ~ v3_ordinal1(sK4(X0))
        & r2_hidden(sK4(X0),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f51,plain,(
    ! [X0] :
      ( v3_ordinal1(k3_tarski(X0))
      | ( ~ v3_ordinal1(sK4(X0))
        & r2_hidden(sK4(X0),X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f27,f50])).

fof(f87,plain,(
    ! [X0] :
      ( v3_ordinal1(k3_tarski(X0))
      | r2_hidden(sK4(X0),X0) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f88,plain,(
    ! [X0] :
      ( v3_ordinal1(k3_tarski(X0))
      | ~ v3_ordinal1(sK4(X0)) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f16,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f92,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f13,axiom,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ! [X1] :
          ( v3_ordinal1(X1)
         => ( r2_hidden(X0,k1_ordinal1(X1))
          <=> r1_ordinal1(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r2_hidden(X0,k1_ordinal1(X1))
          <=> r1_ordinal1(X0,X1) )
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f49,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( r2_hidden(X0,k1_ordinal1(X1))
              | ~ r1_ordinal1(X0,X1) )
            & ( r1_ordinal1(X0,X1)
              | ~ r2_hidden(X0,k1_ordinal1(X1)) ) )
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(nnf_transformation,[],[f26])).

fof(f85,plain,(
    ! [X0,X1] :
      ( r1_ordinal1(X0,X1)
      | ~ r2_hidden(X0,k1_ordinal1(X1))
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f105,plain,(
    ! [X0,X1] :
      ( r1_ordinal1(X0,X1)
      | ~ r2_hidden(X0,k2_xboole_0(X1,k1_tarski(X1)))
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(definition_unfolding,[],[f85,f69])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( ( v3_ordinal1(X1)
        & v3_ordinal1(X0) )
     => ( r1_ordinal1(X0,X1)
      <=> r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( r1_ordinal1(X0,X1)
      <=> r1_tarski(X0,X1) )
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( r1_ordinal1(X0,X1)
      <=> r1_tarski(X0,X1) )
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(flattening,[],[f19])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ( ( r1_ordinal1(X0,X1)
          | ~ r1_tarski(X0,X1) )
        & ( r1_tarski(X0,X1)
          | ~ r1_ordinal1(X0,X1) ) )
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(nnf_transformation,[],[f20])).

fof(f72,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r1_ordinal1(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f11,axiom,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ! [X1] :
          ( v3_ordinal1(X1)
         => ~ ( ~ r2_hidden(X1,X0)
              & X0 != X1
              & ~ r2_hidden(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(X1,X0)
          | X0 = X1
          | r2_hidden(X0,X1)
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(X1,X0)
          | X0 = X1
          | r2_hidden(X0,X1)
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(flattening,[],[f23])).

fof(f83,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,X0)
      | X0 = X1
      | r2_hidden(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f4,axiom,(
    ! [X0] :
      ( v4_ordinal1(X0)
    <=> k3_tarski(X0) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0] :
      ( ( v4_ordinal1(X0)
        | k3_tarski(X0) != X0 )
      & ( k3_tarski(X0) = X0
        | ~ v4_ordinal1(X0) ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f71,plain,(
    ! [X0] :
      ( v4_ordinal1(X0)
      | k3_tarski(X0) != X0 ) ),
    inference(cnf_transformation,[],[f41])).

fof(f80,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,k1_ordinal1(X1))
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f48])).

fof(f99,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,k2_xboole_0(X1,k1_tarski(X1)))
      | X0 != X1 ) ),
    inference(definition_unfolding,[],[f80,f69])).

fof(f113,plain,(
    ! [X1] : r2_hidden(X1,k2_xboole_0(X1,k1_tarski(X1))) ),
    inference(equality_resolution,[],[f99])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f33])).

fof(f61,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f34])).

fof(f108,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f61])).

fof(f70,plain,(
    ! [X0] :
      ( k3_tarski(X0) = X0
      | ~ v4_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f6,axiom,(
    ! [X0] :
    ? [X1] :
    ! [X2] :
      ( r2_hidden(X2,X1)
    <=> ( v3_ordinal1(X2)
        & r2_hidden(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X0] :
    ? [X1] :
    ! [X2] :
      ( ( r2_hidden(X2,X1)
        | ~ v3_ordinal1(X2)
        | ~ r2_hidden(X2,X0) )
      & ( ( v3_ordinal1(X2)
          & r2_hidden(X2,X0) )
        | ~ r2_hidden(X2,X1) ) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f44,plain,(
    ! [X0] :
    ? [X1] :
    ! [X2] :
      ( ( r2_hidden(X2,X1)
        | ~ v3_ordinal1(X2)
        | ~ r2_hidden(X2,X0) )
      & ( ( v3_ordinal1(X2)
          & r2_hidden(X2,X0) )
        | ~ r2_hidden(X2,X1) ) ) ),
    inference(flattening,[],[f43])).

fof(f45,plain,(
    ! [X0] :
      ( ? [X1] :
        ! [X2] :
          ( ( r2_hidden(X2,X1)
            | ~ v3_ordinal1(X2)
            | ~ r2_hidden(X2,X0) )
          & ( ( v3_ordinal1(X2)
              & r2_hidden(X2,X0) )
            | ~ r2_hidden(X2,X1) ) )
     => ! [X2] :
          ( ( r2_hidden(X2,sK3(X0))
            | ~ v3_ordinal1(X2)
            | ~ r2_hidden(X2,X0) )
          & ( ( v3_ordinal1(X2)
              & r2_hidden(X2,X0) )
            | ~ r2_hidden(X2,sK3(X0)) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f46,plain,(
    ! [X0,X2] :
      ( ( r2_hidden(X2,sK3(X0))
        | ~ v3_ordinal1(X2)
        | ~ r2_hidden(X2,X0) )
      & ( ( v3_ordinal1(X2)
          & r2_hidden(X2,X0) )
        | ~ r2_hidden(X2,sK3(X0)) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f44,f45])).

fof(f76,plain,(
    ! [X2,X0] :
      ( r2_hidden(X2,sK3(X0))
      | ~ v3_ordinal1(X2)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f15,axiom,(
    ! [X0] :
    ? [X1] :
      ( ! [X2] :
          ( v3_ordinal1(X2)
         => ( ~ r2_hidden(X2,X0)
           => r1_ordinal1(X1,X2) ) )
      & ~ r2_hidden(X1,X0)
      & v3_ordinal1(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0] :
    ? [X1] :
      ( ! [X2] :
          ( r1_ordinal1(X1,X2)
          | r2_hidden(X2,X0)
          | ~ v3_ordinal1(X2) )
      & ~ r2_hidden(X1,X0)
      & v3_ordinal1(X1) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f29,plain,(
    ! [X0] :
    ? [X1] :
      ( ! [X2] :
          ( r1_ordinal1(X1,X2)
          | r2_hidden(X2,X0)
          | ~ v3_ordinal1(X2) )
      & ~ r2_hidden(X1,X0)
      & v3_ordinal1(X1) ) ),
    inference(flattening,[],[f28])).

fof(f52,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2] :
              ( r1_ordinal1(X1,X2)
              | r2_hidden(X2,X0)
              | ~ v3_ordinal1(X2) )
          & ~ r2_hidden(X1,X0)
          & v3_ordinal1(X1) )
     => ( ! [X2] :
            ( r1_ordinal1(sK5(X0),X2)
            | r2_hidden(X2,X0)
            | ~ v3_ordinal1(X2) )
        & ~ r2_hidden(sK5(X0),X0)
        & v3_ordinal1(sK5(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f53,plain,(
    ! [X0] :
      ( ! [X2] :
          ( r1_ordinal1(sK5(X0),X2)
          | r2_hidden(X2,X0)
          | ~ v3_ordinal1(X2) )
      & ~ r2_hidden(sK5(X0),X0)
      & v3_ordinal1(sK5(X0)) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f29,f52])).

fof(f90,plain,(
    ! [X0] : ~ r2_hidden(sK5(X0),X0) ),
    inference(cnf_transformation,[],[f53])).

fof(f89,plain,(
    ! [X0] : v3_ordinal1(sK5(X0)) ),
    inference(cnf_transformation,[],[f53])).

fof(f12,axiom,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => v3_ordinal1(k1_ordinal1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0] :
      ( v3_ordinal1(k1_ordinal1(X0))
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f84,plain,(
    ! [X0] :
      ( v3_ordinal1(k1_ordinal1(X0))
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f103,plain,(
    ! [X0] :
      ( v3_ordinal1(k2_xboole_0(X0,k1_tarski(X0)))
      | ~ v3_ordinal1(X0) ) ),
    inference(definition_unfolding,[],[f84,f69])).

fof(f97,plain,
    ( ~ r2_hidden(k1_ordinal1(sK7),sK6)
    | ~ v4_ordinal1(sK6) ),
    inference(cnf_transformation,[],[f59])).

fof(f106,plain,
    ( ~ r2_hidden(k2_xboole_0(sK7,k1_tarski(sK7)),sK6)
    | ~ v4_ordinal1(sK6) ),
    inference(definition_unfolding,[],[f97,f69])).

fof(f95,plain,
    ( v3_ordinal1(sK7)
    | ~ v4_ordinal1(sK6) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_7,plain,
    ( ~ r2_hidden(X0,k3_tarski(X1))
    | r2_hidden(sK2(X1,X0),X1) ),
    inference(cnf_transformation,[],[f111])).

cnf(c_1820,plain,
    ( r2_hidden(X0,k3_tarski(X1)) != iProver_top
    | r2_hidden(sK2(X1,X0),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_35,negated_conjecture,
    ( ~ r2_hidden(X0,sK6)
    | r2_hidden(k2_xboole_0(X0,k1_tarski(X0)),sK6)
    | ~ v3_ordinal1(X0)
    | v4_ordinal1(sK6) ),
    inference(cnf_transformation,[],[f107])).

cnf(c_1799,plain,
    ( r2_hidden(X0,sK6) != iProver_top
    | r2_hidden(k2_xboole_0(X0,k1_tarski(X0)),sK6) = iProver_top
    | v3_ordinal1(X0) != iProver_top
    | v4_ordinal1(sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_35])).

cnf(c_33,negated_conjecture,
    ( r2_hidden(sK7,sK6)
    | ~ v4_ordinal1(sK6) ),
    inference(cnf_transformation,[],[f96])).

cnf(c_1801,plain,
    ( r2_hidden(sK7,sK6) = iProver_top
    | v4_ordinal1(sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_6,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X2,X0)
    | r2_hidden(X2,k3_tarski(X1)) ),
    inference(cnf_transformation,[],[f110])).

cnf(c_1821,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X2,X0) != iProver_top
    | r2_hidden(X2,k3_tarski(X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_6035,plain,
    ( r2_hidden(X0,k3_tarski(sK6)) = iProver_top
    | r2_hidden(X0,sK7) != iProver_top
    | v4_ordinal1(sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_1801,c_1821])).

cnf(c_6948,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,k3_tarski(k3_tarski(sK6))) = iProver_top
    | r2_hidden(X1,sK7) != iProver_top
    | v4_ordinal1(sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_6035,c_1821])).

cnf(c_36,negated_conjecture,
    ( v3_ordinal1(sK6) ),
    inference(cnf_transformation,[],[f93])).

cnf(c_37,plain,
    ( v3_ordinal1(sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_36])).

cnf(c_8,plain,
    ( r2_hidden(X0,sK2(X1,X0))
    | ~ r2_hidden(X0,k3_tarski(X1)) ),
    inference(cnf_transformation,[],[f112])).

cnf(c_105,plain,
    ( r2_hidden(X0,sK2(X1,X0)) = iProver_top
    | r2_hidden(X0,k3_tarski(X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_107,plain,
    ( r2_hidden(sK6,sK2(sK6,sK6)) = iProver_top
    | r2_hidden(sK6,k3_tarski(sK6)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_105])).

cnf(c_18,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,k2_xboole_0(X1,k1_tarski(X1))) ),
    inference(cnf_transformation,[],[f100])).

cnf(c_2625,plain,
    ( r2_hidden(X0,k2_xboole_0(sK2(X1,X0),k1_tarski(sK2(X1,X0))))
    | ~ r2_hidden(X0,sK2(X1,X0)) ),
    inference(instantiation,[status(thm)],[c_18])).

cnf(c_2636,plain,
    ( r2_hidden(X0,k2_xboole_0(sK2(X1,X0),k1_tarski(sK2(X1,X0)))) = iProver_top
    | r2_hidden(X0,sK2(X1,X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2625])).

cnf(c_2638,plain,
    ( r2_hidden(sK6,k2_xboole_0(sK2(sK6,sK6),k1_tarski(sK2(sK6,sK6)))) = iProver_top
    | r2_hidden(sK6,sK2(sK6,sK6)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_2636])).

cnf(c_21,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ v3_ordinal1(X1)
    | v3_ordinal1(X0) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_27,plain,
    ( r2_hidden(sK4(X0),X0)
    | v3_ordinal1(k3_tarski(X0)) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_3167,plain,
    ( ~ v3_ordinal1(X0)
    | v3_ordinal1(sK4(X0))
    | v3_ordinal1(k3_tarski(X0)) ),
    inference(resolution,[status(thm)],[c_21,c_27])).

cnf(c_26,plain,
    ( ~ v3_ordinal1(sK4(X0))
    | v3_ordinal1(k3_tarski(X0)) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_3246,plain,
    ( ~ v3_ordinal1(X0)
    | v3_ordinal1(k3_tarski(X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3167,c_26])).

cnf(c_3248,plain,
    ( v3_ordinal1(X0) != iProver_top
    | v3_ordinal1(k3_tarski(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3246])).

cnf(c_3250,plain,
    ( v3_ordinal1(k3_tarski(sK6)) = iProver_top
    | v3_ordinal1(sK6) != iProver_top ),
    inference(instantiation,[status(thm)],[c_3248])).

cnf(c_3271,plain,
    ( ~ r2_hidden(X0,k3_tarski(X1))
    | ~ v3_ordinal1(X1)
    | v3_ordinal1(sK2(X1,X0)) ),
    inference(resolution,[status(thm)],[c_7,c_21])).

cnf(c_3272,plain,
    ( r2_hidden(X0,k3_tarski(X1)) != iProver_top
    | v3_ordinal1(X1) != iProver_top
    | v3_ordinal1(sK2(X1,X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3271])).

cnf(c_3274,plain,
    ( r2_hidden(sK6,k3_tarski(sK6)) != iProver_top
    | v3_ordinal1(sK2(sK6,sK6)) = iProver_top
    | v3_ordinal1(sK6) != iProver_top ),
    inference(instantiation,[status(thm)],[c_3272])).

cnf(c_31,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r1_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_3270,plain,
    ( ~ r2_hidden(X0,k3_tarski(X1))
    | ~ r1_tarski(X1,sK2(X1,X0)) ),
    inference(resolution,[status(thm)],[c_7,c_31])).

cnf(c_3275,plain,
    ( r2_hidden(X0,k3_tarski(X1)) != iProver_top
    | r1_tarski(X1,sK2(X1,X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3270])).

cnf(c_3277,plain,
    ( r2_hidden(sK6,k3_tarski(sK6)) != iProver_top
    | r1_tarski(sK6,sK2(sK6,sK6)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_3275])).

cnf(c_25,plain,
    ( r1_ordinal1(X0,X1)
    | ~ r2_hidden(X0,k2_xboole_0(X1,k1_tarski(X1)))
    | ~ v3_ordinal1(X1)
    | ~ v3_ordinal1(X0) ),
    inference(cnf_transformation,[],[f105])).

cnf(c_12,plain,
    ( ~ r1_ordinal1(X0,X1)
    | r1_tarski(X0,X1)
    | ~ v3_ordinal1(X1)
    | ~ v3_ordinal1(X0) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_577,plain,
    ( ~ r2_hidden(X0,k2_xboole_0(X1,k1_tarski(X1)))
    | r1_tarski(X0,X1)
    | ~ v3_ordinal1(X1)
    | ~ v3_ordinal1(X0) ),
    inference(resolution,[status(thm)],[c_25,c_12])).

cnf(c_3583,plain,
    ( ~ r2_hidden(X0,k2_xboole_0(sK2(X0,X1),k1_tarski(sK2(X0,X1))))
    | r1_tarski(X0,sK2(X0,X1))
    | ~ v3_ordinal1(X0)
    | ~ v3_ordinal1(sK2(X0,X1)) ),
    inference(instantiation,[status(thm)],[c_577])).

cnf(c_3584,plain,
    ( r2_hidden(X0,k2_xboole_0(sK2(X0,X1),k1_tarski(sK2(X0,X1)))) != iProver_top
    | r1_tarski(X0,sK2(X0,X1)) = iProver_top
    | v3_ordinal1(X0) != iProver_top
    | v3_ordinal1(sK2(X0,X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3583])).

cnf(c_3586,plain,
    ( r2_hidden(sK6,k2_xboole_0(sK2(sK6,sK6),k1_tarski(sK2(sK6,sK6)))) != iProver_top
    | r1_tarski(sK6,sK2(sK6,sK6)) = iProver_top
    | v3_ordinal1(sK2(sK6,sK6)) != iProver_top
    | v3_ordinal1(sK6) != iProver_top ),
    inference(instantiation,[status(thm)],[c_3584])).

cnf(c_22,plain,
    ( r2_hidden(X0,X1)
    | r2_hidden(X1,X0)
    | ~ v3_ordinal1(X1)
    | ~ v3_ordinal1(X0)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f83])).

cnf(c_9,plain,
    ( v4_ordinal1(X0)
    | k3_tarski(X0) != X0 ),
    inference(cnf_transformation,[],[f71])).

cnf(c_6334,plain,
    ( r2_hidden(X0,k3_tarski(X0))
    | r2_hidden(k3_tarski(X0),X0)
    | ~ v3_ordinal1(X0)
    | ~ v3_ordinal1(k3_tarski(X0))
    | v4_ordinal1(X0) ),
    inference(resolution,[status(thm)],[c_22,c_9])).

cnf(c_6335,plain,
    ( r2_hidden(X0,k3_tarski(X0)) = iProver_top
    | r2_hidden(k3_tarski(X0),X0) = iProver_top
    | v3_ordinal1(X0) != iProver_top
    | v3_ordinal1(k3_tarski(X0)) != iProver_top
    | v4_ordinal1(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6334])).

cnf(c_6337,plain,
    ( r2_hidden(k3_tarski(sK6),sK6) = iProver_top
    | r2_hidden(sK6,k3_tarski(sK6)) = iProver_top
    | v3_ordinal1(k3_tarski(sK6)) != iProver_top
    | v3_ordinal1(sK6) != iProver_top
    | v4_ordinal1(sK6) = iProver_top ),
    inference(instantiation,[status(thm)],[c_6335])).

cnf(c_17,plain,
    ( r2_hidden(X0,k2_xboole_0(X0,k1_tarski(X0))) ),
    inference(cnf_transformation,[],[f113])).

cnf(c_4820,plain,
    ( r2_hidden(X0,k3_tarski(X1))
    | ~ r2_hidden(k2_xboole_0(X0,k1_tarski(X0)),X1) ),
    inference(resolution,[status(thm)],[c_6,c_17])).

cnf(c_9091,plain,
    ( r2_hidden(X0,k3_tarski(sK6))
    | ~ r2_hidden(X0,sK6)
    | ~ v3_ordinal1(X0)
    | v4_ordinal1(sK6) ),
    inference(resolution,[status(thm)],[c_4820,c_35])).

cnf(c_9878,plain,
    ( ~ r2_hidden(X0,sK6)
    | ~ r1_tarski(k3_tarski(sK6),X0)
    | ~ v3_ordinal1(X0)
    | v4_ordinal1(sK6) ),
    inference(resolution,[status(thm)],[c_9091,c_31])).

cnf(c_1,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f108])).

cnf(c_9943,plain,
    ( ~ r2_hidden(k3_tarski(sK6),sK6)
    | ~ v3_ordinal1(k3_tarski(sK6))
    | v4_ordinal1(sK6) ),
    inference(resolution,[status(thm)],[c_9878,c_1])).

cnf(c_9944,plain,
    ( r2_hidden(k3_tarski(sK6),sK6) != iProver_top
    | v3_ordinal1(k3_tarski(sK6)) != iProver_top
    | v4_ordinal1(sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9943])).

cnf(c_10248,plain,
    ( r2_hidden(X1,sK7) != iProver_top
    | r2_hidden(X0,k3_tarski(k3_tarski(sK6))) = iProver_top
    | r2_hidden(X0,X1) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6948,c_37,c_107,c_2638,c_3250,c_3274,c_3277,c_3586,c_6337,c_9944])).

cnf(c_10249,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,k3_tarski(k3_tarski(sK6))) = iProver_top
    | r2_hidden(X1,sK7) != iProver_top ),
    inference(renaming,[status(thm)],[c_10248])).

cnf(c_10268,plain,
    ( r2_hidden(X0,sK6) != iProver_top
    | r2_hidden(k2_xboole_0(X0,k1_tarski(X0)),k3_tarski(k3_tarski(sK6))) = iProver_top
    | r2_hidden(sK6,sK7) != iProver_top
    | v3_ordinal1(X0) != iProver_top
    | v4_ordinal1(sK6) = iProver_top ),
    inference(superposition,[status(thm)],[c_1799,c_10249])).

cnf(c_10,plain,
    ( ~ v4_ordinal1(X0)
    | k3_tarski(X0) = X0 ),
    inference(cnf_transformation,[],[f70])).

cnf(c_100,plain,
    ( ~ v4_ordinal1(sK6)
    | k3_tarski(sK6) = sK6 ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_102,plain,
    ( k3_tarski(X0) != X0
    | v4_ordinal1(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_104,plain,
    ( k3_tarski(sK6) != sK6
    | v4_ordinal1(sK6) = iProver_top ),
    inference(instantiation,[status(thm)],[c_102])).

cnf(c_13,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,sK3(X1))
    | ~ v3_ordinal1(X0) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_29,plain,
    ( ~ r2_hidden(sK5(X0),X0) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_3539,plain,
    ( ~ r2_hidden(sK5(sK3(X0)),X0)
    | ~ v3_ordinal1(sK5(sK3(X0))) ),
    inference(resolution,[status(thm)],[c_13,c_29])).

cnf(c_30,plain,
    ( v3_ordinal1(sK5(X0)) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_4706,plain,
    ( ~ r2_hidden(sK5(sK3(X0)),X0) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_3539,c_30])).

cnf(c_9892,plain,
    ( ~ r2_hidden(sK5(sK3(k3_tarski(sK6))),sK6)
    | ~ v3_ordinal1(sK5(sK3(k3_tarski(sK6))))
    | v4_ordinal1(sK6) ),
    inference(resolution,[status(thm)],[c_9091,c_4706])).

cnf(c_99,plain,
    ( k3_tarski(X0) = X0
    | v4_ordinal1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_101,plain,
    ( k3_tarski(sK6) = sK6
    | v4_ordinal1(sK6) != iProver_top ),
    inference(instantiation,[status(thm)],[c_99])).

cnf(c_103,plain,
    ( v4_ordinal1(sK6)
    | k3_tarski(sK6) != sK6 ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_10439,plain,
    ( v4_ordinal1(sK6) ),
    inference(global_propositional_subsumption,[status(thm)],[c_9892,c_37,c_101,c_103,c_107,c_2638,c_3250,c_3274,c_3277,c_3586,c_6337,c_9944])).

cnf(c_10724,plain,
    ( v4_ordinal1(sK6) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_10268,c_37,c_107,c_2638,c_3250,c_3274,c_3277,c_3586,c_6337,c_9944])).

cnf(c_23,plain,
    ( ~ v3_ordinal1(X0)
    | v3_ordinal1(k2_xboole_0(X0,k1_tarski(X0))) ),
    inference(cnf_transformation,[],[f103])).

cnf(c_1808,plain,
    ( v3_ordinal1(X0) != iProver_top
    | v3_ordinal1(k2_xboole_0(X0,k1_tarski(X0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_1809,plain,
    ( X0 = X1
    | r2_hidden(X1,X0) = iProver_top
    | r2_hidden(X0,X1) = iProver_top
    | v3_ordinal1(X1) != iProver_top
    | v3_ordinal1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_32,negated_conjecture,
    ( ~ r2_hidden(k2_xboole_0(sK7,k1_tarski(sK7)),sK6)
    | ~ v4_ordinal1(sK6) ),
    inference(cnf_transformation,[],[f106])).

cnf(c_1802,plain,
    ( r2_hidden(k2_xboole_0(sK7,k1_tarski(sK7)),sK6) != iProver_top
    | v4_ordinal1(sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_6596,plain,
    ( k2_xboole_0(sK7,k1_tarski(sK7)) = sK6
    | r2_hidden(sK6,k2_xboole_0(sK7,k1_tarski(sK7))) = iProver_top
    | v3_ordinal1(k2_xboole_0(sK7,k1_tarski(sK7))) != iProver_top
    | v3_ordinal1(sK6) != iProver_top
    | v4_ordinal1(sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_1809,c_1802])).

cnf(c_34,negated_conjecture,
    ( v3_ordinal1(sK7)
    | ~ v4_ordinal1(sK6) ),
    inference(cnf_transformation,[],[f95])).

cnf(c_41,plain,
    ( v3_ordinal1(sK7) = iProver_top
    | v4_ordinal1(sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_1803,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_2922,plain,
    ( r1_tarski(sK6,sK7) != iProver_top
    | v4_ordinal1(sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_1801,c_1803])).

cnf(c_3233,plain,
    ( ~ r2_hidden(sK6,k2_xboole_0(sK7,k1_tarski(sK7)))
    | r1_tarski(sK6,sK7)
    | ~ v3_ordinal1(sK6)
    | ~ v3_ordinal1(sK7) ),
    inference(instantiation,[status(thm)],[c_577])).

cnf(c_3234,plain,
    ( r2_hidden(sK6,k2_xboole_0(sK7,k1_tarski(sK7))) != iProver_top
    | r1_tarski(sK6,sK7) = iProver_top
    | v3_ordinal1(sK6) != iProver_top
    | v3_ordinal1(sK7) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3233])).

cnf(c_7450,plain,
    ( v3_ordinal1(k2_xboole_0(sK7,k1_tarski(sK7))) != iProver_top
    | k2_xboole_0(sK7,k1_tarski(sK7)) = sK6
    | v4_ordinal1(sK6) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6596,c_37,c_41,c_2922,c_3234])).

cnf(c_7451,plain,
    ( k2_xboole_0(sK7,k1_tarski(sK7)) = sK6
    | v3_ordinal1(k2_xboole_0(sK7,k1_tarski(sK7))) != iProver_top
    | v4_ordinal1(sK6) != iProver_top ),
    inference(renaming,[status(thm)],[c_7450])).

cnf(c_7457,plain,
    ( k2_xboole_0(sK7,k1_tarski(sK7)) = sK6
    | v3_ordinal1(sK7) != iProver_top
    | v4_ordinal1(sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_1808,c_7451])).

cnf(c_8139,plain,
    ( k2_xboole_0(sK7,k1_tarski(sK7)) = sK6
    | v4_ordinal1(sK6) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_7457,c_41])).

cnf(c_10730,plain,
    ( k2_xboole_0(sK7,k1_tarski(sK7)) = sK6 ),
    inference(superposition,[status(thm)],[c_10724,c_8139])).

cnf(c_1797,plain,
    ( r2_hidden(X0,k2_xboole_0(X1,k1_tarski(X1))) != iProver_top
    | r1_tarski(X0,X1) = iProver_top
    | v3_ordinal1(X0) != iProver_top
    | v3_ordinal1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_577])).

cnf(c_11491,plain,
    ( r2_hidden(X0,sK6) != iProver_top
    | r1_tarski(X0,sK7) = iProver_top
    | v3_ordinal1(X0) != iProver_top
    | v3_ordinal1(sK7) != iProver_top ),
    inference(superposition,[status(thm)],[c_10730,c_1797])).

cnf(c_286,plain,
    ( v4_ordinal1(X0)
    | k3_tarski(X0) != X0 ),
    inference(prop_impl,[status(thm)],[c_9])).

cnf(c_506,plain,
    ( v3_ordinal1(sK7)
    | k3_tarski(X0) != X0
    | sK6 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_286,c_34])).

cnf(c_507,plain,
    ( v3_ordinal1(sK7)
    | k3_tarski(sK6) != sK6 ),
    inference(unflattening,[status(thm)],[c_506])).

cnf(c_508,plain,
    ( k3_tarski(sK6) != sK6
    | v3_ordinal1(sK7) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_507])).

cnf(c_18622,plain,
    ( v3_ordinal1(X0) != iProver_top
    | r1_tarski(X0,sK7) = iProver_top
    | r2_hidden(X0,sK6) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_11491,c_37,c_41,c_107,c_2638,c_3250,c_3274,c_3277,c_3586,c_6337,c_9944])).

cnf(c_18623,plain,
    ( r2_hidden(X0,sK6) != iProver_top
    | r1_tarski(X0,sK7) = iProver_top
    | v3_ordinal1(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_18622])).

cnf(c_18632,plain,
    ( r2_hidden(X0,k3_tarski(sK6)) != iProver_top
    | r1_tarski(sK2(sK6,X0),sK7) = iProver_top
    | v3_ordinal1(sK2(sK6,X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1820,c_18623])).

cnf(c_1817,plain,
    ( k3_tarski(X0) = X0
    | v4_ordinal1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_10729,plain,
    ( k3_tarski(sK6) = sK6 ),
    inference(superposition,[status(thm)],[c_10724,c_1817])).

cnf(c_18685,plain,
    ( r2_hidden(X0,sK6) != iProver_top
    | r1_tarski(sK2(sK6,X0),sK7) = iProver_top
    | v3_ordinal1(sK2(sK6,X0)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_18632,c_10729])).

cnf(c_1810,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | v3_ordinal1(X1) != iProver_top
    | v3_ordinal1(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_4878,plain,
    ( r2_hidden(X0,k3_tarski(X1)) != iProver_top
    | v3_ordinal1(X1) != iProver_top
    | v3_ordinal1(sK2(X1,X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1820,c_1810])).

cnf(c_16992,plain,
    ( r2_hidden(X0,sK6) != iProver_top
    | v3_ordinal1(sK2(sK6,X0)) = iProver_top
    | v3_ordinal1(sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_10729,c_4878])).

cnf(c_18820,plain,
    ( r1_tarski(sK2(sK6,X0),sK7) = iProver_top
    | r2_hidden(X0,sK6) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_18685,c_37,c_16992])).

cnf(c_18821,plain,
    ( r2_hidden(X0,sK6) != iProver_top
    | r1_tarski(sK2(sK6,X0),sK7) = iProver_top ),
    inference(renaming,[status(thm)],[c_18820])).

cnf(c_1819,plain,
    ( r2_hidden(X0,sK2(X1,X0)) = iProver_top
    | r2_hidden(X0,k3_tarski(X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_3513,plain,
    ( r2_hidden(X0,k3_tarski(X1)) != iProver_top
    | r1_tarski(sK2(X1,X0),X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1819,c_1803])).

cnf(c_18827,plain,
    ( r2_hidden(sK7,k3_tarski(sK6)) != iProver_top
    | r2_hidden(sK7,sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_18821,c_3513])).

cnf(c_18830,plain,
    ( r2_hidden(sK7,sK6) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_18827,c_10729])).

cnf(c_516,plain,
    ( r2_hidden(sK7,sK6)
    | k3_tarski(X0) != X0
    | sK6 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_286,c_33])).

cnf(c_517,plain,
    ( r2_hidden(sK7,sK6)
    | k3_tarski(sK6) != sK6 ),
    inference(unflattening,[status(thm)],[c_516])).

cnf(c_518,plain,
    ( k3_tarski(sK6) != sK6
    | r2_hidden(sK7,sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_517])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_18830,c_10439,c_518,c_100])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n001.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 14:00:00 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  % Running in FOF mode
% 3.86/0.97  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.86/0.97  
% 3.86/0.97  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.86/0.97  
% 3.86/0.97  ------  iProver source info
% 3.86/0.97  
% 3.86/0.97  git: date: 2020-06-30 10:37:57 +0100
% 3.86/0.97  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.86/0.97  git: non_committed_changes: false
% 3.86/0.97  git: last_make_outside_of_git: false
% 3.86/0.97  
% 3.86/0.97  ------ 
% 3.86/0.97  ------ Parsing...
% 3.86/0.97  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.86/0.97  
% 3.86/0.97  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 3.86/0.97  
% 3.86/0.97  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.86/0.97  
% 3.86/0.97  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.86/0.97  ------ Proving...
% 3.86/0.97  ------ Problem Properties 
% 3.86/0.97  
% 3.86/0.97  
% 3.86/0.97  clauses                                 34
% 3.86/0.97  conjectures                             5
% 3.86/0.97  EPR                                     8
% 3.86/0.97  Horn                                    26
% 3.86/0.97  unary                                   6
% 3.86/0.97  binary                                  14
% 3.86/0.97  lits                                    82
% 3.86/0.97  lits eq                                 9
% 3.86/0.97  fd_pure                                 0
% 3.86/0.97  fd_pseudo                               0
% 3.86/0.97  fd_cond                                 0
% 3.86/0.97  fd_pseudo_cond                          6
% 3.86/0.97  AC symbols                              0
% 3.86/0.97  
% 3.86/0.97  ------ Input Options Time Limit: Unbounded
% 3.86/0.97  
% 3.86/0.97  
% 3.86/0.97  ------ 
% 3.86/0.97  Current options:
% 3.86/0.97  ------ 
% 3.86/0.97  
% 3.86/0.97  
% 3.86/0.97  
% 3.86/0.97  
% 3.86/0.97  ------ Proving...
% 3.86/0.97  
% 3.86/0.97  
% 3.86/0.97  % SZS status Theorem for theBenchmark.p
% 3.86/0.97  
% 3.86/0.97  % SZS output start CNFRefutation for theBenchmark.p
% 3.86/0.97  
% 3.86/0.97  fof(f2,axiom,(
% 3.86/0.97    ! [X0,X1] : (k3_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (r2_hidden(X3,X0) & r2_hidden(X2,X3))))),
% 3.86/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.86/0.97  
% 3.86/0.97  fof(f35,plain,(
% 3.86/0.97    ! [X0,X1] : ((k3_tarski(X0) = X1 | ? [X2] : ((! [X3] : (~r2_hidden(X3,X0) | ~r2_hidden(X2,X3)) | ~r2_hidden(X2,X1)) & (? [X3] : (r2_hidden(X3,X0) & r2_hidden(X2,X3)) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ! [X3] : (~r2_hidden(X3,X0) | ~r2_hidden(X2,X3))) & (? [X3] : (r2_hidden(X3,X0) & r2_hidden(X2,X3)) | ~r2_hidden(X2,X1))) | k3_tarski(X0) != X1))),
% 3.86/0.97    inference(nnf_transformation,[],[f2])).
% 3.86/0.97  
% 3.86/0.97  fof(f36,plain,(
% 3.86/0.97    ! [X0,X1] : ((k3_tarski(X0) = X1 | ? [X2] : ((! [X3] : (~r2_hidden(X3,X0) | ~r2_hidden(X2,X3)) | ~r2_hidden(X2,X1)) & (? [X4] : (r2_hidden(X4,X0) & r2_hidden(X2,X4)) | r2_hidden(X2,X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : (~r2_hidden(X6,X0) | ~r2_hidden(X5,X6))) & (? [X7] : (r2_hidden(X7,X0) & r2_hidden(X5,X7)) | ~r2_hidden(X5,X1))) | k3_tarski(X0) != X1))),
% 3.86/0.97    inference(rectify,[],[f35])).
% 3.86/0.97  
% 3.86/0.97  fof(f39,plain,(
% 3.86/0.97    ! [X5,X0] : (? [X7] : (r2_hidden(X7,X0) & r2_hidden(X5,X7)) => (r2_hidden(sK2(X0,X5),X0) & r2_hidden(X5,sK2(X0,X5))))),
% 3.86/0.97    introduced(choice_axiom,[])).
% 3.86/0.97  
% 3.86/0.97  fof(f38,plain,(
% 3.86/0.97    ( ! [X2] : (! [X1,X0] : (? [X4] : (r2_hidden(X4,X0) & r2_hidden(X2,X4)) => (r2_hidden(sK1(X0,X1),X0) & r2_hidden(X2,sK1(X0,X1))))) )),
% 3.86/0.97    introduced(choice_axiom,[])).
% 3.86/0.97  
% 3.86/0.97  fof(f37,plain,(
% 3.86/0.97    ! [X1,X0] : (? [X2] : ((! [X3] : (~r2_hidden(X3,X0) | ~r2_hidden(X2,X3)) | ~r2_hidden(X2,X1)) & (? [X4] : (r2_hidden(X4,X0) & r2_hidden(X2,X4)) | r2_hidden(X2,X1))) => ((! [X3] : (~r2_hidden(X3,X0) | ~r2_hidden(sK0(X0,X1),X3)) | ~r2_hidden(sK0(X0,X1),X1)) & (? [X4] : (r2_hidden(X4,X0) & r2_hidden(sK0(X0,X1),X4)) | r2_hidden(sK0(X0,X1),X1))))),
% 3.86/0.97    introduced(choice_axiom,[])).
% 3.86/0.97  
% 3.86/0.97  fof(f40,plain,(
% 3.86/0.97    ! [X0,X1] : ((k3_tarski(X0) = X1 | ((! [X3] : (~r2_hidden(X3,X0) | ~r2_hidden(sK0(X0,X1),X3)) | ~r2_hidden(sK0(X0,X1),X1)) & ((r2_hidden(sK1(X0,X1),X0) & r2_hidden(sK0(X0,X1),sK1(X0,X1))) | r2_hidden(sK0(X0,X1),X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : (~r2_hidden(X6,X0) | ~r2_hidden(X5,X6))) & ((r2_hidden(sK2(X0,X5),X0) & r2_hidden(X5,sK2(X0,X5))) | ~r2_hidden(X5,X1))) | k3_tarski(X0) != X1))),
% 3.86/0.97    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f36,f39,f38,f37])).
% 3.86/0.97  
% 3.86/0.97  fof(f64,plain,(
% 3.86/0.97    ( ! [X0,X5,X1] : (r2_hidden(sK2(X0,X5),X0) | ~r2_hidden(X5,X1) | k3_tarski(X0) != X1) )),
% 3.86/0.97    inference(cnf_transformation,[],[f40])).
% 3.86/0.97  
% 3.86/0.97  fof(f111,plain,(
% 3.86/0.97    ( ! [X0,X5] : (r2_hidden(sK2(X0,X5),X0) | ~r2_hidden(X5,k3_tarski(X0))) )),
% 3.86/0.97    inference(equality_resolution,[],[f64])).
% 3.86/0.97  
% 3.86/0.97  fof(f17,conjecture,(
% 3.86/0.97    ! [X0] : (v3_ordinal1(X0) => (v4_ordinal1(X0) <=> ! [X1] : (v3_ordinal1(X1) => (r2_hidden(X1,X0) => r2_hidden(k1_ordinal1(X1),X0)))))),
% 3.86/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.86/0.97  
% 3.86/0.97  fof(f18,negated_conjecture,(
% 3.86/0.97    ~! [X0] : (v3_ordinal1(X0) => (v4_ordinal1(X0) <=> ! [X1] : (v3_ordinal1(X1) => (r2_hidden(X1,X0) => r2_hidden(k1_ordinal1(X1),X0)))))),
% 3.86/0.97    inference(negated_conjecture,[],[f17])).
% 3.86/0.97  
% 3.86/0.97  fof(f31,plain,(
% 3.86/0.97    ? [X0] : ((v4_ordinal1(X0) <~> ! [X1] : ((r2_hidden(k1_ordinal1(X1),X0) | ~r2_hidden(X1,X0)) | ~v3_ordinal1(X1))) & v3_ordinal1(X0))),
% 3.86/0.97    inference(ennf_transformation,[],[f18])).
% 3.86/0.97  
% 3.86/0.97  fof(f32,plain,(
% 3.86/0.97    ? [X0] : ((v4_ordinal1(X0) <~> ! [X1] : (r2_hidden(k1_ordinal1(X1),X0) | ~r2_hidden(X1,X0) | ~v3_ordinal1(X1))) & v3_ordinal1(X0))),
% 3.86/0.97    inference(flattening,[],[f31])).
% 3.86/0.97  
% 3.86/0.97  fof(f54,plain,(
% 3.86/0.97    ? [X0] : (((? [X1] : (~r2_hidden(k1_ordinal1(X1),X0) & r2_hidden(X1,X0) & v3_ordinal1(X1)) | ~v4_ordinal1(X0)) & (! [X1] : (r2_hidden(k1_ordinal1(X1),X0) | ~r2_hidden(X1,X0) | ~v3_ordinal1(X1)) | v4_ordinal1(X0))) & v3_ordinal1(X0))),
% 3.86/0.97    inference(nnf_transformation,[],[f32])).
% 3.86/0.97  
% 3.86/0.97  fof(f55,plain,(
% 3.86/0.97    ? [X0] : ((? [X1] : (~r2_hidden(k1_ordinal1(X1),X0) & r2_hidden(X1,X0) & v3_ordinal1(X1)) | ~v4_ordinal1(X0)) & (! [X1] : (r2_hidden(k1_ordinal1(X1),X0) | ~r2_hidden(X1,X0) | ~v3_ordinal1(X1)) | v4_ordinal1(X0)) & v3_ordinal1(X0))),
% 3.86/0.97    inference(flattening,[],[f54])).
% 3.86/0.97  
% 3.86/0.97  fof(f56,plain,(
% 3.86/0.97    ? [X0] : ((? [X1] : (~r2_hidden(k1_ordinal1(X1),X0) & r2_hidden(X1,X0) & v3_ordinal1(X1)) | ~v4_ordinal1(X0)) & (! [X2] : (r2_hidden(k1_ordinal1(X2),X0) | ~r2_hidden(X2,X0) | ~v3_ordinal1(X2)) | v4_ordinal1(X0)) & v3_ordinal1(X0))),
% 3.86/0.97    inference(rectify,[],[f55])).
% 3.86/0.97  
% 3.86/0.97  fof(f58,plain,(
% 3.86/0.97    ( ! [X0] : (? [X1] : (~r2_hidden(k1_ordinal1(X1),X0) & r2_hidden(X1,X0) & v3_ordinal1(X1)) => (~r2_hidden(k1_ordinal1(sK7),X0) & r2_hidden(sK7,X0) & v3_ordinal1(sK7))) )),
% 3.86/0.97    introduced(choice_axiom,[])).
% 3.86/0.97  
% 3.86/0.97  fof(f57,plain,(
% 3.86/0.97    ? [X0] : ((? [X1] : (~r2_hidden(k1_ordinal1(X1),X0) & r2_hidden(X1,X0) & v3_ordinal1(X1)) | ~v4_ordinal1(X0)) & (! [X2] : (r2_hidden(k1_ordinal1(X2),X0) | ~r2_hidden(X2,X0) | ~v3_ordinal1(X2)) | v4_ordinal1(X0)) & v3_ordinal1(X0)) => ((? [X1] : (~r2_hidden(k1_ordinal1(X1),sK6) & r2_hidden(X1,sK6) & v3_ordinal1(X1)) | ~v4_ordinal1(sK6)) & (! [X2] : (r2_hidden(k1_ordinal1(X2),sK6) | ~r2_hidden(X2,sK6) | ~v3_ordinal1(X2)) | v4_ordinal1(sK6)) & v3_ordinal1(sK6))),
% 3.86/0.97    introduced(choice_axiom,[])).
% 3.86/0.97  
% 3.86/0.97  fof(f59,plain,(
% 3.86/0.97    ((~r2_hidden(k1_ordinal1(sK7),sK6) & r2_hidden(sK7,sK6) & v3_ordinal1(sK7)) | ~v4_ordinal1(sK6)) & (! [X2] : (r2_hidden(k1_ordinal1(X2),sK6) | ~r2_hidden(X2,sK6) | ~v3_ordinal1(X2)) | v4_ordinal1(sK6)) & v3_ordinal1(sK6)),
% 3.86/0.97    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7])],[f56,f58,f57])).
% 3.86/0.97  
% 3.86/0.97  fof(f94,plain,(
% 3.86/0.97    ( ! [X2] : (r2_hidden(k1_ordinal1(X2),sK6) | ~r2_hidden(X2,sK6) | ~v3_ordinal1(X2) | v4_ordinal1(sK6)) )),
% 3.86/0.97    inference(cnf_transformation,[],[f59])).
% 3.86/0.97  
% 3.86/0.97  fof(f3,axiom,(
% 3.86/0.97    ! [X0] : k1_ordinal1(X0) = k2_xboole_0(X0,k1_tarski(X0))),
% 3.86/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.86/0.97  
% 3.86/0.97  fof(f69,plain,(
% 3.86/0.97    ( ! [X0] : (k1_ordinal1(X0) = k2_xboole_0(X0,k1_tarski(X0))) )),
% 3.86/0.97    inference(cnf_transformation,[],[f3])).
% 3.86/0.97  
% 3.86/0.97  fof(f107,plain,(
% 3.86/0.97    ( ! [X2] : (r2_hidden(k2_xboole_0(X2,k1_tarski(X2)),sK6) | ~r2_hidden(X2,sK6) | ~v3_ordinal1(X2) | v4_ordinal1(sK6)) )),
% 3.86/0.97    inference(definition_unfolding,[],[f94,f69])).
% 3.86/0.97  
% 3.86/0.97  fof(f96,plain,(
% 3.86/0.97    r2_hidden(sK7,sK6) | ~v4_ordinal1(sK6)),
% 3.86/0.97    inference(cnf_transformation,[],[f59])).
% 3.86/0.97  
% 3.86/0.97  fof(f65,plain,(
% 3.86/0.97    ( ! [X6,X0,X5,X1] : (r2_hidden(X5,X1) | ~r2_hidden(X6,X0) | ~r2_hidden(X5,X6) | k3_tarski(X0) != X1) )),
% 3.86/0.97    inference(cnf_transformation,[],[f40])).
% 3.86/0.97  
% 3.86/0.97  fof(f110,plain,(
% 3.86/0.97    ( ! [X6,X0,X5] : (r2_hidden(X5,k3_tarski(X0)) | ~r2_hidden(X6,X0) | ~r2_hidden(X5,X6)) )),
% 3.86/0.97    inference(equality_resolution,[],[f65])).
% 3.86/0.97  
% 3.86/0.97  fof(f93,plain,(
% 3.86/0.97    v3_ordinal1(sK6)),
% 3.86/0.97    inference(cnf_transformation,[],[f59])).
% 3.86/0.97  
% 3.86/0.97  fof(f63,plain,(
% 3.86/0.97    ( ! [X0,X5,X1] : (r2_hidden(X5,sK2(X0,X5)) | ~r2_hidden(X5,X1) | k3_tarski(X0) != X1) )),
% 3.86/0.97    inference(cnf_transformation,[],[f40])).
% 3.86/0.97  
% 3.86/0.97  fof(f112,plain,(
% 3.86/0.97    ( ! [X0,X5] : (r2_hidden(X5,sK2(X0,X5)) | ~r2_hidden(X5,k3_tarski(X0))) )),
% 3.86/0.97    inference(equality_resolution,[],[f63])).
% 3.86/0.97  
% 3.86/0.97  fof(f8,axiom,(
% 3.86/0.97    ! [X0,X1] : (r2_hidden(X0,k1_ordinal1(X1)) <=> (X0 = X1 | r2_hidden(X0,X1)))),
% 3.86/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.86/0.97  
% 3.86/0.97  fof(f47,plain,(
% 3.86/0.97    ! [X0,X1] : ((r2_hidden(X0,k1_ordinal1(X1)) | (X0 != X1 & ~r2_hidden(X0,X1))) & ((X0 = X1 | r2_hidden(X0,X1)) | ~r2_hidden(X0,k1_ordinal1(X1))))),
% 3.86/0.97    inference(nnf_transformation,[],[f8])).
% 3.86/0.97  
% 3.86/0.97  fof(f48,plain,(
% 3.86/0.97    ! [X0,X1] : ((r2_hidden(X0,k1_ordinal1(X1)) | (X0 != X1 & ~r2_hidden(X0,X1))) & (X0 = X1 | r2_hidden(X0,X1) | ~r2_hidden(X0,k1_ordinal1(X1))))),
% 3.86/0.97    inference(flattening,[],[f47])).
% 3.86/0.97  
% 3.86/0.97  fof(f79,plain,(
% 3.86/0.97    ( ! [X0,X1] : (r2_hidden(X0,k1_ordinal1(X1)) | ~r2_hidden(X0,X1)) )),
% 3.86/0.97    inference(cnf_transformation,[],[f48])).
% 3.86/0.97  
% 3.86/0.97  fof(f100,plain,(
% 3.86/0.97    ( ! [X0,X1] : (r2_hidden(X0,k2_xboole_0(X1,k1_tarski(X1))) | ~r2_hidden(X0,X1)) )),
% 3.86/0.97    inference(definition_unfolding,[],[f79,f69])).
% 3.86/0.97  
% 3.86/0.97  fof(f10,axiom,(
% 3.86/0.97    ! [X0,X1] : (v3_ordinal1(X1) => (r2_hidden(X0,X1) => v3_ordinal1(X0)))),
% 3.86/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.86/0.97  
% 3.86/0.97  fof(f21,plain,(
% 3.86/0.97    ! [X0,X1] : ((v3_ordinal1(X0) | ~r2_hidden(X0,X1)) | ~v3_ordinal1(X1))),
% 3.86/0.97    inference(ennf_transformation,[],[f10])).
% 3.86/0.97  
% 3.86/0.97  fof(f22,plain,(
% 3.86/0.97    ! [X0,X1] : (v3_ordinal1(X0) | ~r2_hidden(X0,X1) | ~v3_ordinal1(X1))),
% 3.86/0.97    inference(flattening,[],[f21])).
% 3.86/0.97  
% 3.86/0.97  fof(f82,plain,(
% 3.86/0.97    ( ! [X0,X1] : (v3_ordinal1(X0) | ~r2_hidden(X0,X1) | ~v3_ordinal1(X1)) )),
% 3.86/0.97    inference(cnf_transformation,[],[f22])).
% 3.86/0.97  
% 3.86/0.97  fof(f14,axiom,(
% 3.86/0.97    ! [X0] : (! [X1] : (r2_hidden(X1,X0) => v3_ordinal1(X1)) => v3_ordinal1(k3_tarski(X0)))),
% 3.86/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.86/0.97  
% 3.86/0.97  fof(f27,plain,(
% 3.86/0.97    ! [X0] : (v3_ordinal1(k3_tarski(X0)) | ? [X1] : (~v3_ordinal1(X1) & r2_hidden(X1,X0)))),
% 3.86/0.97    inference(ennf_transformation,[],[f14])).
% 3.86/0.97  
% 3.86/0.97  fof(f50,plain,(
% 3.86/0.97    ! [X0] : (? [X1] : (~v3_ordinal1(X1) & r2_hidden(X1,X0)) => (~v3_ordinal1(sK4(X0)) & r2_hidden(sK4(X0),X0)))),
% 3.86/0.97    introduced(choice_axiom,[])).
% 3.86/0.97  
% 3.86/0.97  fof(f51,plain,(
% 3.86/0.97    ! [X0] : (v3_ordinal1(k3_tarski(X0)) | (~v3_ordinal1(sK4(X0)) & r2_hidden(sK4(X0),X0)))),
% 3.86/0.97    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f27,f50])).
% 3.86/0.97  
% 3.86/0.97  fof(f87,plain,(
% 3.86/0.97    ( ! [X0] : (v3_ordinal1(k3_tarski(X0)) | r2_hidden(sK4(X0),X0)) )),
% 3.86/0.97    inference(cnf_transformation,[],[f51])).
% 3.86/0.97  
% 3.86/0.97  fof(f88,plain,(
% 3.86/0.97    ( ! [X0] : (v3_ordinal1(k3_tarski(X0)) | ~v3_ordinal1(sK4(X0))) )),
% 3.86/0.97    inference(cnf_transformation,[],[f51])).
% 3.86/0.97  
% 3.86/0.97  fof(f16,axiom,(
% 3.86/0.97    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 3.86/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.86/0.97  
% 3.86/0.97  fof(f30,plain,(
% 3.86/0.97    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 3.86/0.97    inference(ennf_transformation,[],[f16])).
% 3.86/0.97  
% 3.86/0.97  fof(f92,plain,(
% 3.86/0.97    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1)) )),
% 3.86/0.97    inference(cnf_transformation,[],[f30])).
% 3.86/0.97  
% 3.86/0.97  fof(f13,axiom,(
% 3.86/0.97    ! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => (r2_hidden(X0,k1_ordinal1(X1)) <=> r1_ordinal1(X0,X1))))),
% 3.86/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.86/0.97  
% 3.86/0.97  fof(f26,plain,(
% 3.86/0.97    ! [X0] : (! [X1] : ((r2_hidden(X0,k1_ordinal1(X1)) <=> r1_ordinal1(X0,X1)) | ~v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 3.86/0.97    inference(ennf_transformation,[],[f13])).
% 3.86/0.97  
% 3.86/0.97  fof(f49,plain,(
% 3.86/0.97    ! [X0] : (! [X1] : (((r2_hidden(X0,k1_ordinal1(X1)) | ~r1_ordinal1(X0,X1)) & (r1_ordinal1(X0,X1) | ~r2_hidden(X0,k1_ordinal1(X1)))) | ~v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 3.86/0.97    inference(nnf_transformation,[],[f26])).
% 3.86/0.97  
% 3.86/0.97  fof(f85,plain,(
% 3.86/0.97    ( ! [X0,X1] : (r1_ordinal1(X0,X1) | ~r2_hidden(X0,k1_ordinal1(X1)) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0)) )),
% 3.86/0.97    inference(cnf_transformation,[],[f49])).
% 3.86/0.97  
% 3.86/0.97  fof(f105,plain,(
% 3.86/0.97    ( ! [X0,X1] : (r1_ordinal1(X0,X1) | ~r2_hidden(X0,k2_xboole_0(X1,k1_tarski(X1))) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0)) )),
% 3.86/0.97    inference(definition_unfolding,[],[f85,f69])).
% 3.86/0.97  
% 3.86/0.97  fof(f5,axiom,(
% 3.86/0.97    ! [X0,X1] : ((v3_ordinal1(X1) & v3_ordinal1(X0)) => (r1_ordinal1(X0,X1) <=> r1_tarski(X0,X1)))),
% 3.86/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.86/0.97  
% 3.86/0.97  fof(f19,plain,(
% 3.86/0.97    ! [X0,X1] : ((r1_ordinal1(X0,X1) <=> r1_tarski(X0,X1)) | (~v3_ordinal1(X1) | ~v3_ordinal1(X0)))),
% 3.86/0.97    inference(ennf_transformation,[],[f5])).
% 3.86/0.97  
% 3.86/0.97  fof(f20,plain,(
% 3.86/0.97    ! [X0,X1] : ((r1_ordinal1(X0,X1) <=> r1_tarski(X0,X1)) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0))),
% 3.86/0.97    inference(flattening,[],[f19])).
% 3.86/0.97  
% 3.86/0.97  fof(f42,plain,(
% 3.86/0.97    ! [X0,X1] : (((r1_ordinal1(X0,X1) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~r1_ordinal1(X0,X1))) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0))),
% 3.86/0.97    inference(nnf_transformation,[],[f20])).
% 3.86/0.97  
% 3.86/0.97  fof(f72,plain,(
% 3.86/0.97    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r1_ordinal1(X0,X1) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0)) )),
% 3.86/0.97    inference(cnf_transformation,[],[f42])).
% 3.86/0.97  
% 3.86/0.97  fof(f11,axiom,(
% 3.86/0.97    ! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => ~(~r2_hidden(X1,X0) & X0 != X1 & ~r2_hidden(X0,X1))))),
% 3.86/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.86/0.97  
% 3.86/0.97  fof(f23,plain,(
% 3.86/0.97    ! [X0] : (! [X1] : ((r2_hidden(X1,X0) | X0 = X1 | r2_hidden(X0,X1)) | ~v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 3.86/0.97    inference(ennf_transformation,[],[f11])).
% 3.86/0.97  
% 3.86/0.97  fof(f24,plain,(
% 3.86/0.97    ! [X0] : (! [X1] : (r2_hidden(X1,X0) | X0 = X1 | r2_hidden(X0,X1) | ~v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 3.86/0.97    inference(flattening,[],[f23])).
% 3.86/0.97  
% 3.86/0.97  fof(f83,plain,(
% 3.86/0.97    ( ! [X0,X1] : (r2_hidden(X1,X0) | X0 = X1 | r2_hidden(X0,X1) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0)) )),
% 3.86/0.97    inference(cnf_transformation,[],[f24])).
% 3.86/0.97  
% 3.86/0.97  fof(f4,axiom,(
% 3.86/0.97    ! [X0] : (v4_ordinal1(X0) <=> k3_tarski(X0) = X0)),
% 3.86/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.86/0.97  
% 3.86/0.97  fof(f41,plain,(
% 3.86/0.97    ! [X0] : ((v4_ordinal1(X0) | k3_tarski(X0) != X0) & (k3_tarski(X0) = X0 | ~v4_ordinal1(X0)))),
% 3.86/0.97    inference(nnf_transformation,[],[f4])).
% 3.86/0.97  
% 3.86/0.97  fof(f71,plain,(
% 3.86/0.97    ( ! [X0] : (v4_ordinal1(X0) | k3_tarski(X0) != X0) )),
% 3.86/0.97    inference(cnf_transformation,[],[f41])).
% 3.86/0.97  
% 3.86/0.97  fof(f80,plain,(
% 3.86/0.97    ( ! [X0,X1] : (r2_hidden(X0,k1_ordinal1(X1)) | X0 != X1) )),
% 3.86/0.97    inference(cnf_transformation,[],[f48])).
% 3.86/0.97  
% 3.86/0.97  fof(f99,plain,(
% 3.86/0.97    ( ! [X0,X1] : (r2_hidden(X0,k2_xboole_0(X1,k1_tarski(X1))) | X0 != X1) )),
% 3.86/0.97    inference(definition_unfolding,[],[f80,f69])).
% 3.86/0.97  
% 3.86/0.97  fof(f113,plain,(
% 3.86/0.97    ( ! [X1] : (r2_hidden(X1,k2_xboole_0(X1,k1_tarski(X1)))) )),
% 3.86/0.97    inference(equality_resolution,[],[f99])).
% 3.86/0.97  
% 3.86/0.97  fof(f1,axiom,(
% 3.86/0.97    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 3.86/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.86/0.97  
% 3.86/0.97  fof(f33,plain,(
% 3.86/0.97    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.86/0.97    inference(nnf_transformation,[],[f1])).
% 3.86/0.97  
% 3.86/0.97  fof(f34,plain,(
% 3.86/0.97    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.86/0.97    inference(flattening,[],[f33])).
% 3.86/0.97  
% 3.86/0.97  fof(f61,plain,(
% 3.86/0.97    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 3.86/0.97    inference(cnf_transformation,[],[f34])).
% 3.86/0.97  
% 3.86/0.97  fof(f108,plain,(
% 3.86/0.97    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 3.86/0.97    inference(equality_resolution,[],[f61])).
% 3.86/0.97  
% 3.86/0.97  fof(f70,plain,(
% 3.86/0.97    ( ! [X0] : (k3_tarski(X0) = X0 | ~v4_ordinal1(X0)) )),
% 3.86/0.97    inference(cnf_transformation,[],[f41])).
% 3.86/0.97  
% 3.86/0.97  fof(f6,axiom,(
% 3.86/0.97    ! [X0] : ? [X1] : ! [X2] : (r2_hidden(X2,X1) <=> (v3_ordinal1(X2) & r2_hidden(X2,X0)))),
% 3.86/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.86/0.97  
% 3.86/0.97  fof(f43,plain,(
% 3.86/0.97    ! [X0] : ? [X1] : ! [X2] : ((r2_hidden(X2,X1) | (~v3_ordinal1(X2) | ~r2_hidden(X2,X0))) & ((v3_ordinal1(X2) & r2_hidden(X2,X0)) | ~r2_hidden(X2,X1)))),
% 3.86/0.97    inference(nnf_transformation,[],[f6])).
% 3.86/0.97  
% 3.86/0.97  fof(f44,plain,(
% 3.86/0.97    ! [X0] : ? [X1] : ! [X2] : ((r2_hidden(X2,X1) | ~v3_ordinal1(X2) | ~r2_hidden(X2,X0)) & ((v3_ordinal1(X2) & r2_hidden(X2,X0)) | ~r2_hidden(X2,X1)))),
% 3.86/0.97    inference(flattening,[],[f43])).
% 3.86/0.97  
% 3.86/0.97  fof(f45,plain,(
% 3.86/0.97    ! [X0] : (? [X1] : ! [X2] : ((r2_hidden(X2,X1) | ~v3_ordinal1(X2) | ~r2_hidden(X2,X0)) & ((v3_ordinal1(X2) & r2_hidden(X2,X0)) | ~r2_hidden(X2,X1))) => ! [X2] : ((r2_hidden(X2,sK3(X0)) | ~v3_ordinal1(X2) | ~r2_hidden(X2,X0)) & ((v3_ordinal1(X2) & r2_hidden(X2,X0)) | ~r2_hidden(X2,sK3(X0)))))),
% 3.86/0.97    introduced(choice_axiom,[])).
% 3.86/0.97  
% 3.86/0.97  fof(f46,plain,(
% 3.86/0.97    ! [X0] : ! [X2] : ((r2_hidden(X2,sK3(X0)) | ~v3_ordinal1(X2) | ~r2_hidden(X2,X0)) & ((v3_ordinal1(X2) & r2_hidden(X2,X0)) | ~r2_hidden(X2,sK3(X0))))),
% 3.86/0.97    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f44,f45])).
% 3.86/0.97  
% 3.86/0.97  fof(f76,plain,(
% 3.86/0.97    ( ! [X2,X0] : (r2_hidden(X2,sK3(X0)) | ~v3_ordinal1(X2) | ~r2_hidden(X2,X0)) )),
% 3.86/0.97    inference(cnf_transformation,[],[f46])).
% 3.86/0.97  
% 3.86/0.97  fof(f15,axiom,(
% 3.86/0.97    ! [X0] : ? [X1] : (! [X2] : (v3_ordinal1(X2) => (~r2_hidden(X2,X0) => r1_ordinal1(X1,X2))) & ~r2_hidden(X1,X0) & v3_ordinal1(X1))),
% 3.86/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.86/0.97  
% 3.86/0.97  fof(f28,plain,(
% 3.86/0.97    ! [X0] : ? [X1] : (! [X2] : ((r1_ordinal1(X1,X2) | r2_hidden(X2,X0)) | ~v3_ordinal1(X2)) & ~r2_hidden(X1,X0) & v3_ordinal1(X1))),
% 3.86/0.97    inference(ennf_transformation,[],[f15])).
% 3.86/0.97  
% 3.86/0.97  fof(f29,plain,(
% 3.86/0.97    ! [X0] : ? [X1] : (! [X2] : (r1_ordinal1(X1,X2) | r2_hidden(X2,X0) | ~v3_ordinal1(X2)) & ~r2_hidden(X1,X0) & v3_ordinal1(X1))),
% 3.86/0.97    inference(flattening,[],[f28])).
% 3.86/0.97  
% 3.86/0.97  fof(f52,plain,(
% 3.86/0.97    ! [X0] : (? [X1] : (! [X2] : (r1_ordinal1(X1,X2) | r2_hidden(X2,X0) | ~v3_ordinal1(X2)) & ~r2_hidden(X1,X0) & v3_ordinal1(X1)) => (! [X2] : (r1_ordinal1(sK5(X0),X2) | r2_hidden(X2,X0) | ~v3_ordinal1(X2)) & ~r2_hidden(sK5(X0),X0) & v3_ordinal1(sK5(X0))))),
% 3.86/0.97    introduced(choice_axiom,[])).
% 3.86/0.97  
% 3.86/0.97  fof(f53,plain,(
% 3.86/0.97    ! [X0] : (! [X2] : (r1_ordinal1(sK5(X0),X2) | r2_hidden(X2,X0) | ~v3_ordinal1(X2)) & ~r2_hidden(sK5(X0),X0) & v3_ordinal1(sK5(X0)))),
% 3.86/0.97    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f29,f52])).
% 3.86/0.97  
% 3.86/0.97  fof(f90,plain,(
% 3.86/0.97    ( ! [X0] : (~r2_hidden(sK5(X0),X0)) )),
% 3.86/0.97    inference(cnf_transformation,[],[f53])).
% 3.86/0.97  
% 3.86/0.97  fof(f89,plain,(
% 3.86/0.97    ( ! [X0] : (v3_ordinal1(sK5(X0))) )),
% 3.86/0.97    inference(cnf_transformation,[],[f53])).
% 3.86/0.97  
% 3.86/0.97  fof(f12,axiom,(
% 3.86/0.97    ! [X0] : (v3_ordinal1(X0) => v3_ordinal1(k1_ordinal1(X0)))),
% 3.86/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.86/0.97  
% 3.86/0.97  fof(f25,plain,(
% 3.86/0.97    ! [X0] : (v3_ordinal1(k1_ordinal1(X0)) | ~v3_ordinal1(X0))),
% 3.86/0.97    inference(ennf_transformation,[],[f12])).
% 3.86/0.97  
% 3.86/0.97  fof(f84,plain,(
% 3.86/0.97    ( ! [X0] : (v3_ordinal1(k1_ordinal1(X0)) | ~v3_ordinal1(X0)) )),
% 3.86/0.97    inference(cnf_transformation,[],[f25])).
% 3.86/0.97  
% 3.86/0.97  fof(f103,plain,(
% 3.86/0.97    ( ! [X0] : (v3_ordinal1(k2_xboole_0(X0,k1_tarski(X0))) | ~v3_ordinal1(X0)) )),
% 3.86/0.97    inference(definition_unfolding,[],[f84,f69])).
% 3.86/0.97  
% 3.86/0.97  fof(f97,plain,(
% 3.86/0.97    ~r2_hidden(k1_ordinal1(sK7),sK6) | ~v4_ordinal1(sK6)),
% 3.86/0.97    inference(cnf_transformation,[],[f59])).
% 3.86/0.97  
% 3.86/0.97  fof(f106,plain,(
% 3.86/0.97    ~r2_hidden(k2_xboole_0(sK7,k1_tarski(sK7)),sK6) | ~v4_ordinal1(sK6)),
% 3.86/0.97    inference(definition_unfolding,[],[f97,f69])).
% 3.86/0.97  
% 3.86/0.97  fof(f95,plain,(
% 3.86/0.97    v3_ordinal1(sK7) | ~v4_ordinal1(sK6)),
% 3.86/0.97    inference(cnf_transformation,[],[f59])).
% 3.86/0.97  
% 3.86/0.97  cnf(c_7,plain,
% 3.86/0.97      ( ~ r2_hidden(X0,k3_tarski(X1)) | r2_hidden(sK2(X1,X0),X1) ),
% 3.86/0.97      inference(cnf_transformation,[],[f111]) ).
% 3.86/0.97  
% 3.86/0.97  cnf(c_1820,plain,
% 3.86/0.97      ( r2_hidden(X0,k3_tarski(X1)) != iProver_top
% 3.86/0.97      | r2_hidden(sK2(X1,X0),X1) = iProver_top ),
% 3.86/0.97      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 3.86/0.97  
% 3.86/0.97  cnf(c_35,negated_conjecture,
% 3.86/0.97      ( ~ r2_hidden(X0,sK6)
% 3.86/0.97      | r2_hidden(k2_xboole_0(X0,k1_tarski(X0)),sK6)
% 3.86/0.97      | ~ v3_ordinal1(X0)
% 3.86/0.97      | v4_ordinal1(sK6) ),
% 3.86/0.97      inference(cnf_transformation,[],[f107]) ).
% 3.86/0.97  
% 3.86/0.97  cnf(c_1799,plain,
% 3.86/0.97      ( r2_hidden(X0,sK6) != iProver_top
% 3.86/0.97      | r2_hidden(k2_xboole_0(X0,k1_tarski(X0)),sK6) = iProver_top
% 3.86/0.97      | v3_ordinal1(X0) != iProver_top
% 3.86/0.97      | v4_ordinal1(sK6) = iProver_top ),
% 3.86/0.97      inference(predicate_to_equality,[status(thm)],[c_35]) ).
% 3.86/0.97  
% 3.86/0.97  cnf(c_33,negated_conjecture,
% 3.86/0.97      ( r2_hidden(sK7,sK6) | ~ v4_ordinal1(sK6) ),
% 3.86/0.97      inference(cnf_transformation,[],[f96]) ).
% 3.86/0.97  
% 3.86/0.97  cnf(c_1801,plain,
% 3.86/0.97      ( r2_hidden(sK7,sK6) = iProver_top
% 3.86/0.97      | v4_ordinal1(sK6) != iProver_top ),
% 3.86/0.97      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 3.86/0.97  
% 3.86/0.97  cnf(c_6,plain,
% 3.86/0.97      ( ~ r2_hidden(X0,X1)
% 3.86/0.97      | ~ r2_hidden(X2,X0)
% 3.86/0.97      | r2_hidden(X2,k3_tarski(X1)) ),
% 3.86/0.97      inference(cnf_transformation,[],[f110]) ).
% 3.86/0.97  
% 3.86/0.97  cnf(c_1821,plain,
% 3.86/0.97      ( r2_hidden(X0,X1) != iProver_top
% 3.86/0.97      | r2_hidden(X2,X0) != iProver_top
% 3.86/0.97      | r2_hidden(X2,k3_tarski(X1)) = iProver_top ),
% 3.86/0.97      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 3.86/0.97  
% 3.86/0.97  cnf(c_6035,plain,
% 3.86/0.97      ( r2_hidden(X0,k3_tarski(sK6)) = iProver_top
% 3.86/0.97      | r2_hidden(X0,sK7) != iProver_top
% 3.86/0.97      | v4_ordinal1(sK6) != iProver_top ),
% 3.86/0.97      inference(superposition,[status(thm)],[c_1801,c_1821]) ).
% 3.86/0.97  
% 3.86/0.97  cnf(c_6948,plain,
% 3.86/0.97      ( r2_hidden(X0,X1) != iProver_top
% 3.86/0.97      | r2_hidden(X0,k3_tarski(k3_tarski(sK6))) = iProver_top
% 3.86/0.97      | r2_hidden(X1,sK7) != iProver_top
% 3.86/0.97      | v4_ordinal1(sK6) != iProver_top ),
% 3.86/0.97      inference(superposition,[status(thm)],[c_6035,c_1821]) ).
% 3.86/0.97  
% 3.86/0.97  cnf(c_36,negated_conjecture,
% 3.86/0.97      ( v3_ordinal1(sK6) ),
% 3.86/0.97      inference(cnf_transformation,[],[f93]) ).
% 3.86/0.97  
% 3.86/0.97  cnf(c_37,plain,
% 3.86/0.97      ( v3_ordinal1(sK6) = iProver_top ),
% 3.86/0.97      inference(predicate_to_equality,[status(thm)],[c_36]) ).
% 3.86/0.97  
% 3.86/0.97  cnf(c_8,plain,
% 3.86/0.97      ( r2_hidden(X0,sK2(X1,X0)) | ~ r2_hidden(X0,k3_tarski(X1)) ),
% 3.86/0.97      inference(cnf_transformation,[],[f112]) ).
% 3.86/0.97  
% 3.86/0.97  cnf(c_105,plain,
% 3.86/0.97      ( r2_hidden(X0,sK2(X1,X0)) = iProver_top
% 3.86/0.97      | r2_hidden(X0,k3_tarski(X1)) != iProver_top ),
% 3.86/0.97      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 3.86/0.97  
% 3.86/0.97  cnf(c_107,plain,
% 3.86/0.97      ( r2_hidden(sK6,sK2(sK6,sK6)) = iProver_top
% 3.86/0.97      | r2_hidden(sK6,k3_tarski(sK6)) != iProver_top ),
% 3.86/0.97      inference(instantiation,[status(thm)],[c_105]) ).
% 3.86/0.97  
% 3.86/0.97  cnf(c_18,plain,
% 3.86/0.97      ( ~ r2_hidden(X0,X1)
% 3.86/0.97      | r2_hidden(X0,k2_xboole_0(X1,k1_tarski(X1))) ),
% 3.86/0.97      inference(cnf_transformation,[],[f100]) ).
% 3.86/0.97  
% 3.86/0.97  cnf(c_2625,plain,
% 3.86/0.97      ( r2_hidden(X0,k2_xboole_0(sK2(X1,X0),k1_tarski(sK2(X1,X0))))
% 3.86/0.97      | ~ r2_hidden(X0,sK2(X1,X0)) ),
% 3.86/0.97      inference(instantiation,[status(thm)],[c_18]) ).
% 3.86/0.97  
% 3.86/0.97  cnf(c_2636,plain,
% 3.86/0.97      ( r2_hidden(X0,k2_xboole_0(sK2(X1,X0),k1_tarski(sK2(X1,X0)))) = iProver_top
% 3.86/0.97      | r2_hidden(X0,sK2(X1,X0)) != iProver_top ),
% 3.86/0.97      inference(predicate_to_equality,[status(thm)],[c_2625]) ).
% 3.86/0.97  
% 3.86/0.97  cnf(c_2638,plain,
% 3.86/0.97      ( r2_hidden(sK6,k2_xboole_0(sK2(sK6,sK6),k1_tarski(sK2(sK6,sK6)))) = iProver_top
% 3.86/0.97      | r2_hidden(sK6,sK2(sK6,sK6)) != iProver_top ),
% 3.86/0.97      inference(instantiation,[status(thm)],[c_2636]) ).
% 3.86/0.97  
% 3.86/0.97  cnf(c_21,plain,
% 3.86/0.97      ( ~ r2_hidden(X0,X1) | ~ v3_ordinal1(X1) | v3_ordinal1(X0) ),
% 3.86/0.97      inference(cnf_transformation,[],[f82]) ).
% 3.86/0.97  
% 3.86/0.97  cnf(c_27,plain,
% 3.86/0.97      ( r2_hidden(sK4(X0),X0) | v3_ordinal1(k3_tarski(X0)) ),
% 3.86/0.97      inference(cnf_transformation,[],[f87]) ).
% 3.86/0.97  
% 3.86/0.97  cnf(c_3167,plain,
% 3.86/0.97      ( ~ v3_ordinal1(X0)
% 3.86/0.97      | v3_ordinal1(sK4(X0))
% 3.86/0.97      | v3_ordinal1(k3_tarski(X0)) ),
% 3.86/0.97      inference(resolution,[status(thm)],[c_21,c_27]) ).
% 3.86/0.97  
% 3.86/0.97  cnf(c_26,plain,
% 3.86/0.97      ( ~ v3_ordinal1(sK4(X0)) | v3_ordinal1(k3_tarski(X0)) ),
% 3.86/0.97      inference(cnf_transformation,[],[f88]) ).
% 3.86/0.97  
% 3.86/0.97  cnf(c_3246,plain,
% 3.86/0.97      ( ~ v3_ordinal1(X0) | v3_ordinal1(k3_tarski(X0)) ),
% 3.86/0.97      inference(global_propositional_subsumption,
% 3.86/0.97                [status(thm)],
% 3.86/0.97                [c_3167,c_26]) ).
% 3.86/0.97  
% 3.86/0.97  cnf(c_3248,plain,
% 3.86/0.97      ( v3_ordinal1(X0) != iProver_top
% 3.86/0.97      | v3_ordinal1(k3_tarski(X0)) = iProver_top ),
% 3.86/0.97      inference(predicate_to_equality,[status(thm)],[c_3246]) ).
% 3.86/0.97  
% 3.86/0.97  cnf(c_3250,plain,
% 3.86/0.97      ( v3_ordinal1(k3_tarski(sK6)) = iProver_top
% 3.86/0.97      | v3_ordinal1(sK6) != iProver_top ),
% 3.86/0.97      inference(instantiation,[status(thm)],[c_3248]) ).
% 3.86/0.97  
% 3.86/0.97  cnf(c_3271,plain,
% 3.86/0.97      ( ~ r2_hidden(X0,k3_tarski(X1))
% 3.86/0.97      | ~ v3_ordinal1(X1)
% 3.86/0.97      | v3_ordinal1(sK2(X1,X0)) ),
% 3.86/0.97      inference(resolution,[status(thm)],[c_7,c_21]) ).
% 3.86/0.97  
% 3.86/0.97  cnf(c_3272,plain,
% 3.86/0.97      ( r2_hidden(X0,k3_tarski(X1)) != iProver_top
% 3.86/0.97      | v3_ordinal1(X1) != iProver_top
% 3.86/0.97      | v3_ordinal1(sK2(X1,X0)) = iProver_top ),
% 3.86/0.97      inference(predicate_to_equality,[status(thm)],[c_3271]) ).
% 3.86/0.97  
% 3.86/0.97  cnf(c_3274,plain,
% 3.86/0.97      ( r2_hidden(sK6,k3_tarski(sK6)) != iProver_top
% 3.86/0.97      | v3_ordinal1(sK2(sK6,sK6)) = iProver_top
% 3.86/0.97      | v3_ordinal1(sK6) != iProver_top ),
% 3.86/0.97      inference(instantiation,[status(thm)],[c_3272]) ).
% 3.86/0.97  
% 3.86/0.97  cnf(c_31,plain,
% 3.86/0.97      ( ~ r2_hidden(X0,X1) | ~ r1_tarski(X1,X0) ),
% 3.86/0.97      inference(cnf_transformation,[],[f92]) ).
% 3.86/0.97  
% 3.86/0.97  cnf(c_3270,plain,
% 3.86/0.97      ( ~ r2_hidden(X0,k3_tarski(X1)) | ~ r1_tarski(X1,sK2(X1,X0)) ),
% 3.86/0.97      inference(resolution,[status(thm)],[c_7,c_31]) ).
% 3.86/0.97  
% 3.86/0.97  cnf(c_3275,plain,
% 3.86/0.97      ( r2_hidden(X0,k3_tarski(X1)) != iProver_top
% 3.86/0.97      | r1_tarski(X1,sK2(X1,X0)) != iProver_top ),
% 3.86/0.97      inference(predicate_to_equality,[status(thm)],[c_3270]) ).
% 3.86/0.97  
% 3.86/0.97  cnf(c_3277,plain,
% 3.86/0.97      ( r2_hidden(sK6,k3_tarski(sK6)) != iProver_top
% 3.86/0.97      | r1_tarski(sK6,sK2(sK6,sK6)) != iProver_top ),
% 3.86/0.97      inference(instantiation,[status(thm)],[c_3275]) ).
% 3.86/0.97  
% 3.86/0.97  cnf(c_25,plain,
% 3.86/0.97      ( r1_ordinal1(X0,X1)
% 3.86/0.97      | ~ r2_hidden(X0,k2_xboole_0(X1,k1_tarski(X1)))
% 3.86/0.97      | ~ v3_ordinal1(X1)
% 3.86/0.97      | ~ v3_ordinal1(X0) ),
% 3.86/0.97      inference(cnf_transformation,[],[f105]) ).
% 3.86/0.97  
% 3.86/0.97  cnf(c_12,plain,
% 3.86/0.97      ( ~ r1_ordinal1(X0,X1)
% 3.86/0.98      | r1_tarski(X0,X1)
% 3.86/0.98      | ~ v3_ordinal1(X1)
% 3.86/0.98      | ~ v3_ordinal1(X0) ),
% 3.86/0.98      inference(cnf_transformation,[],[f72]) ).
% 3.86/0.98  
% 3.86/0.98  cnf(c_577,plain,
% 3.86/0.98      ( ~ r2_hidden(X0,k2_xboole_0(X1,k1_tarski(X1)))
% 3.86/0.98      | r1_tarski(X0,X1)
% 3.86/0.98      | ~ v3_ordinal1(X1)
% 3.86/0.98      | ~ v3_ordinal1(X0) ),
% 3.86/0.98      inference(resolution,[status(thm)],[c_25,c_12]) ).
% 3.86/0.98  
% 3.86/0.98  cnf(c_3583,plain,
% 3.86/0.98      ( ~ r2_hidden(X0,k2_xboole_0(sK2(X0,X1),k1_tarski(sK2(X0,X1))))
% 3.86/0.98      | r1_tarski(X0,sK2(X0,X1))
% 3.86/0.98      | ~ v3_ordinal1(X0)
% 3.86/0.98      | ~ v3_ordinal1(sK2(X0,X1)) ),
% 3.86/0.98      inference(instantiation,[status(thm)],[c_577]) ).
% 3.86/0.98  
% 3.86/0.98  cnf(c_3584,plain,
% 3.86/0.98      ( r2_hidden(X0,k2_xboole_0(sK2(X0,X1),k1_tarski(sK2(X0,X1)))) != iProver_top
% 3.86/0.98      | r1_tarski(X0,sK2(X0,X1)) = iProver_top
% 3.86/0.98      | v3_ordinal1(X0) != iProver_top
% 3.86/0.98      | v3_ordinal1(sK2(X0,X1)) != iProver_top ),
% 3.86/0.98      inference(predicate_to_equality,[status(thm)],[c_3583]) ).
% 3.86/0.98  
% 3.86/0.98  cnf(c_3586,plain,
% 3.86/0.98      ( r2_hidden(sK6,k2_xboole_0(sK2(sK6,sK6),k1_tarski(sK2(sK6,sK6)))) != iProver_top
% 3.86/0.98      | r1_tarski(sK6,sK2(sK6,sK6)) = iProver_top
% 3.86/0.98      | v3_ordinal1(sK2(sK6,sK6)) != iProver_top
% 3.86/0.98      | v3_ordinal1(sK6) != iProver_top ),
% 3.86/0.98      inference(instantiation,[status(thm)],[c_3584]) ).
% 3.86/0.98  
% 3.86/0.98  cnf(c_22,plain,
% 3.86/0.98      ( r2_hidden(X0,X1)
% 3.86/0.98      | r2_hidden(X1,X0)
% 3.86/0.98      | ~ v3_ordinal1(X1)
% 3.86/0.98      | ~ v3_ordinal1(X0)
% 3.86/0.98      | X1 = X0 ),
% 3.86/0.98      inference(cnf_transformation,[],[f83]) ).
% 3.86/0.98  
% 3.86/0.98  cnf(c_9,plain,
% 3.86/0.98      ( v4_ordinal1(X0) | k3_tarski(X0) != X0 ),
% 3.86/0.98      inference(cnf_transformation,[],[f71]) ).
% 3.86/0.98  
% 3.86/0.98  cnf(c_6334,plain,
% 3.86/0.98      ( r2_hidden(X0,k3_tarski(X0))
% 3.86/0.98      | r2_hidden(k3_tarski(X0),X0)
% 3.86/0.98      | ~ v3_ordinal1(X0)
% 3.86/0.98      | ~ v3_ordinal1(k3_tarski(X0))
% 3.86/0.98      | v4_ordinal1(X0) ),
% 3.86/0.98      inference(resolution,[status(thm)],[c_22,c_9]) ).
% 3.86/0.98  
% 3.86/0.98  cnf(c_6335,plain,
% 3.86/0.98      ( r2_hidden(X0,k3_tarski(X0)) = iProver_top
% 3.86/0.98      | r2_hidden(k3_tarski(X0),X0) = iProver_top
% 3.86/0.98      | v3_ordinal1(X0) != iProver_top
% 3.86/0.98      | v3_ordinal1(k3_tarski(X0)) != iProver_top
% 3.86/0.98      | v4_ordinal1(X0) = iProver_top ),
% 3.86/0.98      inference(predicate_to_equality,[status(thm)],[c_6334]) ).
% 3.86/0.98  
% 3.86/0.98  cnf(c_6337,plain,
% 3.86/0.98      ( r2_hidden(k3_tarski(sK6),sK6) = iProver_top
% 3.86/0.98      | r2_hidden(sK6,k3_tarski(sK6)) = iProver_top
% 3.86/0.98      | v3_ordinal1(k3_tarski(sK6)) != iProver_top
% 3.86/0.98      | v3_ordinal1(sK6) != iProver_top
% 3.86/0.98      | v4_ordinal1(sK6) = iProver_top ),
% 3.86/0.98      inference(instantiation,[status(thm)],[c_6335]) ).
% 3.86/0.98  
% 3.86/0.98  cnf(c_17,plain,
% 3.86/0.98      ( r2_hidden(X0,k2_xboole_0(X0,k1_tarski(X0))) ),
% 3.86/0.98      inference(cnf_transformation,[],[f113]) ).
% 3.86/0.98  
% 3.86/0.98  cnf(c_4820,plain,
% 3.86/0.98      ( r2_hidden(X0,k3_tarski(X1))
% 3.86/0.98      | ~ r2_hidden(k2_xboole_0(X0,k1_tarski(X0)),X1) ),
% 3.86/0.98      inference(resolution,[status(thm)],[c_6,c_17]) ).
% 3.86/0.98  
% 3.86/0.98  cnf(c_9091,plain,
% 3.86/0.98      ( r2_hidden(X0,k3_tarski(sK6))
% 3.86/0.98      | ~ r2_hidden(X0,sK6)
% 3.86/0.98      | ~ v3_ordinal1(X0)
% 3.86/0.98      | v4_ordinal1(sK6) ),
% 3.86/0.98      inference(resolution,[status(thm)],[c_4820,c_35]) ).
% 3.86/0.98  
% 3.86/0.98  cnf(c_9878,plain,
% 3.86/0.98      ( ~ r2_hidden(X0,sK6)
% 3.86/0.98      | ~ r1_tarski(k3_tarski(sK6),X0)
% 3.86/0.98      | ~ v3_ordinal1(X0)
% 3.86/0.98      | v4_ordinal1(sK6) ),
% 3.86/0.98      inference(resolution,[status(thm)],[c_9091,c_31]) ).
% 3.86/0.98  
% 3.86/0.98  cnf(c_1,plain,
% 3.86/0.98      ( r1_tarski(X0,X0) ),
% 3.86/0.98      inference(cnf_transformation,[],[f108]) ).
% 3.86/0.98  
% 3.86/0.98  cnf(c_9943,plain,
% 3.86/0.98      ( ~ r2_hidden(k3_tarski(sK6),sK6)
% 3.86/0.98      | ~ v3_ordinal1(k3_tarski(sK6))
% 3.86/0.98      | v4_ordinal1(sK6) ),
% 3.86/0.98      inference(resolution,[status(thm)],[c_9878,c_1]) ).
% 3.86/0.98  
% 3.86/0.98  cnf(c_9944,plain,
% 3.86/0.98      ( r2_hidden(k3_tarski(sK6),sK6) != iProver_top
% 3.86/0.98      | v3_ordinal1(k3_tarski(sK6)) != iProver_top
% 3.86/0.98      | v4_ordinal1(sK6) = iProver_top ),
% 3.86/0.98      inference(predicate_to_equality,[status(thm)],[c_9943]) ).
% 3.86/0.98  
% 3.86/0.98  cnf(c_10248,plain,
% 3.86/0.98      ( r2_hidden(X1,sK7) != iProver_top
% 3.86/0.98      | r2_hidden(X0,k3_tarski(k3_tarski(sK6))) = iProver_top
% 3.86/0.98      | r2_hidden(X0,X1) != iProver_top ),
% 3.86/0.98      inference(global_propositional_subsumption,
% 3.86/0.98                [status(thm)],
% 3.86/0.98                [c_6948,c_37,c_107,c_2638,c_3250,c_3274,c_3277,c_3586,
% 3.86/0.98                 c_6337,c_9944]) ).
% 3.86/0.98  
% 3.86/0.98  cnf(c_10249,plain,
% 3.86/0.98      ( r2_hidden(X0,X1) != iProver_top
% 3.86/0.98      | r2_hidden(X0,k3_tarski(k3_tarski(sK6))) = iProver_top
% 3.86/0.98      | r2_hidden(X1,sK7) != iProver_top ),
% 3.86/0.98      inference(renaming,[status(thm)],[c_10248]) ).
% 3.86/0.98  
% 3.86/0.98  cnf(c_10268,plain,
% 3.86/0.98      ( r2_hidden(X0,sK6) != iProver_top
% 3.86/0.98      | r2_hidden(k2_xboole_0(X0,k1_tarski(X0)),k3_tarski(k3_tarski(sK6))) = iProver_top
% 3.86/0.98      | r2_hidden(sK6,sK7) != iProver_top
% 3.86/0.98      | v3_ordinal1(X0) != iProver_top
% 3.86/0.98      | v4_ordinal1(sK6) = iProver_top ),
% 3.86/0.98      inference(superposition,[status(thm)],[c_1799,c_10249]) ).
% 3.86/0.98  
% 3.86/0.98  cnf(c_10,plain,
% 3.86/0.98      ( ~ v4_ordinal1(X0) | k3_tarski(X0) = X0 ),
% 3.86/0.98      inference(cnf_transformation,[],[f70]) ).
% 3.86/0.98  
% 3.86/0.98  cnf(c_100,plain,
% 3.86/0.98      ( ~ v4_ordinal1(sK6) | k3_tarski(sK6) = sK6 ),
% 3.86/0.98      inference(instantiation,[status(thm)],[c_10]) ).
% 3.86/0.98  
% 3.86/0.98  cnf(c_102,plain,
% 3.86/0.98      ( k3_tarski(X0) != X0 | v4_ordinal1(X0) = iProver_top ),
% 3.86/0.98      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 3.86/0.98  
% 3.86/0.98  cnf(c_104,plain,
% 3.86/0.98      ( k3_tarski(sK6) != sK6 | v4_ordinal1(sK6) = iProver_top ),
% 3.86/0.98      inference(instantiation,[status(thm)],[c_102]) ).
% 3.86/0.98  
% 3.86/0.98  cnf(c_13,plain,
% 3.86/0.98      ( ~ r2_hidden(X0,X1) | r2_hidden(X0,sK3(X1)) | ~ v3_ordinal1(X0) ),
% 3.86/0.98      inference(cnf_transformation,[],[f76]) ).
% 3.86/0.98  
% 3.86/0.98  cnf(c_29,plain,
% 3.86/0.98      ( ~ r2_hidden(sK5(X0),X0) ),
% 3.86/0.98      inference(cnf_transformation,[],[f90]) ).
% 3.86/0.98  
% 3.86/0.98  cnf(c_3539,plain,
% 3.86/0.98      ( ~ r2_hidden(sK5(sK3(X0)),X0) | ~ v3_ordinal1(sK5(sK3(X0))) ),
% 3.86/0.98      inference(resolution,[status(thm)],[c_13,c_29]) ).
% 3.86/0.98  
% 3.86/0.98  cnf(c_30,plain,
% 3.86/0.98      ( v3_ordinal1(sK5(X0)) ),
% 3.86/0.98      inference(cnf_transformation,[],[f89]) ).
% 3.86/0.98  
% 3.86/0.98  cnf(c_4706,plain,
% 3.86/0.98      ( ~ r2_hidden(sK5(sK3(X0)),X0) ),
% 3.86/0.98      inference(forward_subsumption_resolution,
% 3.86/0.98                [status(thm)],
% 3.86/0.98                [c_3539,c_30]) ).
% 3.86/0.98  
% 3.86/0.98  cnf(c_9892,plain,
% 3.86/0.98      ( ~ r2_hidden(sK5(sK3(k3_tarski(sK6))),sK6)
% 3.86/0.98      | ~ v3_ordinal1(sK5(sK3(k3_tarski(sK6))))
% 3.86/0.98      | v4_ordinal1(sK6) ),
% 3.86/0.98      inference(resolution,[status(thm)],[c_9091,c_4706]) ).
% 3.86/0.98  
% 3.86/0.98  cnf(c_99,plain,
% 3.86/0.98      ( k3_tarski(X0) = X0 | v4_ordinal1(X0) != iProver_top ),
% 3.86/0.98      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 3.86/0.98  
% 3.86/0.98  cnf(c_101,plain,
% 3.86/0.98      ( k3_tarski(sK6) = sK6 | v4_ordinal1(sK6) != iProver_top ),
% 3.86/0.98      inference(instantiation,[status(thm)],[c_99]) ).
% 3.86/0.98  
% 3.86/0.98  cnf(c_103,plain,
% 3.86/0.98      ( v4_ordinal1(sK6) | k3_tarski(sK6) != sK6 ),
% 3.86/0.98      inference(instantiation,[status(thm)],[c_9]) ).
% 3.86/0.98  
% 3.86/0.98  cnf(c_10439,plain,
% 3.86/0.98      ( v4_ordinal1(sK6) ),
% 3.86/0.98      inference(global_propositional_subsumption,
% 3.86/0.98                [status(thm)],
% 3.86/0.98                [c_9892,c_37,c_101,c_103,c_107,c_2638,c_3250,c_3274,
% 3.86/0.98                 c_3277,c_3586,c_6337,c_9944]) ).
% 3.86/0.98  
% 3.86/0.98  cnf(c_10724,plain,
% 3.86/0.98      ( v4_ordinal1(sK6) = iProver_top ),
% 3.86/0.98      inference(global_propositional_subsumption,
% 3.86/0.98                [status(thm)],
% 3.86/0.98                [c_10268,c_37,c_107,c_2638,c_3250,c_3274,c_3277,c_3586,
% 3.86/0.98                 c_6337,c_9944]) ).
% 3.86/0.98  
% 3.86/0.98  cnf(c_23,plain,
% 3.86/0.98      ( ~ v3_ordinal1(X0) | v3_ordinal1(k2_xboole_0(X0,k1_tarski(X0))) ),
% 3.86/0.98      inference(cnf_transformation,[],[f103]) ).
% 3.86/0.98  
% 3.86/0.98  cnf(c_1808,plain,
% 3.86/0.98      ( v3_ordinal1(X0) != iProver_top
% 3.86/0.98      | v3_ordinal1(k2_xboole_0(X0,k1_tarski(X0))) = iProver_top ),
% 3.86/0.98      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 3.86/0.98  
% 3.86/0.98  cnf(c_1809,plain,
% 3.86/0.98      ( X0 = X1
% 3.86/0.98      | r2_hidden(X1,X0) = iProver_top
% 3.86/0.98      | r2_hidden(X0,X1) = iProver_top
% 3.86/0.98      | v3_ordinal1(X1) != iProver_top
% 3.86/0.98      | v3_ordinal1(X0) != iProver_top ),
% 3.86/0.98      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 3.86/0.98  
% 3.86/0.98  cnf(c_32,negated_conjecture,
% 3.86/0.98      ( ~ r2_hidden(k2_xboole_0(sK7,k1_tarski(sK7)),sK6)
% 3.86/0.98      | ~ v4_ordinal1(sK6) ),
% 3.86/0.98      inference(cnf_transformation,[],[f106]) ).
% 3.86/0.98  
% 3.86/0.98  cnf(c_1802,plain,
% 3.86/0.98      ( r2_hidden(k2_xboole_0(sK7,k1_tarski(sK7)),sK6) != iProver_top
% 3.86/0.98      | v4_ordinal1(sK6) != iProver_top ),
% 3.86/0.98      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 3.86/0.98  
% 3.86/0.98  cnf(c_6596,plain,
% 3.86/0.98      ( k2_xboole_0(sK7,k1_tarski(sK7)) = sK6
% 3.86/0.98      | r2_hidden(sK6,k2_xboole_0(sK7,k1_tarski(sK7))) = iProver_top
% 3.86/0.98      | v3_ordinal1(k2_xboole_0(sK7,k1_tarski(sK7))) != iProver_top
% 3.86/0.98      | v3_ordinal1(sK6) != iProver_top
% 3.86/0.98      | v4_ordinal1(sK6) != iProver_top ),
% 3.86/0.98      inference(superposition,[status(thm)],[c_1809,c_1802]) ).
% 3.86/0.98  
% 3.86/0.98  cnf(c_34,negated_conjecture,
% 3.86/0.98      ( v3_ordinal1(sK7) | ~ v4_ordinal1(sK6) ),
% 3.86/0.98      inference(cnf_transformation,[],[f95]) ).
% 3.86/0.98  
% 3.86/0.98  cnf(c_41,plain,
% 3.86/0.98      ( v3_ordinal1(sK7) = iProver_top
% 3.86/0.98      | v4_ordinal1(sK6) != iProver_top ),
% 3.86/0.98      inference(predicate_to_equality,[status(thm)],[c_34]) ).
% 3.86/0.98  
% 3.86/0.98  cnf(c_1803,plain,
% 3.86/0.98      ( r2_hidden(X0,X1) != iProver_top
% 3.86/0.98      | r1_tarski(X1,X0) != iProver_top ),
% 3.86/0.98      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 3.86/0.98  
% 3.86/0.98  cnf(c_2922,plain,
% 3.86/0.98      ( r1_tarski(sK6,sK7) != iProver_top
% 3.86/0.98      | v4_ordinal1(sK6) != iProver_top ),
% 3.86/0.98      inference(superposition,[status(thm)],[c_1801,c_1803]) ).
% 3.86/0.98  
% 3.86/0.98  cnf(c_3233,plain,
% 3.86/0.98      ( ~ r2_hidden(sK6,k2_xboole_0(sK7,k1_tarski(sK7)))
% 3.86/0.98      | r1_tarski(sK6,sK7)
% 3.86/0.98      | ~ v3_ordinal1(sK6)
% 3.86/0.98      | ~ v3_ordinal1(sK7) ),
% 3.86/0.98      inference(instantiation,[status(thm)],[c_577]) ).
% 3.86/0.98  
% 3.86/0.98  cnf(c_3234,plain,
% 3.86/0.98      ( r2_hidden(sK6,k2_xboole_0(sK7,k1_tarski(sK7))) != iProver_top
% 3.86/0.98      | r1_tarski(sK6,sK7) = iProver_top
% 3.86/0.98      | v3_ordinal1(sK6) != iProver_top
% 3.86/0.98      | v3_ordinal1(sK7) != iProver_top ),
% 3.86/0.98      inference(predicate_to_equality,[status(thm)],[c_3233]) ).
% 3.86/0.98  
% 3.86/0.98  cnf(c_7450,plain,
% 3.86/0.98      ( v3_ordinal1(k2_xboole_0(sK7,k1_tarski(sK7))) != iProver_top
% 3.86/0.98      | k2_xboole_0(sK7,k1_tarski(sK7)) = sK6
% 3.86/0.98      | v4_ordinal1(sK6) != iProver_top ),
% 3.86/0.98      inference(global_propositional_subsumption,
% 3.86/0.98                [status(thm)],
% 3.86/0.98                [c_6596,c_37,c_41,c_2922,c_3234]) ).
% 3.86/0.98  
% 3.86/0.98  cnf(c_7451,plain,
% 3.86/0.98      ( k2_xboole_0(sK7,k1_tarski(sK7)) = sK6
% 3.86/0.98      | v3_ordinal1(k2_xboole_0(sK7,k1_tarski(sK7))) != iProver_top
% 3.86/0.98      | v4_ordinal1(sK6) != iProver_top ),
% 3.86/0.98      inference(renaming,[status(thm)],[c_7450]) ).
% 3.86/0.98  
% 3.86/0.98  cnf(c_7457,plain,
% 3.86/0.98      ( k2_xboole_0(sK7,k1_tarski(sK7)) = sK6
% 3.86/0.98      | v3_ordinal1(sK7) != iProver_top
% 3.86/0.98      | v4_ordinal1(sK6) != iProver_top ),
% 3.86/0.98      inference(superposition,[status(thm)],[c_1808,c_7451]) ).
% 3.86/0.98  
% 3.86/0.98  cnf(c_8139,plain,
% 3.86/0.98      ( k2_xboole_0(sK7,k1_tarski(sK7)) = sK6
% 3.86/0.98      | v4_ordinal1(sK6) != iProver_top ),
% 3.86/0.98      inference(global_propositional_subsumption,
% 3.86/0.98                [status(thm)],
% 3.86/0.98                [c_7457,c_41]) ).
% 3.86/0.98  
% 3.86/0.98  cnf(c_10730,plain,
% 3.86/0.98      ( k2_xboole_0(sK7,k1_tarski(sK7)) = sK6 ),
% 3.86/0.98      inference(superposition,[status(thm)],[c_10724,c_8139]) ).
% 3.86/0.98  
% 3.86/0.98  cnf(c_1797,plain,
% 3.86/0.98      ( r2_hidden(X0,k2_xboole_0(X1,k1_tarski(X1))) != iProver_top
% 3.86/0.98      | r1_tarski(X0,X1) = iProver_top
% 3.86/0.98      | v3_ordinal1(X0) != iProver_top
% 3.86/0.98      | v3_ordinal1(X1) != iProver_top ),
% 3.86/0.98      inference(predicate_to_equality,[status(thm)],[c_577]) ).
% 3.86/0.98  
% 3.86/0.98  cnf(c_11491,plain,
% 3.86/0.98      ( r2_hidden(X0,sK6) != iProver_top
% 3.86/0.98      | r1_tarski(X0,sK7) = iProver_top
% 3.86/0.98      | v3_ordinal1(X0) != iProver_top
% 3.86/0.98      | v3_ordinal1(sK7) != iProver_top ),
% 3.86/0.98      inference(superposition,[status(thm)],[c_10730,c_1797]) ).
% 3.86/0.98  
% 3.86/0.98  cnf(c_286,plain,
% 3.86/0.98      ( v4_ordinal1(X0) | k3_tarski(X0) != X0 ),
% 3.86/0.98      inference(prop_impl,[status(thm)],[c_9]) ).
% 3.86/0.98  
% 3.86/0.98  cnf(c_506,plain,
% 3.86/0.98      ( v3_ordinal1(sK7) | k3_tarski(X0) != X0 | sK6 != X0 ),
% 3.86/0.98      inference(resolution_lifted,[status(thm)],[c_286,c_34]) ).
% 3.86/0.98  
% 3.86/0.98  cnf(c_507,plain,
% 3.86/0.98      ( v3_ordinal1(sK7) | k3_tarski(sK6) != sK6 ),
% 3.86/0.98      inference(unflattening,[status(thm)],[c_506]) ).
% 3.86/0.98  
% 3.86/0.98  cnf(c_508,plain,
% 3.86/0.98      ( k3_tarski(sK6) != sK6 | v3_ordinal1(sK7) = iProver_top ),
% 3.86/0.98      inference(predicate_to_equality,[status(thm)],[c_507]) ).
% 3.86/0.98  
% 3.86/0.98  cnf(c_18622,plain,
% 3.86/0.98      ( v3_ordinal1(X0) != iProver_top
% 3.86/0.98      | r1_tarski(X0,sK7) = iProver_top
% 3.86/0.98      | r2_hidden(X0,sK6) != iProver_top ),
% 3.86/0.98      inference(global_propositional_subsumption,
% 3.86/0.98                [status(thm)],
% 3.86/0.98                [c_11491,c_37,c_41,c_107,c_2638,c_3250,c_3274,c_3277,
% 3.86/0.98                 c_3586,c_6337,c_9944]) ).
% 3.86/0.98  
% 3.86/0.98  cnf(c_18623,plain,
% 3.86/0.98      ( r2_hidden(X0,sK6) != iProver_top
% 3.86/0.98      | r1_tarski(X0,sK7) = iProver_top
% 3.86/0.98      | v3_ordinal1(X0) != iProver_top ),
% 3.86/0.98      inference(renaming,[status(thm)],[c_18622]) ).
% 3.86/0.98  
% 3.86/0.98  cnf(c_18632,plain,
% 3.86/0.98      ( r2_hidden(X0,k3_tarski(sK6)) != iProver_top
% 3.86/0.98      | r1_tarski(sK2(sK6,X0),sK7) = iProver_top
% 3.86/0.98      | v3_ordinal1(sK2(sK6,X0)) != iProver_top ),
% 3.86/0.98      inference(superposition,[status(thm)],[c_1820,c_18623]) ).
% 3.86/0.98  
% 3.86/0.98  cnf(c_1817,plain,
% 3.86/0.98      ( k3_tarski(X0) = X0 | v4_ordinal1(X0) != iProver_top ),
% 3.86/0.98      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 3.86/0.98  
% 3.86/0.98  cnf(c_10729,plain,
% 3.86/0.98      ( k3_tarski(sK6) = sK6 ),
% 3.86/0.98      inference(superposition,[status(thm)],[c_10724,c_1817]) ).
% 3.86/0.98  
% 3.86/0.98  cnf(c_18685,plain,
% 3.86/0.98      ( r2_hidden(X0,sK6) != iProver_top
% 3.86/0.98      | r1_tarski(sK2(sK6,X0),sK7) = iProver_top
% 3.86/0.98      | v3_ordinal1(sK2(sK6,X0)) != iProver_top ),
% 3.86/0.98      inference(light_normalisation,[status(thm)],[c_18632,c_10729]) ).
% 3.86/0.98  
% 3.86/0.98  cnf(c_1810,plain,
% 3.86/0.98      ( r2_hidden(X0,X1) != iProver_top
% 3.86/0.98      | v3_ordinal1(X1) != iProver_top
% 3.86/0.98      | v3_ordinal1(X0) = iProver_top ),
% 3.86/0.98      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 3.86/0.98  
% 3.86/0.98  cnf(c_4878,plain,
% 3.86/0.98      ( r2_hidden(X0,k3_tarski(X1)) != iProver_top
% 3.86/0.98      | v3_ordinal1(X1) != iProver_top
% 3.86/0.98      | v3_ordinal1(sK2(X1,X0)) = iProver_top ),
% 3.86/0.98      inference(superposition,[status(thm)],[c_1820,c_1810]) ).
% 3.86/0.98  
% 3.86/0.98  cnf(c_16992,plain,
% 3.86/0.98      ( r2_hidden(X0,sK6) != iProver_top
% 3.86/0.98      | v3_ordinal1(sK2(sK6,X0)) = iProver_top
% 3.86/0.98      | v3_ordinal1(sK6) != iProver_top ),
% 3.86/0.98      inference(superposition,[status(thm)],[c_10729,c_4878]) ).
% 3.86/0.98  
% 3.86/0.98  cnf(c_18820,plain,
% 3.86/0.98      ( r1_tarski(sK2(sK6,X0),sK7) = iProver_top
% 3.86/0.98      | r2_hidden(X0,sK6) != iProver_top ),
% 3.86/0.98      inference(global_propositional_subsumption,
% 3.86/0.98                [status(thm)],
% 3.86/0.98                [c_18685,c_37,c_16992]) ).
% 3.86/0.98  
% 3.86/0.98  cnf(c_18821,plain,
% 3.86/0.98      ( r2_hidden(X0,sK6) != iProver_top
% 3.86/0.98      | r1_tarski(sK2(sK6,X0),sK7) = iProver_top ),
% 3.86/0.98      inference(renaming,[status(thm)],[c_18820]) ).
% 3.86/0.98  
% 3.86/0.98  cnf(c_1819,plain,
% 3.86/0.98      ( r2_hidden(X0,sK2(X1,X0)) = iProver_top
% 3.86/0.98      | r2_hidden(X0,k3_tarski(X1)) != iProver_top ),
% 3.86/0.98      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 3.86/0.98  
% 3.86/0.98  cnf(c_3513,plain,
% 3.86/0.98      ( r2_hidden(X0,k3_tarski(X1)) != iProver_top
% 3.86/0.98      | r1_tarski(sK2(X1,X0),X0) != iProver_top ),
% 3.86/0.98      inference(superposition,[status(thm)],[c_1819,c_1803]) ).
% 3.86/0.98  
% 3.86/0.98  cnf(c_18827,plain,
% 3.86/0.98      ( r2_hidden(sK7,k3_tarski(sK6)) != iProver_top
% 3.86/0.98      | r2_hidden(sK7,sK6) != iProver_top ),
% 3.86/0.98      inference(superposition,[status(thm)],[c_18821,c_3513]) ).
% 3.86/0.98  
% 3.86/0.98  cnf(c_18830,plain,
% 3.86/0.98      ( r2_hidden(sK7,sK6) != iProver_top ),
% 3.86/0.98      inference(light_normalisation,[status(thm)],[c_18827,c_10729]) ).
% 3.86/0.98  
% 3.86/0.98  cnf(c_516,plain,
% 3.86/0.98      ( r2_hidden(sK7,sK6) | k3_tarski(X0) != X0 | sK6 != X0 ),
% 3.86/0.98      inference(resolution_lifted,[status(thm)],[c_286,c_33]) ).
% 3.86/0.98  
% 3.86/0.98  cnf(c_517,plain,
% 3.86/0.98      ( r2_hidden(sK7,sK6) | k3_tarski(sK6) != sK6 ),
% 3.86/0.98      inference(unflattening,[status(thm)],[c_516]) ).
% 3.86/0.98  
% 3.86/0.98  cnf(c_518,plain,
% 3.86/0.98      ( k3_tarski(sK6) != sK6 | r2_hidden(sK7,sK6) = iProver_top ),
% 3.86/0.98      inference(predicate_to_equality,[status(thm)],[c_517]) ).
% 3.86/0.98  
% 3.86/0.98  cnf(contradiction,plain,
% 3.86/0.98      ( $false ),
% 3.86/0.98      inference(minisat,[status(thm)],[c_18830,c_10439,c_518,c_100]) ).
% 3.86/0.98  
% 3.86/0.98  
% 3.86/0.98  % SZS output end CNFRefutation for theBenchmark.p
% 3.86/0.98  
% 3.86/0.98  ------                               Statistics
% 3.86/0.98  
% 3.86/0.98  ------ Selected
% 3.86/0.98  
% 3.86/0.98  total_time:                             0.493
% 3.86/0.98  
%------------------------------------------------------------------------------
