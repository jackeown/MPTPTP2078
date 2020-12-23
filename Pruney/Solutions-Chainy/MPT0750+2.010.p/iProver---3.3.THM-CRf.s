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
% DateTime   : Thu Dec  3 11:54:01 EST 2020

% Result     : Theorem 7.66s
% Output     : CNFRefutation 7.66s
% Verified   : 
% Statistics : Number of formulae       :  252 (2802 expanded)
%              Number of clauses        :  157 ( 869 expanded)
%              Number of leaves         :   25 ( 594 expanded)
%              Depth                    :   28
%              Number of atoms          :  833 (11839 expanded)
%              Number of equality atoms :  295 (2242 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal clause size      :   18 (   3 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f7,axiom,(
    ! [X0,X1] :
      ( ( v3_ordinal1(X1)
        & v3_ordinal1(X0) )
     => ( r1_ordinal1(X0,X1)
      <=> r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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

fof(f51,plain,(
    ! [X0,X1] :
      ( ( ( r1_ordinal1(X0,X1)
          | ~ r1_tarski(X0,X1) )
        & ( r1_tarski(X0,X1)
          | ~ r1_ordinal1(X0,X1) ) )
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(nnf_transformation,[],[f24])).

fof(f82,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r1_ordinal1(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k3_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] :
              ( r2_hidden(X3,X0)
              & r2_hidden(X2,X3) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
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

fof(f45,plain,(
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
    inference(rectify,[],[f44])).

fof(f48,plain,(
    ! [X5,X0] :
      ( ? [X7] :
          ( r2_hidden(X7,X0)
          & r2_hidden(X5,X7) )
     => ( r2_hidden(sK3(X0,X5),X0)
        & r2_hidden(X5,sK3(X0,X5)) ) ) ),
    introduced(choice_axiom,[])).

fof(f47,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( r2_hidden(X4,X0)
          & r2_hidden(X2,X4) )
     => ( r2_hidden(sK2(X0,X1),X0)
        & r2_hidden(X2,sK2(X0,X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f46,plain,(
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

fof(f49,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f45,f48,f47,f46])).

fof(f72,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(X5,sK3(X0,X5))
      | ~ r2_hidden(X5,X1)
      | k3_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f49])).

fof(f121,plain,(
    ! [X0,X5] :
      ( r2_hidden(X5,sK3(X0,X5))
      | ~ r2_hidden(X5,k3_tarski(X0)) ) ),
    inference(equality_resolution,[],[f72])).

fof(f11,axiom,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ! [X1] :
          ( v3_ordinal1(X1)
         => ~ ( ~ r2_hidden(X1,X0)
              & X0 != X1
              & ~ r2_hidden(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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

fof(f89,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,X0)
      | X0 = X1
      | r2_hidden(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f18,conjecture,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ( v4_ordinal1(X0)
      <=> ! [X1] :
            ( v3_ordinal1(X1)
           => ( r2_hidden(X1,X0)
             => r2_hidden(k1_ordinal1(X1),X0) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,negated_conjecture,(
    ~ ! [X0] :
        ( v3_ordinal1(X0)
       => ( v4_ordinal1(X0)
        <=> ! [X1] :
              ( v3_ordinal1(X1)
             => ( r2_hidden(X1,X0)
               => r2_hidden(k1_ordinal1(X1),X0) ) ) ) ) ),
    inference(negated_conjecture,[],[f18])).

fof(f36,plain,(
    ? [X0] :
      ( ( v4_ordinal1(X0)
      <~> ! [X1] :
            ( r2_hidden(k1_ordinal1(X1),X0)
            | ~ r2_hidden(X1,X0)
            | ~ v3_ordinal1(X1) ) )
      & v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f37,plain,(
    ? [X0] :
      ( ( v4_ordinal1(X0)
      <~> ! [X1] :
            ( r2_hidden(k1_ordinal1(X1),X0)
            | ~ r2_hidden(X1,X0)
            | ~ v3_ordinal1(X1) ) )
      & v3_ordinal1(X0) ) ),
    inference(flattening,[],[f36])).

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
    inference(nnf_transformation,[],[f37])).

fof(f61,plain,(
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
    inference(flattening,[],[f60])).

fof(f62,plain,(
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
    inference(rectify,[],[f61])).

fof(f64,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ r2_hidden(k1_ordinal1(X1),X0)
          & r2_hidden(X1,X0)
          & v3_ordinal1(X1) )
     => ( ~ r2_hidden(k1_ordinal1(sK7),X0)
        & r2_hidden(sK7,X0)
        & v3_ordinal1(sK7) ) ) ),
    introduced(choice_axiom,[])).

fof(f63,plain,
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

fof(f65,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7])],[f62,f64,f63])).

fof(f102,plain,(
    ! [X2] :
      ( r2_hidden(k1_ordinal1(X2),sK6)
      | ~ r2_hidden(X2,sK6)
      | ~ v3_ordinal1(X2)
      | v4_ordinal1(sK6) ) ),
    inference(cnf_transformation,[],[f65])).

fof(f5,axiom,(
    ! [X0] : k1_ordinal1(X0) = k2_xboole_0(X0,k1_tarski(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f79,plain,(
    ! [X0] : k1_ordinal1(X0) = k2_xboole_0(X0,k1_tarski(X0)) ),
    inference(cnf_transformation,[],[f5])).

fof(f116,plain,(
    ! [X2] :
      ( r2_hidden(k2_xboole_0(X2,k1_tarski(X2)),sK6)
      | ~ r2_hidden(X2,sK6)
      | ~ v3_ordinal1(X2)
      | v4_ordinal1(sK6) ) ),
    inference(definition_unfolding,[],[f102,f79])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,k1_ordinal1(X1))
    <=> ( X0 = X1
        | r2_hidden(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f52,plain,(
    ! [X0,X1] :
      ( ( r2_hidden(X0,k1_ordinal1(X1))
        | ( X0 != X1
          & ~ r2_hidden(X0,X1) ) )
      & ( X0 = X1
        | r2_hidden(X0,X1)
        | ~ r2_hidden(X0,k1_ordinal1(X1)) ) ) ),
    inference(nnf_transformation,[],[f9])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ( r2_hidden(X0,k1_ordinal1(X1))
        | ( X0 != X1
          & ~ r2_hidden(X0,X1) ) )
      & ( X0 = X1
        | r2_hidden(X0,X1)
        | ~ r2_hidden(X0,k1_ordinal1(X1)) ) ) ),
    inference(flattening,[],[f52])).

fof(f87,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,k1_ordinal1(X1))
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f53])).

fof(f107,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,k2_xboole_0(X1,k1_tarski(X1)))
      | X0 != X1 ) ),
    inference(definition_unfolding,[],[f87,f79])).

fof(f122,plain,(
    ! [X1] : r2_hidden(X1,k2_xboole_0(X1,k1_tarski(X1))) ),
    inference(equality_resolution,[],[f107])).

fof(f74,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | ~ r2_hidden(X6,X0)
      | ~ r2_hidden(X5,X6)
      | k3_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f49])).

fof(f119,plain,(
    ! [X6,X0,X5] :
      ( r2_hidden(X5,k3_tarski(X0))
      | ~ r2_hidden(X6,X0)
      | ~ r2_hidden(X5,X6) ) ),
    inference(equality_resolution,[],[f74])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f42])).

fof(f69,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f43])).

fof(f118,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f69])).

fof(f86,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,k1_ordinal1(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f108,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,k2_xboole_0(X1,k1_tarski(X1)))
      | ~ r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f86,f79])).

fof(f17,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f100,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f101,plain,(
    v3_ordinal1(sK6) ),
    inference(cnf_transformation,[],[f65])).

fof(f14,axiom,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ! [X1] :
          ( v3_ordinal1(X1)
         => ( r2_hidden(X0,k1_ordinal1(X1))
          <=> r1_ordinal1(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r2_hidden(X0,k1_ordinal1(X1))
          <=> r1_ordinal1(X0,X1) )
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f55,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( r2_hidden(X0,k1_ordinal1(X1))
              | ~ r1_ordinal1(X0,X1) )
            & ( r1_ordinal1(X0,X1)
              | ~ r2_hidden(X0,k1_ordinal1(X1)) ) )
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(nnf_transformation,[],[f31])).

fof(f93,plain,(
    ! [X0,X1] :
      ( r1_ordinal1(X0,X1)
      | ~ r2_hidden(X0,k1_ordinal1(X1))
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f114,plain,(
    ! [X0,X1] :
      ( r1_ordinal1(X0,X1)
      | ~ r2_hidden(X0,k2_xboole_0(X1,k1_tarski(X1)))
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(definition_unfolding,[],[f93,f79])).

fof(f6,axiom,(
    ! [X0] :
      ( v4_ordinal1(X0)
    <=> k3_tarski(X0) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f50,plain,(
    ! [X0] :
      ( ( v4_ordinal1(X0)
        | k3_tarski(X0) != X0 )
      & ( k3_tarski(X0) = X0
        | ~ v4_ordinal1(X0) ) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f80,plain,(
    ! [X0] :
      ( k3_tarski(X0) = X0
      | ~ v4_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f15,axiom,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(X1,X0)
         => v3_ordinal1(X1) )
     => v3_ordinal1(k3_tarski(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0] :
      ( v3_ordinal1(k3_tarski(X0))
      | ? [X1] :
          ( ~ v3_ordinal1(X1)
          & r2_hidden(X1,X0) ) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f56,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ v3_ordinal1(X1)
          & r2_hidden(X1,X0) )
     => ( ~ v3_ordinal1(sK4(X0))
        & r2_hidden(sK4(X0),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f57,plain,(
    ! [X0] :
      ( v3_ordinal1(k3_tarski(X0))
      | ( ~ v3_ordinal1(sK4(X0))
        & r2_hidden(sK4(X0),X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f32,f56])).

fof(f95,plain,(
    ! [X0] :
      ( v3_ordinal1(k3_tarski(X0))
      | r2_hidden(sK4(X0),X0) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( v3_ordinal1(X1)
     => ( r2_hidden(X0,X1)
       => v3_ordinal1(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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

fof(f88,plain,(
    ! [X0,X1] :
      ( v3_ordinal1(X0)
      | ~ r2_hidden(X0,X1)
      | ~ v3_ordinal1(X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f96,plain,(
    ! [X0] :
      ( v3_ordinal1(k3_tarski(X0))
      | ~ v3_ordinal1(sK4(X0)) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f16,axiom,(
    ! [X0] :
    ? [X1] :
      ( ! [X2] :
          ( v3_ordinal1(X2)
         => ( ~ r2_hidden(X2,X0)
           => r1_ordinal1(X1,X2) ) )
      & ~ r2_hidden(X1,X0)
      & v3_ordinal1(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0] :
    ? [X1] :
      ( ! [X2] :
          ( r1_ordinal1(X1,X2)
          | r2_hidden(X2,X0)
          | ~ v3_ordinal1(X2) )
      & ~ r2_hidden(X1,X0)
      & v3_ordinal1(X1) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f34,plain,(
    ! [X0] :
    ? [X1] :
      ( ! [X2] :
          ( r1_ordinal1(X1,X2)
          | r2_hidden(X2,X0)
          | ~ v3_ordinal1(X2) )
      & ~ r2_hidden(X1,X0)
      & v3_ordinal1(X1) ) ),
    inference(flattening,[],[f33])).

fof(f58,plain,(
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

fof(f59,plain,(
    ! [X0] :
      ( ! [X2] :
          ( r1_ordinal1(sK5(X0),X2)
          | r2_hidden(X2,X0)
          | ~ v3_ordinal1(X2) )
      & ~ r2_hidden(sK5(X0),X0)
      & v3_ordinal1(sK5(X0)) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f34,f58])).

fof(f98,plain,(
    ! [X0] : ~ r2_hidden(sK5(X0),X0) ),
    inference(cnf_transformation,[],[f59])).

fof(f73,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(sK3(X0,X5),X0)
      | ~ r2_hidden(X5,X1)
      | k3_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f49])).

fof(f120,plain,(
    ! [X0,X5] :
      ( r2_hidden(sK3(X0,X5),X0)
      | ~ r2_hidden(X5,k3_tarski(X0)) ) ),
    inference(equality_resolution,[],[f73])).

fof(f81,plain,(
    ! [X0] :
      ( v4_ordinal1(X0)
      | k3_tarski(X0) != X0 ) ),
    inference(cnf_transformation,[],[f50])).

fof(f105,plain,
    ( ~ r2_hidden(k1_ordinal1(sK7),sK6)
    | ~ v4_ordinal1(sK6) ),
    inference(cnf_transformation,[],[f65])).

fof(f115,plain,
    ( ~ r2_hidden(k2_xboole_0(sK7,k1_tarski(sK7)),sK6)
    | ~ v4_ordinal1(sK6) ),
    inference(definition_unfolding,[],[f105,f79])).

fof(f103,plain,
    ( v3_ordinal1(sK7)
    | ~ v4_ordinal1(sK6) ),
    inference(cnf_transformation,[],[f65])).

fof(f104,plain,
    ( r2_hidden(sK7,sK6)
    | ~ v4_ordinal1(sK6) ),
    inference(cnf_transformation,[],[f65])).

fof(f12,axiom,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => v3_ordinal1(k1_ordinal1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0] :
      ( v3_ordinal1(k1_ordinal1(X0))
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f90,plain,(
    ! [X0] :
      ( v3_ordinal1(k1_ordinal1(X0))
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f110,plain,(
    ! [X0] :
      ( v3_ordinal1(k2_xboole_0(X0,k1_tarski(X0)))
      | ~ v3_ordinal1(X0) ) ),
    inference(definition_unfolding,[],[f90,f79])).

fof(f13,axiom,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ! [X1] :
          ( v3_ordinal1(X1)
         => ( r2_hidden(X0,X1)
          <=> r1_ordinal1(k1_ordinal1(X0),X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r2_hidden(X0,X1)
          <=> r1_ordinal1(k1_ordinal1(X0),X1) )
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f54,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( r2_hidden(X0,X1)
              | ~ r1_ordinal1(k1_ordinal1(X0),X1) )
            & ( r1_ordinal1(k1_ordinal1(X0),X1)
              | ~ r2_hidden(X0,X1) ) )
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(nnf_transformation,[],[f30])).

fof(f91,plain,(
    ! [X0,X1] :
      ( r1_ordinal1(k1_ordinal1(X0),X1)
      | ~ r2_hidden(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f112,plain,(
    ! [X0,X1] :
      ( r1_ordinal1(k2_xboole_0(X0,k1_tarski(X0)),X1)
      | ~ r2_hidden(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(definition_unfolding,[],[f91,f79])).

fof(f85,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | r2_hidden(X0,X1)
      | ~ r2_hidden(X0,k1_ordinal1(X1)) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f109,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | r2_hidden(X0,X1)
      | ~ r2_hidden(X0,k2_xboole_0(X1,k1_tarski(X1))) ) ),
    inference(definition_unfolding,[],[f85,f79])).

fof(f94,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,k1_ordinal1(X1))
      | ~ r1_ordinal1(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f113,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,k2_xboole_0(X1,k1_tarski(X1)))
      | ~ r1_ordinal1(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(definition_unfolding,[],[f94,f79])).

cnf(c_16,plain,
    ( ~ r1_ordinal1(X0,X1)
    | r1_tarski(X0,X1)
    | ~ v3_ordinal1(X1)
    | ~ v3_ordinal1(X0) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_24236,plain,
    ( ~ r1_ordinal1(X0,sK3(X0,sK7))
    | r1_tarski(X0,sK3(X0,sK7))
    | ~ v3_ordinal1(X0)
    | ~ v3_ordinal1(sK3(X0,sK7)) ),
    inference(instantiation,[status(thm)],[c_16])).

cnf(c_24248,plain,
    ( ~ r1_ordinal1(sK6,sK3(sK6,sK7))
    | r1_tarski(sK6,sK3(sK6,sK7))
    | ~ v3_ordinal1(sK3(sK6,sK7))
    | ~ v3_ordinal1(sK6) ),
    inference(instantiation,[status(thm)],[c_24236])).

cnf(c_11,plain,
    ( r2_hidden(X0,sK3(X1,X0))
    | ~ r2_hidden(X0,k3_tarski(X1)) ),
    inference(cnf_transformation,[],[f121])).

cnf(c_1783,plain,
    ( r2_hidden(X0,sK3(X1,X0)) = iProver_top
    | r2_hidden(X0,k3_tarski(X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_22,plain,
    ( r2_hidden(X0,X1)
    | r2_hidden(X1,X0)
    | ~ v3_ordinal1(X1)
    | ~ v3_ordinal1(X0)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f89])).

cnf(c_1773,plain,
    ( X0 = X1
    | r2_hidden(X1,X0) = iProver_top
    | r2_hidden(X0,X1) = iProver_top
    | v3_ordinal1(X1) != iProver_top
    | v3_ordinal1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_37,negated_conjecture,
    ( ~ r2_hidden(X0,sK6)
    | r2_hidden(k2_xboole_0(X0,k1_tarski(X0)),sK6)
    | v4_ordinal1(sK6)
    | ~ v3_ordinal1(X0) ),
    inference(cnf_transformation,[],[f116])).

cnf(c_1759,plain,
    ( r2_hidden(X0,sK6) != iProver_top
    | r2_hidden(k2_xboole_0(X0,k1_tarski(X0)),sK6) = iProver_top
    | v4_ordinal1(sK6) = iProver_top
    | v3_ordinal1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_37])).

cnf(c_18,plain,
    ( r2_hidden(X0,k2_xboole_0(X0,k1_tarski(X0))) ),
    inference(cnf_transformation,[],[f122])).

cnf(c_1777,plain,
    ( r2_hidden(X0,k2_xboole_0(X0,k1_tarski(X0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_9,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X2,X0)
    | r2_hidden(X2,k3_tarski(X1)) ),
    inference(cnf_transformation,[],[f119])).

cnf(c_1785,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X2,X0) != iProver_top
    | r2_hidden(X2,k3_tarski(X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_4497,plain,
    ( r2_hidden(X0,k2_xboole_0(X1,k1_tarski(X1))) != iProver_top
    | r2_hidden(X0,k3_tarski(sK6)) = iProver_top
    | r2_hidden(X1,sK6) != iProver_top
    | v4_ordinal1(sK6) = iProver_top
    | v3_ordinal1(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1759,c_1785])).

cnf(c_4860,plain,
    ( r2_hidden(X0,k3_tarski(sK6)) = iProver_top
    | r2_hidden(X0,sK6) != iProver_top
    | v4_ordinal1(sK6) = iProver_top
    | v3_ordinal1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1777,c_4497])).

cnf(c_5,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f118])).

cnf(c_1789,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_19,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,k2_xboole_0(X1,k1_tarski(X1))) ),
    inference(cnf_transformation,[],[f108])).

cnf(c_1776,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,k2_xboole_0(X1,k1_tarski(X1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_33,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r1_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f100])).

cnf(c_1763,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_2901,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r1_tarski(k2_xboole_0(X1,k1_tarski(X1)),X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1776,c_1763])).

cnf(c_3445,plain,
    ( r2_hidden(k2_xboole_0(X0,k1_tarski(X0)),X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1789,c_2901])).

cnf(c_6053,plain,
    ( r2_hidden(k2_xboole_0(k3_tarski(sK6),k1_tarski(k3_tarski(sK6))),sK6) != iProver_top
    | v4_ordinal1(sK6) = iProver_top
    | v3_ordinal1(k2_xboole_0(k3_tarski(sK6),k1_tarski(k3_tarski(sK6)))) != iProver_top ),
    inference(superposition,[status(thm)],[c_4860,c_3445])).

cnf(c_9299,plain,
    ( r2_hidden(k3_tarski(sK6),sK6) != iProver_top
    | v4_ordinal1(sK6) = iProver_top
    | v3_ordinal1(k2_xboole_0(k3_tarski(sK6),k1_tarski(k3_tarski(sK6)))) != iProver_top
    | v3_ordinal1(k3_tarski(sK6)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1759,c_6053])).

cnf(c_38,negated_conjecture,
    ( v3_ordinal1(sK6) ),
    inference(cnf_transformation,[],[f101])).

cnf(c_39,plain,
    ( v3_ordinal1(sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_38])).

cnf(c_47,plain,
    ( ~ r2_hidden(sK6,sK6)
    | ~ r1_tarski(sK6,sK6) ),
    inference(instantiation,[status(thm)],[c_33])).

cnf(c_46,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_48,plain,
    ( r2_hidden(sK6,sK6) != iProver_top
    | r1_tarski(sK6,sK6) != iProver_top ),
    inference(instantiation,[status(thm)],[c_46])).

cnf(c_27,plain,
    ( r1_ordinal1(X0,X1)
    | ~ r2_hidden(X0,k2_xboole_0(X1,k1_tarski(X1)))
    | ~ v3_ordinal1(X1)
    | ~ v3_ordinal1(X0) ),
    inference(cnf_transformation,[],[f114])).

cnf(c_65,plain,
    ( r1_ordinal1(sK6,sK6)
    | ~ r2_hidden(sK6,k2_xboole_0(sK6,k1_tarski(sK6)))
    | ~ v3_ordinal1(sK6) ),
    inference(instantiation,[status(thm)],[c_27])).

cnf(c_64,plain,
    ( r1_ordinal1(X0,X1) = iProver_top
    | r2_hidden(X0,k2_xboole_0(X1,k1_tarski(X1))) != iProver_top
    | v3_ordinal1(X0) != iProver_top
    | v3_ordinal1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_66,plain,
    ( r1_ordinal1(sK6,sK6) = iProver_top
    | r2_hidden(sK6,k2_xboole_0(sK6,k1_tarski(sK6))) != iProver_top
    | v3_ordinal1(sK6) != iProver_top ),
    inference(instantiation,[status(thm)],[c_64])).

cnf(c_80,plain,
    ( r2_hidden(sK6,sK6)
    | ~ v3_ordinal1(sK6)
    | sK6 = sK6 ),
    inference(instantiation,[status(thm)],[c_22])).

cnf(c_90,plain,
    ( r2_hidden(sK6,k2_xboole_0(sK6,k1_tarski(sK6))) ),
    inference(instantiation,[status(thm)],[c_18])).

cnf(c_89,plain,
    ( r2_hidden(X0,k2_xboole_0(X0,k1_tarski(X0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_91,plain,
    ( r2_hidden(sK6,k2_xboole_0(sK6,k1_tarski(sK6))) = iProver_top ),
    inference(instantiation,[status(thm)],[c_89])).

cnf(c_94,plain,
    ( ~ r1_ordinal1(sK6,sK6)
    | r1_tarski(sK6,sK6)
    | ~ v3_ordinal1(sK6) ),
    inference(instantiation,[status(thm)],[c_16])).

cnf(c_93,plain,
    ( r1_ordinal1(X0,X1) != iProver_top
    | r1_tarski(X0,X1) = iProver_top
    | v3_ordinal1(X0) != iProver_top
    | v3_ordinal1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_95,plain,
    ( r1_ordinal1(sK6,sK6) != iProver_top
    | r1_tarski(sK6,sK6) = iProver_top
    | v3_ordinal1(sK6) != iProver_top ),
    inference(instantiation,[status(thm)],[c_93])).

cnf(c_14,plain,
    ( ~ v4_ordinal1(X0)
    | k3_tarski(X0) = X0 ),
    inference(cnf_transformation,[],[f80])).

cnf(c_99,plain,
    ( k3_tarski(X0) = X0
    | v4_ordinal1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_101,plain,
    ( k3_tarski(sK6) = sK6
    | v4_ordinal1(sK6) != iProver_top ),
    inference(instantiation,[status(thm)],[c_99])).

cnf(c_1031,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_2848,plain,
    ( k3_tarski(X0) != X1
    | sK6 != X1
    | sK6 = k3_tarski(X0) ),
    inference(instantiation,[status(thm)],[c_1031])).

cnf(c_2849,plain,
    ( k3_tarski(sK6) != sK6
    | sK6 = k3_tarski(sK6)
    | sK6 != sK6 ),
    inference(instantiation,[status(thm)],[c_2848])).

cnf(c_1032,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_1973,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,sK6)
    | X2 != X0
    | sK6 != X1 ),
    inference(instantiation,[status(thm)],[c_1032])).

cnf(c_3271,plain,
    ( r2_hidden(X0,sK6)
    | ~ r2_hidden(k3_tarski(sK6),sK6)
    | X0 != k3_tarski(sK6)
    | sK6 != sK6 ),
    inference(instantiation,[status(thm)],[c_1973])).

cnf(c_3273,plain,
    ( X0 != k3_tarski(sK6)
    | sK6 != sK6
    | r2_hidden(X0,sK6) = iProver_top
    | r2_hidden(k3_tarski(sK6),sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3271])).

cnf(c_3275,plain,
    ( sK6 != k3_tarski(sK6)
    | sK6 != sK6
    | r2_hidden(k3_tarski(sK6),sK6) != iProver_top
    | r2_hidden(sK6,sK6) = iProver_top ),
    inference(instantiation,[status(thm)],[c_3273])).

cnf(c_29,plain,
    ( r2_hidden(sK4(X0),X0)
    | v3_ordinal1(k3_tarski(X0)) ),
    inference(cnf_transformation,[],[f95])).

cnf(c_1767,plain,
    ( r2_hidden(sK4(X0),X0) = iProver_top
    | v3_ordinal1(k3_tarski(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_21,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ v3_ordinal1(X1)
    | v3_ordinal1(X0) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_1774,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | v3_ordinal1(X1) != iProver_top
    | v3_ordinal1(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_3698,plain,
    ( v3_ordinal1(X0) != iProver_top
    | v3_ordinal1(sK4(X0)) = iProver_top
    | v3_ordinal1(k3_tarski(X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1767,c_1774])).

cnf(c_28,plain,
    ( ~ v3_ordinal1(sK4(X0))
    | v3_ordinal1(k3_tarski(X0)) ),
    inference(cnf_transformation,[],[f96])).

cnf(c_61,plain,
    ( v3_ordinal1(sK4(X0)) != iProver_top
    | v3_ordinal1(k3_tarski(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_7828,plain,
    ( v3_ordinal1(X0) != iProver_top
    | v3_ordinal1(k3_tarski(X0)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3698,c_61])).

cnf(c_7831,plain,
    ( v3_ordinal1(k3_tarski(sK6)) = iProver_top
    | v3_ordinal1(sK6) != iProver_top ),
    inference(instantiation,[status(thm)],[c_7828])).

cnf(c_6049,plain,
    ( r2_hidden(X0,sK6) != iProver_top
    | r1_tarski(k3_tarski(sK6),X0) != iProver_top
    | v4_ordinal1(sK6) = iProver_top
    | v3_ordinal1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_4860,c_1763])).

cnf(c_8466,plain,
    ( r2_hidden(k3_tarski(sK6),sK6) != iProver_top
    | v4_ordinal1(sK6) = iProver_top
    | v3_ordinal1(k3_tarski(sK6)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1789,c_6049])).

cnf(c_9506,plain,
    ( r2_hidden(k3_tarski(sK6),sK6) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_9299,c_38,c_39,c_47,c_48,c_65,c_66,c_80,c_90,c_91,c_94,c_95,c_101,c_2849,c_3275,c_7831,c_8466])).

cnf(c_9510,plain,
    ( k3_tarski(sK6) = sK6
    | r2_hidden(sK6,k3_tarski(sK6)) = iProver_top
    | v3_ordinal1(k3_tarski(sK6)) != iProver_top
    | v3_ordinal1(sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_1773,c_9506])).

cnf(c_2129,plain,
    ( r2_hidden(k3_tarski(sK6),sK6)
    | r2_hidden(sK6,k3_tarski(sK6))
    | ~ v3_ordinal1(k3_tarski(sK6))
    | ~ v3_ordinal1(sK6)
    | k3_tarski(sK6) = sK6 ),
    inference(instantiation,[status(thm)],[c_22])).

cnf(c_2136,plain,
    ( k3_tarski(sK6) = sK6
    | r2_hidden(k3_tarski(sK6),sK6) = iProver_top
    | r2_hidden(sK6,k3_tarski(sK6)) = iProver_top
    | v3_ordinal1(k3_tarski(sK6)) != iProver_top
    | v3_ordinal1(sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2129])).

cnf(c_9514,plain,
    ( k3_tarski(sK6) = sK6
    | r2_hidden(sK6,k3_tarski(sK6)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_9510,c_38,c_39,c_47,c_48,c_65,c_66,c_80,c_90,c_91,c_94,c_95,c_101,c_2136,c_2849,c_3275,c_7831,c_8466])).

cnf(c_9519,plain,
    ( k3_tarski(sK6) = sK6
    | r2_hidden(X0,k3_tarski(k3_tarski(sK6))) = iProver_top
    | r2_hidden(X0,sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_9514,c_1785])).

cnf(c_31,plain,
    ( ~ r2_hidden(sK5(X0),X0) ),
    inference(cnf_transformation,[],[f98])).

cnf(c_1765,plain,
    ( r2_hidden(sK5(X0),X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_12174,plain,
    ( k3_tarski(sK6) = sK6
    | r2_hidden(sK5(k3_tarski(k3_tarski(sK6))),sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_9519,c_1765])).

cnf(c_2810,plain,
    ( ~ r1_ordinal1(sK3(X0,X1),sK6)
    | r1_tarski(sK3(X0,X1),sK6)
    | ~ v3_ordinal1(sK3(X0,X1))
    | ~ v3_ordinal1(sK6) ),
    inference(instantiation,[status(thm)],[c_16])).

cnf(c_2821,plain,
    ( r1_ordinal1(sK3(X0,X1),sK6) != iProver_top
    | r1_tarski(sK3(X0,X1),sK6) = iProver_top
    | v3_ordinal1(sK3(X0,X1)) != iProver_top
    | v3_ordinal1(sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2810])).

cnf(c_2823,plain,
    ( r1_ordinal1(sK3(sK6,sK6),sK6) != iProver_top
    | r1_tarski(sK3(sK6,sK6),sK6) = iProver_top
    | v3_ordinal1(sK3(sK6,sK6)) != iProver_top
    | v3_ordinal1(sK6) != iProver_top ),
    inference(instantiation,[status(thm)],[c_2821])).

cnf(c_3181,plain,
    ( r2_hidden(X0,k3_tarski(X1)) != iProver_top
    | r1_tarski(sK3(X1,X0),X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1783,c_1763])).

cnf(c_3183,plain,
    ( r2_hidden(sK6,k3_tarski(sK6)) != iProver_top
    | r1_tarski(sK3(sK6,sK6),sK6) != iProver_top ),
    inference(instantiation,[status(thm)],[c_3181])).

cnf(c_10,plain,
    ( ~ r2_hidden(X0,k3_tarski(X1))
    | r2_hidden(sK3(X1,X0),X1) ),
    inference(cnf_transformation,[],[f120])).

cnf(c_1784,plain,
    ( r2_hidden(X0,k3_tarski(X1)) != iProver_top
    | r2_hidden(sK3(X1,X0),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_3694,plain,
    ( r2_hidden(X0,k3_tarski(X1)) != iProver_top
    | v3_ordinal1(X1) != iProver_top
    | v3_ordinal1(sK3(X1,X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1784,c_1774])).

cnf(c_3703,plain,
    ( r2_hidden(sK6,k3_tarski(sK6)) != iProver_top
    | v3_ordinal1(sK3(sK6,sK6)) = iProver_top
    | v3_ordinal1(sK6) != iProver_top ),
    inference(instantiation,[status(thm)],[c_3694])).

cnf(c_1769,plain,
    ( r1_ordinal1(X0,X1) = iProver_top
    | r2_hidden(X0,k2_xboole_0(X1,k1_tarski(X1))) != iProver_top
    | v3_ordinal1(X0) != iProver_top
    | v3_ordinal1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_3551,plain,
    ( r1_ordinal1(X0,X1) = iProver_top
    | r2_hidden(X0,X1) != iProver_top
    | v3_ordinal1(X0) != iProver_top
    | v3_ordinal1(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1776,c_1769])).

cnf(c_82,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | v3_ordinal1(X1) != iProver_top
    | v3_ordinal1(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_86,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,k2_xboole_0(X1,k1_tarski(X1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_12356,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r1_ordinal1(X0,X1) = iProver_top
    | v3_ordinal1(X1) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3551,c_64,c_82,c_86])).

cnf(c_12357,plain,
    ( r1_ordinal1(X0,X1) = iProver_top
    | r2_hidden(X0,X1) != iProver_top
    | v3_ordinal1(X1) != iProver_top ),
    inference(renaming,[status(thm)],[c_12356])).

cnf(c_12365,plain,
    ( r1_ordinal1(sK3(X0,X1),X0) = iProver_top
    | r2_hidden(X1,k3_tarski(X0)) != iProver_top
    | v3_ordinal1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1784,c_12357])).

cnf(c_12408,plain,
    ( r1_ordinal1(sK3(sK6,sK6),sK6) = iProver_top
    | r2_hidden(sK6,k3_tarski(sK6)) != iProver_top
    | v3_ordinal1(sK6) != iProver_top ),
    inference(instantiation,[status(thm)],[c_12365])).

cnf(c_12448,plain,
    ( k3_tarski(sK6) = sK6 ),
    inference(global_propositional_subsumption,[status(thm)],[c_12174,c_39,c_2823,c_3183,c_3703,c_9514,c_12408])).

cnf(c_13,plain,
    ( v4_ordinal1(X0)
    | k3_tarski(X0) != X0 ),
    inference(cnf_transformation,[],[f81])).

cnf(c_1781,plain,
    ( k3_tarski(X0) != X0
    | v4_ordinal1(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_12556,plain,
    ( v4_ordinal1(sK6) = iProver_top ),
    inference(superposition,[status(thm)],[c_12448,c_1781])).

cnf(c_34,negated_conjecture,
    ( ~ r2_hidden(k2_xboole_0(sK7,k1_tarski(sK7)),sK6)
    | ~ v4_ordinal1(sK6) ),
    inference(cnf_transformation,[],[f115])).

cnf(c_1762,plain,
    ( r2_hidden(k2_xboole_0(sK7,k1_tarski(sK7)),sK6) != iProver_top
    | v4_ordinal1(sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_5612,plain,
    ( k2_xboole_0(sK7,k1_tarski(sK7)) = sK6
    | r2_hidden(sK6,k2_xboole_0(sK7,k1_tarski(sK7))) = iProver_top
    | v4_ordinal1(sK6) != iProver_top
    | v3_ordinal1(k2_xboole_0(sK7,k1_tarski(sK7))) != iProver_top
    | v3_ordinal1(sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_1773,c_1762])).

cnf(c_36,negated_conjecture,
    ( ~ v4_ordinal1(sK6)
    | v3_ordinal1(sK7) ),
    inference(cnf_transformation,[],[f103])).

cnf(c_43,plain,
    ( v4_ordinal1(sK6) != iProver_top
    | v3_ordinal1(sK7) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_36])).

cnf(c_35,negated_conjecture,
    ( r2_hidden(sK7,sK6)
    | ~ v4_ordinal1(sK6) ),
    inference(cnf_transformation,[],[f104])).

cnf(c_44,plain,
    ( r2_hidden(sK7,sK6) = iProver_top
    | v4_ordinal1(sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_35])).

cnf(c_45,plain,
    ( r2_hidden(k2_xboole_0(sK7,k1_tarski(sK7)),sK6) != iProver_top
    | v4_ordinal1(sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_23,plain,
    ( ~ v3_ordinal1(X0)
    | v3_ordinal1(k2_xboole_0(X0,k1_tarski(X0))) ),
    inference(cnf_transformation,[],[f110])).

cnf(c_1860,plain,
    ( v3_ordinal1(k2_xboole_0(sK7,k1_tarski(sK7)))
    | ~ v3_ordinal1(sK7) ),
    inference(instantiation,[status(thm)],[c_23])).

cnf(c_1861,plain,
    ( v3_ordinal1(k2_xboole_0(sK7,k1_tarski(sK7))) = iProver_top
    | v3_ordinal1(sK7) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1860])).

cnf(c_1030,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_2059,plain,
    ( k2_xboole_0(sK7,k1_tarski(sK7)) = k2_xboole_0(sK7,k1_tarski(sK7)) ),
    inference(instantiation,[status(thm)],[c_1030])).

cnf(c_1920,plain,
    ( X0 != X1
    | k2_xboole_0(sK7,k1_tarski(sK7)) != X1
    | k2_xboole_0(sK7,k1_tarski(sK7)) = X0 ),
    inference(instantiation,[status(thm)],[c_1031])).

cnf(c_2309,plain,
    ( X0 != k2_xboole_0(sK7,k1_tarski(sK7))
    | k2_xboole_0(sK7,k1_tarski(sK7)) = X0
    | k2_xboole_0(sK7,k1_tarski(sK7)) != k2_xboole_0(sK7,k1_tarski(sK7)) ),
    inference(instantiation,[status(thm)],[c_1920])).

cnf(c_2310,plain,
    ( k2_xboole_0(sK7,k1_tarski(sK7)) != k2_xboole_0(sK7,k1_tarski(sK7))
    | k2_xboole_0(sK7,k1_tarski(sK7)) = sK6
    | sK6 != k2_xboole_0(sK7,k1_tarski(sK7)) ),
    inference(instantiation,[status(thm)],[c_2309])).

cnf(c_25,plain,
    ( r1_ordinal1(k2_xboole_0(X0,k1_tarski(X0)),X1)
    | ~ r2_hidden(X0,X1)
    | ~ v3_ordinal1(X1)
    | ~ v3_ordinal1(X0) ),
    inference(cnf_transformation,[],[f112])).

cnf(c_228,plain,
    ( ~ v3_ordinal1(X1)
    | ~ r2_hidden(X0,X1)
    | r1_ordinal1(k2_xboole_0(X0,k1_tarski(X0)),X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_25,c_21])).

cnf(c_229,plain,
    ( r1_ordinal1(k2_xboole_0(X0,k1_tarski(X0)),X1)
    | ~ r2_hidden(X0,X1)
    | ~ v3_ordinal1(X1) ),
    inference(renaming,[status(thm)],[c_228])).

cnf(c_2180,plain,
    ( r1_ordinal1(k2_xboole_0(X0,k1_tarski(X0)),sK6)
    | ~ r2_hidden(X0,sK6)
    | ~ v3_ordinal1(sK6) ),
    inference(instantiation,[status(thm)],[c_229])).

cnf(c_2599,plain,
    ( r1_ordinal1(k2_xboole_0(sK7,k1_tarski(sK7)),sK6)
    | ~ r2_hidden(sK7,sK6)
    | ~ v3_ordinal1(sK6) ),
    inference(instantiation,[status(thm)],[c_2180])).

cnf(c_2600,plain,
    ( r1_ordinal1(k2_xboole_0(sK7,k1_tarski(sK7)),sK6) = iProver_top
    | r2_hidden(sK7,sK6) != iProver_top
    | v3_ordinal1(sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2599])).

cnf(c_20,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k2_xboole_0(X1,k1_tarski(X1)))
    | X1 = X0 ),
    inference(cnf_transformation,[],[f109])).

cnf(c_3624,plain,
    ( r2_hidden(k2_xboole_0(sK7,k1_tarski(sK7)),X0)
    | ~ r2_hidden(k2_xboole_0(sK7,k1_tarski(sK7)),k2_xboole_0(X0,k1_tarski(X0)))
    | X0 = k2_xboole_0(sK7,k1_tarski(sK7)) ),
    inference(instantiation,[status(thm)],[c_20])).

cnf(c_3630,plain,
    ( X0 = k2_xboole_0(sK7,k1_tarski(sK7))
    | r2_hidden(k2_xboole_0(sK7,k1_tarski(sK7)),X0) = iProver_top
    | r2_hidden(k2_xboole_0(sK7,k1_tarski(sK7)),k2_xboole_0(X0,k1_tarski(X0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3624])).

cnf(c_3632,plain,
    ( sK6 = k2_xboole_0(sK7,k1_tarski(sK7))
    | r2_hidden(k2_xboole_0(sK7,k1_tarski(sK7)),k2_xboole_0(sK6,k1_tarski(sK6))) != iProver_top
    | r2_hidden(k2_xboole_0(sK7,k1_tarski(sK7)),sK6) = iProver_top ),
    inference(instantiation,[status(thm)],[c_3630])).

cnf(c_26,plain,
    ( ~ r1_ordinal1(X0,X1)
    | r2_hidden(X0,k2_xboole_0(X1,k1_tarski(X1)))
    | ~ v3_ordinal1(X1)
    | ~ v3_ordinal1(X0) ),
    inference(cnf_transformation,[],[f113])).

cnf(c_2770,plain,
    ( ~ r1_ordinal1(k2_xboole_0(X0,k1_tarski(X0)),sK6)
    | r2_hidden(k2_xboole_0(X0,k1_tarski(X0)),k2_xboole_0(sK6,k1_tarski(sK6)))
    | ~ v3_ordinal1(k2_xboole_0(X0,k1_tarski(X0)))
    | ~ v3_ordinal1(sK6) ),
    inference(instantiation,[status(thm)],[c_26])).

cnf(c_5346,plain,
    ( ~ r1_ordinal1(k2_xboole_0(sK7,k1_tarski(sK7)),sK6)
    | r2_hidden(k2_xboole_0(sK7,k1_tarski(sK7)),k2_xboole_0(sK6,k1_tarski(sK6)))
    | ~ v3_ordinal1(k2_xboole_0(sK7,k1_tarski(sK7)))
    | ~ v3_ordinal1(sK6) ),
    inference(instantiation,[status(thm)],[c_2770])).

cnf(c_5353,plain,
    ( r1_ordinal1(k2_xboole_0(sK7,k1_tarski(sK7)),sK6) != iProver_top
    | r2_hidden(k2_xboole_0(sK7,k1_tarski(sK7)),k2_xboole_0(sK6,k1_tarski(sK6))) = iProver_top
    | v3_ordinal1(k2_xboole_0(sK7,k1_tarski(sK7))) != iProver_top
    | v3_ordinal1(sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5346])).

cnf(c_5735,plain,
    ( k2_xboole_0(sK7,k1_tarski(sK7)) = sK6
    | v4_ordinal1(sK6) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5612,c_39,c_43,c_44,c_45,c_1861,c_2059,c_2310,c_2600,c_3632,c_5353])).

cnf(c_12690,plain,
    ( k2_xboole_0(sK7,k1_tarski(sK7)) = sK6 ),
    inference(superposition,[status(thm)],[c_12556,c_5735])).

cnf(c_1757,plain,
    ( r1_ordinal1(k2_xboole_0(X0,k1_tarski(X0)),X1) = iProver_top
    | r2_hidden(X0,X1) != iProver_top
    | v3_ordinal1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_229])).

cnf(c_12806,plain,
    ( r1_ordinal1(sK6,X0) = iProver_top
    | r2_hidden(sK7,X0) != iProver_top
    | v3_ordinal1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_12690,c_1757])).

cnf(c_15427,plain,
    ( r1_ordinal1(sK6,sK3(X0,sK7)) = iProver_top
    | r2_hidden(sK7,k3_tarski(X0)) != iProver_top
    | v3_ordinal1(sK3(X0,sK7)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1783,c_12806])).

cnf(c_15438,plain,
    ( r1_ordinal1(sK6,sK3(X0,sK7))
    | ~ r2_hidden(sK7,k3_tarski(X0))
    | ~ v3_ordinal1(sK3(X0,sK7)) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_15427])).

cnf(c_15440,plain,
    ( r1_ordinal1(sK6,sK3(sK6,sK7))
    | ~ r2_hidden(sK7,k3_tarski(sK6))
    | ~ v3_ordinal1(sK3(sK6,sK7)) ),
    inference(instantiation,[status(thm)],[c_15438])).

cnf(c_10912,plain,
    ( ~ r2_hidden(sK3(X0,sK7),X0)
    | ~ r1_tarski(X0,sK3(X0,sK7)) ),
    inference(instantiation,[status(thm)],[c_33])).

cnf(c_10914,plain,
    ( ~ r2_hidden(sK3(sK6,sK7),sK6)
    | ~ r1_tarski(sK6,sK3(sK6,sK7)) ),
    inference(instantiation,[status(thm)],[c_10912])).

cnf(c_2227,plain,
    ( ~ r2_hidden(sK3(sK6,X0),X1)
    | ~ v3_ordinal1(X1)
    | v3_ordinal1(sK3(sK6,X0)) ),
    inference(instantiation,[status(thm)],[c_21])).

cnf(c_2731,plain,
    ( ~ r2_hidden(sK3(sK6,X0),sK6)
    | v3_ordinal1(sK3(sK6,X0))
    | ~ v3_ordinal1(sK6) ),
    inference(instantiation,[status(thm)],[c_2227])).

cnf(c_10866,plain,
    ( ~ r2_hidden(sK3(sK6,sK7),sK6)
    | v3_ordinal1(sK3(sK6,sK7))
    | ~ v3_ordinal1(sK6) ),
    inference(instantiation,[status(thm)],[c_2731])).

cnf(c_3406,plain,
    ( r2_hidden(X0,k3_tarski(sK6))
    | r2_hidden(k3_tarski(sK6),X0)
    | ~ v3_ordinal1(X0)
    | ~ v3_ordinal1(k3_tarski(sK6))
    | k3_tarski(sK6) = X0 ),
    inference(instantiation,[status(thm)],[c_22])).

cnf(c_10696,plain,
    ( r2_hidden(k3_tarski(sK6),sK7)
    | r2_hidden(sK7,k3_tarski(sK6))
    | ~ v3_ordinal1(k3_tarski(sK6))
    | ~ v3_ordinal1(sK7)
    | k3_tarski(sK6) = sK7 ),
    inference(instantiation,[status(thm)],[c_3406])).

cnf(c_9508,plain,
    ( ~ r2_hidden(k3_tarski(sK6),sK6) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_9506])).

cnf(c_7830,plain,
    ( ~ v3_ordinal1(X0)
    | v3_ordinal1(k3_tarski(X0)) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_7828])).

cnf(c_7832,plain,
    ( v3_ordinal1(k3_tarski(sK6))
    | ~ v3_ordinal1(sK6) ),
    inference(instantiation,[status(thm)],[c_7830])).

cnf(c_2464,plain,
    ( r2_hidden(X0,sK6)
    | ~ r2_hidden(sK7,sK6)
    | X0 != sK7
    | sK6 != sK6 ),
    inference(instantiation,[status(thm)],[c_1973])).

cnf(c_5760,plain,
    ( r2_hidden(k3_tarski(X0),sK6)
    | ~ r2_hidden(sK7,sK6)
    | k3_tarski(X0) != sK7
    | sK6 != sK6 ),
    inference(instantiation,[status(thm)],[c_2464])).

cnf(c_5766,plain,
    ( r2_hidden(k3_tarski(sK6),sK6)
    | ~ r2_hidden(sK7,sK6)
    | k3_tarski(sK6) != sK7
    | sK6 != sK6 ),
    inference(instantiation,[status(thm)],[c_5760])).

cnf(c_5413,plain,
    ( r2_hidden(sK3(X0,sK7),X0)
    | ~ r2_hidden(sK7,k3_tarski(X0)) ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_5424,plain,
    ( r2_hidden(sK3(sK6,sK7),sK6)
    | ~ r2_hidden(sK7,k3_tarski(sK6)) ),
    inference(instantiation,[status(thm)],[c_5413])).

cnf(c_1761,plain,
    ( r2_hidden(sK7,sK6) = iProver_top
    | v4_ordinal1(sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_35])).

cnf(c_4496,plain,
    ( r2_hidden(X0,k3_tarski(sK6)) = iProver_top
    | r2_hidden(X0,sK7) != iProver_top
    | v4_ordinal1(sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_1761,c_1785])).

cnf(c_4835,plain,
    ( r2_hidden(X0,sK7) != iProver_top
    | r1_tarski(k3_tarski(sK6),X0) != iProver_top
    | v4_ordinal1(sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_4496,c_1763])).

cnf(c_5361,plain,
    ( r2_hidden(k3_tarski(sK6),sK7) != iProver_top
    | v4_ordinal1(sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_1789,c_4835])).

cnf(c_5362,plain,
    ( ~ r2_hidden(k3_tarski(sK6),sK7)
    | ~ v4_ordinal1(sK6) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_5361])).

cnf(c_308,plain,
    ( v4_ordinal1(X0)
    | k3_tarski(X0) != X0 ),
    inference(prop_impl,[status(thm)],[c_13])).

cnf(c_550,plain,
    ( r2_hidden(sK7,sK6)
    | k3_tarski(X0) != X0
    | sK6 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_308,c_35])).

cnf(c_551,plain,
    ( r2_hidden(sK7,sK6)
    | k3_tarski(sK6) != sK6 ),
    inference(unflattening,[status(thm)],[c_550])).

cnf(c_540,plain,
    ( v3_ordinal1(sK7)
    | k3_tarski(X0) != X0
    | sK6 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_308,c_36])).

cnf(c_541,plain,
    ( v3_ordinal1(sK7)
    | k3_tarski(sK6) != sK6 ),
    inference(unflattening,[status(thm)],[c_540])).

cnf(c_103,plain,
    ( v4_ordinal1(sK6)
    | k3_tarski(sK6) != sK6 ),
    inference(instantiation,[status(thm)],[c_13])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_24248,c_15440,c_12448,c_10914,c_10866,c_10696,c_9508,c_7832,c_5766,c_5424,c_5362,c_551,c_541,c_103,c_94,c_90,c_80,c_65,c_47,c_38])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n023.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 12:49:21 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 7.66/1.53  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.66/1.53  
% 7.66/1.53  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.66/1.53  
% 7.66/1.53  ------  iProver source info
% 7.66/1.53  
% 7.66/1.53  git: date: 2020-06-30 10:37:57 +0100
% 7.66/1.53  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.66/1.53  git: non_committed_changes: false
% 7.66/1.53  git: last_make_outside_of_git: false
% 7.66/1.53  
% 7.66/1.53  ------ 
% 7.66/1.53  
% 7.66/1.53  ------ Input Options
% 7.66/1.53  
% 7.66/1.53  --out_options                           all
% 7.66/1.53  --tptp_safe_out                         true
% 7.66/1.53  --problem_path                          ""
% 7.66/1.53  --include_path                          ""
% 7.66/1.53  --clausifier                            res/vclausify_rel
% 7.66/1.53  --clausifier_options                    ""
% 7.66/1.53  --stdin                                 false
% 7.66/1.53  --stats_out                             all
% 7.66/1.53  
% 7.66/1.53  ------ General Options
% 7.66/1.53  
% 7.66/1.53  --fof                                   false
% 7.66/1.53  --time_out_real                         305.
% 7.66/1.53  --time_out_virtual                      -1.
% 7.66/1.53  --symbol_type_check                     false
% 7.66/1.53  --clausify_out                          false
% 7.66/1.53  --sig_cnt_out                           false
% 7.66/1.53  --trig_cnt_out                          false
% 7.66/1.53  --trig_cnt_out_tolerance                1.
% 7.66/1.53  --trig_cnt_out_sk_spl                   false
% 7.66/1.53  --abstr_cl_out                          false
% 7.66/1.53  
% 7.66/1.53  ------ Global Options
% 7.66/1.53  
% 7.66/1.53  --schedule                              default
% 7.66/1.53  --add_important_lit                     false
% 7.66/1.53  --prop_solver_per_cl                    1000
% 7.66/1.53  --min_unsat_core                        false
% 7.66/1.53  --soft_assumptions                      false
% 7.66/1.53  --soft_lemma_size                       3
% 7.66/1.53  --prop_impl_unit_size                   0
% 7.66/1.53  --prop_impl_unit                        []
% 7.66/1.53  --share_sel_clauses                     true
% 7.66/1.53  --reset_solvers                         false
% 7.66/1.53  --bc_imp_inh                            [conj_cone]
% 7.66/1.53  --conj_cone_tolerance                   3.
% 7.66/1.53  --extra_neg_conj                        none
% 7.66/1.53  --large_theory_mode                     true
% 7.66/1.53  --prolific_symb_bound                   200
% 7.66/1.53  --lt_threshold                          2000
% 7.66/1.53  --clause_weak_htbl                      true
% 7.66/1.53  --gc_record_bc_elim                     false
% 7.66/1.53  
% 7.66/1.53  ------ Preprocessing Options
% 7.66/1.53  
% 7.66/1.53  --preprocessing_flag                    true
% 7.66/1.53  --time_out_prep_mult                    0.1
% 7.66/1.53  --splitting_mode                        input
% 7.66/1.53  --splitting_grd                         true
% 7.66/1.53  --splitting_cvd                         false
% 7.66/1.53  --splitting_cvd_svl                     false
% 7.66/1.53  --splitting_nvd                         32
% 7.66/1.53  --sub_typing                            true
% 7.66/1.53  --prep_gs_sim                           true
% 7.66/1.53  --prep_unflatten                        true
% 7.66/1.53  --prep_res_sim                          true
% 7.66/1.53  --prep_upred                            true
% 7.66/1.53  --prep_sem_filter                       exhaustive
% 7.66/1.53  --prep_sem_filter_out                   false
% 7.66/1.53  --pred_elim                             true
% 7.66/1.53  --res_sim_input                         true
% 7.66/1.53  --eq_ax_congr_red                       true
% 7.66/1.53  --pure_diseq_elim                       true
% 7.66/1.53  --brand_transform                       false
% 7.66/1.53  --non_eq_to_eq                          false
% 7.66/1.53  --prep_def_merge                        true
% 7.66/1.53  --prep_def_merge_prop_impl              false
% 7.66/1.53  --prep_def_merge_mbd                    true
% 7.66/1.53  --prep_def_merge_tr_red                 false
% 7.66/1.53  --prep_def_merge_tr_cl                  false
% 7.66/1.53  --smt_preprocessing                     true
% 7.66/1.53  --smt_ac_axioms                         fast
% 7.66/1.53  --preprocessed_out                      false
% 7.66/1.53  --preprocessed_stats                    false
% 7.66/1.53  
% 7.66/1.53  ------ Abstraction refinement Options
% 7.66/1.53  
% 7.66/1.53  --abstr_ref                             []
% 7.66/1.53  --abstr_ref_prep                        false
% 7.66/1.53  --abstr_ref_until_sat                   false
% 7.66/1.53  --abstr_ref_sig_restrict                funpre
% 7.66/1.53  --abstr_ref_af_restrict_to_split_sk     false
% 7.66/1.53  --abstr_ref_under                       []
% 7.66/1.53  
% 7.66/1.53  ------ SAT Options
% 7.66/1.53  
% 7.66/1.53  --sat_mode                              false
% 7.66/1.53  --sat_fm_restart_options                ""
% 7.66/1.53  --sat_gr_def                            false
% 7.66/1.53  --sat_epr_types                         true
% 7.66/1.53  --sat_non_cyclic_types                  false
% 7.66/1.53  --sat_finite_models                     false
% 7.66/1.53  --sat_fm_lemmas                         false
% 7.66/1.53  --sat_fm_prep                           false
% 7.66/1.53  --sat_fm_uc_incr                        true
% 7.66/1.53  --sat_out_model                         small
% 7.66/1.53  --sat_out_clauses                       false
% 7.66/1.53  
% 7.66/1.53  ------ QBF Options
% 7.66/1.53  
% 7.66/1.53  --qbf_mode                              false
% 7.66/1.53  --qbf_elim_univ                         false
% 7.66/1.53  --qbf_dom_inst                          none
% 7.66/1.53  --qbf_dom_pre_inst                      false
% 7.66/1.53  --qbf_sk_in                             false
% 7.66/1.53  --qbf_pred_elim                         true
% 7.66/1.53  --qbf_split                             512
% 7.66/1.53  
% 7.66/1.53  ------ BMC1 Options
% 7.66/1.53  
% 7.66/1.53  --bmc1_incremental                      false
% 7.66/1.53  --bmc1_axioms                           reachable_all
% 7.66/1.53  --bmc1_min_bound                        0
% 7.66/1.53  --bmc1_max_bound                        -1
% 7.66/1.53  --bmc1_max_bound_default                -1
% 7.66/1.53  --bmc1_symbol_reachability              true
% 7.66/1.53  --bmc1_property_lemmas                  false
% 7.66/1.53  --bmc1_k_induction                      false
% 7.66/1.53  --bmc1_non_equiv_states                 false
% 7.66/1.53  --bmc1_deadlock                         false
% 7.66/1.53  --bmc1_ucm                              false
% 7.66/1.53  --bmc1_add_unsat_core                   none
% 7.66/1.53  --bmc1_unsat_core_children              false
% 7.66/1.53  --bmc1_unsat_core_extrapolate_axioms    false
% 7.66/1.53  --bmc1_out_stat                         full
% 7.66/1.53  --bmc1_ground_init                      false
% 7.66/1.53  --bmc1_pre_inst_next_state              false
% 7.66/1.53  --bmc1_pre_inst_state                   false
% 7.66/1.53  --bmc1_pre_inst_reach_state             false
% 7.66/1.53  --bmc1_out_unsat_core                   false
% 7.66/1.53  --bmc1_aig_witness_out                  false
% 7.66/1.53  --bmc1_verbose                          false
% 7.66/1.53  --bmc1_dump_clauses_tptp                false
% 7.66/1.53  --bmc1_dump_unsat_core_tptp             false
% 7.66/1.53  --bmc1_dump_file                        -
% 7.66/1.53  --bmc1_ucm_expand_uc_limit              128
% 7.66/1.53  --bmc1_ucm_n_expand_iterations          6
% 7.66/1.53  --bmc1_ucm_extend_mode                  1
% 7.66/1.53  --bmc1_ucm_init_mode                    2
% 7.66/1.53  --bmc1_ucm_cone_mode                    none
% 7.66/1.53  --bmc1_ucm_reduced_relation_type        0
% 7.66/1.53  --bmc1_ucm_relax_model                  4
% 7.66/1.53  --bmc1_ucm_full_tr_after_sat            true
% 7.66/1.53  --bmc1_ucm_expand_neg_assumptions       false
% 7.66/1.53  --bmc1_ucm_layered_model                none
% 7.66/1.53  --bmc1_ucm_max_lemma_size               10
% 7.66/1.53  
% 7.66/1.53  ------ AIG Options
% 7.66/1.53  
% 7.66/1.53  --aig_mode                              false
% 7.66/1.53  
% 7.66/1.53  ------ Instantiation Options
% 7.66/1.53  
% 7.66/1.53  --instantiation_flag                    true
% 7.66/1.53  --inst_sos_flag                         true
% 7.66/1.53  --inst_sos_phase                        true
% 7.66/1.53  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.66/1.53  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.66/1.53  --inst_lit_sel_side                     num_symb
% 7.66/1.53  --inst_solver_per_active                1400
% 7.66/1.53  --inst_solver_calls_frac                1.
% 7.66/1.53  --inst_passive_queue_type               priority_queues
% 7.66/1.53  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.66/1.53  --inst_passive_queues_freq              [25;2]
% 7.66/1.53  --inst_dismatching                      true
% 7.66/1.53  --inst_eager_unprocessed_to_passive     true
% 7.66/1.53  --inst_prop_sim_given                   true
% 7.66/1.53  --inst_prop_sim_new                     false
% 7.66/1.53  --inst_subs_new                         false
% 7.66/1.53  --inst_eq_res_simp                      false
% 7.66/1.53  --inst_subs_given                       false
% 7.66/1.53  --inst_orphan_elimination               true
% 7.66/1.53  --inst_learning_loop_flag               true
% 7.66/1.53  --inst_learning_start                   3000
% 7.66/1.53  --inst_learning_factor                  2
% 7.66/1.53  --inst_start_prop_sim_after_learn       3
% 7.66/1.53  --inst_sel_renew                        solver
% 7.66/1.53  --inst_lit_activity_flag                true
% 7.66/1.53  --inst_restr_to_given                   false
% 7.66/1.53  --inst_activity_threshold               500
% 7.66/1.53  --inst_out_proof                        true
% 7.66/1.53  
% 7.66/1.53  ------ Resolution Options
% 7.66/1.53  
% 7.66/1.53  --resolution_flag                       true
% 7.66/1.53  --res_lit_sel                           adaptive
% 7.66/1.53  --res_lit_sel_side                      none
% 7.66/1.53  --res_ordering                          kbo
% 7.66/1.53  --res_to_prop_solver                    active
% 7.66/1.53  --res_prop_simpl_new                    false
% 7.66/1.53  --res_prop_simpl_given                  true
% 7.66/1.53  --res_passive_queue_type                priority_queues
% 7.66/1.53  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.66/1.53  --res_passive_queues_freq               [15;5]
% 7.66/1.53  --res_forward_subs                      full
% 7.66/1.53  --res_backward_subs                     full
% 7.66/1.53  --res_forward_subs_resolution           true
% 7.66/1.53  --res_backward_subs_resolution          true
% 7.66/1.53  --res_orphan_elimination                true
% 7.66/1.53  --res_time_limit                        2.
% 7.66/1.53  --res_out_proof                         true
% 7.66/1.53  
% 7.66/1.53  ------ Superposition Options
% 7.66/1.53  
% 7.66/1.53  --superposition_flag                    true
% 7.66/1.53  --sup_passive_queue_type                priority_queues
% 7.66/1.53  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.66/1.53  --sup_passive_queues_freq               [8;1;4]
% 7.66/1.53  --demod_completeness_check              fast
% 7.66/1.53  --demod_use_ground                      true
% 7.66/1.53  --sup_to_prop_solver                    passive
% 7.66/1.53  --sup_prop_simpl_new                    true
% 7.66/1.53  --sup_prop_simpl_given                  true
% 7.66/1.53  --sup_fun_splitting                     true
% 7.66/1.53  --sup_smt_interval                      50000
% 7.66/1.53  
% 7.66/1.53  ------ Superposition Simplification Setup
% 7.66/1.53  
% 7.66/1.53  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 7.66/1.53  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 7.66/1.53  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 7.66/1.53  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 7.66/1.53  --sup_full_triv                         [TrivRules;PropSubs]
% 7.66/1.53  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 7.66/1.53  --sup_full_bw                           [BwDemod;BwSubsumption]
% 7.66/1.53  --sup_immed_triv                        [TrivRules]
% 7.66/1.53  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.66/1.53  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.66/1.53  --sup_immed_bw_main                     []
% 7.66/1.53  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 7.66/1.53  --sup_input_triv                        [Unflattening;TrivRules]
% 7.66/1.53  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.66/1.53  --sup_input_bw                          []
% 7.66/1.53  
% 7.66/1.53  ------ Combination Options
% 7.66/1.53  
% 7.66/1.53  --comb_res_mult                         3
% 7.66/1.53  --comb_sup_mult                         2
% 7.66/1.53  --comb_inst_mult                        10
% 7.66/1.53  
% 7.66/1.53  ------ Debug Options
% 7.66/1.53  
% 7.66/1.53  --dbg_backtrace                         false
% 7.66/1.53  --dbg_dump_prop_clauses                 false
% 7.66/1.53  --dbg_dump_prop_clauses_file            -
% 7.66/1.53  --dbg_out_stat                          false
% 7.66/1.53  ------ Parsing...
% 7.66/1.53  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.66/1.53  
% 7.66/1.53  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e  sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 7.66/1.53  
% 7.66/1.53  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.66/1.53  
% 7.66/1.53  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.66/1.53  ------ Proving...
% 7.66/1.53  ------ Problem Properties 
% 7.66/1.53  
% 7.66/1.53  
% 7.66/1.53  clauses                                 37
% 7.66/1.53  conjectures                             5
% 7.66/1.53  EPR                                     12
% 7.66/1.53  Horn                                    28
% 7.66/1.53  unary                                   5
% 7.66/1.53  binary                                  14
% 7.66/1.53  lits                                    97
% 7.66/1.53  lits eq                                 8
% 7.66/1.53  fd_pure                                 0
% 7.66/1.53  fd_pseudo                               0
% 7.66/1.53  fd_cond                                 0
% 7.66/1.53  fd_pseudo_cond                          6
% 7.66/1.53  AC symbols                              0
% 7.66/1.53  
% 7.66/1.53  ------ Schedule dynamic 5 is on 
% 7.66/1.53  
% 7.66/1.53  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 7.66/1.53  
% 7.66/1.53  
% 7.66/1.53  ------ 
% 7.66/1.53  Current options:
% 7.66/1.53  ------ 
% 7.66/1.53  
% 7.66/1.53  ------ Input Options
% 7.66/1.53  
% 7.66/1.53  --out_options                           all
% 7.66/1.53  --tptp_safe_out                         true
% 7.66/1.53  --problem_path                          ""
% 7.66/1.53  --include_path                          ""
% 7.66/1.53  --clausifier                            res/vclausify_rel
% 7.66/1.53  --clausifier_options                    ""
% 7.66/1.53  --stdin                                 false
% 7.66/1.53  --stats_out                             all
% 7.66/1.53  
% 7.66/1.53  ------ General Options
% 7.66/1.53  
% 7.66/1.53  --fof                                   false
% 7.66/1.53  --time_out_real                         305.
% 7.66/1.53  --time_out_virtual                      -1.
% 7.66/1.53  --symbol_type_check                     false
% 7.66/1.53  --clausify_out                          false
% 7.66/1.53  --sig_cnt_out                           false
% 7.66/1.53  --trig_cnt_out                          false
% 7.66/1.53  --trig_cnt_out_tolerance                1.
% 7.66/1.53  --trig_cnt_out_sk_spl                   false
% 7.66/1.53  --abstr_cl_out                          false
% 7.66/1.53  
% 7.66/1.53  ------ Global Options
% 7.66/1.53  
% 7.66/1.53  --schedule                              default
% 7.66/1.53  --add_important_lit                     false
% 7.66/1.53  --prop_solver_per_cl                    1000
% 7.66/1.53  --min_unsat_core                        false
% 7.66/1.53  --soft_assumptions                      false
% 7.66/1.53  --soft_lemma_size                       3
% 7.66/1.53  --prop_impl_unit_size                   0
% 7.66/1.53  --prop_impl_unit                        []
% 7.66/1.53  --share_sel_clauses                     true
% 7.66/1.53  --reset_solvers                         false
% 7.66/1.53  --bc_imp_inh                            [conj_cone]
% 7.66/1.53  --conj_cone_tolerance                   3.
% 7.66/1.53  --extra_neg_conj                        none
% 7.66/1.53  --large_theory_mode                     true
% 7.66/1.53  --prolific_symb_bound                   200
% 7.66/1.53  --lt_threshold                          2000
% 7.66/1.53  --clause_weak_htbl                      true
% 7.66/1.53  --gc_record_bc_elim                     false
% 7.66/1.53  
% 7.66/1.53  ------ Preprocessing Options
% 7.66/1.53  
% 7.66/1.53  --preprocessing_flag                    true
% 7.66/1.53  --time_out_prep_mult                    0.1
% 7.66/1.53  --splitting_mode                        input
% 7.66/1.53  --splitting_grd                         true
% 7.66/1.53  --splitting_cvd                         false
% 7.66/1.53  --splitting_cvd_svl                     false
% 7.66/1.53  --splitting_nvd                         32
% 7.66/1.53  --sub_typing                            true
% 7.66/1.53  --prep_gs_sim                           true
% 7.66/1.53  --prep_unflatten                        true
% 7.66/1.53  --prep_res_sim                          true
% 7.66/1.53  --prep_upred                            true
% 7.66/1.53  --prep_sem_filter                       exhaustive
% 7.66/1.53  --prep_sem_filter_out                   false
% 7.66/1.53  --pred_elim                             true
% 7.66/1.53  --res_sim_input                         true
% 7.66/1.53  --eq_ax_congr_red                       true
% 7.66/1.53  --pure_diseq_elim                       true
% 7.66/1.53  --brand_transform                       false
% 7.66/1.53  --non_eq_to_eq                          false
% 7.66/1.53  --prep_def_merge                        true
% 7.66/1.53  --prep_def_merge_prop_impl              false
% 7.66/1.53  --prep_def_merge_mbd                    true
% 7.66/1.53  --prep_def_merge_tr_red                 false
% 7.66/1.53  --prep_def_merge_tr_cl                  false
% 7.66/1.53  --smt_preprocessing                     true
% 7.66/1.53  --smt_ac_axioms                         fast
% 7.66/1.53  --preprocessed_out                      false
% 7.66/1.53  --preprocessed_stats                    false
% 7.66/1.53  
% 7.66/1.53  ------ Abstraction refinement Options
% 7.66/1.53  
% 7.66/1.53  --abstr_ref                             []
% 7.66/1.53  --abstr_ref_prep                        false
% 7.66/1.53  --abstr_ref_until_sat                   false
% 7.66/1.53  --abstr_ref_sig_restrict                funpre
% 7.66/1.53  --abstr_ref_af_restrict_to_split_sk     false
% 7.66/1.53  --abstr_ref_under                       []
% 7.66/1.53  
% 7.66/1.53  ------ SAT Options
% 7.66/1.53  
% 7.66/1.53  --sat_mode                              false
% 7.66/1.53  --sat_fm_restart_options                ""
% 7.66/1.53  --sat_gr_def                            false
% 7.66/1.53  --sat_epr_types                         true
% 7.66/1.53  --sat_non_cyclic_types                  false
% 7.66/1.53  --sat_finite_models                     false
% 7.66/1.53  --sat_fm_lemmas                         false
% 7.66/1.53  --sat_fm_prep                           false
% 7.66/1.53  --sat_fm_uc_incr                        true
% 7.66/1.53  --sat_out_model                         small
% 7.66/1.53  --sat_out_clauses                       false
% 7.66/1.53  
% 7.66/1.53  ------ QBF Options
% 7.66/1.53  
% 7.66/1.53  --qbf_mode                              false
% 7.66/1.53  --qbf_elim_univ                         false
% 7.66/1.53  --qbf_dom_inst                          none
% 7.66/1.53  --qbf_dom_pre_inst                      false
% 7.66/1.53  --qbf_sk_in                             false
% 7.66/1.53  --qbf_pred_elim                         true
% 7.66/1.53  --qbf_split                             512
% 7.66/1.53  
% 7.66/1.53  ------ BMC1 Options
% 7.66/1.53  
% 7.66/1.53  --bmc1_incremental                      false
% 7.66/1.53  --bmc1_axioms                           reachable_all
% 7.66/1.53  --bmc1_min_bound                        0
% 7.66/1.53  --bmc1_max_bound                        -1
% 7.66/1.53  --bmc1_max_bound_default                -1
% 7.66/1.53  --bmc1_symbol_reachability              true
% 7.66/1.53  --bmc1_property_lemmas                  false
% 7.66/1.53  --bmc1_k_induction                      false
% 7.66/1.53  --bmc1_non_equiv_states                 false
% 7.66/1.53  --bmc1_deadlock                         false
% 7.66/1.53  --bmc1_ucm                              false
% 7.66/1.53  --bmc1_add_unsat_core                   none
% 7.66/1.53  --bmc1_unsat_core_children              false
% 7.66/1.53  --bmc1_unsat_core_extrapolate_axioms    false
% 7.66/1.53  --bmc1_out_stat                         full
% 7.66/1.53  --bmc1_ground_init                      false
% 7.66/1.53  --bmc1_pre_inst_next_state              false
% 7.66/1.53  --bmc1_pre_inst_state                   false
% 7.66/1.53  --bmc1_pre_inst_reach_state             false
% 7.66/1.53  --bmc1_out_unsat_core                   false
% 7.66/1.53  --bmc1_aig_witness_out                  false
% 7.66/1.53  --bmc1_verbose                          false
% 7.66/1.53  --bmc1_dump_clauses_tptp                false
% 7.66/1.53  --bmc1_dump_unsat_core_tptp             false
% 7.66/1.53  --bmc1_dump_file                        -
% 7.66/1.53  --bmc1_ucm_expand_uc_limit              128
% 7.66/1.53  --bmc1_ucm_n_expand_iterations          6
% 7.66/1.53  --bmc1_ucm_extend_mode                  1
% 7.66/1.53  --bmc1_ucm_init_mode                    2
% 7.66/1.53  --bmc1_ucm_cone_mode                    none
% 7.66/1.53  --bmc1_ucm_reduced_relation_type        0
% 7.66/1.53  --bmc1_ucm_relax_model                  4
% 7.66/1.53  --bmc1_ucm_full_tr_after_sat            true
% 7.66/1.53  --bmc1_ucm_expand_neg_assumptions       false
% 7.66/1.53  --bmc1_ucm_layered_model                none
% 7.66/1.53  --bmc1_ucm_max_lemma_size               10
% 7.66/1.53  
% 7.66/1.53  ------ AIG Options
% 7.66/1.53  
% 7.66/1.53  --aig_mode                              false
% 7.66/1.53  
% 7.66/1.53  ------ Instantiation Options
% 7.66/1.53  
% 7.66/1.53  --instantiation_flag                    true
% 7.66/1.53  --inst_sos_flag                         true
% 7.66/1.53  --inst_sos_phase                        true
% 7.66/1.53  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.66/1.53  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.66/1.53  --inst_lit_sel_side                     none
% 7.66/1.53  --inst_solver_per_active                1400
% 7.66/1.53  --inst_solver_calls_frac                1.
% 7.66/1.53  --inst_passive_queue_type               priority_queues
% 7.66/1.53  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.66/1.53  --inst_passive_queues_freq              [25;2]
% 7.66/1.53  --inst_dismatching                      true
% 7.66/1.53  --inst_eager_unprocessed_to_passive     true
% 7.66/1.53  --inst_prop_sim_given                   true
% 7.66/1.53  --inst_prop_sim_new                     false
% 7.66/1.53  --inst_subs_new                         false
% 7.66/1.53  --inst_eq_res_simp                      false
% 7.66/1.53  --inst_subs_given                       false
% 7.66/1.53  --inst_orphan_elimination               true
% 7.66/1.53  --inst_learning_loop_flag               true
% 7.66/1.53  --inst_learning_start                   3000
% 7.66/1.53  --inst_learning_factor                  2
% 7.66/1.53  --inst_start_prop_sim_after_learn       3
% 7.66/1.53  --inst_sel_renew                        solver
% 7.66/1.53  --inst_lit_activity_flag                true
% 7.66/1.53  --inst_restr_to_given                   false
% 7.66/1.53  --inst_activity_threshold               500
% 7.66/1.53  --inst_out_proof                        true
% 7.66/1.53  
% 7.66/1.53  ------ Resolution Options
% 7.66/1.53  
% 7.66/1.53  --resolution_flag                       false
% 7.66/1.53  --res_lit_sel                           adaptive
% 7.66/1.53  --res_lit_sel_side                      none
% 7.66/1.53  --res_ordering                          kbo
% 7.66/1.53  --res_to_prop_solver                    active
% 7.66/1.53  --res_prop_simpl_new                    false
% 7.66/1.53  --res_prop_simpl_given                  true
% 7.66/1.53  --res_passive_queue_type                priority_queues
% 7.66/1.53  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.66/1.53  --res_passive_queues_freq               [15;5]
% 7.66/1.53  --res_forward_subs                      full
% 7.66/1.53  --res_backward_subs                     full
% 7.66/1.53  --res_forward_subs_resolution           true
% 7.66/1.53  --res_backward_subs_resolution          true
% 7.66/1.53  --res_orphan_elimination                true
% 7.66/1.53  --res_time_limit                        2.
% 7.66/1.53  --res_out_proof                         true
% 7.66/1.53  
% 7.66/1.53  ------ Superposition Options
% 7.66/1.53  
% 7.66/1.53  --superposition_flag                    true
% 7.66/1.53  --sup_passive_queue_type                priority_queues
% 7.66/1.53  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.66/1.53  --sup_passive_queues_freq               [8;1;4]
% 7.66/1.53  --demod_completeness_check              fast
% 7.66/1.53  --demod_use_ground                      true
% 7.66/1.53  --sup_to_prop_solver                    passive
% 7.66/1.53  --sup_prop_simpl_new                    true
% 7.66/1.53  --sup_prop_simpl_given                  true
% 7.66/1.53  --sup_fun_splitting                     true
% 7.66/1.53  --sup_smt_interval                      50000
% 7.66/1.53  
% 7.66/1.53  ------ Superposition Simplification Setup
% 7.66/1.53  
% 7.66/1.53  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 7.66/1.53  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 7.66/1.53  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 7.66/1.53  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 7.66/1.53  --sup_full_triv                         [TrivRules;PropSubs]
% 7.66/1.53  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 7.66/1.53  --sup_full_bw                           [BwDemod;BwSubsumption]
% 7.66/1.53  --sup_immed_triv                        [TrivRules]
% 7.66/1.53  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.66/1.53  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.66/1.53  --sup_immed_bw_main                     []
% 7.66/1.53  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 7.66/1.53  --sup_input_triv                        [Unflattening;TrivRules]
% 7.66/1.53  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.66/1.53  --sup_input_bw                          []
% 7.66/1.53  
% 7.66/1.53  ------ Combination Options
% 7.66/1.53  
% 7.66/1.53  --comb_res_mult                         3
% 7.66/1.53  --comb_sup_mult                         2
% 7.66/1.53  --comb_inst_mult                        10
% 7.66/1.53  
% 7.66/1.53  ------ Debug Options
% 7.66/1.53  
% 7.66/1.53  --dbg_backtrace                         false
% 7.66/1.53  --dbg_dump_prop_clauses                 false
% 7.66/1.53  --dbg_dump_prop_clauses_file            -
% 7.66/1.53  --dbg_out_stat                          false
% 7.66/1.53  
% 7.66/1.53  
% 7.66/1.53  
% 7.66/1.53  
% 7.66/1.53  ------ Proving...
% 7.66/1.53  
% 7.66/1.53  
% 7.66/1.53  % SZS status Theorem for theBenchmark.p
% 7.66/1.53  
% 7.66/1.53  % SZS output start CNFRefutation for theBenchmark.p
% 7.66/1.53  
% 7.66/1.53  fof(f7,axiom,(
% 7.66/1.53    ! [X0,X1] : ((v3_ordinal1(X1) & v3_ordinal1(X0)) => (r1_ordinal1(X0,X1) <=> r1_tarski(X0,X1)))),
% 7.66/1.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.66/1.53  
% 7.66/1.53  fof(f23,plain,(
% 7.66/1.53    ! [X0,X1] : ((r1_ordinal1(X0,X1) <=> r1_tarski(X0,X1)) | (~v3_ordinal1(X1) | ~v3_ordinal1(X0)))),
% 7.66/1.53    inference(ennf_transformation,[],[f7])).
% 7.66/1.53  
% 7.66/1.53  fof(f24,plain,(
% 7.66/1.53    ! [X0,X1] : ((r1_ordinal1(X0,X1) <=> r1_tarski(X0,X1)) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0))),
% 7.66/1.53    inference(flattening,[],[f23])).
% 7.66/1.53  
% 7.66/1.53  fof(f51,plain,(
% 7.66/1.53    ! [X0,X1] : (((r1_ordinal1(X0,X1) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~r1_ordinal1(X0,X1))) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0))),
% 7.66/1.53    inference(nnf_transformation,[],[f24])).
% 7.66/1.53  
% 7.66/1.53  fof(f82,plain,(
% 7.66/1.53    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r1_ordinal1(X0,X1) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0)) )),
% 7.66/1.53    inference(cnf_transformation,[],[f51])).
% 7.66/1.53  
% 7.66/1.53  fof(f3,axiom,(
% 7.66/1.53    ! [X0,X1] : (k3_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (r2_hidden(X3,X0) & r2_hidden(X2,X3))))),
% 7.66/1.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.66/1.53  
% 7.66/1.53  fof(f44,plain,(
% 7.66/1.53    ! [X0,X1] : ((k3_tarski(X0) = X1 | ? [X2] : ((! [X3] : (~r2_hidden(X3,X0) | ~r2_hidden(X2,X3)) | ~r2_hidden(X2,X1)) & (? [X3] : (r2_hidden(X3,X0) & r2_hidden(X2,X3)) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ! [X3] : (~r2_hidden(X3,X0) | ~r2_hidden(X2,X3))) & (? [X3] : (r2_hidden(X3,X0) & r2_hidden(X2,X3)) | ~r2_hidden(X2,X1))) | k3_tarski(X0) != X1))),
% 7.66/1.53    inference(nnf_transformation,[],[f3])).
% 7.66/1.53  
% 7.66/1.53  fof(f45,plain,(
% 7.66/1.53    ! [X0,X1] : ((k3_tarski(X0) = X1 | ? [X2] : ((! [X3] : (~r2_hidden(X3,X0) | ~r2_hidden(X2,X3)) | ~r2_hidden(X2,X1)) & (? [X4] : (r2_hidden(X4,X0) & r2_hidden(X2,X4)) | r2_hidden(X2,X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : (~r2_hidden(X6,X0) | ~r2_hidden(X5,X6))) & (? [X7] : (r2_hidden(X7,X0) & r2_hidden(X5,X7)) | ~r2_hidden(X5,X1))) | k3_tarski(X0) != X1))),
% 7.66/1.53    inference(rectify,[],[f44])).
% 7.66/1.53  
% 7.66/1.53  fof(f48,plain,(
% 7.66/1.53    ! [X5,X0] : (? [X7] : (r2_hidden(X7,X0) & r2_hidden(X5,X7)) => (r2_hidden(sK3(X0,X5),X0) & r2_hidden(X5,sK3(X0,X5))))),
% 7.66/1.53    introduced(choice_axiom,[])).
% 7.66/1.53  
% 7.66/1.53  fof(f47,plain,(
% 7.66/1.53    ( ! [X2] : (! [X1,X0] : (? [X4] : (r2_hidden(X4,X0) & r2_hidden(X2,X4)) => (r2_hidden(sK2(X0,X1),X0) & r2_hidden(X2,sK2(X0,X1))))) )),
% 7.66/1.53    introduced(choice_axiom,[])).
% 7.66/1.53  
% 7.66/1.53  fof(f46,plain,(
% 7.66/1.53    ! [X1,X0] : (? [X2] : ((! [X3] : (~r2_hidden(X3,X0) | ~r2_hidden(X2,X3)) | ~r2_hidden(X2,X1)) & (? [X4] : (r2_hidden(X4,X0) & r2_hidden(X2,X4)) | r2_hidden(X2,X1))) => ((! [X3] : (~r2_hidden(X3,X0) | ~r2_hidden(sK1(X0,X1),X3)) | ~r2_hidden(sK1(X0,X1),X1)) & (? [X4] : (r2_hidden(X4,X0) & r2_hidden(sK1(X0,X1),X4)) | r2_hidden(sK1(X0,X1),X1))))),
% 7.66/1.53    introduced(choice_axiom,[])).
% 7.66/1.53  
% 7.66/1.53  fof(f49,plain,(
% 7.66/1.53    ! [X0,X1] : ((k3_tarski(X0) = X1 | ((! [X3] : (~r2_hidden(X3,X0) | ~r2_hidden(sK1(X0,X1),X3)) | ~r2_hidden(sK1(X0,X1),X1)) & ((r2_hidden(sK2(X0,X1),X0) & r2_hidden(sK1(X0,X1),sK2(X0,X1))) | r2_hidden(sK1(X0,X1),X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : (~r2_hidden(X6,X0) | ~r2_hidden(X5,X6))) & ((r2_hidden(sK3(X0,X5),X0) & r2_hidden(X5,sK3(X0,X5))) | ~r2_hidden(X5,X1))) | k3_tarski(X0) != X1))),
% 7.66/1.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f45,f48,f47,f46])).
% 7.66/1.53  
% 7.66/1.53  fof(f72,plain,(
% 7.66/1.53    ( ! [X0,X5,X1] : (r2_hidden(X5,sK3(X0,X5)) | ~r2_hidden(X5,X1) | k3_tarski(X0) != X1) )),
% 7.66/1.53    inference(cnf_transformation,[],[f49])).
% 7.66/1.53  
% 7.66/1.53  fof(f121,plain,(
% 7.66/1.53    ( ! [X0,X5] : (r2_hidden(X5,sK3(X0,X5)) | ~r2_hidden(X5,k3_tarski(X0))) )),
% 7.66/1.53    inference(equality_resolution,[],[f72])).
% 7.66/1.53  
% 7.66/1.53  fof(f11,axiom,(
% 7.66/1.53    ! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => ~(~r2_hidden(X1,X0) & X0 != X1 & ~r2_hidden(X0,X1))))),
% 7.66/1.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.66/1.53  
% 7.66/1.53  fof(f27,plain,(
% 7.66/1.53    ! [X0] : (! [X1] : ((r2_hidden(X1,X0) | X0 = X1 | r2_hidden(X0,X1)) | ~v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 7.66/1.53    inference(ennf_transformation,[],[f11])).
% 7.66/1.53  
% 7.66/1.53  fof(f28,plain,(
% 7.66/1.53    ! [X0] : (! [X1] : (r2_hidden(X1,X0) | X0 = X1 | r2_hidden(X0,X1) | ~v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 7.66/1.53    inference(flattening,[],[f27])).
% 7.66/1.53  
% 7.66/1.53  fof(f89,plain,(
% 7.66/1.53    ( ! [X0,X1] : (r2_hidden(X1,X0) | X0 = X1 | r2_hidden(X0,X1) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0)) )),
% 7.66/1.53    inference(cnf_transformation,[],[f28])).
% 7.66/1.53  
% 7.66/1.53  fof(f18,conjecture,(
% 7.66/1.53    ! [X0] : (v3_ordinal1(X0) => (v4_ordinal1(X0) <=> ! [X1] : (v3_ordinal1(X1) => (r2_hidden(X1,X0) => r2_hidden(k1_ordinal1(X1),X0)))))),
% 7.66/1.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.66/1.53  
% 7.66/1.53  fof(f19,negated_conjecture,(
% 7.66/1.53    ~! [X0] : (v3_ordinal1(X0) => (v4_ordinal1(X0) <=> ! [X1] : (v3_ordinal1(X1) => (r2_hidden(X1,X0) => r2_hidden(k1_ordinal1(X1),X0)))))),
% 7.66/1.53    inference(negated_conjecture,[],[f18])).
% 7.66/1.53  
% 7.66/1.53  fof(f36,plain,(
% 7.66/1.53    ? [X0] : ((v4_ordinal1(X0) <~> ! [X1] : ((r2_hidden(k1_ordinal1(X1),X0) | ~r2_hidden(X1,X0)) | ~v3_ordinal1(X1))) & v3_ordinal1(X0))),
% 7.66/1.53    inference(ennf_transformation,[],[f19])).
% 7.66/1.53  
% 7.66/1.53  fof(f37,plain,(
% 7.66/1.53    ? [X0] : ((v4_ordinal1(X0) <~> ! [X1] : (r2_hidden(k1_ordinal1(X1),X0) | ~r2_hidden(X1,X0) | ~v3_ordinal1(X1))) & v3_ordinal1(X0))),
% 7.66/1.53    inference(flattening,[],[f36])).
% 7.66/1.53  
% 7.66/1.53  fof(f60,plain,(
% 7.66/1.53    ? [X0] : (((? [X1] : (~r2_hidden(k1_ordinal1(X1),X0) & r2_hidden(X1,X0) & v3_ordinal1(X1)) | ~v4_ordinal1(X0)) & (! [X1] : (r2_hidden(k1_ordinal1(X1),X0) | ~r2_hidden(X1,X0) | ~v3_ordinal1(X1)) | v4_ordinal1(X0))) & v3_ordinal1(X0))),
% 7.66/1.53    inference(nnf_transformation,[],[f37])).
% 7.66/1.53  
% 7.66/1.53  fof(f61,plain,(
% 7.66/1.53    ? [X0] : ((? [X1] : (~r2_hidden(k1_ordinal1(X1),X0) & r2_hidden(X1,X0) & v3_ordinal1(X1)) | ~v4_ordinal1(X0)) & (! [X1] : (r2_hidden(k1_ordinal1(X1),X0) | ~r2_hidden(X1,X0) | ~v3_ordinal1(X1)) | v4_ordinal1(X0)) & v3_ordinal1(X0))),
% 7.66/1.53    inference(flattening,[],[f60])).
% 7.66/1.53  
% 7.66/1.53  fof(f62,plain,(
% 7.66/1.53    ? [X0] : ((? [X1] : (~r2_hidden(k1_ordinal1(X1),X0) & r2_hidden(X1,X0) & v3_ordinal1(X1)) | ~v4_ordinal1(X0)) & (! [X2] : (r2_hidden(k1_ordinal1(X2),X0) | ~r2_hidden(X2,X0) | ~v3_ordinal1(X2)) | v4_ordinal1(X0)) & v3_ordinal1(X0))),
% 7.66/1.53    inference(rectify,[],[f61])).
% 7.66/1.53  
% 7.66/1.53  fof(f64,plain,(
% 7.66/1.53    ( ! [X0] : (? [X1] : (~r2_hidden(k1_ordinal1(X1),X0) & r2_hidden(X1,X0) & v3_ordinal1(X1)) => (~r2_hidden(k1_ordinal1(sK7),X0) & r2_hidden(sK7,X0) & v3_ordinal1(sK7))) )),
% 7.66/1.53    introduced(choice_axiom,[])).
% 7.66/1.53  
% 7.66/1.53  fof(f63,plain,(
% 7.66/1.53    ? [X0] : ((? [X1] : (~r2_hidden(k1_ordinal1(X1),X0) & r2_hidden(X1,X0) & v3_ordinal1(X1)) | ~v4_ordinal1(X0)) & (! [X2] : (r2_hidden(k1_ordinal1(X2),X0) | ~r2_hidden(X2,X0) | ~v3_ordinal1(X2)) | v4_ordinal1(X0)) & v3_ordinal1(X0)) => ((? [X1] : (~r2_hidden(k1_ordinal1(X1),sK6) & r2_hidden(X1,sK6) & v3_ordinal1(X1)) | ~v4_ordinal1(sK6)) & (! [X2] : (r2_hidden(k1_ordinal1(X2),sK6) | ~r2_hidden(X2,sK6) | ~v3_ordinal1(X2)) | v4_ordinal1(sK6)) & v3_ordinal1(sK6))),
% 7.66/1.53    introduced(choice_axiom,[])).
% 7.66/1.53  
% 7.66/1.53  fof(f65,plain,(
% 7.66/1.53    ((~r2_hidden(k1_ordinal1(sK7),sK6) & r2_hidden(sK7,sK6) & v3_ordinal1(sK7)) | ~v4_ordinal1(sK6)) & (! [X2] : (r2_hidden(k1_ordinal1(X2),sK6) | ~r2_hidden(X2,sK6) | ~v3_ordinal1(X2)) | v4_ordinal1(sK6)) & v3_ordinal1(sK6)),
% 7.66/1.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7])],[f62,f64,f63])).
% 7.66/1.53  
% 7.66/1.53  fof(f102,plain,(
% 7.66/1.53    ( ! [X2] : (r2_hidden(k1_ordinal1(X2),sK6) | ~r2_hidden(X2,sK6) | ~v3_ordinal1(X2) | v4_ordinal1(sK6)) )),
% 7.66/1.53    inference(cnf_transformation,[],[f65])).
% 7.66/1.53  
% 7.66/1.53  fof(f5,axiom,(
% 7.66/1.53    ! [X0] : k1_ordinal1(X0) = k2_xboole_0(X0,k1_tarski(X0))),
% 7.66/1.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.66/1.53  
% 7.66/1.53  fof(f79,plain,(
% 7.66/1.53    ( ! [X0] : (k1_ordinal1(X0) = k2_xboole_0(X0,k1_tarski(X0))) )),
% 7.66/1.53    inference(cnf_transformation,[],[f5])).
% 7.66/1.53  
% 7.66/1.53  fof(f116,plain,(
% 7.66/1.53    ( ! [X2] : (r2_hidden(k2_xboole_0(X2,k1_tarski(X2)),sK6) | ~r2_hidden(X2,sK6) | ~v3_ordinal1(X2) | v4_ordinal1(sK6)) )),
% 7.66/1.53    inference(definition_unfolding,[],[f102,f79])).
% 7.66/1.53  
% 7.66/1.53  fof(f9,axiom,(
% 7.66/1.53    ! [X0,X1] : (r2_hidden(X0,k1_ordinal1(X1)) <=> (X0 = X1 | r2_hidden(X0,X1)))),
% 7.66/1.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.66/1.53  
% 7.66/1.53  fof(f52,plain,(
% 7.66/1.53    ! [X0,X1] : ((r2_hidden(X0,k1_ordinal1(X1)) | (X0 != X1 & ~r2_hidden(X0,X1))) & ((X0 = X1 | r2_hidden(X0,X1)) | ~r2_hidden(X0,k1_ordinal1(X1))))),
% 7.66/1.53    inference(nnf_transformation,[],[f9])).
% 7.66/1.53  
% 7.66/1.53  fof(f53,plain,(
% 7.66/1.53    ! [X0,X1] : ((r2_hidden(X0,k1_ordinal1(X1)) | (X0 != X1 & ~r2_hidden(X0,X1))) & (X0 = X1 | r2_hidden(X0,X1) | ~r2_hidden(X0,k1_ordinal1(X1))))),
% 7.66/1.53    inference(flattening,[],[f52])).
% 7.66/1.53  
% 7.66/1.53  fof(f87,plain,(
% 7.66/1.53    ( ! [X0,X1] : (r2_hidden(X0,k1_ordinal1(X1)) | X0 != X1) )),
% 7.66/1.53    inference(cnf_transformation,[],[f53])).
% 7.66/1.53  
% 7.66/1.53  fof(f107,plain,(
% 7.66/1.53    ( ! [X0,X1] : (r2_hidden(X0,k2_xboole_0(X1,k1_tarski(X1))) | X0 != X1) )),
% 7.66/1.53    inference(definition_unfolding,[],[f87,f79])).
% 7.66/1.53  
% 7.66/1.53  fof(f122,plain,(
% 7.66/1.53    ( ! [X1] : (r2_hidden(X1,k2_xboole_0(X1,k1_tarski(X1)))) )),
% 7.66/1.53    inference(equality_resolution,[],[f107])).
% 7.66/1.53  
% 7.66/1.53  fof(f74,plain,(
% 7.66/1.53    ( ! [X6,X0,X5,X1] : (r2_hidden(X5,X1) | ~r2_hidden(X6,X0) | ~r2_hidden(X5,X6) | k3_tarski(X0) != X1) )),
% 7.66/1.53    inference(cnf_transformation,[],[f49])).
% 7.66/1.53  
% 7.66/1.53  fof(f119,plain,(
% 7.66/1.53    ( ! [X6,X0,X5] : (r2_hidden(X5,k3_tarski(X0)) | ~r2_hidden(X6,X0) | ~r2_hidden(X5,X6)) )),
% 7.66/1.53    inference(equality_resolution,[],[f74])).
% 7.66/1.53  
% 7.66/1.53  fof(f2,axiom,(
% 7.66/1.53    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 7.66/1.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.66/1.53  
% 7.66/1.53  fof(f42,plain,(
% 7.66/1.53    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 7.66/1.53    inference(nnf_transformation,[],[f2])).
% 7.66/1.53  
% 7.66/1.53  fof(f43,plain,(
% 7.66/1.53    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 7.66/1.53    inference(flattening,[],[f42])).
% 7.66/1.53  
% 7.66/1.53  fof(f69,plain,(
% 7.66/1.53    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 7.66/1.53    inference(cnf_transformation,[],[f43])).
% 7.66/1.53  
% 7.66/1.53  fof(f118,plain,(
% 7.66/1.53    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 7.66/1.53    inference(equality_resolution,[],[f69])).
% 7.66/1.53  
% 7.66/1.53  fof(f86,plain,(
% 7.66/1.53    ( ! [X0,X1] : (r2_hidden(X0,k1_ordinal1(X1)) | ~r2_hidden(X0,X1)) )),
% 7.66/1.53    inference(cnf_transformation,[],[f53])).
% 7.66/1.53  
% 7.66/1.53  fof(f108,plain,(
% 7.66/1.53    ( ! [X0,X1] : (r2_hidden(X0,k2_xboole_0(X1,k1_tarski(X1))) | ~r2_hidden(X0,X1)) )),
% 7.66/1.53    inference(definition_unfolding,[],[f86,f79])).
% 7.66/1.53  
% 7.66/1.53  fof(f17,axiom,(
% 7.66/1.53    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 7.66/1.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.66/1.53  
% 7.66/1.53  fof(f35,plain,(
% 7.66/1.53    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 7.66/1.53    inference(ennf_transformation,[],[f17])).
% 7.66/1.53  
% 7.66/1.53  fof(f100,plain,(
% 7.66/1.53    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1)) )),
% 7.66/1.53    inference(cnf_transformation,[],[f35])).
% 7.66/1.53  
% 7.66/1.53  fof(f101,plain,(
% 7.66/1.53    v3_ordinal1(sK6)),
% 7.66/1.53    inference(cnf_transformation,[],[f65])).
% 7.66/1.53  
% 7.66/1.53  fof(f14,axiom,(
% 7.66/1.53    ! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => (r2_hidden(X0,k1_ordinal1(X1)) <=> r1_ordinal1(X0,X1))))),
% 7.66/1.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.66/1.53  
% 7.66/1.53  fof(f31,plain,(
% 7.66/1.53    ! [X0] : (! [X1] : ((r2_hidden(X0,k1_ordinal1(X1)) <=> r1_ordinal1(X0,X1)) | ~v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 7.66/1.53    inference(ennf_transformation,[],[f14])).
% 7.66/1.53  
% 7.66/1.53  fof(f55,plain,(
% 7.66/1.53    ! [X0] : (! [X1] : (((r2_hidden(X0,k1_ordinal1(X1)) | ~r1_ordinal1(X0,X1)) & (r1_ordinal1(X0,X1) | ~r2_hidden(X0,k1_ordinal1(X1)))) | ~v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 7.66/1.53    inference(nnf_transformation,[],[f31])).
% 7.66/1.53  
% 7.66/1.53  fof(f93,plain,(
% 7.66/1.53    ( ! [X0,X1] : (r1_ordinal1(X0,X1) | ~r2_hidden(X0,k1_ordinal1(X1)) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0)) )),
% 7.66/1.53    inference(cnf_transformation,[],[f55])).
% 7.66/1.53  
% 7.66/1.53  fof(f114,plain,(
% 7.66/1.53    ( ! [X0,X1] : (r1_ordinal1(X0,X1) | ~r2_hidden(X0,k2_xboole_0(X1,k1_tarski(X1))) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0)) )),
% 7.66/1.53    inference(definition_unfolding,[],[f93,f79])).
% 7.66/1.53  
% 7.66/1.53  fof(f6,axiom,(
% 7.66/1.53    ! [X0] : (v4_ordinal1(X0) <=> k3_tarski(X0) = X0)),
% 7.66/1.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.66/1.53  
% 7.66/1.53  fof(f50,plain,(
% 7.66/1.53    ! [X0] : ((v4_ordinal1(X0) | k3_tarski(X0) != X0) & (k3_tarski(X0) = X0 | ~v4_ordinal1(X0)))),
% 7.66/1.53    inference(nnf_transformation,[],[f6])).
% 7.66/1.53  
% 7.66/1.53  fof(f80,plain,(
% 7.66/1.53    ( ! [X0] : (k3_tarski(X0) = X0 | ~v4_ordinal1(X0)) )),
% 7.66/1.53    inference(cnf_transformation,[],[f50])).
% 7.66/1.53  
% 7.66/1.53  fof(f15,axiom,(
% 7.66/1.53    ! [X0] : (! [X1] : (r2_hidden(X1,X0) => v3_ordinal1(X1)) => v3_ordinal1(k3_tarski(X0)))),
% 7.66/1.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.66/1.53  
% 7.66/1.53  fof(f32,plain,(
% 7.66/1.53    ! [X0] : (v3_ordinal1(k3_tarski(X0)) | ? [X1] : (~v3_ordinal1(X1) & r2_hidden(X1,X0)))),
% 7.66/1.53    inference(ennf_transformation,[],[f15])).
% 7.66/1.53  
% 7.66/1.53  fof(f56,plain,(
% 7.66/1.53    ! [X0] : (? [X1] : (~v3_ordinal1(X1) & r2_hidden(X1,X0)) => (~v3_ordinal1(sK4(X0)) & r2_hidden(sK4(X0),X0)))),
% 7.66/1.53    introduced(choice_axiom,[])).
% 7.66/1.53  
% 7.66/1.53  fof(f57,plain,(
% 7.66/1.53    ! [X0] : (v3_ordinal1(k3_tarski(X0)) | (~v3_ordinal1(sK4(X0)) & r2_hidden(sK4(X0),X0)))),
% 7.66/1.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f32,f56])).
% 7.66/1.53  
% 7.66/1.53  fof(f95,plain,(
% 7.66/1.53    ( ! [X0] : (v3_ordinal1(k3_tarski(X0)) | r2_hidden(sK4(X0),X0)) )),
% 7.66/1.53    inference(cnf_transformation,[],[f57])).
% 7.66/1.53  
% 7.66/1.53  fof(f10,axiom,(
% 7.66/1.53    ! [X0,X1] : (v3_ordinal1(X1) => (r2_hidden(X0,X1) => v3_ordinal1(X0)))),
% 7.66/1.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.66/1.53  
% 7.66/1.53  fof(f25,plain,(
% 7.66/1.53    ! [X0,X1] : ((v3_ordinal1(X0) | ~r2_hidden(X0,X1)) | ~v3_ordinal1(X1))),
% 7.66/1.53    inference(ennf_transformation,[],[f10])).
% 7.66/1.53  
% 7.66/1.53  fof(f26,plain,(
% 7.66/1.53    ! [X0,X1] : (v3_ordinal1(X0) | ~r2_hidden(X0,X1) | ~v3_ordinal1(X1))),
% 7.66/1.53    inference(flattening,[],[f25])).
% 7.66/1.53  
% 7.66/1.53  fof(f88,plain,(
% 7.66/1.53    ( ! [X0,X1] : (v3_ordinal1(X0) | ~r2_hidden(X0,X1) | ~v3_ordinal1(X1)) )),
% 7.66/1.53    inference(cnf_transformation,[],[f26])).
% 7.66/1.53  
% 7.66/1.53  fof(f96,plain,(
% 7.66/1.53    ( ! [X0] : (v3_ordinal1(k3_tarski(X0)) | ~v3_ordinal1(sK4(X0))) )),
% 7.66/1.53    inference(cnf_transformation,[],[f57])).
% 7.66/1.53  
% 7.66/1.53  fof(f16,axiom,(
% 7.66/1.53    ! [X0] : ? [X1] : (! [X2] : (v3_ordinal1(X2) => (~r2_hidden(X2,X0) => r1_ordinal1(X1,X2))) & ~r2_hidden(X1,X0) & v3_ordinal1(X1))),
% 7.66/1.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.66/1.53  
% 7.66/1.53  fof(f33,plain,(
% 7.66/1.53    ! [X0] : ? [X1] : (! [X2] : ((r1_ordinal1(X1,X2) | r2_hidden(X2,X0)) | ~v3_ordinal1(X2)) & ~r2_hidden(X1,X0) & v3_ordinal1(X1))),
% 7.66/1.53    inference(ennf_transformation,[],[f16])).
% 7.66/1.53  
% 7.66/1.53  fof(f34,plain,(
% 7.66/1.53    ! [X0] : ? [X1] : (! [X2] : (r1_ordinal1(X1,X2) | r2_hidden(X2,X0) | ~v3_ordinal1(X2)) & ~r2_hidden(X1,X0) & v3_ordinal1(X1))),
% 7.66/1.53    inference(flattening,[],[f33])).
% 7.66/1.53  
% 7.66/1.53  fof(f58,plain,(
% 7.66/1.53    ! [X0] : (? [X1] : (! [X2] : (r1_ordinal1(X1,X2) | r2_hidden(X2,X0) | ~v3_ordinal1(X2)) & ~r2_hidden(X1,X0) & v3_ordinal1(X1)) => (! [X2] : (r1_ordinal1(sK5(X0),X2) | r2_hidden(X2,X0) | ~v3_ordinal1(X2)) & ~r2_hidden(sK5(X0),X0) & v3_ordinal1(sK5(X0))))),
% 7.66/1.53    introduced(choice_axiom,[])).
% 7.66/1.53  
% 7.66/1.53  fof(f59,plain,(
% 7.66/1.53    ! [X0] : (! [X2] : (r1_ordinal1(sK5(X0),X2) | r2_hidden(X2,X0) | ~v3_ordinal1(X2)) & ~r2_hidden(sK5(X0),X0) & v3_ordinal1(sK5(X0)))),
% 7.66/1.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f34,f58])).
% 7.66/1.53  
% 7.66/1.53  fof(f98,plain,(
% 7.66/1.53    ( ! [X0] : (~r2_hidden(sK5(X0),X0)) )),
% 7.66/1.53    inference(cnf_transformation,[],[f59])).
% 7.66/1.53  
% 7.66/1.53  fof(f73,plain,(
% 7.66/1.53    ( ! [X0,X5,X1] : (r2_hidden(sK3(X0,X5),X0) | ~r2_hidden(X5,X1) | k3_tarski(X0) != X1) )),
% 7.66/1.53    inference(cnf_transformation,[],[f49])).
% 7.66/1.53  
% 7.66/1.53  fof(f120,plain,(
% 7.66/1.53    ( ! [X0,X5] : (r2_hidden(sK3(X0,X5),X0) | ~r2_hidden(X5,k3_tarski(X0))) )),
% 7.66/1.53    inference(equality_resolution,[],[f73])).
% 7.66/1.53  
% 7.66/1.53  fof(f81,plain,(
% 7.66/1.53    ( ! [X0] : (v4_ordinal1(X0) | k3_tarski(X0) != X0) )),
% 7.66/1.53    inference(cnf_transformation,[],[f50])).
% 7.66/1.53  
% 7.66/1.53  fof(f105,plain,(
% 7.66/1.53    ~r2_hidden(k1_ordinal1(sK7),sK6) | ~v4_ordinal1(sK6)),
% 7.66/1.53    inference(cnf_transformation,[],[f65])).
% 7.66/1.53  
% 7.66/1.53  fof(f115,plain,(
% 7.66/1.53    ~r2_hidden(k2_xboole_0(sK7,k1_tarski(sK7)),sK6) | ~v4_ordinal1(sK6)),
% 7.66/1.53    inference(definition_unfolding,[],[f105,f79])).
% 7.66/1.53  
% 7.66/1.53  fof(f103,plain,(
% 7.66/1.53    v3_ordinal1(sK7) | ~v4_ordinal1(sK6)),
% 7.66/1.53    inference(cnf_transformation,[],[f65])).
% 7.66/1.53  
% 7.66/1.53  fof(f104,plain,(
% 7.66/1.53    r2_hidden(sK7,sK6) | ~v4_ordinal1(sK6)),
% 7.66/1.53    inference(cnf_transformation,[],[f65])).
% 7.66/1.53  
% 7.66/1.53  fof(f12,axiom,(
% 7.66/1.53    ! [X0] : (v3_ordinal1(X0) => v3_ordinal1(k1_ordinal1(X0)))),
% 7.66/1.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.66/1.53  
% 7.66/1.53  fof(f29,plain,(
% 7.66/1.53    ! [X0] : (v3_ordinal1(k1_ordinal1(X0)) | ~v3_ordinal1(X0))),
% 7.66/1.53    inference(ennf_transformation,[],[f12])).
% 7.66/1.53  
% 7.66/1.53  fof(f90,plain,(
% 7.66/1.53    ( ! [X0] : (v3_ordinal1(k1_ordinal1(X0)) | ~v3_ordinal1(X0)) )),
% 7.66/1.53    inference(cnf_transformation,[],[f29])).
% 7.66/1.53  
% 7.66/1.53  fof(f110,plain,(
% 7.66/1.53    ( ! [X0] : (v3_ordinal1(k2_xboole_0(X0,k1_tarski(X0))) | ~v3_ordinal1(X0)) )),
% 7.66/1.53    inference(definition_unfolding,[],[f90,f79])).
% 7.66/1.53  
% 7.66/1.53  fof(f13,axiom,(
% 7.66/1.53    ! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => (r2_hidden(X0,X1) <=> r1_ordinal1(k1_ordinal1(X0),X1))))),
% 7.66/1.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.66/1.53  
% 7.66/1.53  fof(f30,plain,(
% 7.66/1.53    ! [X0] : (! [X1] : ((r2_hidden(X0,X1) <=> r1_ordinal1(k1_ordinal1(X0),X1)) | ~v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 7.66/1.53    inference(ennf_transformation,[],[f13])).
% 7.66/1.53  
% 7.66/1.53  fof(f54,plain,(
% 7.66/1.53    ! [X0] : (! [X1] : (((r2_hidden(X0,X1) | ~r1_ordinal1(k1_ordinal1(X0),X1)) & (r1_ordinal1(k1_ordinal1(X0),X1) | ~r2_hidden(X0,X1))) | ~v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 7.66/1.53    inference(nnf_transformation,[],[f30])).
% 7.66/1.53  
% 7.66/1.53  fof(f91,plain,(
% 7.66/1.53    ( ! [X0,X1] : (r1_ordinal1(k1_ordinal1(X0),X1) | ~r2_hidden(X0,X1) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0)) )),
% 7.66/1.53    inference(cnf_transformation,[],[f54])).
% 7.66/1.53  
% 7.66/1.53  fof(f112,plain,(
% 7.66/1.53    ( ! [X0,X1] : (r1_ordinal1(k2_xboole_0(X0,k1_tarski(X0)),X1) | ~r2_hidden(X0,X1) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0)) )),
% 7.66/1.53    inference(definition_unfolding,[],[f91,f79])).
% 7.66/1.53  
% 7.66/1.53  fof(f85,plain,(
% 7.66/1.53    ( ! [X0,X1] : (X0 = X1 | r2_hidden(X0,X1) | ~r2_hidden(X0,k1_ordinal1(X1))) )),
% 7.66/1.53    inference(cnf_transformation,[],[f53])).
% 7.66/1.53  
% 7.66/1.53  fof(f109,plain,(
% 7.66/1.53    ( ! [X0,X1] : (X0 = X1 | r2_hidden(X0,X1) | ~r2_hidden(X0,k2_xboole_0(X1,k1_tarski(X1)))) )),
% 7.66/1.53    inference(definition_unfolding,[],[f85,f79])).
% 7.66/1.53  
% 7.66/1.53  fof(f94,plain,(
% 7.66/1.53    ( ! [X0,X1] : (r2_hidden(X0,k1_ordinal1(X1)) | ~r1_ordinal1(X0,X1) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0)) )),
% 7.66/1.53    inference(cnf_transformation,[],[f55])).
% 7.66/1.53  
% 7.66/1.53  fof(f113,plain,(
% 7.66/1.53    ( ! [X0,X1] : (r2_hidden(X0,k2_xboole_0(X1,k1_tarski(X1))) | ~r1_ordinal1(X0,X1) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0)) )),
% 7.66/1.53    inference(definition_unfolding,[],[f94,f79])).
% 7.66/1.53  
% 7.66/1.53  cnf(c_16,plain,
% 7.66/1.53      ( ~ r1_ordinal1(X0,X1)
% 7.66/1.53      | r1_tarski(X0,X1)
% 7.66/1.53      | ~ v3_ordinal1(X1)
% 7.66/1.53      | ~ v3_ordinal1(X0) ),
% 7.66/1.53      inference(cnf_transformation,[],[f82]) ).
% 7.66/1.53  
% 7.66/1.53  cnf(c_24236,plain,
% 7.66/1.53      ( ~ r1_ordinal1(X0,sK3(X0,sK7))
% 7.66/1.53      | r1_tarski(X0,sK3(X0,sK7))
% 7.66/1.53      | ~ v3_ordinal1(X0)
% 7.66/1.53      | ~ v3_ordinal1(sK3(X0,sK7)) ),
% 7.66/1.53      inference(instantiation,[status(thm)],[c_16]) ).
% 7.66/1.53  
% 7.66/1.53  cnf(c_24248,plain,
% 7.66/1.53      ( ~ r1_ordinal1(sK6,sK3(sK6,sK7))
% 7.66/1.53      | r1_tarski(sK6,sK3(sK6,sK7))
% 7.66/1.53      | ~ v3_ordinal1(sK3(sK6,sK7))
% 7.66/1.53      | ~ v3_ordinal1(sK6) ),
% 7.66/1.53      inference(instantiation,[status(thm)],[c_24236]) ).
% 7.66/1.53  
% 7.66/1.53  cnf(c_11,plain,
% 7.66/1.53      ( r2_hidden(X0,sK3(X1,X0)) | ~ r2_hidden(X0,k3_tarski(X1)) ),
% 7.66/1.53      inference(cnf_transformation,[],[f121]) ).
% 7.66/1.53  
% 7.66/1.53  cnf(c_1783,plain,
% 7.66/1.53      ( r2_hidden(X0,sK3(X1,X0)) = iProver_top
% 7.66/1.53      | r2_hidden(X0,k3_tarski(X1)) != iProver_top ),
% 7.66/1.53      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 7.66/1.53  
% 7.66/1.53  cnf(c_22,plain,
% 7.66/1.53      ( r2_hidden(X0,X1)
% 7.66/1.53      | r2_hidden(X1,X0)
% 7.66/1.53      | ~ v3_ordinal1(X1)
% 7.66/1.53      | ~ v3_ordinal1(X0)
% 7.66/1.53      | X1 = X0 ),
% 7.66/1.53      inference(cnf_transformation,[],[f89]) ).
% 7.66/1.53  
% 7.66/1.53  cnf(c_1773,plain,
% 7.66/1.53      ( X0 = X1
% 7.66/1.53      | r2_hidden(X1,X0) = iProver_top
% 7.66/1.53      | r2_hidden(X0,X1) = iProver_top
% 7.66/1.53      | v3_ordinal1(X1) != iProver_top
% 7.66/1.53      | v3_ordinal1(X0) != iProver_top ),
% 7.66/1.53      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 7.66/1.53  
% 7.66/1.53  cnf(c_37,negated_conjecture,
% 7.66/1.53      ( ~ r2_hidden(X0,sK6)
% 7.66/1.53      | r2_hidden(k2_xboole_0(X0,k1_tarski(X0)),sK6)
% 7.66/1.53      | v4_ordinal1(sK6)
% 7.66/1.53      | ~ v3_ordinal1(X0) ),
% 7.66/1.53      inference(cnf_transformation,[],[f116]) ).
% 7.66/1.53  
% 7.66/1.53  cnf(c_1759,plain,
% 7.66/1.53      ( r2_hidden(X0,sK6) != iProver_top
% 7.66/1.53      | r2_hidden(k2_xboole_0(X0,k1_tarski(X0)),sK6) = iProver_top
% 7.66/1.53      | v4_ordinal1(sK6) = iProver_top
% 7.66/1.53      | v3_ordinal1(X0) != iProver_top ),
% 7.66/1.53      inference(predicate_to_equality,[status(thm)],[c_37]) ).
% 7.66/1.53  
% 7.66/1.53  cnf(c_18,plain,
% 7.66/1.53      ( r2_hidden(X0,k2_xboole_0(X0,k1_tarski(X0))) ),
% 7.66/1.53      inference(cnf_transformation,[],[f122]) ).
% 7.66/1.53  
% 7.66/1.53  cnf(c_1777,plain,
% 7.66/1.53      ( r2_hidden(X0,k2_xboole_0(X0,k1_tarski(X0))) = iProver_top ),
% 7.66/1.53      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 7.66/1.53  
% 7.66/1.53  cnf(c_9,plain,
% 7.66/1.53      ( ~ r2_hidden(X0,X1)
% 7.66/1.53      | ~ r2_hidden(X2,X0)
% 7.66/1.53      | r2_hidden(X2,k3_tarski(X1)) ),
% 7.66/1.53      inference(cnf_transformation,[],[f119]) ).
% 7.66/1.53  
% 7.66/1.53  cnf(c_1785,plain,
% 7.66/1.53      ( r2_hidden(X0,X1) != iProver_top
% 7.66/1.53      | r2_hidden(X2,X0) != iProver_top
% 7.66/1.53      | r2_hidden(X2,k3_tarski(X1)) = iProver_top ),
% 7.66/1.53      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 7.66/1.53  
% 7.66/1.53  cnf(c_4497,plain,
% 7.66/1.53      ( r2_hidden(X0,k2_xboole_0(X1,k1_tarski(X1))) != iProver_top
% 7.66/1.53      | r2_hidden(X0,k3_tarski(sK6)) = iProver_top
% 7.66/1.53      | r2_hidden(X1,sK6) != iProver_top
% 7.66/1.53      | v4_ordinal1(sK6) = iProver_top
% 7.66/1.53      | v3_ordinal1(X1) != iProver_top ),
% 7.66/1.53      inference(superposition,[status(thm)],[c_1759,c_1785]) ).
% 7.66/1.53  
% 7.66/1.53  cnf(c_4860,plain,
% 7.66/1.53      ( r2_hidden(X0,k3_tarski(sK6)) = iProver_top
% 7.66/1.53      | r2_hidden(X0,sK6) != iProver_top
% 7.66/1.53      | v4_ordinal1(sK6) = iProver_top
% 7.66/1.53      | v3_ordinal1(X0) != iProver_top ),
% 7.66/1.53      inference(superposition,[status(thm)],[c_1777,c_4497]) ).
% 7.66/1.53  
% 7.66/1.53  cnf(c_5,plain,
% 7.66/1.53      ( r1_tarski(X0,X0) ),
% 7.66/1.53      inference(cnf_transformation,[],[f118]) ).
% 7.66/1.53  
% 7.66/1.53  cnf(c_1789,plain,
% 7.66/1.53      ( r1_tarski(X0,X0) = iProver_top ),
% 7.66/1.53      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 7.66/1.53  
% 7.66/1.53  cnf(c_19,plain,
% 7.66/1.53      ( ~ r2_hidden(X0,X1)
% 7.66/1.53      | r2_hidden(X0,k2_xboole_0(X1,k1_tarski(X1))) ),
% 7.66/1.53      inference(cnf_transformation,[],[f108]) ).
% 7.66/1.53  
% 7.66/1.53  cnf(c_1776,plain,
% 7.66/1.53      ( r2_hidden(X0,X1) != iProver_top
% 7.66/1.53      | r2_hidden(X0,k2_xboole_0(X1,k1_tarski(X1))) = iProver_top ),
% 7.66/1.53      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 7.66/1.53  
% 7.66/1.53  cnf(c_33,plain,
% 7.66/1.53      ( ~ r2_hidden(X0,X1) | ~ r1_tarski(X1,X0) ),
% 7.66/1.53      inference(cnf_transformation,[],[f100]) ).
% 7.66/1.53  
% 7.66/1.53  cnf(c_1763,plain,
% 7.66/1.53      ( r2_hidden(X0,X1) != iProver_top
% 7.66/1.53      | r1_tarski(X1,X0) != iProver_top ),
% 7.66/1.53      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 7.66/1.53  
% 7.66/1.53  cnf(c_2901,plain,
% 7.66/1.53      ( r2_hidden(X0,X1) != iProver_top
% 7.66/1.53      | r1_tarski(k2_xboole_0(X1,k1_tarski(X1)),X0) != iProver_top ),
% 7.66/1.53      inference(superposition,[status(thm)],[c_1776,c_1763]) ).
% 7.66/1.53  
% 7.66/1.53  cnf(c_3445,plain,
% 7.66/1.53      ( r2_hidden(k2_xboole_0(X0,k1_tarski(X0)),X0) != iProver_top ),
% 7.66/1.53      inference(superposition,[status(thm)],[c_1789,c_2901]) ).
% 7.66/1.53  
% 7.66/1.53  cnf(c_6053,plain,
% 7.66/1.53      ( r2_hidden(k2_xboole_0(k3_tarski(sK6),k1_tarski(k3_tarski(sK6))),sK6) != iProver_top
% 7.66/1.53      | v4_ordinal1(sK6) = iProver_top
% 7.66/1.53      | v3_ordinal1(k2_xboole_0(k3_tarski(sK6),k1_tarski(k3_tarski(sK6)))) != iProver_top ),
% 7.66/1.53      inference(superposition,[status(thm)],[c_4860,c_3445]) ).
% 7.66/1.53  
% 7.66/1.53  cnf(c_9299,plain,
% 7.66/1.53      ( r2_hidden(k3_tarski(sK6),sK6) != iProver_top
% 7.66/1.53      | v4_ordinal1(sK6) = iProver_top
% 7.66/1.53      | v3_ordinal1(k2_xboole_0(k3_tarski(sK6),k1_tarski(k3_tarski(sK6)))) != iProver_top
% 7.66/1.53      | v3_ordinal1(k3_tarski(sK6)) != iProver_top ),
% 7.66/1.53      inference(superposition,[status(thm)],[c_1759,c_6053]) ).
% 7.66/1.53  
% 7.66/1.53  cnf(c_38,negated_conjecture,
% 7.66/1.53      ( v3_ordinal1(sK6) ),
% 7.66/1.53      inference(cnf_transformation,[],[f101]) ).
% 7.66/1.53  
% 7.66/1.53  cnf(c_39,plain,
% 7.66/1.53      ( v3_ordinal1(sK6) = iProver_top ),
% 7.66/1.53      inference(predicate_to_equality,[status(thm)],[c_38]) ).
% 7.66/1.53  
% 7.66/1.53  cnf(c_47,plain,
% 7.66/1.53      ( ~ r2_hidden(sK6,sK6) | ~ r1_tarski(sK6,sK6) ),
% 7.66/1.53      inference(instantiation,[status(thm)],[c_33]) ).
% 7.66/1.53  
% 7.66/1.53  cnf(c_46,plain,
% 7.66/1.53      ( r2_hidden(X0,X1) != iProver_top
% 7.66/1.53      | r1_tarski(X1,X0) != iProver_top ),
% 7.66/1.53      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 7.66/1.53  
% 7.66/1.53  cnf(c_48,plain,
% 7.66/1.53      ( r2_hidden(sK6,sK6) != iProver_top
% 7.66/1.53      | r1_tarski(sK6,sK6) != iProver_top ),
% 7.66/1.53      inference(instantiation,[status(thm)],[c_46]) ).
% 7.66/1.53  
% 7.66/1.53  cnf(c_27,plain,
% 7.66/1.53      ( r1_ordinal1(X0,X1)
% 7.66/1.53      | ~ r2_hidden(X0,k2_xboole_0(X1,k1_tarski(X1)))
% 7.66/1.53      | ~ v3_ordinal1(X1)
% 7.66/1.53      | ~ v3_ordinal1(X0) ),
% 7.66/1.53      inference(cnf_transformation,[],[f114]) ).
% 7.66/1.53  
% 7.66/1.53  cnf(c_65,plain,
% 7.66/1.53      ( r1_ordinal1(sK6,sK6)
% 7.66/1.53      | ~ r2_hidden(sK6,k2_xboole_0(sK6,k1_tarski(sK6)))
% 7.66/1.53      | ~ v3_ordinal1(sK6) ),
% 7.66/1.53      inference(instantiation,[status(thm)],[c_27]) ).
% 7.66/1.53  
% 7.66/1.53  cnf(c_64,plain,
% 7.66/1.53      ( r1_ordinal1(X0,X1) = iProver_top
% 7.66/1.53      | r2_hidden(X0,k2_xboole_0(X1,k1_tarski(X1))) != iProver_top
% 7.66/1.53      | v3_ordinal1(X0) != iProver_top
% 7.66/1.53      | v3_ordinal1(X1) != iProver_top ),
% 7.66/1.53      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 7.66/1.53  
% 7.66/1.53  cnf(c_66,plain,
% 7.66/1.53      ( r1_ordinal1(sK6,sK6) = iProver_top
% 7.66/1.53      | r2_hidden(sK6,k2_xboole_0(sK6,k1_tarski(sK6))) != iProver_top
% 7.66/1.53      | v3_ordinal1(sK6) != iProver_top ),
% 7.66/1.53      inference(instantiation,[status(thm)],[c_64]) ).
% 7.66/1.53  
% 7.66/1.53  cnf(c_80,plain,
% 7.66/1.53      ( r2_hidden(sK6,sK6) | ~ v3_ordinal1(sK6) | sK6 = sK6 ),
% 7.66/1.53      inference(instantiation,[status(thm)],[c_22]) ).
% 7.66/1.53  
% 7.66/1.53  cnf(c_90,plain,
% 7.66/1.53      ( r2_hidden(sK6,k2_xboole_0(sK6,k1_tarski(sK6))) ),
% 7.66/1.53      inference(instantiation,[status(thm)],[c_18]) ).
% 7.66/1.53  
% 7.66/1.53  cnf(c_89,plain,
% 7.66/1.53      ( r2_hidden(X0,k2_xboole_0(X0,k1_tarski(X0))) = iProver_top ),
% 7.66/1.53      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 7.66/1.53  
% 7.66/1.53  cnf(c_91,plain,
% 7.66/1.53      ( r2_hidden(sK6,k2_xboole_0(sK6,k1_tarski(sK6))) = iProver_top ),
% 7.66/1.53      inference(instantiation,[status(thm)],[c_89]) ).
% 7.66/1.53  
% 7.66/1.53  cnf(c_94,plain,
% 7.66/1.53      ( ~ r1_ordinal1(sK6,sK6)
% 7.66/1.53      | r1_tarski(sK6,sK6)
% 7.66/1.53      | ~ v3_ordinal1(sK6) ),
% 7.66/1.53      inference(instantiation,[status(thm)],[c_16]) ).
% 7.66/1.53  
% 7.66/1.53  cnf(c_93,plain,
% 7.66/1.53      ( r1_ordinal1(X0,X1) != iProver_top
% 7.66/1.53      | r1_tarski(X0,X1) = iProver_top
% 7.66/1.53      | v3_ordinal1(X0) != iProver_top
% 7.66/1.53      | v3_ordinal1(X1) != iProver_top ),
% 7.66/1.53      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 7.66/1.53  
% 7.66/1.53  cnf(c_95,plain,
% 7.66/1.53      ( r1_ordinal1(sK6,sK6) != iProver_top
% 7.66/1.53      | r1_tarski(sK6,sK6) = iProver_top
% 7.66/1.53      | v3_ordinal1(sK6) != iProver_top ),
% 7.66/1.53      inference(instantiation,[status(thm)],[c_93]) ).
% 7.66/1.53  
% 7.66/1.53  cnf(c_14,plain,
% 7.66/1.53      ( ~ v4_ordinal1(X0) | k3_tarski(X0) = X0 ),
% 7.66/1.53      inference(cnf_transformation,[],[f80]) ).
% 7.66/1.53  
% 7.66/1.53  cnf(c_99,plain,
% 7.66/1.53      ( k3_tarski(X0) = X0 | v4_ordinal1(X0) != iProver_top ),
% 7.66/1.53      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 7.66/1.53  
% 7.66/1.53  cnf(c_101,plain,
% 7.66/1.53      ( k3_tarski(sK6) = sK6 | v4_ordinal1(sK6) != iProver_top ),
% 7.66/1.53      inference(instantiation,[status(thm)],[c_99]) ).
% 7.66/1.53  
% 7.66/1.53  cnf(c_1031,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 7.66/1.53  
% 7.66/1.53  cnf(c_2848,plain,
% 7.66/1.53      ( k3_tarski(X0) != X1 | sK6 != X1 | sK6 = k3_tarski(X0) ),
% 7.66/1.53      inference(instantiation,[status(thm)],[c_1031]) ).
% 7.66/1.53  
% 7.66/1.53  cnf(c_2849,plain,
% 7.66/1.53      ( k3_tarski(sK6) != sK6 | sK6 = k3_tarski(sK6) | sK6 != sK6 ),
% 7.66/1.53      inference(instantiation,[status(thm)],[c_2848]) ).
% 7.66/1.53  
% 7.66/1.53  cnf(c_1032,plain,
% 7.66/1.53      ( ~ r2_hidden(X0,X1) | r2_hidden(X2,X3) | X2 != X0 | X3 != X1 ),
% 7.66/1.53      theory(equality) ).
% 7.66/1.53  
% 7.66/1.53  cnf(c_1973,plain,
% 7.66/1.53      ( ~ r2_hidden(X0,X1) | r2_hidden(X2,sK6) | X2 != X0 | sK6 != X1 ),
% 7.66/1.53      inference(instantiation,[status(thm)],[c_1032]) ).
% 7.66/1.53  
% 7.66/1.53  cnf(c_3271,plain,
% 7.66/1.53      ( r2_hidden(X0,sK6)
% 7.66/1.53      | ~ r2_hidden(k3_tarski(sK6),sK6)
% 7.66/1.53      | X0 != k3_tarski(sK6)
% 7.66/1.53      | sK6 != sK6 ),
% 7.66/1.53      inference(instantiation,[status(thm)],[c_1973]) ).
% 7.66/1.53  
% 7.66/1.53  cnf(c_3273,plain,
% 7.66/1.53      ( X0 != k3_tarski(sK6)
% 7.66/1.53      | sK6 != sK6
% 7.66/1.53      | r2_hidden(X0,sK6) = iProver_top
% 7.66/1.53      | r2_hidden(k3_tarski(sK6),sK6) != iProver_top ),
% 7.66/1.53      inference(predicate_to_equality,[status(thm)],[c_3271]) ).
% 7.66/1.53  
% 7.66/1.53  cnf(c_3275,plain,
% 7.66/1.53      ( sK6 != k3_tarski(sK6)
% 7.66/1.53      | sK6 != sK6
% 7.66/1.53      | r2_hidden(k3_tarski(sK6),sK6) != iProver_top
% 7.66/1.53      | r2_hidden(sK6,sK6) = iProver_top ),
% 7.66/1.53      inference(instantiation,[status(thm)],[c_3273]) ).
% 7.66/1.53  
% 7.66/1.53  cnf(c_29,plain,
% 7.66/1.53      ( r2_hidden(sK4(X0),X0) | v3_ordinal1(k3_tarski(X0)) ),
% 7.66/1.53      inference(cnf_transformation,[],[f95]) ).
% 7.66/1.53  
% 7.66/1.53  cnf(c_1767,plain,
% 7.66/1.53      ( r2_hidden(sK4(X0),X0) = iProver_top
% 7.66/1.53      | v3_ordinal1(k3_tarski(X0)) = iProver_top ),
% 7.66/1.53      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 7.66/1.53  
% 7.66/1.53  cnf(c_21,plain,
% 7.66/1.53      ( ~ r2_hidden(X0,X1) | ~ v3_ordinal1(X1) | v3_ordinal1(X0) ),
% 7.66/1.53      inference(cnf_transformation,[],[f88]) ).
% 7.66/1.53  
% 7.66/1.53  cnf(c_1774,plain,
% 7.66/1.53      ( r2_hidden(X0,X1) != iProver_top
% 7.66/1.53      | v3_ordinal1(X1) != iProver_top
% 7.66/1.53      | v3_ordinal1(X0) = iProver_top ),
% 7.66/1.53      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 7.66/1.53  
% 7.66/1.53  cnf(c_3698,plain,
% 7.66/1.53      ( v3_ordinal1(X0) != iProver_top
% 7.66/1.53      | v3_ordinal1(sK4(X0)) = iProver_top
% 7.66/1.53      | v3_ordinal1(k3_tarski(X0)) = iProver_top ),
% 7.66/1.53      inference(superposition,[status(thm)],[c_1767,c_1774]) ).
% 7.66/1.53  
% 7.66/1.53  cnf(c_28,plain,
% 7.66/1.53      ( ~ v3_ordinal1(sK4(X0)) | v3_ordinal1(k3_tarski(X0)) ),
% 7.66/1.53      inference(cnf_transformation,[],[f96]) ).
% 7.66/1.53  
% 7.66/1.53  cnf(c_61,plain,
% 7.66/1.53      ( v3_ordinal1(sK4(X0)) != iProver_top
% 7.66/1.53      | v3_ordinal1(k3_tarski(X0)) = iProver_top ),
% 7.66/1.53      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 7.66/1.53  
% 7.66/1.53  cnf(c_7828,plain,
% 7.66/1.53      ( v3_ordinal1(X0) != iProver_top
% 7.66/1.53      | v3_ordinal1(k3_tarski(X0)) = iProver_top ),
% 7.66/1.53      inference(global_propositional_subsumption,
% 7.66/1.53                [status(thm)],
% 7.66/1.53                [c_3698,c_61]) ).
% 7.66/1.53  
% 7.66/1.53  cnf(c_7831,plain,
% 7.66/1.53      ( v3_ordinal1(k3_tarski(sK6)) = iProver_top
% 7.66/1.53      | v3_ordinal1(sK6) != iProver_top ),
% 7.66/1.53      inference(instantiation,[status(thm)],[c_7828]) ).
% 7.66/1.53  
% 7.66/1.53  cnf(c_6049,plain,
% 7.66/1.53      ( r2_hidden(X0,sK6) != iProver_top
% 7.66/1.53      | r1_tarski(k3_tarski(sK6),X0) != iProver_top
% 7.66/1.53      | v4_ordinal1(sK6) = iProver_top
% 7.66/1.53      | v3_ordinal1(X0) != iProver_top ),
% 7.66/1.53      inference(superposition,[status(thm)],[c_4860,c_1763]) ).
% 7.66/1.53  
% 7.66/1.53  cnf(c_8466,plain,
% 7.66/1.53      ( r2_hidden(k3_tarski(sK6),sK6) != iProver_top
% 7.66/1.53      | v4_ordinal1(sK6) = iProver_top
% 7.66/1.53      | v3_ordinal1(k3_tarski(sK6)) != iProver_top ),
% 7.66/1.53      inference(superposition,[status(thm)],[c_1789,c_6049]) ).
% 7.66/1.53  
% 7.66/1.53  cnf(c_9506,plain,
% 7.66/1.53      ( r2_hidden(k3_tarski(sK6),sK6) != iProver_top ),
% 7.66/1.53      inference(global_propositional_subsumption,
% 7.66/1.53                [status(thm)],
% 7.66/1.53                [c_9299,c_38,c_39,c_47,c_48,c_65,c_66,c_80,c_90,c_91,
% 7.66/1.53                 c_94,c_95,c_101,c_2849,c_3275,c_7831,c_8466]) ).
% 7.66/1.53  
% 7.66/1.53  cnf(c_9510,plain,
% 7.66/1.53      ( k3_tarski(sK6) = sK6
% 7.66/1.53      | r2_hidden(sK6,k3_tarski(sK6)) = iProver_top
% 7.66/1.53      | v3_ordinal1(k3_tarski(sK6)) != iProver_top
% 7.66/1.53      | v3_ordinal1(sK6) != iProver_top ),
% 7.66/1.53      inference(superposition,[status(thm)],[c_1773,c_9506]) ).
% 7.66/1.53  
% 7.66/1.53  cnf(c_2129,plain,
% 7.66/1.53      ( r2_hidden(k3_tarski(sK6),sK6)
% 7.66/1.53      | r2_hidden(sK6,k3_tarski(sK6))
% 7.66/1.53      | ~ v3_ordinal1(k3_tarski(sK6))
% 7.66/1.53      | ~ v3_ordinal1(sK6)
% 7.66/1.53      | k3_tarski(sK6) = sK6 ),
% 7.66/1.53      inference(instantiation,[status(thm)],[c_22]) ).
% 7.66/1.53  
% 7.66/1.53  cnf(c_2136,plain,
% 7.66/1.53      ( k3_tarski(sK6) = sK6
% 7.66/1.53      | r2_hidden(k3_tarski(sK6),sK6) = iProver_top
% 7.66/1.53      | r2_hidden(sK6,k3_tarski(sK6)) = iProver_top
% 7.66/1.53      | v3_ordinal1(k3_tarski(sK6)) != iProver_top
% 7.66/1.53      | v3_ordinal1(sK6) != iProver_top ),
% 7.66/1.53      inference(predicate_to_equality,[status(thm)],[c_2129]) ).
% 7.66/1.53  
% 7.66/1.53  cnf(c_9514,plain,
% 7.66/1.53      ( k3_tarski(sK6) = sK6
% 7.66/1.53      | r2_hidden(sK6,k3_tarski(sK6)) = iProver_top ),
% 7.66/1.53      inference(global_propositional_subsumption,
% 7.66/1.53                [status(thm)],
% 7.66/1.53                [c_9510,c_38,c_39,c_47,c_48,c_65,c_66,c_80,c_90,c_91,
% 7.66/1.53                 c_94,c_95,c_101,c_2136,c_2849,c_3275,c_7831,c_8466]) ).
% 7.66/1.53  
% 7.66/1.53  cnf(c_9519,plain,
% 7.66/1.53      ( k3_tarski(sK6) = sK6
% 7.66/1.53      | r2_hidden(X0,k3_tarski(k3_tarski(sK6))) = iProver_top
% 7.66/1.53      | r2_hidden(X0,sK6) != iProver_top ),
% 7.66/1.53      inference(superposition,[status(thm)],[c_9514,c_1785]) ).
% 7.66/1.53  
% 7.66/1.53  cnf(c_31,plain,
% 7.66/1.53      ( ~ r2_hidden(sK5(X0),X0) ),
% 7.66/1.53      inference(cnf_transformation,[],[f98]) ).
% 7.66/1.53  
% 7.66/1.53  cnf(c_1765,plain,
% 7.66/1.53      ( r2_hidden(sK5(X0),X0) != iProver_top ),
% 7.66/1.53      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 7.66/1.53  
% 7.66/1.53  cnf(c_12174,plain,
% 7.66/1.53      ( k3_tarski(sK6) = sK6
% 7.66/1.53      | r2_hidden(sK5(k3_tarski(k3_tarski(sK6))),sK6) != iProver_top ),
% 7.66/1.53      inference(superposition,[status(thm)],[c_9519,c_1765]) ).
% 7.66/1.53  
% 7.66/1.53  cnf(c_2810,plain,
% 7.66/1.53      ( ~ r1_ordinal1(sK3(X0,X1),sK6)
% 7.66/1.53      | r1_tarski(sK3(X0,X1),sK6)
% 7.66/1.53      | ~ v3_ordinal1(sK3(X0,X1))
% 7.66/1.53      | ~ v3_ordinal1(sK6) ),
% 7.66/1.53      inference(instantiation,[status(thm)],[c_16]) ).
% 7.66/1.53  
% 7.66/1.53  cnf(c_2821,plain,
% 7.66/1.53      ( r1_ordinal1(sK3(X0,X1),sK6) != iProver_top
% 7.66/1.53      | r1_tarski(sK3(X0,X1),sK6) = iProver_top
% 7.66/1.53      | v3_ordinal1(sK3(X0,X1)) != iProver_top
% 7.66/1.53      | v3_ordinal1(sK6) != iProver_top ),
% 7.66/1.53      inference(predicate_to_equality,[status(thm)],[c_2810]) ).
% 7.66/1.53  
% 7.66/1.53  cnf(c_2823,plain,
% 7.66/1.53      ( r1_ordinal1(sK3(sK6,sK6),sK6) != iProver_top
% 7.66/1.53      | r1_tarski(sK3(sK6,sK6),sK6) = iProver_top
% 7.66/1.53      | v3_ordinal1(sK3(sK6,sK6)) != iProver_top
% 7.66/1.53      | v3_ordinal1(sK6) != iProver_top ),
% 7.66/1.53      inference(instantiation,[status(thm)],[c_2821]) ).
% 7.66/1.53  
% 7.66/1.53  cnf(c_3181,plain,
% 7.66/1.53      ( r2_hidden(X0,k3_tarski(X1)) != iProver_top
% 7.66/1.53      | r1_tarski(sK3(X1,X0),X0) != iProver_top ),
% 7.66/1.53      inference(superposition,[status(thm)],[c_1783,c_1763]) ).
% 7.66/1.53  
% 7.66/1.53  cnf(c_3183,plain,
% 7.66/1.53      ( r2_hidden(sK6,k3_tarski(sK6)) != iProver_top
% 7.66/1.53      | r1_tarski(sK3(sK6,sK6),sK6) != iProver_top ),
% 7.66/1.53      inference(instantiation,[status(thm)],[c_3181]) ).
% 7.66/1.53  
% 7.66/1.53  cnf(c_10,plain,
% 7.66/1.53      ( ~ r2_hidden(X0,k3_tarski(X1)) | r2_hidden(sK3(X1,X0),X1) ),
% 7.66/1.53      inference(cnf_transformation,[],[f120]) ).
% 7.66/1.53  
% 7.66/1.53  cnf(c_1784,plain,
% 7.66/1.53      ( r2_hidden(X0,k3_tarski(X1)) != iProver_top
% 7.66/1.53      | r2_hidden(sK3(X1,X0),X1) = iProver_top ),
% 7.66/1.53      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 7.66/1.53  
% 7.66/1.53  cnf(c_3694,plain,
% 7.66/1.53      ( r2_hidden(X0,k3_tarski(X1)) != iProver_top
% 7.66/1.53      | v3_ordinal1(X1) != iProver_top
% 7.66/1.53      | v3_ordinal1(sK3(X1,X0)) = iProver_top ),
% 7.66/1.53      inference(superposition,[status(thm)],[c_1784,c_1774]) ).
% 7.66/1.53  
% 7.66/1.53  cnf(c_3703,plain,
% 7.66/1.53      ( r2_hidden(sK6,k3_tarski(sK6)) != iProver_top
% 7.66/1.53      | v3_ordinal1(sK3(sK6,sK6)) = iProver_top
% 7.66/1.53      | v3_ordinal1(sK6) != iProver_top ),
% 7.66/1.53      inference(instantiation,[status(thm)],[c_3694]) ).
% 7.66/1.53  
% 7.66/1.53  cnf(c_1769,plain,
% 7.66/1.53      ( r1_ordinal1(X0,X1) = iProver_top
% 7.66/1.53      | r2_hidden(X0,k2_xboole_0(X1,k1_tarski(X1))) != iProver_top
% 7.66/1.53      | v3_ordinal1(X0) != iProver_top
% 7.66/1.53      | v3_ordinal1(X1) != iProver_top ),
% 7.66/1.53      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 7.66/1.53  
% 7.66/1.53  cnf(c_3551,plain,
% 7.66/1.53      ( r1_ordinal1(X0,X1) = iProver_top
% 7.66/1.53      | r2_hidden(X0,X1) != iProver_top
% 7.66/1.53      | v3_ordinal1(X0) != iProver_top
% 7.66/1.53      | v3_ordinal1(X1) != iProver_top ),
% 7.66/1.53      inference(superposition,[status(thm)],[c_1776,c_1769]) ).
% 7.66/1.53  
% 7.66/1.53  cnf(c_82,plain,
% 7.66/1.53      ( r2_hidden(X0,X1) != iProver_top
% 7.66/1.53      | v3_ordinal1(X1) != iProver_top
% 7.66/1.53      | v3_ordinal1(X0) = iProver_top ),
% 7.66/1.53      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 7.66/1.53  
% 7.66/1.53  cnf(c_86,plain,
% 7.66/1.53      ( r2_hidden(X0,X1) != iProver_top
% 7.66/1.53      | r2_hidden(X0,k2_xboole_0(X1,k1_tarski(X1))) = iProver_top ),
% 7.66/1.53      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 7.66/1.53  
% 7.66/1.53  cnf(c_12356,plain,
% 7.66/1.53      ( r2_hidden(X0,X1) != iProver_top
% 7.66/1.53      | r1_ordinal1(X0,X1) = iProver_top
% 7.66/1.53      | v3_ordinal1(X1) != iProver_top ),
% 7.66/1.53      inference(global_propositional_subsumption,
% 7.66/1.53                [status(thm)],
% 7.66/1.53                [c_3551,c_64,c_82,c_86]) ).
% 7.66/1.53  
% 7.66/1.53  cnf(c_12357,plain,
% 7.66/1.53      ( r1_ordinal1(X0,X1) = iProver_top
% 7.66/1.53      | r2_hidden(X0,X1) != iProver_top
% 7.66/1.53      | v3_ordinal1(X1) != iProver_top ),
% 7.66/1.53      inference(renaming,[status(thm)],[c_12356]) ).
% 7.66/1.53  
% 7.66/1.53  cnf(c_12365,plain,
% 7.66/1.53      ( r1_ordinal1(sK3(X0,X1),X0) = iProver_top
% 7.66/1.53      | r2_hidden(X1,k3_tarski(X0)) != iProver_top
% 7.66/1.53      | v3_ordinal1(X0) != iProver_top ),
% 7.66/1.53      inference(superposition,[status(thm)],[c_1784,c_12357]) ).
% 7.66/1.53  
% 7.66/1.53  cnf(c_12408,plain,
% 7.66/1.53      ( r1_ordinal1(sK3(sK6,sK6),sK6) = iProver_top
% 7.66/1.53      | r2_hidden(sK6,k3_tarski(sK6)) != iProver_top
% 7.66/1.53      | v3_ordinal1(sK6) != iProver_top ),
% 7.66/1.53      inference(instantiation,[status(thm)],[c_12365]) ).
% 7.66/1.53  
% 7.66/1.53  cnf(c_12448,plain,
% 7.66/1.53      ( k3_tarski(sK6) = sK6 ),
% 7.66/1.53      inference(global_propositional_subsumption,
% 7.66/1.53                [status(thm)],
% 7.66/1.53                [c_12174,c_39,c_2823,c_3183,c_3703,c_9514,c_12408]) ).
% 7.66/1.53  
% 7.66/1.53  cnf(c_13,plain,
% 7.66/1.53      ( v4_ordinal1(X0) | k3_tarski(X0) != X0 ),
% 7.66/1.53      inference(cnf_transformation,[],[f81]) ).
% 7.66/1.53  
% 7.66/1.53  cnf(c_1781,plain,
% 7.66/1.53      ( k3_tarski(X0) != X0 | v4_ordinal1(X0) = iProver_top ),
% 7.66/1.53      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 7.66/1.53  
% 7.66/1.53  cnf(c_12556,plain,
% 7.66/1.53      ( v4_ordinal1(sK6) = iProver_top ),
% 7.66/1.53      inference(superposition,[status(thm)],[c_12448,c_1781]) ).
% 7.66/1.53  
% 7.66/1.53  cnf(c_34,negated_conjecture,
% 7.66/1.53      ( ~ r2_hidden(k2_xboole_0(sK7,k1_tarski(sK7)),sK6)
% 7.66/1.53      | ~ v4_ordinal1(sK6) ),
% 7.66/1.53      inference(cnf_transformation,[],[f115]) ).
% 7.66/1.53  
% 7.66/1.53  cnf(c_1762,plain,
% 7.66/1.53      ( r2_hidden(k2_xboole_0(sK7,k1_tarski(sK7)),sK6) != iProver_top
% 7.66/1.53      | v4_ordinal1(sK6) != iProver_top ),
% 7.66/1.53      inference(predicate_to_equality,[status(thm)],[c_34]) ).
% 7.66/1.53  
% 7.66/1.53  cnf(c_5612,plain,
% 7.66/1.53      ( k2_xboole_0(sK7,k1_tarski(sK7)) = sK6
% 7.66/1.53      | r2_hidden(sK6,k2_xboole_0(sK7,k1_tarski(sK7))) = iProver_top
% 7.66/1.53      | v4_ordinal1(sK6) != iProver_top
% 7.66/1.53      | v3_ordinal1(k2_xboole_0(sK7,k1_tarski(sK7))) != iProver_top
% 7.66/1.53      | v3_ordinal1(sK6) != iProver_top ),
% 7.66/1.53      inference(superposition,[status(thm)],[c_1773,c_1762]) ).
% 7.66/1.53  
% 7.66/1.53  cnf(c_36,negated_conjecture,
% 7.66/1.53      ( ~ v4_ordinal1(sK6) | v3_ordinal1(sK7) ),
% 7.66/1.53      inference(cnf_transformation,[],[f103]) ).
% 7.66/1.53  
% 7.66/1.53  cnf(c_43,plain,
% 7.66/1.53      ( v4_ordinal1(sK6) != iProver_top
% 7.66/1.53      | v3_ordinal1(sK7) = iProver_top ),
% 7.66/1.53      inference(predicate_to_equality,[status(thm)],[c_36]) ).
% 7.66/1.53  
% 7.66/1.53  cnf(c_35,negated_conjecture,
% 7.66/1.53      ( r2_hidden(sK7,sK6) | ~ v4_ordinal1(sK6) ),
% 7.66/1.53      inference(cnf_transformation,[],[f104]) ).
% 7.66/1.53  
% 7.66/1.53  cnf(c_44,plain,
% 7.66/1.53      ( r2_hidden(sK7,sK6) = iProver_top
% 7.66/1.53      | v4_ordinal1(sK6) != iProver_top ),
% 7.66/1.53      inference(predicate_to_equality,[status(thm)],[c_35]) ).
% 7.66/1.53  
% 7.66/1.53  cnf(c_45,plain,
% 7.66/1.53      ( r2_hidden(k2_xboole_0(sK7,k1_tarski(sK7)),sK6) != iProver_top
% 7.66/1.53      | v4_ordinal1(sK6) != iProver_top ),
% 7.66/1.53      inference(predicate_to_equality,[status(thm)],[c_34]) ).
% 7.66/1.53  
% 7.66/1.53  cnf(c_23,plain,
% 7.66/1.53      ( ~ v3_ordinal1(X0) | v3_ordinal1(k2_xboole_0(X0,k1_tarski(X0))) ),
% 7.66/1.53      inference(cnf_transformation,[],[f110]) ).
% 7.66/1.53  
% 7.66/1.53  cnf(c_1860,plain,
% 7.66/1.53      ( v3_ordinal1(k2_xboole_0(sK7,k1_tarski(sK7)))
% 7.66/1.53      | ~ v3_ordinal1(sK7) ),
% 7.66/1.53      inference(instantiation,[status(thm)],[c_23]) ).
% 7.66/1.53  
% 7.66/1.53  cnf(c_1861,plain,
% 7.66/1.53      ( v3_ordinal1(k2_xboole_0(sK7,k1_tarski(sK7))) = iProver_top
% 7.66/1.53      | v3_ordinal1(sK7) != iProver_top ),
% 7.66/1.53      inference(predicate_to_equality,[status(thm)],[c_1860]) ).
% 7.66/1.53  
% 7.66/1.53  cnf(c_1030,plain,( X0 = X0 ),theory(equality) ).
% 7.66/1.53  
% 7.66/1.53  cnf(c_2059,plain,
% 7.66/1.53      ( k2_xboole_0(sK7,k1_tarski(sK7)) = k2_xboole_0(sK7,k1_tarski(sK7)) ),
% 7.66/1.53      inference(instantiation,[status(thm)],[c_1030]) ).
% 7.66/1.53  
% 7.66/1.53  cnf(c_1920,plain,
% 7.66/1.53      ( X0 != X1
% 7.66/1.53      | k2_xboole_0(sK7,k1_tarski(sK7)) != X1
% 7.66/1.53      | k2_xboole_0(sK7,k1_tarski(sK7)) = X0 ),
% 7.66/1.53      inference(instantiation,[status(thm)],[c_1031]) ).
% 7.66/1.53  
% 7.66/1.53  cnf(c_2309,plain,
% 7.66/1.53      ( X0 != k2_xboole_0(sK7,k1_tarski(sK7))
% 7.66/1.53      | k2_xboole_0(sK7,k1_tarski(sK7)) = X0
% 7.66/1.53      | k2_xboole_0(sK7,k1_tarski(sK7)) != k2_xboole_0(sK7,k1_tarski(sK7)) ),
% 7.66/1.53      inference(instantiation,[status(thm)],[c_1920]) ).
% 7.66/1.53  
% 7.66/1.53  cnf(c_2310,plain,
% 7.66/1.53      ( k2_xboole_0(sK7,k1_tarski(sK7)) != k2_xboole_0(sK7,k1_tarski(sK7))
% 7.66/1.53      | k2_xboole_0(sK7,k1_tarski(sK7)) = sK6
% 7.66/1.53      | sK6 != k2_xboole_0(sK7,k1_tarski(sK7)) ),
% 7.66/1.53      inference(instantiation,[status(thm)],[c_2309]) ).
% 7.66/1.53  
% 7.66/1.53  cnf(c_25,plain,
% 7.66/1.53      ( r1_ordinal1(k2_xboole_0(X0,k1_tarski(X0)),X1)
% 7.66/1.53      | ~ r2_hidden(X0,X1)
% 7.66/1.53      | ~ v3_ordinal1(X1)
% 7.66/1.53      | ~ v3_ordinal1(X0) ),
% 7.66/1.53      inference(cnf_transformation,[],[f112]) ).
% 7.66/1.53  
% 7.66/1.53  cnf(c_228,plain,
% 7.66/1.53      ( ~ v3_ordinal1(X1)
% 7.66/1.53      | ~ r2_hidden(X0,X1)
% 7.66/1.53      | r1_ordinal1(k2_xboole_0(X0,k1_tarski(X0)),X1) ),
% 7.66/1.53      inference(global_propositional_subsumption,
% 7.66/1.53                [status(thm)],
% 7.66/1.53                [c_25,c_21]) ).
% 7.66/1.53  
% 7.66/1.53  cnf(c_229,plain,
% 7.66/1.53      ( r1_ordinal1(k2_xboole_0(X0,k1_tarski(X0)),X1)
% 7.66/1.53      | ~ r2_hidden(X0,X1)
% 7.66/1.53      | ~ v3_ordinal1(X1) ),
% 7.66/1.53      inference(renaming,[status(thm)],[c_228]) ).
% 7.66/1.53  
% 7.66/1.53  cnf(c_2180,plain,
% 7.66/1.53      ( r1_ordinal1(k2_xboole_0(X0,k1_tarski(X0)),sK6)
% 7.66/1.53      | ~ r2_hidden(X0,sK6)
% 7.66/1.53      | ~ v3_ordinal1(sK6) ),
% 7.66/1.53      inference(instantiation,[status(thm)],[c_229]) ).
% 7.66/1.53  
% 7.66/1.53  cnf(c_2599,plain,
% 7.66/1.53      ( r1_ordinal1(k2_xboole_0(sK7,k1_tarski(sK7)),sK6)
% 7.66/1.53      | ~ r2_hidden(sK7,sK6)
% 7.66/1.53      | ~ v3_ordinal1(sK6) ),
% 7.66/1.53      inference(instantiation,[status(thm)],[c_2180]) ).
% 7.66/1.53  
% 7.66/1.53  cnf(c_2600,plain,
% 7.66/1.53      ( r1_ordinal1(k2_xboole_0(sK7,k1_tarski(sK7)),sK6) = iProver_top
% 7.66/1.53      | r2_hidden(sK7,sK6) != iProver_top
% 7.66/1.53      | v3_ordinal1(sK6) != iProver_top ),
% 7.66/1.53      inference(predicate_to_equality,[status(thm)],[c_2599]) ).
% 7.66/1.53  
% 7.66/1.53  cnf(c_20,plain,
% 7.66/1.53      ( r2_hidden(X0,X1)
% 7.66/1.53      | ~ r2_hidden(X0,k2_xboole_0(X1,k1_tarski(X1)))
% 7.66/1.53      | X1 = X0 ),
% 7.66/1.53      inference(cnf_transformation,[],[f109]) ).
% 7.66/1.53  
% 7.66/1.53  cnf(c_3624,plain,
% 7.66/1.53      ( r2_hidden(k2_xboole_0(sK7,k1_tarski(sK7)),X0)
% 7.66/1.53      | ~ r2_hidden(k2_xboole_0(sK7,k1_tarski(sK7)),k2_xboole_0(X0,k1_tarski(X0)))
% 7.66/1.53      | X0 = k2_xboole_0(sK7,k1_tarski(sK7)) ),
% 7.66/1.53      inference(instantiation,[status(thm)],[c_20]) ).
% 7.66/1.53  
% 7.66/1.53  cnf(c_3630,plain,
% 7.66/1.53      ( X0 = k2_xboole_0(sK7,k1_tarski(sK7))
% 7.66/1.53      | r2_hidden(k2_xboole_0(sK7,k1_tarski(sK7)),X0) = iProver_top
% 7.66/1.53      | r2_hidden(k2_xboole_0(sK7,k1_tarski(sK7)),k2_xboole_0(X0,k1_tarski(X0))) != iProver_top ),
% 7.66/1.53      inference(predicate_to_equality,[status(thm)],[c_3624]) ).
% 7.66/1.53  
% 7.66/1.53  cnf(c_3632,plain,
% 7.66/1.53      ( sK6 = k2_xboole_0(sK7,k1_tarski(sK7))
% 7.66/1.53      | r2_hidden(k2_xboole_0(sK7,k1_tarski(sK7)),k2_xboole_0(sK6,k1_tarski(sK6))) != iProver_top
% 7.66/1.53      | r2_hidden(k2_xboole_0(sK7,k1_tarski(sK7)),sK6) = iProver_top ),
% 7.66/1.53      inference(instantiation,[status(thm)],[c_3630]) ).
% 7.66/1.53  
% 7.66/1.53  cnf(c_26,plain,
% 7.66/1.53      ( ~ r1_ordinal1(X0,X1)
% 7.66/1.53      | r2_hidden(X0,k2_xboole_0(X1,k1_tarski(X1)))
% 7.66/1.53      | ~ v3_ordinal1(X1)
% 7.66/1.53      | ~ v3_ordinal1(X0) ),
% 7.66/1.53      inference(cnf_transformation,[],[f113]) ).
% 7.66/1.53  
% 7.66/1.53  cnf(c_2770,plain,
% 7.66/1.53      ( ~ r1_ordinal1(k2_xboole_0(X0,k1_tarski(X0)),sK6)
% 7.66/1.53      | r2_hidden(k2_xboole_0(X0,k1_tarski(X0)),k2_xboole_0(sK6,k1_tarski(sK6)))
% 7.66/1.53      | ~ v3_ordinal1(k2_xboole_0(X0,k1_tarski(X0)))
% 7.66/1.53      | ~ v3_ordinal1(sK6) ),
% 7.66/1.53      inference(instantiation,[status(thm)],[c_26]) ).
% 7.66/1.53  
% 7.66/1.53  cnf(c_5346,plain,
% 7.66/1.53      ( ~ r1_ordinal1(k2_xboole_0(sK7,k1_tarski(sK7)),sK6)
% 7.66/1.53      | r2_hidden(k2_xboole_0(sK7,k1_tarski(sK7)),k2_xboole_0(sK6,k1_tarski(sK6)))
% 7.66/1.53      | ~ v3_ordinal1(k2_xboole_0(sK7,k1_tarski(sK7)))
% 7.66/1.53      | ~ v3_ordinal1(sK6) ),
% 7.66/1.53      inference(instantiation,[status(thm)],[c_2770]) ).
% 7.66/1.53  
% 7.66/1.53  cnf(c_5353,plain,
% 7.66/1.53      ( r1_ordinal1(k2_xboole_0(sK7,k1_tarski(sK7)),sK6) != iProver_top
% 7.66/1.53      | r2_hidden(k2_xboole_0(sK7,k1_tarski(sK7)),k2_xboole_0(sK6,k1_tarski(sK6))) = iProver_top
% 7.66/1.53      | v3_ordinal1(k2_xboole_0(sK7,k1_tarski(sK7))) != iProver_top
% 7.66/1.53      | v3_ordinal1(sK6) != iProver_top ),
% 7.66/1.53      inference(predicate_to_equality,[status(thm)],[c_5346]) ).
% 7.66/1.53  
% 7.66/1.53  cnf(c_5735,plain,
% 7.66/1.53      ( k2_xboole_0(sK7,k1_tarski(sK7)) = sK6
% 7.66/1.53      | v4_ordinal1(sK6) != iProver_top ),
% 7.66/1.53      inference(global_propositional_subsumption,
% 7.66/1.53                [status(thm)],
% 7.66/1.53                [c_5612,c_39,c_43,c_44,c_45,c_1861,c_2059,c_2310,c_2600,
% 7.66/1.53                 c_3632,c_5353]) ).
% 7.66/1.53  
% 7.66/1.53  cnf(c_12690,plain,
% 7.66/1.53      ( k2_xboole_0(sK7,k1_tarski(sK7)) = sK6 ),
% 7.66/1.53      inference(superposition,[status(thm)],[c_12556,c_5735]) ).
% 7.66/1.53  
% 7.66/1.53  cnf(c_1757,plain,
% 7.66/1.53      ( r1_ordinal1(k2_xboole_0(X0,k1_tarski(X0)),X1) = iProver_top
% 7.66/1.53      | r2_hidden(X0,X1) != iProver_top
% 7.66/1.53      | v3_ordinal1(X1) != iProver_top ),
% 7.66/1.53      inference(predicate_to_equality,[status(thm)],[c_229]) ).
% 7.66/1.53  
% 7.66/1.53  cnf(c_12806,plain,
% 7.66/1.53      ( r1_ordinal1(sK6,X0) = iProver_top
% 7.66/1.53      | r2_hidden(sK7,X0) != iProver_top
% 7.66/1.53      | v3_ordinal1(X0) != iProver_top ),
% 7.66/1.53      inference(superposition,[status(thm)],[c_12690,c_1757]) ).
% 7.66/1.53  
% 7.66/1.53  cnf(c_15427,plain,
% 7.66/1.53      ( r1_ordinal1(sK6,sK3(X0,sK7)) = iProver_top
% 7.66/1.53      | r2_hidden(sK7,k3_tarski(X0)) != iProver_top
% 7.66/1.53      | v3_ordinal1(sK3(X0,sK7)) != iProver_top ),
% 7.66/1.53      inference(superposition,[status(thm)],[c_1783,c_12806]) ).
% 7.66/1.53  
% 7.66/1.53  cnf(c_15438,plain,
% 7.66/1.53      ( r1_ordinal1(sK6,sK3(X0,sK7))
% 7.66/1.53      | ~ r2_hidden(sK7,k3_tarski(X0))
% 7.66/1.53      | ~ v3_ordinal1(sK3(X0,sK7)) ),
% 7.66/1.53      inference(predicate_to_equality_rev,[status(thm)],[c_15427]) ).
% 7.66/1.53  
% 7.66/1.53  cnf(c_15440,plain,
% 7.66/1.53      ( r1_ordinal1(sK6,sK3(sK6,sK7))
% 7.66/1.53      | ~ r2_hidden(sK7,k3_tarski(sK6))
% 7.66/1.53      | ~ v3_ordinal1(sK3(sK6,sK7)) ),
% 7.66/1.53      inference(instantiation,[status(thm)],[c_15438]) ).
% 7.66/1.53  
% 7.66/1.53  cnf(c_10912,plain,
% 7.66/1.53      ( ~ r2_hidden(sK3(X0,sK7),X0) | ~ r1_tarski(X0,sK3(X0,sK7)) ),
% 7.66/1.53      inference(instantiation,[status(thm)],[c_33]) ).
% 7.66/1.53  
% 7.66/1.53  cnf(c_10914,plain,
% 7.66/1.53      ( ~ r2_hidden(sK3(sK6,sK7),sK6) | ~ r1_tarski(sK6,sK3(sK6,sK7)) ),
% 7.66/1.53      inference(instantiation,[status(thm)],[c_10912]) ).
% 7.66/1.53  
% 7.66/1.53  cnf(c_2227,plain,
% 7.66/1.53      ( ~ r2_hidden(sK3(sK6,X0),X1)
% 7.66/1.53      | ~ v3_ordinal1(X1)
% 7.66/1.53      | v3_ordinal1(sK3(sK6,X0)) ),
% 7.66/1.53      inference(instantiation,[status(thm)],[c_21]) ).
% 7.66/1.53  
% 7.66/1.53  cnf(c_2731,plain,
% 7.66/1.53      ( ~ r2_hidden(sK3(sK6,X0),sK6)
% 7.66/1.53      | v3_ordinal1(sK3(sK6,X0))
% 7.66/1.53      | ~ v3_ordinal1(sK6) ),
% 7.66/1.53      inference(instantiation,[status(thm)],[c_2227]) ).
% 7.66/1.53  
% 7.66/1.53  cnf(c_10866,plain,
% 7.66/1.53      ( ~ r2_hidden(sK3(sK6,sK7),sK6)
% 7.66/1.53      | v3_ordinal1(sK3(sK6,sK7))
% 7.66/1.53      | ~ v3_ordinal1(sK6) ),
% 7.66/1.53      inference(instantiation,[status(thm)],[c_2731]) ).
% 7.66/1.53  
% 7.66/1.53  cnf(c_3406,plain,
% 7.66/1.53      ( r2_hidden(X0,k3_tarski(sK6))
% 7.66/1.53      | r2_hidden(k3_tarski(sK6),X0)
% 7.66/1.53      | ~ v3_ordinal1(X0)
% 7.66/1.53      | ~ v3_ordinal1(k3_tarski(sK6))
% 7.66/1.53      | k3_tarski(sK6) = X0 ),
% 7.66/1.53      inference(instantiation,[status(thm)],[c_22]) ).
% 7.66/1.53  
% 7.66/1.53  cnf(c_10696,plain,
% 7.66/1.53      ( r2_hidden(k3_tarski(sK6),sK7)
% 7.66/1.53      | r2_hidden(sK7,k3_tarski(sK6))
% 7.66/1.53      | ~ v3_ordinal1(k3_tarski(sK6))
% 7.66/1.53      | ~ v3_ordinal1(sK7)
% 7.66/1.53      | k3_tarski(sK6) = sK7 ),
% 7.66/1.53      inference(instantiation,[status(thm)],[c_3406]) ).
% 7.66/1.53  
% 7.66/1.53  cnf(c_9508,plain,
% 7.66/1.53      ( ~ r2_hidden(k3_tarski(sK6),sK6) ),
% 7.66/1.53      inference(predicate_to_equality_rev,[status(thm)],[c_9506]) ).
% 7.66/1.53  
% 7.66/1.53  cnf(c_7830,plain,
% 7.66/1.53      ( ~ v3_ordinal1(X0) | v3_ordinal1(k3_tarski(X0)) ),
% 7.66/1.53      inference(predicate_to_equality_rev,[status(thm)],[c_7828]) ).
% 7.66/1.53  
% 7.66/1.53  cnf(c_7832,plain,
% 7.66/1.53      ( v3_ordinal1(k3_tarski(sK6)) | ~ v3_ordinal1(sK6) ),
% 7.66/1.53      inference(instantiation,[status(thm)],[c_7830]) ).
% 7.66/1.53  
% 7.66/1.53  cnf(c_2464,plain,
% 7.66/1.53      ( r2_hidden(X0,sK6)
% 7.66/1.53      | ~ r2_hidden(sK7,sK6)
% 7.66/1.53      | X0 != sK7
% 7.66/1.53      | sK6 != sK6 ),
% 7.66/1.53      inference(instantiation,[status(thm)],[c_1973]) ).
% 7.66/1.53  
% 7.66/1.53  cnf(c_5760,plain,
% 7.66/1.53      ( r2_hidden(k3_tarski(X0),sK6)
% 7.66/1.53      | ~ r2_hidden(sK7,sK6)
% 7.66/1.53      | k3_tarski(X0) != sK7
% 7.66/1.53      | sK6 != sK6 ),
% 7.66/1.53      inference(instantiation,[status(thm)],[c_2464]) ).
% 7.66/1.53  
% 7.66/1.53  cnf(c_5766,plain,
% 7.66/1.53      ( r2_hidden(k3_tarski(sK6),sK6)
% 7.66/1.53      | ~ r2_hidden(sK7,sK6)
% 7.66/1.53      | k3_tarski(sK6) != sK7
% 7.66/1.53      | sK6 != sK6 ),
% 7.66/1.53      inference(instantiation,[status(thm)],[c_5760]) ).
% 7.66/1.53  
% 7.66/1.53  cnf(c_5413,plain,
% 7.66/1.53      ( r2_hidden(sK3(X0,sK7),X0) | ~ r2_hidden(sK7,k3_tarski(X0)) ),
% 7.66/1.53      inference(instantiation,[status(thm)],[c_10]) ).
% 7.66/1.53  
% 7.66/1.53  cnf(c_5424,plain,
% 7.66/1.53      ( r2_hidden(sK3(sK6,sK7),sK6) | ~ r2_hidden(sK7,k3_tarski(sK6)) ),
% 7.66/1.53      inference(instantiation,[status(thm)],[c_5413]) ).
% 7.66/1.53  
% 7.66/1.53  cnf(c_1761,plain,
% 7.66/1.53      ( r2_hidden(sK7,sK6) = iProver_top
% 7.66/1.53      | v4_ordinal1(sK6) != iProver_top ),
% 7.66/1.53      inference(predicate_to_equality,[status(thm)],[c_35]) ).
% 7.66/1.53  
% 7.66/1.53  cnf(c_4496,plain,
% 7.66/1.53      ( r2_hidden(X0,k3_tarski(sK6)) = iProver_top
% 7.66/1.53      | r2_hidden(X0,sK7) != iProver_top
% 7.66/1.53      | v4_ordinal1(sK6) != iProver_top ),
% 7.66/1.53      inference(superposition,[status(thm)],[c_1761,c_1785]) ).
% 7.66/1.53  
% 7.66/1.53  cnf(c_4835,plain,
% 7.66/1.53      ( r2_hidden(X0,sK7) != iProver_top
% 7.66/1.53      | r1_tarski(k3_tarski(sK6),X0) != iProver_top
% 7.66/1.53      | v4_ordinal1(sK6) != iProver_top ),
% 7.66/1.53      inference(superposition,[status(thm)],[c_4496,c_1763]) ).
% 7.66/1.53  
% 7.66/1.53  cnf(c_5361,plain,
% 7.66/1.53      ( r2_hidden(k3_tarski(sK6),sK7) != iProver_top
% 7.66/1.53      | v4_ordinal1(sK6) != iProver_top ),
% 7.66/1.53      inference(superposition,[status(thm)],[c_1789,c_4835]) ).
% 7.66/1.53  
% 7.66/1.53  cnf(c_5362,plain,
% 7.66/1.53      ( ~ r2_hidden(k3_tarski(sK6),sK7) | ~ v4_ordinal1(sK6) ),
% 7.66/1.53      inference(predicate_to_equality_rev,[status(thm)],[c_5361]) ).
% 7.66/1.53  
% 7.66/1.53  cnf(c_308,plain,
% 7.66/1.53      ( v4_ordinal1(X0) | k3_tarski(X0) != X0 ),
% 7.66/1.53      inference(prop_impl,[status(thm)],[c_13]) ).
% 7.66/1.53  
% 7.66/1.53  cnf(c_550,plain,
% 7.66/1.53      ( r2_hidden(sK7,sK6) | k3_tarski(X0) != X0 | sK6 != X0 ),
% 7.66/1.53      inference(resolution_lifted,[status(thm)],[c_308,c_35]) ).
% 7.66/1.53  
% 7.66/1.53  cnf(c_551,plain,
% 7.66/1.53      ( r2_hidden(sK7,sK6) | k3_tarski(sK6) != sK6 ),
% 7.66/1.53      inference(unflattening,[status(thm)],[c_550]) ).
% 7.66/1.53  
% 7.66/1.53  cnf(c_540,plain,
% 7.66/1.53      ( v3_ordinal1(sK7) | k3_tarski(X0) != X0 | sK6 != X0 ),
% 7.66/1.53      inference(resolution_lifted,[status(thm)],[c_308,c_36]) ).
% 7.66/1.53  
% 7.66/1.53  cnf(c_541,plain,
% 7.66/1.53      ( v3_ordinal1(sK7) | k3_tarski(sK6) != sK6 ),
% 7.66/1.53      inference(unflattening,[status(thm)],[c_540]) ).
% 7.66/1.53  
% 7.66/1.53  cnf(c_103,plain,
% 7.66/1.53      ( v4_ordinal1(sK6) | k3_tarski(sK6) != sK6 ),
% 7.66/1.53      inference(instantiation,[status(thm)],[c_13]) ).
% 7.66/1.53  
% 7.66/1.53  cnf(contradiction,plain,
% 7.66/1.53      ( $false ),
% 7.66/1.53      inference(minisat,
% 7.66/1.53                [status(thm)],
% 7.66/1.53                [c_24248,c_15440,c_12448,c_10914,c_10866,c_10696,c_9508,
% 7.66/1.53                 c_7832,c_5766,c_5424,c_5362,c_551,c_541,c_103,c_94,c_90,
% 7.66/1.53                 c_80,c_65,c_47,c_38]) ).
% 7.66/1.53  
% 7.66/1.53  
% 7.66/1.53  % SZS output end CNFRefutation for theBenchmark.p
% 7.66/1.53  
% 7.66/1.53  ------                               Statistics
% 7.66/1.53  
% 7.66/1.53  ------ General
% 7.66/1.53  
% 7.66/1.53  abstr_ref_over_cycles:                  0
% 7.66/1.53  abstr_ref_under_cycles:                 0
% 7.66/1.53  gc_basic_clause_elim:                   0
% 7.66/1.53  forced_gc_time:                         0
% 7.66/1.53  parsing_time:                           0.008
% 7.66/1.53  unif_index_cands_time:                  0.
% 7.66/1.53  unif_index_add_time:                    0.
% 7.66/1.53  orderings_time:                         0.
% 7.66/1.53  out_proof_time:                         0.021
% 7.66/1.53  total_time:                             0.735
% 7.66/1.53  num_of_symbols:                         47
% 7.66/1.53  num_of_terms:                           19776
% 7.66/1.53  
% 7.66/1.53  ------ Preprocessing
% 7.66/1.53  
% 7.66/1.53  num_of_splits:                          0
% 7.66/1.53  num_of_split_atoms:                     0
% 7.66/1.53  num_of_reused_defs:                     0
% 7.66/1.53  num_eq_ax_congr_red:                    42
% 7.66/1.53  num_of_sem_filtered_clauses:            1
% 7.66/1.53  num_of_subtypes:                        0
% 7.66/1.53  monotx_restored_types:                  0
% 7.66/1.53  sat_num_of_epr_types:                   0
% 7.66/1.53  sat_num_of_non_cyclic_types:            0
% 7.66/1.53  sat_guarded_non_collapsed_types:        0
% 7.66/1.53  num_pure_diseq_elim:                    0
% 7.66/1.53  simp_replaced_by:                       0
% 7.66/1.53  res_preprocessed:                       165
% 7.66/1.53  prep_upred:                             0
% 7.66/1.53  prep_unflattend:                        8
% 7.66/1.53  smt_new_axioms:                         0
% 7.66/1.53  pred_elim_cands:                        5
% 7.66/1.53  pred_elim:                              0
% 7.66/1.53  pred_elim_cl:                           0
% 7.66/1.53  pred_elim_cycles:                       2
% 7.66/1.53  merged_defs:                            8
% 7.66/1.53  merged_defs_ncl:                        0
% 7.66/1.53  bin_hyper_res:                          8
% 7.66/1.53  prep_cycles:                            4
% 7.66/1.53  pred_elim_time:                         0.002
% 7.66/1.53  splitting_time:                         0.
% 7.66/1.53  sem_filter_time:                        0.
% 7.66/1.53  monotx_time:                            0.
% 7.66/1.53  subtype_inf_time:                       0.
% 7.66/1.53  
% 7.66/1.53  ------ Problem properties
% 7.66/1.53  
% 7.66/1.53  clauses:                                37
% 7.66/1.53  conjectures:                            5
% 7.66/1.53  epr:                                    12
% 7.66/1.53  horn:                                   28
% 7.66/1.53  ground:                                 4
% 7.66/1.53  unary:                                  5
% 7.66/1.53  binary:                                 14
% 7.66/1.53  lits:                                   97
% 7.66/1.53  lits_eq:                                8
% 7.66/1.53  fd_pure:                                0
% 7.66/1.53  fd_pseudo:                              0
% 7.66/1.53  fd_cond:                                0
% 7.66/1.53  fd_pseudo_cond:                         6
% 7.66/1.53  ac_symbols:                             0
% 7.66/1.53  
% 7.66/1.53  ------ Propositional Solver
% 7.66/1.53  
% 7.66/1.53  prop_solver_calls:                      31
% 7.66/1.53  prop_fast_solver_calls:                 2103
% 7.66/1.53  smt_solver_calls:                       0
% 7.66/1.53  smt_fast_solver_calls:                  0
% 7.66/1.53  prop_num_of_clauses:                    9477
% 7.66/1.53  prop_preprocess_simplified:             22699
% 7.66/1.53  prop_fo_subsumed:                       220
% 7.66/1.53  prop_solver_time:                       0.
% 7.66/1.53  smt_solver_time:                        0.
% 7.66/1.53  smt_fast_solver_time:                   0.
% 7.66/1.53  prop_fast_solver_time:                  0.
% 7.66/1.53  prop_unsat_core_time:                   0.001
% 7.66/1.53  
% 7.66/1.53  ------ QBF
% 7.66/1.53  
% 7.66/1.53  qbf_q_res:                              0
% 7.66/1.53  qbf_num_tautologies:                    0
% 7.66/1.53  qbf_prep_cycles:                        0
% 7.66/1.53  
% 7.66/1.53  ------ BMC1
% 7.66/1.53  
% 7.66/1.53  bmc1_current_bound:                     -1
% 7.66/1.53  bmc1_last_solved_bound:                 -1
% 7.66/1.53  bmc1_unsat_core_size:                   -1
% 7.66/1.53  bmc1_unsat_core_parents_size:           -1
% 7.66/1.53  bmc1_merge_next_fun:                    0
% 7.66/1.53  bmc1_unsat_core_clauses_time:           0.
% 7.66/1.53  
% 7.66/1.53  ------ Instantiation
% 7.66/1.53  
% 7.66/1.53  inst_num_of_clauses:                    2399
% 7.66/1.53  inst_num_in_passive:                    982
% 7.66/1.53  inst_num_in_active:                     1009
% 7.66/1.53  inst_num_in_unprocessed:                407
% 7.66/1.53  inst_num_of_loops:                      1272
% 7.66/1.53  inst_num_of_learning_restarts:          0
% 7.66/1.53  inst_num_moves_active_passive:          261
% 7.66/1.53  inst_lit_activity:                      0
% 7.66/1.53  inst_lit_activity_moves:                0
% 7.66/1.53  inst_num_tautologies:                   0
% 7.66/1.53  inst_num_prop_implied:                  0
% 7.66/1.53  inst_num_existing_simplified:           0
% 7.66/1.53  inst_num_eq_res_simplified:             0
% 7.66/1.53  inst_num_child_elim:                    0
% 7.66/1.53  inst_num_of_dismatching_blockings:      2664
% 7.66/1.53  inst_num_of_non_proper_insts:           2570
% 7.66/1.53  inst_num_of_duplicates:                 0
% 7.66/1.53  inst_inst_num_from_inst_to_res:         0
% 7.66/1.53  inst_dismatching_checking_time:         0.
% 7.66/1.53  
% 7.66/1.53  ------ Resolution
% 7.66/1.53  
% 7.66/1.53  res_num_of_clauses:                     0
% 7.66/1.53  res_num_in_passive:                     0
% 7.66/1.53  res_num_in_active:                      0
% 7.66/1.53  res_num_of_loops:                       169
% 7.66/1.53  res_forward_subset_subsumed:            214
% 7.66/1.53  res_backward_subset_subsumed:           2
% 7.66/1.53  res_forward_subsumed:                   0
% 7.66/1.53  res_backward_subsumed:                  0
% 7.66/1.53  res_forward_subsumption_resolution:     0
% 7.66/1.53  res_backward_subsumption_resolution:    0
% 7.66/1.53  res_clause_to_clause_subsumption:       5654
% 7.66/1.53  res_orphan_elimination:                 0
% 7.66/1.53  res_tautology_del:                      234
% 7.66/1.53  res_num_eq_res_simplified:              0
% 7.66/1.53  res_num_sel_changes:                    0
% 7.66/1.53  res_moves_from_active_to_pass:          0
% 7.66/1.53  
% 7.66/1.53  ------ Superposition
% 7.66/1.53  
% 7.66/1.53  sup_time_total:                         0.
% 7.66/1.53  sup_time_generating:                    0.
% 7.66/1.53  sup_time_sim_full:                      0.
% 7.66/1.53  sup_time_sim_immed:                     0.
% 7.66/1.53  
% 7.66/1.53  sup_num_of_clauses:                     889
% 7.66/1.53  sup_num_in_active:                      170
% 7.66/1.53  sup_num_in_passive:                     719
% 7.66/1.53  sup_num_of_loops:                       254
% 7.66/1.53  sup_fw_superposition:                   621
% 7.66/1.53  sup_bw_superposition:                   852
% 7.66/1.53  sup_immediate_simplified:               280
% 7.66/1.53  sup_given_eliminated:                   0
% 7.66/1.53  comparisons_done:                       0
% 7.66/1.53  comparisons_avoided:                    0
% 7.66/1.53  
% 7.66/1.53  ------ Simplifications
% 7.66/1.53  
% 7.66/1.53  
% 7.66/1.53  sim_fw_subset_subsumed:                 136
% 7.66/1.53  sim_bw_subset_subsumed:                 54
% 7.66/1.53  sim_fw_subsumed:                        88
% 7.66/1.53  sim_bw_subsumed:                        21
% 7.66/1.53  sim_fw_subsumption_res:                 0
% 7.66/1.53  sim_bw_subsumption_res:                 0
% 7.66/1.53  sim_tautology_del:                      68
% 7.66/1.53  sim_eq_tautology_del:                   14
% 7.66/1.53  sim_eq_res_simp:                        0
% 7.66/1.53  sim_fw_demodulated:                     17
% 7.66/1.53  sim_bw_demodulated:                     53
% 7.66/1.53  sim_light_normalised:                   71
% 7.66/1.53  sim_joinable_taut:                      0
% 7.66/1.53  sim_joinable_simp:                      0
% 7.66/1.53  sim_ac_normalised:                      0
% 7.66/1.53  sim_smt_subsumption:                    0
% 7.66/1.53  
%------------------------------------------------------------------------------
