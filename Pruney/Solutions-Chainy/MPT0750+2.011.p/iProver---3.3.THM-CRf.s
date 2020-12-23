%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:54:01 EST 2020

% Result     : Theorem 11.81s
% Output     : CNFRefutation 11.81s
% Verified   : 
% Statistics : Number of formulae       :  273 (2156 expanded)
%              Number of clauses        :  166 ( 648 expanded)
%              Number of leaves         :   28 ( 478 expanded)
%              Depth                    :   23
%              Number of atoms          :  904 (9472 expanded)
%              Number of equality atoms :  317 (1568 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal clause size      :   18 (   3 average)
%              Maximal term depth       :    7 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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

fof(f70,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK0(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f7,axiom,(
    ! [X0] :
    ? [X1] :
    ! [X2] :
      ( r2_hidden(X2,X1)
    <=> ( v3_ordinal1(X2)
        & r2_hidden(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f50,plain,(
    ! [X0] :
    ? [X1] :
    ! [X2] :
      ( ( r2_hidden(X2,X1)
        | ~ v3_ordinal1(X2)
        | ~ r2_hidden(X2,X0) )
      & ( ( v3_ordinal1(X2)
          & r2_hidden(X2,X0) )
        | ~ r2_hidden(X2,X1) ) ) ),
    inference(nnf_transformation,[],[f7])).

fof(f51,plain,(
    ! [X0] :
    ? [X1] :
    ! [X2] :
      ( ( r2_hidden(X2,X1)
        | ~ v3_ordinal1(X2)
        | ~ r2_hidden(X2,X0) )
      & ( ( v3_ordinal1(X2)
          & r2_hidden(X2,X0) )
        | ~ r2_hidden(X2,X1) ) ) ),
    inference(flattening,[],[f50])).

fof(f52,plain,(
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
          ( ( r2_hidden(X2,sK4(X0))
            | ~ v3_ordinal1(X2)
            | ~ r2_hidden(X2,X0) )
          & ( ( v3_ordinal1(X2)
              & r2_hidden(X2,X0) )
            | ~ r2_hidden(X2,sK4(X0)) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f53,plain,(
    ! [X0,X2] :
      ( ( r2_hidden(X2,sK4(X0))
        | ~ v3_ordinal1(X2)
        | ~ r2_hidden(X2,X0) )
      & ( ( v3_ordinal1(X2)
          & r2_hidden(X2,X0) )
        | ~ r2_hidden(X2,sK4(X0)) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f51,f52])).

fof(f86,plain,(
    ! [X2,X0] :
      ( r2_hidden(X2,X0)
      | ~ r2_hidden(X2,sK4(X0)) ) ),
    inference(cnf_transformation,[],[f53])).

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
    inference(nnf_transformation,[],[f35])).

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
     => ( ~ r2_hidden(k1_ordinal1(sK9),X0)
        & r2_hidden(sK9,X0)
        & v3_ordinal1(sK9) ) ) ),
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
            ( ~ r2_hidden(k1_ordinal1(X1),sK8)
            & r2_hidden(X1,sK8)
            & v3_ordinal1(X1) )
        | ~ v4_ordinal1(sK8) )
      & ( ! [X2] :
            ( r2_hidden(k1_ordinal1(X2),sK8)
            | ~ r2_hidden(X2,sK8)
            | ~ v3_ordinal1(X2) )
        | v4_ordinal1(sK8) )
      & v3_ordinal1(sK8) ) ),
    introduced(choice_axiom,[])).

fof(f68,plain,
    ( ( ( ~ r2_hidden(k1_ordinal1(sK9),sK8)
        & r2_hidden(sK9,sK8)
        & v3_ordinal1(sK9) )
      | ~ v4_ordinal1(sK8) )
    & ( ! [X2] :
          ( r2_hidden(k1_ordinal1(X2),sK8)
          | ~ r2_hidden(X2,sK8)
          | ~ v3_ordinal1(X2) )
      | v4_ordinal1(sK8) )
    & v3_ordinal1(sK8) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8,sK9])],[f65,f67,f66])).

fof(f107,plain,(
    ! [X2] :
      ( r2_hidden(k1_ordinal1(X2),sK8)
      | ~ r2_hidden(X2,sK8)
      | ~ v3_ordinal1(X2)
      | v4_ordinal1(sK8) ) ),
    inference(cnf_transformation,[],[f68])).

fof(f4,axiom,(
    ! [X0] : k1_ordinal1(X0) = k2_xboole_0(X0,k1_tarski(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f81,plain,(
    ! [X0] : k1_ordinal1(X0) = k2_xboole_0(X0,k1_tarski(X0)) ),
    inference(cnf_transformation,[],[f4])).

fof(f119,plain,(
    ! [X2] :
      ( r2_hidden(k2_xboole_0(X2,k1_tarski(X2)),sK8)
      | ~ r2_hidden(X2,sK8)
      | ~ v3_ordinal1(X2)
      | v4_ordinal1(sK8) ) ),
    inference(definition_unfolding,[],[f107,f81])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k3_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] :
              ( r2_hidden(X3,X0)
              & r2_hidden(X2,X3) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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

fof(f77,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | ~ r2_hidden(X6,X0)
      | ~ r2_hidden(X5,X6)
      | k3_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f47])).

fof(f122,plain,(
    ! [X6,X0,X5] :
      ( r2_hidden(X5,k3_tarski(X0))
      | ~ r2_hidden(X6,X0)
      | ~ r2_hidden(X5,X6) ) ),
    inference(equality_resolution,[],[f77])).

fof(f106,plain,(
    v3_ordinal1(sK8) ),
    inference(cnf_transformation,[],[f68])).

fof(f5,axiom,(
    ! [X0] :
      ( v4_ordinal1(X0)
    <=> k3_tarski(X0) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
    ! [X0] :
      ( ( v4_ordinal1(X0)
        | k3_tarski(X0) != X0 )
      & ( k3_tarski(X0) = X0
        | ~ v4_ordinal1(X0) ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f83,plain,(
    ! [X0] :
      ( v4_ordinal1(X0)
      | k3_tarski(X0) != X0 ) ),
    inference(cnf_transformation,[],[f48])).

fof(f76,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(sK3(X0,X5),X0)
      | ~ r2_hidden(X5,X1)
      | k3_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f47])).

fof(f123,plain,(
    ! [X0,X5] :
      ( r2_hidden(sK3(X0,X5),X0)
      | ~ r2_hidden(X5,k3_tarski(X0)) ) ),
    inference(equality_resolution,[],[f76])).

fof(f11,axiom,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ! [X1] :
          ( v3_ordinal1(X1)
         => ~ ( ~ r2_hidden(X1,X0)
              & X0 != X1
              & ~ r2_hidden(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(X1,X0)
          | X0 = X1
          | r2_hidden(X0,X1)
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(X1,X0)
          | X0 = X1
          | r2_hidden(X0,X1)
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(flattening,[],[f25])).

fof(f94,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,X0)
      | X0 = X1
      | r2_hidden(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f13,axiom,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ! [X1] :
          ( v3_ordinal1(X1)
         => ( r2_hidden(X0,k1_ordinal1(X1))
          <=> r1_ordinal1(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r2_hidden(X0,k1_ordinal1(X1))
          <=> r1_ordinal1(X0,X1) )
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f56,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( r2_hidden(X0,k1_ordinal1(X1))
              | ~ r1_ordinal1(X0,X1) )
            & ( r1_ordinal1(X0,X1)
              | ~ r2_hidden(X0,k1_ordinal1(X1)) ) )
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(nnf_transformation,[],[f28])).

fof(f96,plain,(
    ! [X0,X1] :
      ( r1_ordinal1(X0,X1)
      | ~ r2_hidden(X0,k1_ordinal1(X1))
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f117,plain,(
    ! [X0,X1] :
      ( r1_ordinal1(X0,X1)
      | ~ r2_hidden(X0,k2_xboole_0(X1,k1_tarski(X1)))
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(definition_unfolding,[],[f96,f81])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ( v3_ordinal1(X1)
        & v3_ordinal1(X0) )
     => ( r1_ordinal1(X0,X1)
      <=> r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( r1_ordinal1(X0,X1)
      <=> r1_tarski(X0,X1) )
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( r1_ordinal1(X0,X1)
      <=> r1_tarski(X0,X1) )
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(flattening,[],[f21])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ( ( r1_ordinal1(X0,X1)
          | ~ r1_tarski(X0,X1) )
        & ( r1_tarski(X0,X1)
          | ~ r1_ordinal1(X0,X1) ) )
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(nnf_transformation,[],[f22])).

fof(f84,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r1_ordinal1(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f75,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(X5,sK3(X0,X5))
      | ~ r2_hidden(X5,X1)
      | k3_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f47])).

fof(f124,plain,(
    ! [X0,X5] :
      ( r2_hidden(X5,sK3(X0,X5))
      | ~ r2_hidden(X5,k3_tarski(X0)) ) ),
    inference(equality_resolution,[],[f75])).

fof(f17,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f105,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( v3_ordinal1(X1)
     => ( r2_hidden(X0,X1)
       => v3_ordinal1(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] :
      ( v3_ordinal1(X0)
      | ~ r2_hidden(X0,X1)
      | ~ v3_ordinal1(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f24,plain,(
    ! [X0,X1] :
      ( v3_ordinal1(X0)
      | ~ r2_hidden(X0,X1)
      | ~ v3_ordinal1(X1) ) ),
    inference(flattening,[],[f23])).

fof(f93,plain,(
    ! [X0,X1] :
      ( v3_ordinal1(X0)
      | ~ r2_hidden(X0,X1)
      | ~ v3_ordinal1(X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,k1_ordinal1(X1))
    <=> ( X0 = X1
        | r2_hidden(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f54,plain,(
    ! [X0,X1] :
      ( ( r2_hidden(X0,k1_ordinal1(X1))
        | ( X0 != X1
          & ~ r2_hidden(X0,X1) ) )
      & ( X0 = X1
        | r2_hidden(X0,X1)
        | ~ r2_hidden(X0,k1_ordinal1(X1)) ) ) ),
    inference(nnf_transformation,[],[f9])).

fof(f55,plain,(
    ! [X0,X1] :
      ( ( r2_hidden(X0,k1_ordinal1(X1))
        | ( X0 != X1
          & ~ r2_hidden(X0,X1) ) )
      & ( X0 = X1
        | r2_hidden(X0,X1)
        | ~ r2_hidden(X0,k1_ordinal1(X1)) ) ) ),
    inference(flattening,[],[f54])).

fof(f92,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,k1_ordinal1(X1))
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f55])).

fof(f112,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,k2_xboole_0(X1,k1_tarski(X1)))
      | X0 != X1 ) ),
    inference(definition_unfolding,[],[f92,f81])).

fof(f125,plain,(
    ! [X1] : r2_hidden(X1,k2_xboole_0(X1,k1_tarski(X1))) ),
    inference(equality_resolution,[],[f112])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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

fof(f73,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f41])).

fof(f120,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f73])).

fof(f91,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,k1_ordinal1(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f113,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,k2_xboole_0(X1,k1_tarski(X1)))
      | ~ r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f91,f81])).

fof(f12,axiom,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => v3_ordinal1(k1_ordinal1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0] :
      ( v3_ordinal1(k1_ordinal1(X0))
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f95,plain,(
    ! [X0] :
      ( v3_ordinal1(k1_ordinal1(X0))
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f115,plain,(
    ! [X0] :
      ( v3_ordinal1(k2_xboole_0(X0,k1_tarski(X0)))
      | ~ v3_ordinal1(X0) ) ),
    inference(definition_unfolding,[],[f95,f81])).

fof(f14,axiom,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(X1,X0)
         => v3_ordinal1(X1) )
     => v3_ordinal1(k3_tarski(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0] :
      ( v3_ordinal1(k3_tarski(X0))
      | ? [X1] :
          ( ~ v3_ordinal1(X1)
          & r2_hidden(X1,X0) ) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f57,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ v3_ordinal1(X1)
          & r2_hidden(X1,X0) )
     => ( ~ v3_ordinal1(sK5(X0))
        & r2_hidden(sK5(X0),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f58,plain,(
    ! [X0] :
      ( v3_ordinal1(k3_tarski(X0))
      | ( ~ v3_ordinal1(sK5(X0))
        & r2_hidden(sK5(X0),X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f29,f57])).

fof(f98,plain,(
    ! [X0] :
      ( v3_ordinal1(k3_tarski(X0))
      | r2_hidden(sK5(X0),X0) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f99,plain,(
    ! [X0] :
      ( v3_ordinal1(k3_tarski(X0))
      | ~ v3_ordinal1(sK5(X0)) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f108,plain,
    ( v3_ordinal1(sK9)
    | ~ v4_ordinal1(sK8) ),
    inference(cnf_transformation,[],[f68])).

fof(f97,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,k1_ordinal1(X1))
      | ~ r1_ordinal1(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f116,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,k2_xboole_0(X1,k1_tarski(X1)))
      | ~ r1_ordinal1(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(definition_unfolding,[],[f97,f81])).

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

fof(f31,plain,(
    ! [X0] :
    ? [X1] :
      ( ! [X2] :
          ( r1_ordinal1(X1,X2)
          | r2_hidden(X2,X0)
          | ~ v3_ordinal1(X2) )
      & ~ r2_hidden(X1,X0)
      & v3_ordinal1(X1) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f32,plain,(
    ! [X0] :
    ? [X1] :
      ( ! [X2] :
          ( r1_ordinal1(X1,X2)
          | r2_hidden(X2,X0)
          | ~ v3_ordinal1(X2) )
      & ~ r2_hidden(X1,X0)
      & v3_ordinal1(X1) ) ),
    inference(flattening,[],[f31])).

fof(f61,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2] :
              ( r1_ordinal1(X1,X2)
              | r2_hidden(X2,X0)
              | ~ v3_ordinal1(X2) )
          & ~ r2_hidden(X1,X0)
          & v3_ordinal1(X1) )
     => ( ! [X2] :
            ( r1_ordinal1(sK7(X0),X2)
            | r2_hidden(X2,X0)
            | ~ v3_ordinal1(X2) )
        & ~ r2_hidden(sK7(X0),X0)
        & v3_ordinal1(sK7(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f62,plain,(
    ! [X0] :
      ( ! [X2] :
          ( r1_ordinal1(sK7(X0),X2)
          | r2_hidden(X2,X0)
          | ~ v3_ordinal1(X2) )
      & ~ r2_hidden(sK7(X0),X0)
      & v3_ordinal1(sK7(X0)) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f32,f61])).

fof(f104,plain,(
    ! [X2,X0] :
      ( r1_ordinal1(sK7(X0),X2)
      | r2_hidden(X2,X0)
      | ~ v3_ordinal1(X2) ) ),
    inference(cnf_transformation,[],[f62])).

fof(f102,plain,(
    ! [X0] : v3_ordinal1(sK7(X0)) ),
    inference(cnf_transformation,[],[f62])).

fof(f90,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | r2_hidden(X0,X1)
      | ~ r2_hidden(X0,k1_ordinal1(X1)) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f114,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | r2_hidden(X0,X1)
      | ~ r2_hidden(X0,k2_xboole_0(X1,k1_tarski(X1))) ) ),
    inference(definition_unfolding,[],[f90,f81])).

fof(f103,plain,(
    ! [X0] : ~ r2_hidden(sK7(X0),X0) ),
    inference(cnf_transformation,[],[f62])).

fof(f71,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK0(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f110,plain,
    ( ~ r2_hidden(k1_ordinal1(sK9),sK8)
    | ~ v4_ordinal1(sK8) ),
    inference(cnf_transformation,[],[f68])).

fof(f118,plain,
    ( ~ r2_hidden(k2_xboole_0(sK9,k1_tarski(sK9)),sK8)
    | ~ v4_ordinal1(sK8) ),
    inference(definition_unfolding,[],[f110,f81])).

fof(f109,plain,
    ( r2_hidden(sK9,sK8)
    | ~ v4_ordinal1(sK8) ),
    inference(cnf_transformation,[],[f68])).

fof(f69,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f82,plain,(
    ! [X0] :
      ( k3_tarski(X0) = X0
      | ~ v4_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_1,plain,
    ( r2_hidden(sK0(X0,X1),X0)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_1927,plain,
    ( r2_hidden(sK0(X0,X1),X0) = iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_18,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(X0,sK4(X1)) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_1913,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r2_hidden(X0,sK4(X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_3632,plain,
    ( r2_hidden(sK0(sK4(X0),X1),X0) = iProver_top
    | r1_tarski(sK4(X0),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_1927,c_1913])).

cnf(c_7482,plain,
    ( r2_hidden(sK0(sK4(sK4(X0)),X1),X0) = iProver_top
    | r1_tarski(sK4(sK4(X0)),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_3632,c_1913])).

cnf(c_39,negated_conjecture,
    ( ~ r2_hidden(X0,sK8)
    | r2_hidden(k2_xboole_0(X0,k1_tarski(X0)),sK8)
    | ~ v3_ordinal1(X0)
    | v4_ordinal1(sK8) ),
    inference(cnf_transformation,[],[f119])).

cnf(c_1896,plain,
    ( r2_hidden(X0,sK8) != iProver_top
    | r2_hidden(k2_xboole_0(X0,k1_tarski(X0)),sK8) = iProver_top
    | v3_ordinal1(X0) != iProver_top
    | v4_ordinal1(sK8) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_39])).

cnf(c_9,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X2,X0)
    | r2_hidden(X2,k3_tarski(X1)) ),
    inference(cnf_transformation,[],[f122])).

cnf(c_1920,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X2,X0) != iProver_top
    | r2_hidden(X2,k3_tarski(X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_5486,plain,
    ( r2_hidden(X0,k2_xboole_0(X1,k1_tarski(X1))) != iProver_top
    | r2_hidden(X0,k3_tarski(sK8)) = iProver_top
    | r2_hidden(X1,sK8) != iProver_top
    | v3_ordinal1(X1) != iProver_top
    | v4_ordinal1(sK8) = iProver_top ),
    inference(superposition,[status(thm)],[c_1896,c_1920])).

cnf(c_12947,plain,
    ( r2_hidden(X0,sK8) != iProver_top
    | r2_hidden(sK0(sK4(sK4(k2_xboole_0(X0,k1_tarski(X0)))),X1),k3_tarski(sK8)) = iProver_top
    | r1_tarski(sK4(sK4(k2_xboole_0(X0,k1_tarski(X0)))),X1) = iProver_top
    | v3_ordinal1(X0) != iProver_top
    | v4_ordinal1(sK8) = iProver_top ),
    inference(superposition,[status(thm)],[c_7482,c_5486])).

cnf(c_40,negated_conjecture,
    ( v3_ordinal1(sK8) ),
    inference(cnf_transformation,[],[f106])).

cnf(c_41,plain,
    ( v3_ordinal1(sK8) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_40])).

cnf(c_12,plain,
    ( v4_ordinal1(X0)
    | k3_tarski(X0) != X0 ),
    inference(cnf_transformation,[],[f83])).

cnf(c_111,plain,
    ( k3_tarski(X0) != X0
    | v4_ordinal1(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_113,plain,
    ( k3_tarski(sK8) != sK8
    | v4_ordinal1(sK8) = iProver_top ),
    inference(instantiation,[status(thm)],[c_111])).

cnf(c_10,plain,
    ( ~ r2_hidden(X0,k3_tarski(X1))
    | r2_hidden(sK3(X1,X0),X1) ),
    inference(cnf_transformation,[],[f123])).

cnf(c_117,plain,
    ( r2_hidden(X0,k3_tarski(X1)) != iProver_top
    | r2_hidden(sK3(X1,X0),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_119,plain,
    ( r2_hidden(sK3(sK8,sK8),sK8) = iProver_top
    | r2_hidden(sK8,k3_tarski(sK8)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_117])).

cnf(c_24,plain,
    ( r2_hidden(X0,X1)
    | r2_hidden(X1,X0)
    | ~ v3_ordinal1(X1)
    | ~ v3_ordinal1(X0)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f94])).

cnf(c_2272,plain,
    ( r2_hidden(k3_tarski(sK8),sK8)
    | r2_hidden(sK8,k3_tarski(sK8))
    | ~ v3_ordinal1(k3_tarski(sK8))
    | ~ v3_ordinal1(sK8)
    | k3_tarski(sK8) = sK8 ),
    inference(instantiation,[status(thm)],[c_24])).

cnf(c_2279,plain,
    ( k3_tarski(sK8) = sK8
    | r2_hidden(k3_tarski(sK8),sK8) = iProver_top
    | r2_hidden(sK8,k3_tarski(sK8)) = iProver_top
    | v3_ordinal1(k3_tarski(sK8)) != iProver_top
    | v3_ordinal1(sK8) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2272])).

cnf(c_27,plain,
    ( r1_ordinal1(X0,X1)
    | ~ r2_hidden(X0,k2_xboole_0(X1,k1_tarski(X1)))
    | ~ v3_ordinal1(X1)
    | ~ v3_ordinal1(X0) ),
    inference(cnf_transformation,[],[f117])).

cnf(c_15,plain,
    ( ~ r1_ordinal1(X0,X1)
    | r1_tarski(X0,X1)
    | ~ v3_ordinal1(X1)
    | ~ v3_ordinal1(X0) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_630,plain,
    ( ~ r2_hidden(X0,k2_xboole_0(X1,k1_tarski(X1)))
    | r1_tarski(X0,X1)
    | ~ v3_ordinal1(X1)
    | ~ v3_ordinal1(X0) ),
    inference(resolution,[status(thm)],[c_27,c_15])).

cnf(c_3067,plain,
    ( ~ r2_hidden(sK3(X0,X1),k2_xboole_0(sK8,k1_tarski(sK8)))
    | r1_tarski(sK3(X0,X1),sK8)
    | ~ v3_ordinal1(sK3(X0,X1))
    | ~ v3_ordinal1(sK8) ),
    inference(instantiation,[status(thm)],[c_630])).

cnf(c_3078,plain,
    ( r2_hidden(sK3(X0,X1),k2_xboole_0(sK8,k1_tarski(sK8))) != iProver_top
    | r1_tarski(sK3(X0,X1),sK8) = iProver_top
    | v3_ordinal1(sK3(X0,X1)) != iProver_top
    | v3_ordinal1(sK8) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3067])).

cnf(c_3080,plain,
    ( r2_hidden(sK3(sK8,sK8),k2_xboole_0(sK8,k1_tarski(sK8))) != iProver_top
    | r1_tarski(sK3(sK8,sK8),sK8) = iProver_top
    | v3_ordinal1(sK3(sK8,sK8)) != iProver_top
    | v3_ordinal1(sK8) != iProver_top ),
    inference(instantiation,[status(thm)],[c_3078])).

cnf(c_3573,plain,
    ( r2_hidden(k2_xboole_0(k3_tarski(sK8),k1_tarski(k3_tarski(sK8))),sK8)
    | ~ r2_hidden(k3_tarski(sK8),sK8)
    | ~ v3_ordinal1(k3_tarski(sK8))
    | v4_ordinal1(sK8) ),
    inference(instantiation,[status(thm)],[c_39])).

cnf(c_3574,plain,
    ( r2_hidden(k2_xboole_0(k3_tarski(sK8),k1_tarski(k3_tarski(sK8))),sK8) = iProver_top
    | r2_hidden(k3_tarski(sK8),sK8) != iProver_top
    | v3_ordinal1(k3_tarski(sK8)) != iProver_top
    | v4_ordinal1(sK8) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3573])).

cnf(c_11,plain,
    ( r2_hidden(X0,sK3(X1,X0))
    | ~ r2_hidden(X0,k3_tarski(X1)) ),
    inference(cnf_transformation,[],[f124])).

cnf(c_1918,plain,
    ( r2_hidden(X0,sK3(X1,X0)) = iProver_top
    | r2_hidden(X0,k3_tarski(X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_35,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r1_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f105])).

cnf(c_1900,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_35])).

cnf(c_4011,plain,
    ( r2_hidden(X0,k3_tarski(X1)) != iProver_top
    | r1_tarski(sK3(X1,X0),X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1918,c_1900])).

cnf(c_4013,plain,
    ( r2_hidden(sK8,k3_tarski(sK8)) != iProver_top
    | r1_tarski(sK3(sK8,sK8),sK8) != iProver_top ),
    inference(instantiation,[status(thm)],[c_4011])).

cnf(c_1919,plain,
    ( r2_hidden(X0,k3_tarski(X1)) != iProver_top
    | r2_hidden(sK3(X1,X0),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_23,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ v3_ordinal1(X1)
    | v3_ordinal1(X0) ),
    inference(cnf_transformation,[],[f93])).

cnf(c_1909,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | v3_ordinal1(X1) != iProver_top
    | v3_ordinal1(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_4250,plain,
    ( r2_hidden(X0,k3_tarski(X1)) != iProver_top
    | v3_ordinal1(X1) != iProver_top
    | v3_ordinal1(sK3(X1,X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1919,c_1909])).

cnf(c_4261,plain,
    ( r2_hidden(sK8,k3_tarski(sK8)) != iProver_top
    | v3_ordinal1(sK3(sK8,sK8)) = iProver_top
    | v3_ordinal1(sK8) != iProver_top ),
    inference(instantiation,[status(thm)],[c_4250])).

cnf(c_20,plain,
    ( r2_hidden(X0,k2_xboole_0(X0,k1_tarski(X0))) ),
    inference(cnf_transformation,[],[f125])).

cnf(c_1912,plain,
    ( r2_hidden(X0,k2_xboole_0(X0,k1_tarski(X0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_6001,plain,
    ( r2_hidden(X0,k3_tarski(sK8)) = iProver_top
    | r2_hidden(X0,sK8) != iProver_top
    | v3_ordinal1(X0) != iProver_top
    | v4_ordinal1(sK8) = iProver_top ),
    inference(superposition,[status(thm)],[c_1912,c_5486])).

cnf(c_4,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f120])).

cnf(c_1924,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_21,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,k2_xboole_0(X1,k1_tarski(X1))) ),
    inference(cnf_transformation,[],[f113])).

cnf(c_1911,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,k2_xboole_0(X1,k1_tarski(X1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_3944,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r1_tarski(k2_xboole_0(X1,k1_tarski(X1)),X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1911,c_1900])).

cnf(c_4709,plain,
    ( r2_hidden(k2_xboole_0(X0,k1_tarski(X0)),X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1924,c_3944])).

cnf(c_7889,plain,
    ( r2_hidden(k2_xboole_0(k3_tarski(sK8),k1_tarski(k3_tarski(sK8))),sK8) != iProver_top
    | v3_ordinal1(k2_xboole_0(k3_tarski(sK8),k1_tarski(k3_tarski(sK8)))) != iProver_top
    | v4_ordinal1(sK8) = iProver_top ),
    inference(superposition,[status(thm)],[c_6001,c_4709])).

cnf(c_8497,plain,
    ( ~ r2_hidden(sK3(sK8,X0),X1)
    | r2_hidden(sK3(sK8,X0),k2_xboole_0(X1,k1_tarski(X1))) ),
    inference(instantiation,[status(thm)],[c_21])).

cnf(c_8498,plain,
    ( r2_hidden(sK3(sK8,X0),X1) != iProver_top
    | r2_hidden(sK3(sK8,X0),k2_xboole_0(X1,k1_tarski(X1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8497])).

cnf(c_8500,plain,
    ( r2_hidden(sK3(sK8,sK8),k2_xboole_0(sK8,k1_tarski(sK8))) = iProver_top
    | r2_hidden(sK3(sK8,sK8),sK8) != iProver_top ),
    inference(instantiation,[status(thm)],[c_8498])).

cnf(c_25,plain,
    ( ~ v3_ordinal1(X0)
    | v3_ordinal1(k2_xboole_0(X0,k1_tarski(X0))) ),
    inference(cnf_transformation,[],[f115])).

cnf(c_9468,plain,
    ( v3_ordinal1(k2_xboole_0(k3_tarski(sK8),k1_tarski(k3_tarski(sK8))))
    | ~ v3_ordinal1(k3_tarski(sK8)) ),
    inference(instantiation,[status(thm)],[c_25])).

cnf(c_9469,plain,
    ( v3_ordinal1(k2_xboole_0(k3_tarski(sK8),k1_tarski(k3_tarski(sK8)))) = iProver_top
    | v3_ordinal1(k3_tarski(sK8)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9468])).

cnf(c_29,plain,
    ( r2_hidden(sK5(X0),X0)
    | v3_ordinal1(k3_tarski(X0)) ),
    inference(cnf_transformation,[],[f98])).

cnf(c_1905,plain,
    ( r2_hidden(sK5(X0),X0) = iProver_top
    | v3_ordinal1(k3_tarski(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_4255,plain,
    ( v3_ordinal1(X0) != iProver_top
    | v3_ordinal1(sK5(X0)) = iProver_top
    | v3_ordinal1(k3_tarski(X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1905,c_1909])).

cnf(c_28,plain,
    ( ~ v3_ordinal1(sK5(X0))
    | v3_ordinal1(k3_tarski(X0)) ),
    inference(cnf_transformation,[],[f99])).

cnf(c_69,plain,
    ( v3_ordinal1(sK5(X0)) != iProver_top
    | v3_ordinal1(k3_tarski(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_12307,plain,
    ( v3_ordinal1(X0) != iProver_top
    | v3_ordinal1(k3_tarski(X0)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4255,c_69])).

cnf(c_12310,plain,
    ( v3_ordinal1(k3_tarski(sK8)) = iProver_top
    | v3_ordinal1(sK8) != iProver_top ),
    inference(instantiation,[status(thm)],[c_12307])).

cnf(c_12985,plain,
    ( v4_ordinal1(sK8) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_12947,c_41,c_113,c_119,c_2279,c_3080,c_3574,c_4013,c_4261,c_7889,c_8500,c_9469,c_12310])).

cnf(c_38,negated_conjecture,
    ( v3_ordinal1(sK9)
    | ~ v4_ordinal1(sK8) ),
    inference(cnf_transformation,[],[f108])).

cnf(c_1897,plain,
    ( v3_ordinal1(sK9) = iProver_top
    | v4_ordinal1(sK8) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_38])).

cnf(c_12991,plain,
    ( v3_ordinal1(sK9) = iProver_top ),
    inference(superposition,[status(thm)],[c_12985,c_1897])).

cnf(c_26,plain,
    ( ~ r1_ordinal1(X0,X1)
    | r2_hidden(X0,k2_xboole_0(X1,k1_tarski(X1)))
    | ~ v3_ordinal1(X1)
    | ~ v3_ordinal1(X0) ),
    inference(cnf_transformation,[],[f116])).

cnf(c_32,plain,
    ( r1_ordinal1(sK7(X0),X1)
    | r2_hidden(X1,X0)
    | ~ v3_ordinal1(X1) ),
    inference(cnf_transformation,[],[f104])).

cnf(c_661,plain,
    ( r2_hidden(X0,X1)
    | r2_hidden(X2,k2_xboole_0(X3,k1_tarski(X3)))
    | ~ v3_ordinal1(X3)
    | ~ v3_ordinal1(X2)
    | ~ v3_ordinal1(X0)
    | X0 != X3
    | sK7(X1) != X2 ),
    inference(resolution_lifted,[status(thm)],[c_26,c_32])).

cnf(c_662,plain,
    ( r2_hidden(X0,X1)
    | r2_hidden(sK7(X1),k2_xboole_0(X0,k1_tarski(X0)))
    | ~ v3_ordinal1(X0)
    | ~ v3_ordinal1(sK7(X1)) ),
    inference(unflattening,[status(thm)],[c_661])).

cnf(c_34,plain,
    ( v3_ordinal1(sK7(X0)) ),
    inference(cnf_transformation,[],[f102])).

cnf(c_674,plain,
    ( r2_hidden(X0,X1)
    | r2_hidden(sK7(X1),k2_xboole_0(X0,k1_tarski(X0)))
    | ~ v3_ordinal1(X0) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_662,c_34])).

cnf(c_1892,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r2_hidden(sK7(X1),k2_xboole_0(X0,k1_tarski(X0))) = iProver_top
    | v3_ordinal1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_674])).

cnf(c_22,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k2_xboole_0(X1,k1_tarski(X1)))
    | X1 = X0 ),
    inference(cnf_transformation,[],[f114])).

cnf(c_1910,plain,
    ( X0 = X1
    | r2_hidden(X1,X0) = iProver_top
    | r2_hidden(X1,k2_xboole_0(X0,k1_tarski(X0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_4477,plain,
    ( sK7(X0) = X1
    | r2_hidden(X1,X0) = iProver_top
    | r2_hidden(sK7(X0),X1) = iProver_top
    | v3_ordinal1(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1892,c_1910])).

cnf(c_33,plain,
    ( ~ r2_hidden(sK7(X0),X0) ),
    inference(cnf_transformation,[],[f103])).

cnf(c_1902,plain,
    ( r2_hidden(sK7(X0),X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_27208,plain,
    ( sK7(X0) = X0
    | r2_hidden(X0,X0) = iProver_top
    | v3_ordinal1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_4477,c_1902])).

cnf(c_3135,plain,
    ( r1_tarski(k2_xboole_0(X0,k1_tarski(X0)),X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1912,c_1900])).

cnf(c_4471,plain,
    ( sK0(k2_xboole_0(X0,k1_tarski(X0)),X1) = X0
    | r2_hidden(sK0(k2_xboole_0(X0,k1_tarski(X0)),X1),X0) = iProver_top
    | r1_tarski(k2_xboole_0(X0,k1_tarski(X0)),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_1927,c_1910])).

cnf(c_0,plain,
    ( ~ r2_hidden(sK0(X0,X1),X1)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_1928,plain,
    ( r2_hidden(sK0(X0,X1),X1) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_23177,plain,
    ( sK0(k2_xboole_0(X0,k1_tarski(X0)),X0) = X0
    | r1_tarski(k2_xboole_0(X0,k1_tarski(X0)),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_4471,c_1928])).

cnf(c_23293,plain,
    ( sK0(k2_xboole_0(X0,k1_tarski(X0)),X0) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_23177,c_3135])).

cnf(c_23299,plain,
    ( r2_hidden(X0,X0) != iProver_top
    | r1_tarski(k2_xboole_0(X0,k1_tarski(X0)),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_23293,c_1928])).

cnf(c_29259,plain,
    ( sK7(X0) = X0
    | v3_ordinal1(X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_27208,c_3135,c_23299])).

cnf(c_29269,plain,
    ( sK7(sK9) = sK9 ),
    inference(superposition,[status(thm)],[c_12991,c_29259])).

cnf(c_29747,plain,
    ( sK7(sK9) = X0
    | r2_hidden(X0,sK9) = iProver_top
    | r2_hidden(sK9,X0) = iProver_top
    | v3_ordinal1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_29269,c_4477])).

cnf(c_29761,plain,
    ( sK9 = X0
    | r2_hidden(X0,sK9) = iProver_top
    | r2_hidden(sK9,X0) = iProver_top
    | v3_ordinal1(X0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_29747,c_29269])).

cnf(c_39633,plain,
    ( k3_tarski(X0) = sK9
    | r2_hidden(k3_tarski(X0),sK9) = iProver_top
    | v3_ordinal1(X0) != iProver_top
    | v3_ordinal1(sK3(X0,sK9)) = iProver_top
    | v3_ordinal1(k3_tarski(X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_29761,c_4250])).

cnf(c_39737,plain,
    ( k3_tarski(sK8) = sK9
    | r2_hidden(k3_tarski(sK8),sK9) = iProver_top
    | v3_ordinal1(sK3(sK8,sK9)) = iProver_top
    | v3_ordinal1(k3_tarski(sK8)) != iProver_top
    | v3_ordinal1(sK8) != iProver_top ),
    inference(instantiation,[status(thm)],[c_39633])).

cnf(c_1895,plain,
    ( v3_ordinal1(sK8) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_40])).

cnf(c_29270,plain,
    ( sK7(sK8) = sK8 ),
    inference(superposition,[status(thm)],[c_1895,c_29259])).

cnf(c_681,plain,
    ( r2_hidden(X0,X1)
    | r1_tarski(X2,X3)
    | ~ v3_ordinal1(X3)
    | ~ v3_ordinal1(X2)
    | ~ v3_ordinal1(X0)
    | X0 != X3
    | sK7(X1) != X2 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_32])).

cnf(c_682,plain,
    ( r2_hidden(X0,X1)
    | r1_tarski(sK7(X1),X0)
    | ~ v3_ordinal1(X0)
    | ~ v3_ordinal1(sK7(X1)) ),
    inference(unflattening,[status(thm)],[c_681])).

cnf(c_694,plain,
    ( r2_hidden(X0,X1)
    | r1_tarski(sK7(X1),X0)
    | ~ v3_ordinal1(X0) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_682,c_34])).

cnf(c_1891,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r1_tarski(sK7(X1),X0) = iProver_top
    | v3_ordinal1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_694])).

cnf(c_29535,plain,
    ( r2_hidden(X0,sK8) = iProver_top
    | r1_tarski(sK8,X0) = iProver_top
    | v3_ordinal1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_29270,c_1891])).

cnf(c_1908,plain,
    ( X0 = X1
    | r2_hidden(X1,X0) = iProver_top
    | r2_hidden(X0,X1) = iProver_top
    | v3_ordinal1(X1) != iProver_top
    | v3_ordinal1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_36,negated_conjecture,
    ( ~ r2_hidden(k2_xboole_0(sK9,k1_tarski(sK9)),sK8)
    | ~ v4_ordinal1(sK8) ),
    inference(cnf_transformation,[],[f118])).

cnf(c_1899,plain,
    ( r2_hidden(k2_xboole_0(sK9,k1_tarski(sK9)),sK8) != iProver_top
    | v4_ordinal1(sK8) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_36])).

cnf(c_6573,plain,
    ( k2_xboole_0(sK9,k1_tarski(sK9)) = sK8
    | r2_hidden(sK8,k2_xboole_0(sK9,k1_tarski(sK9))) = iProver_top
    | v3_ordinal1(k2_xboole_0(sK9,k1_tarski(sK9))) != iProver_top
    | v3_ordinal1(sK8) != iProver_top
    | v4_ordinal1(sK8) != iProver_top ),
    inference(superposition,[status(thm)],[c_1908,c_1899])).

cnf(c_45,plain,
    ( v3_ordinal1(sK9) = iProver_top
    | v4_ordinal1(sK8) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_38])).

cnf(c_2006,plain,
    ( ~ r2_hidden(sK8,k2_xboole_0(sK9,k1_tarski(sK9)))
    | r1_tarski(sK8,sK9)
    | ~ v3_ordinal1(sK8)
    | ~ v3_ordinal1(sK9) ),
    inference(instantiation,[status(thm)],[c_630])).

cnf(c_2013,plain,
    ( r2_hidden(sK8,k2_xboole_0(sK9,k1_tarski(sK9))) != iProver_top
    | r1_tarski(sK8,sK9) = iProver_top
    | v3_ordinal1(sK8) != iProver_top
    | v3_ordinal1(sK9) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2006])).

cnf(c_2112,plain,
    ( v3_ordinal1(k2_xboole_0(sK9,k1_tarski(sK9)))
    | ~ v3_ordinal1(sK9) ),
    inference(instantiation,[status(thm)],[c_25])).

cnf(c_2113,plain,
    ( v3_ordinal1(k2_xboole_0(sK9,k1_tarski(sK9))) = iProver_top
    | v3_ordinal1(sK9) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2112])).

cnf(c_37,negated_conjecture,
    ( r2_hidden(sK9,sK8)
    | ~ v4_ordinal1(sK8) ),
    inference(cnf_transformation,[],[f109])).

cnf(c_1898,plain,
    ( r2_hidden(sK9,sK8) = iProver_top
    | v4_ordinal1(sK8) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_37])).

cnf(c_3136,plain,
    ( r1_tarski(sK8,sK9) != iProver_top
    | v4_ordinal1(sK8) != iProver_top ),
    inference(superposition,[status(thm)],[c_1898,c_1900])).

cnf(c_6773,plain,
    ( k2_xboole_0(sK9,k1_tarski(sK9)) = sK8
    | v4_ordinal1(sK8) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6573,c_41,c_45,c_2013,c_2113,c_3136])).

cnf(c_12990,plain,
    ( k2_xboole_0(sK9,k1_tarski(sK9)) = sK8 ),
    inference(superposition,[status(thm)],[c_12985,c_6773])).

cnf(c_1894,plain,
    ( r2_hidden(X0,k2_xboole_0(X1,k1_tarski(X1))) != iProver_top
    | r1_tarski(X0,X1) = iProver_top
    | v3_ordinal1(X0) != iProver_top
    | v3_ordinal1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_630])).

cnf(c_13267,plain,
    ( r2_hidden(X0,sK8) != iProver_top
    | r1_tarski(X0,sK9) = iProver_top
    | v3_ordinal1(X0) != iProver_top
    | v3_ordinal1(sK9) != iProver_top ),
    inference(superposition,[status(thm)],[c_12990,c_1894])).

cnf(c_21128,plain,
    ( v3_ordinal1(X0) != iProver_top
    | r1_tarski(X0,sK9) = iProver_top
    | r2_hidden(X0,sK8) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_13267,c_41,c_45,c_113,c_119,c_2279,c_3080,c_3574,c_4013,c_4261,c_7889,c_8500,c_9469,c_12310])).

cnf(c_21129,plain,
    ( r2_hidden(X0,sK8) != iProver_top
    | r1_tarski(X0,sK9) = iProver_top
    | v3_ordinal1(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_21128])).

cnf(c_29850,plain,
    ( r1_tarski(X0,sK9) = iProver_top
    | r1_tarski(sK8,X0) = iProver_top
    | v3_ordinal1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_29535,c_21129])).

cnf(c_39135,plain,
    ( r2_hidden(sK9,k3_tarski(X0)) != iProver_top
    | r1_tarski(sK8,sK3(X0,sK9)) = iProver_top
    | v3_ordinal1(sK3(X0,sK9)) != iProver_top ),
    inference(superposition,[status(thm)],[c_29850,c_4011])).

cnf(c_39176,plain,
    ( r2_hidden(sK9,k3_tarski(sK8)) != iProver_top
    | r1_tarski(sK8,sK3(sK8,sK9)) = iProver_top
    | v3_ordinal1(sK3(sK8,sK9)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_39135])).

cnf(c_20284,plain,
    ( ~ r2_hidden(sK3(X0,sK9),X0)
    | ~ r1_tarski(X0,sK3(X0,sK9)) ),
    inference(instantiation,[status(thm)],[c_35])).

cnf(c_20285,plain,
    ( r2_hidden(sK3(X0,sK9),X0) != iProver_top
    | r1_tarski(X0,sK3(X0,sK9)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20284])).

cnf(c_20287,plain,
    ( r2_hidden(sK3(sK8,sK9),sK8) != iProver_top
    | r1_tarski(sK8,sK3(sK8,sK9)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_20285])).

cnf(c_10518,plain,
    ( r1_tarski(k3_tarski(sK8),k3_tarski(sK8)) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_10519,plain,
    ( r1_tarski(k3_tarski(sK8),k3_tarski(sK8)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10518])).

cnf(c_1149,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X1)
    | X2 != X0 ),
    theory(equality)).

cnf(c_3596,plain,
    ( ~ r1_tarski(X0,k3_tarski(sK8))
    | r1_tarski(sK8,k3_tarski(sK8))
    | sK8 != X0 ),
    inference(instantiation,[status(thm)],[c_1149])).

cnf(c_6917,plain,
    ( ~ r1_tarski(k3_tarski(sK8),k3_tarski(sK8))
    | r1_tarski(sK8,k3_tarski(sK8))
    | sK8 != k3_tarski(sK8) ),
    inference(instantiation,[status(thm)],[c_3596])).

cnf(c_6918,plain,
    ( sK8 != k3_tarski(sK8)
    | r1_tarski(k3_tarski(sK8),k3_tarski(sK8)) != iProver_top
    | r1_tarski(sK8,k3_tarski(sK8)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6917])).

cnf(c_5485,plain,
    ( r2_hidden(X0,k3_tarski(sK8)) = iProver_top
    | r2_hidden(X0,sK9) != iProver_top
    | v4_ordinal1(sK8) != iProver_top ),
    inference(superposition,[status(thm)],[c_1898,c_1920])).

cnf(c_5778,plain,
    ( r2_hidden(X0,sK9) != iProver_top
    | r1_tarski(k3_tarski(sK8),X0) != iProver_top
    | v4_ordinal1(sK8) != iProver_top ),
    inference(superposition,[status(thm)],[c_5485,c_1900])).

cnf(c_6847,plain,
    ( r2_hidden(k3_tarski(sK8),sK9) != iProver_top
    | v4_ordinal1(sK8) != iProver_top ),
    inference(superposition,[status(thm)],[c_1924,c_5778])).

cnf(c_2,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | ~ r1_tarski(X1,X2) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_3004,plain,
    ( r2_hidden(sK9,X0)
    | ~ r2_hidden(sK9,sK8)
    | ~ r1_tarski(sK8,X0) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_3756,plain,
    ( r2_hidden(sK9,k3_tarski(X0))
    | ~ r2_hidden(sK9,sK8)
    | ~ r1_tarski(sK8,k3_tarski(X0)) ),
    inference(instantiation,[status(thm)],[c_3004])).

cnf(c_3761,plain,
    ( r2_hidden(sK9,k3_tarski(X0)) = iProver_top
    | r2_hidden(sK9,sK8) != iProver_top
    | r1_tarski(sK8,k3_tarski(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3756])).

cnf(c_3763,plain,
    ( r2_hidden(sK9,k3_tarski(sK8)) = iProver_top
    | r2_hidden(sK9,sK8) != iProver_top
    | r1_tarski(sK8,k3_tarski(sK8)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_3761])).

cnf(c_3755,plain,
    ( r2_hidden(sK3(X0,sK9),X0)
    | ~ r2_hidden(sK9,k3_tarski(X0)) ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_3757,plain,
    ( r2_hidden(sK3(X0,sK9),X0) = iProver_top
    | r2_hidden(sK9,k3_tarski(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3755])).

cnf(c_3759,plain,
    ( r2_hidden(sK3(sK8,sK9),sK8) = iProver_top
    | r2_hidden(sK9,k3_tarski(sK8)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_3757])).

cnf(c_1150,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_2147,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,sK8)
    | X2 != X0
    | sK8 != X1 ),
    inference(instantiation,[status(thm)],[c_1150])).

cnf(c_3552,plain,
    ( r2_hidden(X0,sK8)
    | ~ r2_hidden(k3_tarski(sK8),sK8)
    | X0 != k3_tarski(sK8)
    | sK8 != sK8 ),
    inference(instantiation,[status(thm)],[c_2147])).

cnf(c_3555,plain,
    ( ~ r2_hidden(k3_tarski(sK8),sK8)
    | r2_hidden(sK8,sK8)
    | sK8 != k3_tarski(sK8)
    | sK8 != sK8 ),
    inference(instantiation,[status(thm)],[c_3552])).

cnf(c_2628,plain,
    ( r2_hidden(X0,sK8)
    | ~ r2_hidden(sK9,sK8)
    | X0 != sK9
    | sK8 != sK8 ),
    inference(instantiation,[status(thm)],[c_2147])).

cnf(c_3469,plain,
    ( r2_hidden(k3_tarski(X0),sK8)
    | ~ r2_hidden(sK9,sK8)
    | k3_tarski(X0) != sK9
    | sK8 != sK8 ),
    inference(instantiation,[status(thm)],[c_2628])).

cnf(c_3471,plain,
    ( r2_hidden(k3_tarski(sK8),sK8)
    | ~ r2_hidden(sK9,sK8)
    | k3_tarski(sK8) != sK9
    | sK8 != sK8 ),
    inference(instantiation,[status(thm)],[c_3469])).

cnf(c_1148,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_3110,plain,
    ( k3_tarski(X0) != X1
    | sK8 != X1
    | sK8 = k3_tarski(X0) ),
    inference(instantiation,[status(thm)],[c_1148])).

cnf(c_3111,plain,
    ( k3_tarski(sK8) != sK8
    | sK8 = k3_tarski(sK8)
    | sK8 != sK8 ),
    inference(instantiation,[status(thm)],[c_3110])).

cnf(c_320,plain,
    ( v4_ordinal1(X0)
    | k3_tarski(X0) != X0 ),
    inference(prop_impl,[status(thm)],[c_12])).

cnf(c_569,plain,
    ( r2_hidden(sK9,sK8)
    | k3_tarski(X0) != X0
    | sK8 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_320,c_37])).

cnf(c_570,plain,
    ( r2_hidden(sK9,sK8)
    | k3_tarski(sK8) != sK8 ),
    inference(unflattening,[status(thm)],[c_569])).

cnf(c_13,plain,
    ( ~ v4_ordinal1(X0)
    | k3_tarski(X0) = X0 ),
    inference(cnf_transformation,[],[f82])).

cnf(c_108,plain,
    ( k3_tarski(X0) = X0
    | v4_ordinal1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_110,plain,
    ( k3_tarski(sK8) = sK8
    | v4_ordinal1(sK8) != iProver_top ),
    inference(instantiation,[status(thm)],[c_108])).

cnf(c_103,plain,
    ( ~ r1_ordinal1(sK8,sK8)
    | r1_tarski(sK8,sK8)
    | ~ v3_ordinal1(sK8) ),
    inference(instantiation,[status(thm)],[c_15])).

cnf(c_92,plain,
    ( r2_hidden(sK8,k2_xboole_0(sK8,k1_tarski(sK8))) ),
    inference(instantiation,[status(thm)],[c_20])).

cnf(c_82,plain,
    ( r2_hidden(sK8,sK8)
    | ~ v3_ordinal1(sK8)
    | sK8 = sK8 ),
    inference(instantiation,[status(thm)],[c_24])).

cnf(c_73,plain,
    ( r1_ordinal1(sK8,sK8)
    | ~ r2_hidden(sK8,k2_xboole_0(sK8,k1_tarski(sK8)))
    | ~ v3_ordinal1(sK8) ),
    inference(instantiation,[status(thm)],[c_27])).

cnf(c_49,plain,
    ( ~ r2_hidden(sK8,sK8)
    | ~ r1_tarski(sK8,sK8) ),
    inference(instantiation,[status(thm)],[c_35])).

cnf(c_46,plain,
    ( r2_hidden(sK9,sK8) = iProver_top
    | v4_ordinal1(sK8) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_37])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_39737,c_39176,c_20287,c_12985,c_12310,c_10519,c_6918,c_6847,c_3763,c_3759,c_3555,c_3471,c_3111,c_570,c_110,c_103,c_92,c_82,c_73,c_49,c_46,c_41,c_40])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 17:39:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 11.81/2.00  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 11.81/2.00  
% 11.81/2.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 11.81/2.00  
% 11.81/2.00  ------  iProver source info
% 11.81/2.00  
% 11.81/2.00  git: date: 2020-06-30 10:37:57 +0100
% 11.81/2.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 11.81/2.00  git: non_committed_changes: false
% 11.81/2.00  git: last_make_outside_of_git: false
% 11.81/2.00  
% 11.81/2.00  ------ 
% 11.81/2.00  
% 11.81/2.00  ------ Input Options
% 11.81/2.00  
% 11.81/2.00  --out_options                           all
% 11.81/2.00  --tptp_safe_out                         true
% 11.81/2.00  --problem_path                          ""
% 11.81/2.00  --include_path                          ""
% 11.81/2.00  --clausifier                            res/vclausify_rel
% 11.81/2.00  --clausifier_options                    ""
% 11.81/2.00  --stdin                                 false
% 11.81/2.00  --stats_out                             all
% 11.81/2.00  
% 11.81/2.00  ------ General Options
% 11.81/2.00  
% 11.81/2.00  --fof                                   false
% 11.81/2.00  --time_out_real                         305.
% 11.81/2.00  --time_out_virtual                      -1.
% 11.81/2.00  --symbol_type_check                     false
% 11.81/2.00  --clausify_out                          false
% 11.81/2.00  --sig_cnt_out                           false
% 11.81/2.00  --trig_cnt_out                          false
% 11.81/2.00  --trig_cnt_out_tolerance                1.
% 11.81/2.00  --trig_cnt_out_sk_spl                   false
% 11.81/2.00  --abstr_cl_out                          false
% 11.81/2.00  
% 11.81/2.00  ------ Global Options
% 11.81/2.00  
% 11.81/2.00  --schedule                              default
% 11.81/2.00  --add_important_lit                     false
% 11.81/2.00  --prop_solver_per_cl                    1000
% 11.81/2.00  --min_unsat_core                        false
% 11.81/2.00  --soft_assumptions                      false
% 11.81/2.00  --soft_lemma_size                       3
% 11.81/2.00  --prop_impl_unit_size                   0
% 11.81/2.00  --prop_impl_unit                        []
% 11.81/2.00  --share_sel_clauses                     true
% 11.81/2.00  --reset_solvers                         false
% 11.81/2.00  --bc_imp_inh                            [conj_cone]
% 11.81/2.00  --conj_cone_tolerance                   3.
% 11.81/2.00  --extra_neg_conj                        none
% 11.81/2.00  --large_theory_mode                     true
% 11.81/2.00  --prolific_symb_bound                   200
% 11.81/2.00  --lt_threshold                          2000
% 11.81/2.00  --clause_weak_htbl                      true
% 11.81/2.00  --gc_record_bc_elim                     false
% 11.81/2.00  
% 11.81/2.00  ------ Preprocessing Options
% 11.81/2.00  
% 11.81/2.00  --preprocessing_flag                    true
% 11.81/2.00  --time_out_prep_mult                    0.1
% 11.81/2.00  --splitting_mode                        input
% 11.81/2.00  --splitting_grd                         true
% 11.81/2.00  --splitting_cvd                         false
% 11.81/2.00  --splitting_cvd_svl                     false
% 11.81/2.00  --splitting_nvd                         32
% 11.81/2.00  --sub_typing                            true
% 11.81/2.00  --prep_gs_sim                           true
% 11.81/2.00  --prep_unflatten                        true
% 11.81/2.00  --prep_res_sim                          true
% 11.81/2.00  --prep_upred                            true
% 11.81/2.00  --prep_sem_filter                       exhaustive
% 11.81/2.00  --prep_sem_filter_out                   false
% 11.81/2.00  --pred_elim                             true
% 11.81/2.00  --res_sim_input                         true
% 11.81/2.00  --eq_ax_congr_red                       true
% 11.81/2.00  --pure_diseq_elim                       true
% 11.81/2.00  --brand_transform                       false
% 11.81/2.00  --non_eq_to_eq                          false
% 11.81/2.00  --prep_def_merge                        true
% 11.81/2.00  --prep_def_merge_prop_impl              false
% 11.81/2.00  --prep_def_merge_mbd                    true
% 11.81/2.00  --prep_def_merge_tr_red                 false
% 11.81/2.00  --prep_def_merge_tr_cl                  false
% 11.81/2.00  --smt_preprocessing                     true
% 11.81/2.00  --smt_ac_axioms                         fast
% 11.81/2.00  --preprocessed_out                      false
% 11.81/2.00  --preprocessed_stats                    false
% 11.81/2.00  
% 11.81/2.00  ------ Abstraction refinement Options
% 11.81/2.00  
% 11.81/2.00  --abstr_ref                             []
% 11.81/2.00  --abstr_ref_prep                        false
% 11.81/2.00  --abstr_ref_until_sat                   false
% 11.81/2.00  --abstr_ref_sig_restrict                funpre
% 11.81/2.00  --abstr_ref_af_restrict_to_split_sk     false
% 11.81/2.00  --abstr_ref_under                       []
% 11.81/2.00  
% 11.81/2.00  ------ SAT Options
% 11.81/2.00  
% 11.81/2.00  --sat_mode                              false
% 11.81/2.00  --sat_fm_restart_options                ""
% 11.81/2.00  --sat_gr_def                            false
% 11.81/2.00  --sat_epr_types                         true
% 11.81/2.00  --sat_non_cyclic_types                  false
% 11.81/2.00  --sat_finite_models                     false
% 11.81/2.00  --sat_fm_lemmas                         false
% 11.81/2.00  --sat_fm_prep                           false
% 11.81/2.00  --sat_fm_uc_incr                        true
% 11.81/2.00  --sat_out_model                         small
% 11.81/2.00  --sat_out_clauses                       false
% 11.81/2.00  
% 11.81/2.00  ------ QBF Options
% 11.81/2.00  
% 11.81/2.00  --qbf_mode                              false
% 11.81/2.00  --qbf_elim_univ                         false
% 11.81/2.00  --qbf_dom_inst                          none
% 11.81/2.00  --qbf_dom_pre_inst                      false
% 11.81/2.00  --qbf_sk_in                             false
% 11.81/2.00  --qbf_pred_elim                         true
% 11.81/2.00  --qbf_split                             512
% 11.81/2.00  
% 11.81/2.00  ------ BMC1 Options
% 11.81/2.00  
% 11.81/2.00  --bmc1_incremental                      false
% 11.81/2.00  --bmc1_axioms                           reachable_all
% 11.81/2.00  --bmc1_min_bound                        0
% 11.81/2.00  --bmc1_max_bound                        -1
% 11.81/2.00  --bmc1_max_bound_default                -1
% 11.81/2.00  --bmc1_symbol_reachability              true
% 11.81/2.00  --bmc1_property_lemmas                  false
% 11.81/2.00  --bmc1_k_induction                      false
% 11.81/2.00  --bmc1_non_equiv_states                 false
% 11.81/2.00  --bmc1_deadlock                         false
% 11.81/2.00  --bmc1_ucm                              false
% 11.81/2.00  --bmc1_add_unsat_core                   none
% 11.81/2.00  --bmc1_unsat_core_children              false
% 11.81/2.00  --bmc1_unsat_core_extrapolate_axioms    false
% 11.81/2.00  --bmc1_out_stat                         full
% 11.81/2.00  --bmc1_ground_init                      false
% 11.81/2.00  --bmc1_pre_inst_next_state              false
% 11.81/2.00  --bmc1_pre_inst_state                   false
% 11.81/2.00  --bmc1_pre_inst_reach_state             false
% 11.81/2.00  --bmc1_out_unsat_core                   false
% 11.81/2.00  --bmc1_aig_witness_out                  false
% 11.81/2.00  --bmc1_verbose                          false
% 11.81/2.00  --bmc1_dump_clauses_tptp                false
% 11.81/2.00  --bmc1_dump_unsat_core_tptp             false
% 11.81/2.00  --bmc1_dump_file                        -
% 11.81/2.00  --bmc1_ucm_expand_uc_limit              128
% 11.81/2.00  --bmc1_ucm_n_expand_iterations          6
% 11.81/2.00  --bmc1_ucm_extend_mode                  1
% 11.81/2.00  --bmc1_ucm_init_mode                    2
% 11.81/2.00  --bmc1_ucm_cone_mode                    none
% 11.81/2.00  --bmc1_ucm_reduced_relation_type        0
% 11.81/2.00  --bmc1_ucm_relax_model                  4
% 11.81/2.00  --bmc1_ucm_full_tr_after_sat            true
% 11.81/2.00  --bmc1_ucm_expand_neg_assumptions       false
% 11.81/2.00  --bmc1_ucm_layered_model                none
% 11.81/2.00  --bmc1_ucm_max_lemma_size               10
% 11.81/2.00  
% 11.81/2.00  ------ AIG Options
% 11.81/2.00  
% 11.81/2.00  --aig_mode                              false
% 11.81/2.00  
% 11.81/2.00  ------ Instantiation Options
% 11.81/2.00  
% 11.81/2.00  --instantiation_flag                    true
% 11.81/2.00  --inst_sos_flag                         true
% 11.81/2.00  --inst_sos_phase                        true
% 11.81/2.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 11.81/2.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 11.81/2.00  --inst_lit_sel_side                     num_symb
% 11.81/2.00  --inst_solver_per_active                1400
% 11.81/2.00  --inst_solver_calls_frac                1.
% 11.81/2.00  --inst_passive_queue_type               priority_queues
% 11.81/2.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 11.81/2.00  --inst_passive_queues_freq              [25;2]
% 11.81/2.00  --inst_dismatching                      true
% 11.81/2.00  --inst_eager_unprocessed_to_passive     true
% 11.81/2.00  --inst_prop_sim_given                   true
% 11.81/2.00  --inst_prop_sim_new                     false
% 11.81/2.00  --inst_subs_new                         false
% 11.81/2.00  --inst_eq_res_simp                      false
% 11.81/2.00  --inst_subs_given                       false
% 11.81/2.00  --inst_orphan_elimination               true
% 11.81/2.00  --inst_learning_loop_flag               true
% 11.81/2.00  --inst_learning_start                   3000
% 11.81/2.00  --inst_learning_factor                  2
% 11.81/2.00  --inst_start_prop_sim_after_learn       3
% 11.81/2.00  --inst_sel_renew                        solver
% 11.81/2.00  --inst_lit_activity_flag                true
% 11.81/2.00  --inst_restr_to_given                   false
% 11.81/2.00  --inst_activity_threshold               500
% 11.81/2.00  --inst_out_proof                        true
% 11.81/2.00  
% 11.81/2.00  ------ Resolution Options
% 11.81/2.00  
% 11.81/2.00  --resolution_flag                       true
% 11.81/2.00  --res_lit_sel                           adaptive
% 11.81/2.00  --res_lit_sel_side                      none
% 11.81/2.00  --res_ordering                          kbo
% 11.81/2.00  --res_to_prop_solver                    active
% 11.81/2.00  --res_prop_simpl_new                    false
% 11.81/2.00  --res_prop_simpl_given                  true
% 11.81/2.00  --res_passive_queue_type                priority_queues
% 11.81/2.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 11.81/2.00  --res_passive_queues_freq               [15;5]
% 11.81/2.00  --res_forward_subs                      full
% 11.81/2.00  --res_backward_subs                     full
% 11.81/2.00  --res_forward_subs_resolution           true
% 11.81/2.00  --res_backward_subs_resolution          true
% 11.81/2.00  --res_orphan_elimination                true
% 11.81/2.00  --res_time_limit                        2.
% 11.81/2.00  --res_out_proof                         true
% 11.81/2.00  
% 11.81/2.00  ------ Superposition Options
% 11.81/2.00  
% 11.81/2.00  --superposition_flag                    true
% 11.81/2.00  --sup_passive_queue_type                priority_queues
% 11.81/2.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 11.81/2.00  --sup_passive_queues_freq               [8;1;4]
% 11.81/2.00  --demod_completeness_check              fast
% 11.81/2.00  --demod_use_ground                      true
% 11.81/2.00  --sup_to_prop_solver                    passive
% 11.81/2.00  --sup_prop_simpl_new                    true
% 11.81/2.00  --sup_prop_simpl_given                  true
% 11.81/2.00  --sup_fun_splitting                     true
% 11.81/2.00  --sup_smt_interval                      50000
% 11.81/2.00  
% 11.81/2.00  ------ Superposition Simplification Setup
% 11.81/2.00  
% 11.81/2.00  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 11.81/2.00  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 11.81/2.00  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 11.81/2.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 11.81/2.00  --sup_full_triv                         [TrivRules;PropSubs]
% 11.81/2.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 11.81/2.00  --sup_full_bw                           [BwDemod;BwSubsumption]
% 11.81/2.00  --sup_immed_triv                        [TrivRules]
% 11.81/2.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 11.81/2.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 11.81/2.00  --sup_immed_bw_main                     []
% 11.81/2.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 11.81/2.00  --sup_input_triv                        [Unflattening;TrivRules]
% 11.81/2.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 11.81/2.00  --sup_input_bw                          []
% 11.81/2.00  
% 11.81/2.00  ------ Combination Options
% 11.81/2.00  
% 11.81/2.00  --comb_res_mult                         3
% 11.81/2.00  --comb_sup_mult                         2
% 11.81/2.00  --comb_inst_mult                        10
% 11.81/2.00  
% 11.81/2.00  ------ Debug Options
% 11.81/2.00  
% 11.81/2.00  --dbg_backtrace                         false
% 11.81/2.00  --dbg_dump_prop_clauses                 false
% 11.81/2.00  --dbg_dump_prop_clauses_file            -
% 11.81/2.00  --dbg_out_stat                          false
% 11.81/2.00  ------ Parsing...
% 11.81/2.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 11.81/2.00  
% 11.81/2.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 11.81/2.00  
% 11.81/2.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 11.81/2.00  
% 11.81/2.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 11.81/2.00  ------ Proving...
% 11.81/2.00  ------ Problem Properties 
% 11.81/2.00  
% 11.81/2.00  
% 11.81/2.00  clauses                                 38
% 11.81/2.00  conjectures                             5
% 11.81/2.00  EPR                                     9
% 11.81/2.00  Horn                                    29
% 11.81/2.00  unary                                   7
% 11.81/2.00  binary                                  16
% 11.81/2.00  lits                                    90
% 11.81/2.00  lits eq                                 8
% 11.81/2.00  fd_pure                                 0
% 11.81/2.00  fd_pseudo                               0
% 11.81/2.00  fd_cond                                 0
% 11.81/2.00  fd_pseudo_cond                          6
% 11.81/2.00  AC symbols                              0
% 11.81/2.00  
% 11.81/2.00  ------ Schedule dynamic 5 is on 
% 11.81/2.00  
% 11.81/2.00  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 11.81/2.00  
% 11.81/2.00  
% 11.81/2.00  ------ 
% 11.81/2.00  Current options:
% 11.81/2.00  ------ 
% 11.81/2.00  
% 11.81/2.00  ------ Input Options
% 11.81/2.00  
% 11.81/2.00  --out_options                           all
% 11.81/2.00  --tptp_safe_out                         true
% 11.81/2.00  --problem_path                          ""
% 11.81/2.00  --include_path                          ""
% 11.81/2.00  --clausifier                            res/vclausify_rel
% 11.81/2.00  --clausifier_options                    ""
% 11.81/2.00  --stdin                                 false
% 11.81/2.00  --stats_out                             all
% 11.81/2.00  
% 11.81/2.00  ------ General Options
% 11.81/2.00  
% 11.81/2.00  --fof                                   false
% 11.81/2.00  --time_out_real                         305.
% 11.81/2.00  --time_out_virtual                      -1.
% 11.81/2.00  --symbol_type_check                     false
% 11.81/2.00  --clausify_out                          false
% 11.81/2.00  --sig_cnt_out                           false
% 11.81/2.00  --trig_cnt_out                          false
% 11.81/2.00  --trig_cnt_out_tolerance                1.
% 11.81/2.00  --trig_cnt_out_sk_spl                   false
% 11.81/2.00  --abstr_cl_out                          false
% 11.81/2.00  
% 11.81/2.00  ------ Global Options
% 11.81/2.00  
% 11.81/2.00  --schedule                              default
% 11.81/2.00  --add_important_lit                     false
% 11.81/2.00  --prop_solver_per_cl                    1000
% 11.81/2.00  --min_unsat_core                        false
% 11.81/2.00  --soft_assumptions                      false
% 11.81/2.00  --soft_lemma_size                       3
% 11.81/2.00  --prop_impl_unit_size                   0
% 11.81/2.00  --prop_impl_unit                        []
% 11.81/2.00  --share_sel_clauses                     true
% 11.81/2.00  --reset_solvers                         false
% 11.81/2.00  --bc_imp_inh                            [conj_cone]
% 11.81/2.00  --conj_cone_tolerance                   3.
% 11.81/2.00  --extra_neg_conj                        none
% 11.81/2.00  --large_theory_mode                     true
% 11.81/2.00  --prolific_symb_bound                   200
% 11.81/2.00  --lt_threshold                          2000
% 11.81/2.00  --clause_weak_htbl                      true
% 11.81/2.00  --gc_record_bc_elim                     false
% 11.81/2.00  
% 11.81/2.00  ------ Preprocessing Options
% 11.81/2.00  
% 11.81/2.00  --preprocessing_flag                    true
% 11.81/2.00  --time_out_prep_mult                    0.1
% 11.81/2.00  --splitting_mode                        input
% 11.81/2.00  --splitting_grd                         true
% 11.81/2.00  --splitting_cvd                         false
% 11.81/2.00  --splitting_cvd_svl                     false
% 11.81/2.00  --splitting_nvd                         32
% 11.81/2.00  --sub_typing                            true
% 11.81/2.00  --prep_gs_sim                           true
% 11.81/2.00  --prep_unflatten                        true
% 11.81/2.00  --prep_res_sim                          true
% 11.81/2.00  --prep_upred                            true
% 11.81/2.00  --prep_sem_filter                       exhaustive
% 11.81/2.00  --prep_sem_filter_out                   false
% 11.81/2.00  --pred_elim                             true
% 11.81/2.00  --res_sim_input                         true
% 11.81/2.00  --eq_ax_congr_red                       true
% 11.81/2.00  --pure_diseq_elim                       true
% 11.81/2.00  --brand_transform                       false
% 11.81/2.00  --non_eq_to_eq                          false
% 11.81/2.00  --prep_def_merge                        true
% 11.81/2.00  --prep_def_merge_prop_impl              false
% 11.81/2.00  --prep_def_merge_mbd                    true
% 11.81/2.00  --prep_def_merge_tr_red                 false
% 11.81/2.00  --prep_def_merge_tr_cl                  false
% 11.81/2.00  --smt_preprocessing                     true
% 11.81/2.00  --smt_ac_axioms                         fast
% 11.81/2.00  --preprocessed_out                      false
% 11.81/2.00  --preprocessed_stats                    false
% 11.81/2.00  
% 11.81/2.00  ------ Abstraction refinement Options
% 11.81/2.00  
% 11.81/2.00  --abstr_ref                             []
% 11.81/2.00  --abstr_ref_prep                        false
% 11.81/2.00  --abstr_ref_until_sat                   false
% 11.81/2.00  --abstr_ref_sig_restrict                funpre
% 11.81/2.00  --abstr_ref_af_restrict_to_split_sk     false
% 11.81/2.00  --abstr_ref_under                       []
% 11.81/2.00  
% 11.81/2.00  ------ SAT Options
% 11.81/2.00  
% 11.81/2.00  --sat_mode                              false
% 11.81/2.00  --sat_fm_restart_options                ""
% 11.81/2.00  --sat_gr_def                            false
% 11.81/2.00  --sat_epr_types                         true
% 11.81/2.00  --sat_non_cyclic_types                  false
% 11.81/2.00  --sat_finite_models                     false
% 11.81/2.00  --sat_fm_lemmas                         false
% 11.81/2.00  --sat_fm_prep                           false
% 11.81/2.00  --sat_fm_uc_incr                        true
% 11.81/2.00  --sat_out_model                         small
% 11.81/2.00  --sat_out_clauses                       false
% 11.81/2.00  
% 11.81/2.00  ------ QBF Options
% 11.81/2.00  
% 11.81/2.00  --qbf_mode                              false
% 11.81/2.00  --qbf_elim_univ                         false
% 11.81/2.00  --qbf_dom_inst                          none
% 11.81/2.00  --qbf_dom_pre_inst                      false
% 11.81/2.00  --qbf_sk_in                             false
% 11.81/2.00  --qbf_pred_elim                         true
% 11.81/2.00  --qbf_split                             512
% 11.81/2.00  
% 11.81/2.00  ------ BMC1 Options
% 11.81/2.00  
% 11.81/2.00  --bmc1_incremental                      false
% 11.81/2.00  --bmc1_axioms                           reachable_all
% 11.81/2.00  --bmc1_min_bound                        0
% 11.81/2.00  --bmc1_max_bound                        -1
% 11.81/2.00  --bmc1_max_bound_default                -1
% 11.81/2.00  --bmc1_symbol_reachability              true
% 11.81/2.00  --bmc1_property_lemmas                  false
% 11.81/2.00  --bmc1_k_induction                      false
% 11.81/2.00  --bmc1_non_equiv_states                 false
% 11.81/2.00  --bmc1_deadlock                         false
% 11.81/2.00  --bmc1_ucm                              false
% 11.81/2.00  --bmc1_add_unsat_core                   none
% 11.81/2.00  --bmc1_unsat_core_children              false
% 11.81/2.00  --bmc1_unsat_core_extrapolate_axioms    false
% 11.81/2.00  --bmc1_out_stat                         full
% 11.81/2.00  --bmc1_ground_init                      false
% 11.81/2.00  --bmc1_pre_inst_next_state              false
% 11.81/2.00  --bmc1_pre_inst_state                   false
% 11.81/2.00  --bmc1_pre_inst_reach_state             false
% 11.81/2.00  --bmc1_out_unsat_core                   false
% 11.81/2.00  --bmc1_aig_witness_out                  false
% 11.81/2.00  --bmc1_verbose                          false
% 11.81/2.00  --bmc1_dump_clauses_tptp                false
% 11.81/2.00  --bmc1_dump_unsat_core_tptp             false
% 11.81/2.00  --bmc1_dump_file                        -
% 11.81/2.00  --bmc1_ucm_expand_uc_limit              128
% 11.81/2.00  --bmc1_ucm_n_expand_iterations          6
% 11.81/2.00  --bmc1_ucm_extend_mode                  1
% 11.81/2.00  --bmc1_ucm_init_mode                    2
% 11.81/2.00  --bmc1_ucm_cone_mode                    none
% 11.81/2.00  --bmc1_ucm_reduced_relation_type        0
% 11.81/2.00  --bmc1_ucm_relax_model                  4
% 11.81/2.00  --bmc1_ucm_full_tr_after_sat            true
% 11.81/2.00  --bmc1_ucm_expand_neg_assumptions       false
% 11.81/2.00  --bmc1_ucm_layered_model                none
% 11.81/2.00  --bmc1_ucm_max_lemma_size               10
% 11.81/2.00  
% 11.81/2.00  ------ AIG Options
% 11.81/2.00  
% 11.81/2.00  --aig_mode                              false
% 11.81/2.00  
% 11.81/2.00  ------ Instantiation Options
% 11.81/2.00  
% 11.81/2.00  --instantiation_flag                    true
% 11.81/2.00  --inst_sos_flag                         true
% 11.81/2.00  --inst_sos_phase                        true
% 11.81/2.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 11.81/2.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 11.81/2.00  --inst_lit_sel_side                     none
% 11.81/2.00  --inst_solver_per_active                1400
% 11.81/2.00  --inst_solver_calls_frac                1.
% 11.81/2.00  --inst_passive_queue_type               priority_queues
% 11.81/2.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 11.81/2.00  --inst_passive_queues_freq              [25;2]
% 11.81/2.00  --inst_dismatching                      true
% 11.81/2.00  --inst_eager_unprocessed_to_passive     true
% 11.81/2.00  --inst_prop_sim_given                   true
% 11.81/2.00  --inst_prop_sim_new                     false
% 11.81/2.00  --inst_subs_new                         false
% 11.81/2.00  --inst_eq_res_simp                      false
% 11.81/2.00  --inst_subs_given                       false
% 11.81/2.00  --inst_orphan_elimination               true
% 11.81/2.00  --inst_learning_loop_flag               true
% 11.81/2.00  --inst_learning_start                   3000
% 11.81/2.00  --inst_learning_factor                  2
% 11.81/2.00  --inst_start_prop_sim_after_learn       3
% 11.81/2.00  --inst_sel_renew                        solver
% 11.81/2.00  --inst_lit_activity_flag                true
% 11.81/2.00  --inst_restr_to_given                   false
% 11.81/2.00  --inst_activity_threshold               500
% 11.81/2.00  --inst_out_proof                        true
% 11.81/2.00  
% 11.81/2.00  ------ Resolution Options
% 11.81/2.00  
% 11.81/2.00  --resolution_flag                       false
% 11.81/2.00  --res_lit_sel                           adaptive
% 11.81/2.00  --res_lit_sel_side                      none
% 11.81/2.00  --res_ordering                          kbo
% 11.81/2.00  --res_to_prop_solver                    active
% 11.81/2.00  --res_prop_simpl_new                    false
% 11.81/2.00  --res_prop_simpl_given                  true
% 11.81/2.00  --res_passive_queue_type                priority_queues
% 11.81/2.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 11.81/2.00  --res_passive_queues_freq               [15;5]
% 11.81/2.00  --res_forward_subs                      full
% 11.81/2.00  --res_backward_subs                     full
% 11.81/2.00  --res_forward_subs_resolution           true
% 11.81/2.00  --res_backward_subs_resolution          true
% 11.81/2.00  --res_orphan_elimination                true
% 11.81/2.00  --res_time_limit                        2.
% 11.81/2.00  --res_out_proof                         true
% 11.81/2.00  
% 11.81/2.00  ------ Superposition Options
% 11.81/2.00  
% 11.81/2.00  --superposition_flag                    true
% 11.81/2.00  --sup_passive_queue_type                priority_queues
% 11.81/2.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 11.81/2.00  --sup_passive_queues_freq               [8;1;4]
% 11.81/2.00  --demod_completeness_check              fast
% 11.81/2.00  --demod_use_ground                      true
% 11.81/2.00  --sup_to_prop_solver                    passive
% 11.81/2.00  --sup_prop_simpl_new                    true
% 11.81/2.00  --sup_prop_simpl_given                  true
% 11.81/2.00  --sup_fun_splitting                     true
% 11.81/2.00  --sup_smt_interval                      50000
% 11.81/2.00  
% 11.81/2.00  ------ Superposition Simplification Setup
% 11.81/2.00  
% 11.81/2.00  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 11.81/2.00  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 11.81/2.00  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 11.81/2.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 11.81/2.00  --sup_full_triv                         [TrivRules;PropSubs]
% 11.81/2.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 11.81/2.00  --sup_full_bw                           [BwDemod;BwSubsumption]
% 11.81/2.00  --sup_immed_triv                        [TrivRules]
% 11.81/2.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 11.81/2.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 11.81/2.00  --sup_immed_bw_main                     []
% 11.81/2.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 11.81/2.00  --sup_input_triv                        [Unflattening;TrivRules]
% 11.81/2.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 11.81/2.00  --sup_input_bw                          []
% 11.81/2.00  
% 11.81/2.00  ------ Combination Options
% 11.81/2.00  
% 11.81/2.00  --comb_res_mult                         3
% 11.81/2.00  --comb_sup_mult                         2
% 11.81/2.00  --comb_inst_mult                        10
% 11.81/2.00  
% 11.81/2.00  ------ Debug Options
% 11.81/2.00  
% 11.81/2.00  --dbg_backtrace                         false
% 11.81/2.00  --dbg_dump_prop_clauses                 false
% 11.81/2.00  --dbg_dump_prop_clauses_file            -
% 11.81/2.00  --dbg_out_stat                          false
% 11.81/2.00  
% 11.81/2.00  
% 11.81/2.00  
% 11.81/2.00  
% 11.81/2.00  ------ Proving...
% 11.81/2.00  
% 11.81/2.00  
% 11.81/2.00  % SZS status Theorem for theBenchmark.p
% 11.81/2.00  
% 11.81/2.00  % SZS output start CNFRefutation for theBenchmark.p
% 11.81/2.00  
% 11.81/2.00  fof(f1,axiom,(
% 11.81/2.00    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 11.81/2.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.81/2.00  
% 11.81/2.00  fof(f20,plain,(
% 11.81/2.00    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 11.81/2.00    inference(ennf_transformation,[],[f1])).
% 11.81/2.00  
% 11.81/2.00  fof(f36,plain,(
% 11.81/2.00    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 11.81/2.00    inference(nnf_transformation,[],[f20])).
% 11.81/2.00  
% 11.81/2.00  fof(f37,plain,(
% 11.81/2.00    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 11.81/2.00    inference(rectify,[],[f36])).
% 11.81/2.00  
% 11.81/2.00  fof(f38,plain,(
% 11.81/2.00    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 11.81/2.00    introduced(choice_axiom,[])).
% 11.81/2.00  
% 11.81/2.00  fof(f39,plain,(
% 11.81/2.00    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 11.81/2.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f37,f38])).
% 11.81/2.00  
% 11.81/2.00  fof(f70,plain,(
% 11.81/2.00    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK0(X0,X1),X0)) )),
% 11.81/2.00    inference(cnf_transformation,[],[f39])).
% 11.81/2.00  
% 11.81/2.00  fof(f7,axiom,(
% 11.81/2.00    ! [X0] : ? [X1] : ! [X2] : (r2_hidden(X2,X1) <=> (v3_ordinal1(X2) & r2_hidden(X2,X0)))),
% 11.81/2.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.81/2.00  
% 11.81/2.00  fof(f50,plain,(
% 11.81/2.00    ! [X0] : ? [X1] : ! [X2] : ((r2_hidden(X2,X1) | (~v3_ordinal1(X2) | ~r2_hidden(X2,X0))) & ((v3_ordinal1(X2) & r2_hidden(X2,X0)) | ~r2_hidden(X2,X1)))),
% 11.81/2.00    inference(nnf_transformation,[],[f7])).
% 11.81/2.00  
% 11.81/2.00  fof(f51,plain,(
% 11.81/2.00    ! [X0] : ? [X1] : ! [X2] : ((r2_hidden(X2,X1) | ~v3_ordinal1(X2) | ~r2_hidden(X2,X0)) & ((v3_ordinal1(X2) & r2_hidden(X2,X0)) | ~r2_hidden(X2,X1)))),
% 11.81/2.00    inference(flattening,[],[f50])).
% 11.81/2.00  
% 11.81/2.00  fof(f52,plain,(
% 11.81/2.00    ! [X0] : (? [X1] : ! [X2] : ((r2_hidden(X2,X1) | ~v3_ordinal1(X2) | ~r2_hidden(X2,X0)) & ((v3_ordinal1(X2) & r2_hidden(X2,X0)) | ~r2_hidden(X2,X1))) => ! [X2] : ((r2_hidden(X2,sK4(X0)) | ~v3_ordinal1(X2) | ~r2_hidden(X2,X0)) & ((v3_ordinal1(X2) & r2_hidden(X2,X0)) | ~r2_hidden(X2,sK4(X0)))))),
% 11.81/2.00    introduced(choice_axiom,[])).
% 11.81/2.00  
% 11.81/2.00  fof(f53,plain,(
% 11.81/2.00    ! [X0] : ! [X2] : ((r2_hidden(X2,sK4(X0)) | ~v3_ordinal1(X2) | ~r2_hidden(X2,X0)) & ((v3_ordinal1(X2) & r2_hidden(X2,X0)) | ~r2_hidden(X2,sK4(X0))))),
% 11.81/2.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f51,f52])).
% 11.81/2.00  
% 11.81/2.00  fof(f86,plain,(
% 11.81/2.00    ( ! [X2,X0] : (r2_hidden(X2,X0) | ~r2_hidden(X2,sK4(X0))) )),
% 11.81/2.00    inference(cnf_transformation,[],[f53])).
% 11.81/2.00  
% 11.81/2.00  fof(f18,conjecture,(
% 11.81/2.00    ! [X0] : (v3_ordinal1(X0) => (v4_ordinal1(X0) <=> ! [X1] : (v3_ordinal1(X1) => (r2_hidden(X1,X0) => r2_hidden(k1_ordinal1(X1),X0)))))),
% 11.81/2.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.81/2.00  
% 11.81/2.00  fof(f19,negated_conjecture,(
% 11.81/2.00    ~! [X0] : (v3_ordinal1(X0) => (v4_ordinal1(X0) <=> ! [X1] : (v3_ordinal1(X1) => (r2_hidden(X1,X0) => r2_hidden(k1_ordinal1(X1),X0)))))),
% 11.81/2.00    inference(negated_conjecture,[],[f18])).
% 11.81/2.00  
% 11.81/2.00  fof(f34,plain,(
% 11.81/2.00    ? [X0] : ((v4_ordinal1(X0) <~> ! [X1] : ((r2_hidden(k1_ordinal1(X1),X0) | ~r2_hidden(X1,X0)) | ~v3_ordinal1(X1))) & v3_ordinal1(X0))),
% 11.81/2.00    inference(ennf_transformation,[],[f19])).
% 11.81/2.00  
% 11.81/2.00  fof(f35,plain,(
% 11.81/2.00    ? [X0] : ((v4_ordinal1(X0) <~> ! [X1] : (r2_hidden(k1_ordinal1(X1),X0) | ~r2_hidden(X1,X0) | ~v3_ordinal1(X1))) & v3_ordinal1(X0))),
% 11.81/2.00    inference(flattening,[],[f34])).
% 11.81/2.00  
% 11.81/2.00  fof(f63,plain,(
% 11.81/2.00    ? [X0] : (((? [X1] : (~r2_hidden(k1_ordinal1(X1),X0) & r2_hidden(X1,X0) & v3_ordinal1(X1)) | ~v4_ordinal1(X0)) & (! [X1] : (r2_hidden(k1_ordinal1(X1),X0) | ~r2_hidden(X1,X0) | ~v3_ordinal1(X1)) | v4_ordinal1(X0))) & v3_ordinal1(X0))),
% 11.81/2.00    inference(nnf_transformation,[],[f35])).
% 11.81/2.00  
% 11.81/2.00  fof(f64,plain,(
% 11.81/2.00    ? [X0] : ((? [X1] : (~r2_hidden(k1_ordinal1(X1),X0) & r2_hidden(X1,X0) & v3_ordinal1(X1)) | ~v4_ordinal1(X0)) & (! [X1] : (r2_hidden(k1_ordinal1(X1),X0) | ~r2_hidden(X1,X0) | ~v3_ordinal1(X1)) | v4_ordinal1(X0)) & v3_ordinal1(X0))),
% 11.81/2.00    inference(flattening,[],[f63])).
% 11.81/2.00  
% 11.81/2.00  fof(f65,plain,(
% 11.81/2.00    ? [X0] : ((? [X1] : (~r2_hidden(k1_ordinal1(X1),X0) & r2_hidden(X1,X0) & v3_ordinal1(X1)) | ~v4_ordinal1(X0)) & (! [X2] : (r2_hidden(k1_ordinal1(X2),X0) | ~r2_hidden(X2,X0) | ~v3_ordinal1(X2)) | v4_ordinal1(X0)) & v3_ordinal1(X0))),
% 11.81/2.00    inference(rectify,[],[f64])).
% 11.81/2.00  
% 11.81/2.00  fof(f67,plain,(
% 11.81/2.00    ( ! [X0] : (? [X1] : (~r2_hidden(k1_ordinal1(X1),X0) & r2_hidden(X1,X0) & v3_ordinal1(X1)) => (~r2_hidden(k1_ordinal1(sK9),X0) & r2_hidden(sK9,X0) & v3_ordinal1(sK9))) )),
% 11.81/2.00    introduced(choice_axiom,[])).
% 11.81/2.00  
% 11.81/2.00  fof(f66,plain,(
% 11.81/2.00    ? [X0] : ((? [X1] : (~r2_hidden(k1_ordinal1(X1),X0) & r2_hidden(X1,X0) & v3_ordinal1(X1)) | ~v4_ordinal1(X0)) & (! [X2] : (r2_hidden(k1_ordinal1(X2),X0) | ~r2_hidden(X2,X0) | ~v3_ordinal1(X2)) | v4_ordinal1(X0)) & v3_ordinal1(X0)) => ((? [X1] : (~r2_hidden(k1_ordinal1(X1),sK8) & r2_hidden(X1,sK8) & v3_ordinal1(X1)) | ~v4_ordinal1(sK8)) & (! [X2] : (r2_hidden(k1_ordinal1(X2),sK8) | ~r2_hidden(X2,sK8) | ~v3_ordinal1(X2)) | v4_ordinal1(sK8)) & v3_ordinal1(sK8))),
% 11.81/2.00    introduced(choice_axiom,[])).
% 11.81/2.00  
% 11.81/2.00  fof(f68,plain,(
% 11.81/2.00    ((~r2_hidden(k1_ordinal1(sK9),sK8) & r2_hidden(sK9,sK8) & v3_ordinal1(sK9)) | ~v4_ordinal1(sK8)) & (! [X2] : (r2_hidden(k1_ordinal1(X2),sK8) | ~r2_hidden(X2,sK8) | ~v3_ordinal1(X2)) | v4_ordinal1(sK8)) & v3_ordinal1(sK8)),
% 11.81/2.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8,sK9])],[f65,f67,f66])).
% 11.81/2.00  
% 11.81/2.00  fof(f107,plain,(
% 11.81/2.00    ( ! [X2] : (r2_hidden(k1_ordinal1(X2),sK8) | ~r2_hidden(X2,sK8) | ~v3_ordinal1(X2) | v4_ordinal1(sK8)) )),
% 11.81/2.00    inference(cnf_transformation,[],[f68])).
% 11.81/2.00  
% 11.81/2.00  fof(f4,axiom,(
% 11.81/2.00    ! [X0] : k1_ordinal1(X0) = k2_xboole_0(X0,k1_tarski(X0))),
% 11.81/2.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.81/2.00  
% 11.81/2.00  fof(f81,plain,(
% 11.81/2.00    ( ! [X0] : (k1_ordinal1(X0) = k2_xboole_0(X0,k1_tarski(X0))) )),
% 11.81/2.00    inference(cnf_transformation,[],[f4])).
% 11.81/2.00  
% 11.81/2.00  fof(f119,plain,(
% 11.81/2.00    ( ! [X2] : (r2_hidden(k2_xboole_0(X2,k1_tarski(X2)),sK8) | ~r2_hidden(X2,sK8) | ~v3_ordinal1(X2) | v4_ordinal1(sK8)) )),
% 11.81/2.00    inference(definition_unfolding,[],[f107,f81])).
% 11.81/2.00  
% 11.81/2.00  fof(f3,axiom,(
% 11.81/2.00    ! [X0,X1] : (k3_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (r2_hidden(X3,X0) & r2_hidden(X2,X3))))),
% 11.81/2.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.81/2.00  
% 11.81/2.00  fof(f42,plain,(
% 11.81/2.00    ! [X0,X1] : ((k3_tarski(X0) = X1 | ? [X2] : ((! [X3] : (~r2_hidden(X3,X0) | ~r2_hidden(X2,X3)) | ~r2_hidden(X2,X1)) & (? [X3] : (r2_hidden(X3,X0) & r2_hidden(X2,X3)) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ! [X3] : (~r2_hidden(X3,X0) | ~r2_hidden(X2,X3))) & (? [X3] : (r2_hidden(X3,X0) & r2_hidden(X2,X3)) | ~r2_hidden(X2,X1))) | k3_tarski(X0) != X1))),
% 11.81/2.00    inference(nnf_transformation,[],[f3])).
% 11.81/2.00  
% 11.81/2.00  fof(f43,plain,(
% 11.81/2.00    ! [X0,X1] : ((k3_tarski(X0) = X1 | ? [X2] : ((! [X3] : (~r2_hidden(X3,X0) | ~r2_hidden(X2,X3)) | ~r2_hidden(X2,X1)) & (? [X4] : (r2_hidden(X4,X0) & r2_hidden(X2,X4)) | r2_hidden(X2,X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : (~r2_hidden(X6,X0) | ~r2_hidden(X5,X6))) & (? [X7] : (r2_hidden(X7,X0) & r2_hidden(X5,X7)) | ~r2_hidden(X5,X1))) | k3_tarski(X0) != X1))),
% 11.81/2.00    inference(rectify,[],[f42])).
% 11.81/2.00  
% 11.81/2.00  fof(f46,plain,(
% 11.81/2.00    ! [X5,X0] : (? [X7] : (r2_hidden(X7,X0) & r2_hidden(X5,X7)) => (r2_hidden(sK3(X0,X5),X0) & r2_hidden(X5,sK3(X0,X5))))),
% 11.81/2.00    introduced(choice_axiom,[])).
% 11.81/2.00  
% 11.81/2.00  fof(f45,plain,(
% 11.81/2.00    ( ! [X2] : (! [X1,X0] : (? [X4] : (r2_hidden(X4,X0) & r2_hidden(X2,X4)) => (r2_hidden(sK2(X0,X1),X0) & r2_hidden(X2,sK2(X0,X1))))) )),
% 11.81/2.00    introduced(choice_axiom,[])).
% 11.81/2.00  
% 11.81/2.00  fof(f44,plain,(
% 11.81/2.00    ! [X1,X0] : (? [X2] : ((! [X3] : (~r2_hidden(X3,X0) | ~r2_hidden(X2,X3)) | ~r2_hidden(X2,X1)) & (? [X4] : (r2_hidden(X4,X0) & r2_hidden(X2,X4)) | r2_hidden(X2,X1))) => ((! [X3] : (~r2_hidden(X3,X0) | ~r2_hidden(sK1(X0,X1),X3)) | ~r2_hidden(sK1(X0,X1),X1)) & (? [X4] : (r2_hidden(X4,X0) & r2_hidden(sK1(X0,X1),X4)) | r2_hidden(sK1(X0,X1),X1))))),
% 11.81/2.00    introduced(choice_axiom,[])).
% 11.81/2.00  
% 11.81/2.00  fof(f47,plain,(
% 11.81/2.00    ! [X0,X1] : ((k3_tarski(X0) = X1 | ((! [X3] : (~r2_hidden(X3,X0) | ~r2_hidden(sK1(X0,X1),X3)) | ~r2_hidden(sK1(X0,X1),X1)) & ((r2_hidden(sK2(X0,X1),X0) & r2_hidden(sK1(X0,X1),sK2(X0,X1))) | r2_hidden(sK1(X0,X1),X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : (~r2_hidden(X6,X0) | ~r2_hidden(X5,X6))) & ((r2_hidden(sK3(X0,X5),X0) & r2_hidden(X5,sK3(X0,X5))) | ~r2_hidden(X5,X1))) | k3_tarski(X0) != X1))),
% 11.81/2.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f43,f46,f45,f44])).
% 11.81/2.00  
% 11.81/2.00  fof(f77,plain,(
% 11.81/2.00    ( ! [X6,X0,X5,X1] : (r2_hidden(X5,X1) | ~r2_hidden(X6,X0) | ~r2_hidden(X5,X6) | k3_tarski(X0) != X1) )),
% 11.81/2.00    inference(cnf_transformation,[],[f47])).
% 11.81/2.00  
% 11.81/2.00  fof(f122,plain,(
% 11.81/2.00    ( ! [X6,X0,X5] : (r2_hidden(X5,k3_tarski(X0)) | ~r2_hidden(X6,X0) | ~r2_hidden(X5,X6)) )),
% 11.81/2.00    inference(equality_resolution,[],[f77])).
% 11.81/2.00  
% 11.81/2.00  fof(f106,plain,(
% 11.81/2.00    v3_ordinal1(sK8)),
% 11.81/2.00    inference(cnf_transformation,[],[f68])).
% 11.81/2.00  
% 11.81/2.00  fof(f5,axiom,(
% 11.81/2.00    ! [X0] : (v4_ordinal1(X0) <=> k3_tarski(X0) = X0)),
% 11.81/2.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.81/2.00  
% 11.81/2.00  fof(f48,plain,(
% 11.81/2.00    ! [X0] : ((v4_ordinal1(X0) | k3_tarski(X0) != X0) & (k3_tarski(X0) = X0 | ~v4_ordinal1(X0)))),
% 11.81/2.00    inference(nnf_transformation,[],[f5])).
% 11.81/2.00  
% 11.81/2.00  fof(f83,plain,(
% 11.81/2.00    ( ! [X0] : (v4_ordinal1(X0) | k3_tarski(X0) != X0) )),
% 11.81/2.00    inference(cnf_transformation,[],[f48])).
% 11.81/2.00  
% 11.81/2.00  fof(f76,plain,(
% 11.81/2.00    ( ! [X0,X5,X1] : (r2_hidden(sK3(X0,X5),X0) | ~r2_hidden(X5,X1) | k3_tarski(X0) != X1) )),
% 11.81/2.00    inference(cnf_transformation,[],[f47])).
% 11.81/2.00  
% 11.81/2.00  fof(f123,plain,(
% 11.81/2.00    ( ! [X0,X5] : (r2_hidden(sK3(X0,X5),X0) | ~r2_hidden(X5,k3_tarski(X0))) )),
% 11.81/2.00    inference(equality_resolution,[],[f76])).
% 11.81/2.00  
% 11.81/2.00  fof(f11,axiom,(
% 11.81/2.00    ! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => ~(~r2_hidden(X1,X0) & X0 != X1 & ~r2_hidden(X0,X1))))),
% 11.81/2.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.81/2.00  
% 11.81/2.00  fof(f25,plain,(
% 11.81/2.00    ! [X0] : (! [X1] : ((r2_hidden(X1,X0) | X0 = X1 | r2_hidden(X0,X1)) | ~v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 11.81/2.00    inference(ennf_transformation,[],[f11])).
% 11.81/2.00  
% 11.81/2.00  fof(f26,plain,(
% 11.81/2.00    ! [X0] : (! [X1] : (r2_hidden(X1,X0) | X0 = X1 | r2_hidden(X0,X1) | ~v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 11.81/2.00    inference(flattening,[],[f25])).
% 11.81/2.00  
% 11.81/2.00  fof(f94,plain,(
% 11.81/2.00    ( ! [X0,X1] : (r2_hidden(X1,X0) | X0 = X1 | r2_hidden(X0,X1) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0)) )),
% 11.81/2.00    inference(cnf_transformation,[],[f26])).
% 11.81/2.00  
% 11.81/2.00  fof(f13,axiom,(
% 11.81/2.00    ! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => (r2_hidden(X0,k1_ordinal1(X1)) <=> r1_ordinal1(X0,X1))))),
% 11.81/2.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.81/2.00  
% 11.81/2.00  fof(f28,plain,(
% 11.81/2.00    ! [X0] : (! [X1] : ((r2_hidden(X0,k1_ordinal1(X1)) <=> r1_ordinal1(X0,X1)) | ~v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 11.81/2.00    inference(ennf_transformation,[],[f13])).
% 11.81/2.00  
% 11.81/2.00  fof(f56,plain,(
% 11.81/2.00    ! [X0] : (! [X1] : (((r2_hidden(X0,k1_ordinal1(X1)) | ~r1_ordinal1(X0,X1)) & (r1_ordinal1(X0,X1) | ~r2_hidden(X0,k1_ordinal1(X1)))) | ~v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 11.81/2.00    inference(nnf_transformation,[],[f28])).
% 11.81/2.00  
% 11.81/2.00  fof(f96,plain,(
% 11.81/2.00    ( ! [X0,X1] : (r1_ordinal1(X0,X1) | ~r2_hidden(X0,k1_ordinal1(X1)) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0)) )),
% 11.81/2.00    inference(cnf_transformation,[],[f56])).
% 11.81/2.00  
% 11.81/2.00  fof(f117,plain,(
% 11.81/2.00    ( ! [X0,X1] : (r1_ordinal1(X0,X1) | ~r2_hidden(X0,k2_xboole_0(X1,k1_tarski(X1))) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0)) )),
% 11.81/2.00    inference(definition_unfolding,[],[f96,f81])).
% 11.81/2.00  
% 11.81/2.00  fof(f6,axiom,(
% 11.81/2.00    ! [X0,X1] : ((v3_ordinal1(X1) & v3_ordinal1(X0)) => (r1_ordinal1(X0,X1) <=> r1_tarski(X0,X1)))),
% 11.81/2.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.81/2.00  
% 11.81/2.00  fof(f21,plain,(
% 11.81/2.00    ! [X0,X1] : ((r1_ordinal1(X0,X1) <=> r1_tarski(X0,X1)) | (~v3_ordinal1(X1) | ~v3_ordinal1(X0)))),
% 11.81/2.00    inference(ennf_transformation,[],[f6])).
% 11.81/2.00  
% 11.81/2.00  fof(f22,plain,(
% 11.81/2.00    ! [X0,X1] : ((r1_ordinal1(X0,X1) <=> r1_tarski(X0,X1)) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0))),
% 11.81/2.00    inference(flattening,[],[f21])).
% 11.81/2.00  
% 11.81/2.00  fof(f49,plain,(
% 11.81/2.00    ! [X0,X1] : (((r1_ordinal1(X0,X1) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~r1_ordinal1(X0,X1))) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0))),
% 11.81/2.00    inference(nnf_transformation,[],[f22])).
% 11.81/2.00  
% 11.81/2.00  fof(f84,plain,(
% 11.81/2.00    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r1_ordinal1(X0,X1) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0)) )),
% 11.81/2.00    inference(cnf_transformation,[],[f49])).
% 11.81/2.00  
% 11.81/2.00  fof(f75,plain,(
% 11.81/2.00    ( ! [X0,X5,X1] : (r2_hidden(X5,sK3(X0,X5)) | ~r2_hidden(X5,X1) | k3_tarski(X0) != X1) )),
% 11.81/2.00    inference(cnf_transformation,[],[f47])).
% 11.81/2.00  
% 11.81/2.00  fof(f124,plain,(
% 11.81/2.00    ( ! [X0,X5] : (r2_hidden(X5,sK3(X0,X5)) | ~r2_hidden(X5,k3_tarski(X0))) )),
% 11.81/2.00    inference(equality_resolution,[],[f75])).
% 11.81/2.00  
% 11.81/2.00  fof(f17,axiom,(
% 11.81/2.00    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 11.81/2.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.81/2.00  
% 11.81/2.00  fof(f33,plain,(
% 11.81/2.00    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 11.81/2.00    inference(ennf_transformation,[],[f17])).
% 11.81/2.00  
% 11.81/2.00  fof(f105,plain,(
% 11.81/2.00    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1)) )),
% 11.81/2.00    inference(cnf_transformation,[],[f33])).
% 11.81/2.00  
% 11.81/2.00  fof(f10,axiom,(
% 11.81/2.00    ! [X0,X1] : (v3_ordinal1(X1) => (r2_hidden(X0,X1) => v3_ordinal1(X0)))),
% 11.81/2.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.81/2.00  
% 11.81/2.00  fof(f23,plain,(
% 11.81/2.00    ! [X0,X1] : ((v3_ordinal1(X0) | ~r2_hidden(X0,X1)) | ~v3_ordinal1(X1))),
% 11.81/2.00    inference(ennf_transformation,[],[f10])).
% 11.81/2.00  
% 11.81/2.00  fof(f24,plain,(
% 11.81/2.00    ! [X0,X1] : (v3_ordinal1(X0) | ~r2_hidden(X0,X1) | ~v3_ordinal1(X1))),
% 11.81/2.00    inference(flattening,[],[f23])).
% 11.81/2.00  
% 11.81/2.00  fof(f93,plain,(
% 11.81/2.00    ( ! [X0,X1] : (v3_ordinal1(X0) | ~r2_hidden(X0,X1) | ~v3_ordinal1(X1)) )),
% 11.81/2.00    inference(cnf_transformation,[],[f24])).
% 11.81/2.00  
% 11.81/2.00  fof(f9,axiom,(
% 11.81/2.00    ! [X0,X1] : (r2_hidden(X0,k1_ordinal1(X1)) <=> (X0 = X1 | r2_hidden(X0,X1)))),
% 11.81/2.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.81/2.00  
% 11.81/2.00  fof(f54,plain,(
% 11.81/2.00    ! [X0,X1] : ((r2_hidden(X0,k1_ordinal1(X1)) | (X0 != X1 & ~r2_hidden(X0,X1))) & ((X0 = X1 | r2_hidden(X0,X1)) | ~r2_hidden(X0,k1_ordinal1(X1))))),
% 11.81/2.00    inference(nnf_transformation,[],[f9])).
% 11.81/2.00  
% 11.81/2.00  fof(f55,plain,(
% 11.81/2.00    ! [X0,X1] : ((r2_hidden(X0,k1_ordinal1(X1)) | (X0 != X1 & ~r2_hidden(X0,X1))) & (X0 = X1 | r2_hidden(X0,X1) | ~r2_hidden(X0,k1_ordinal1(X1))))),
% 11.81/2.00    inference(flattening,[],[f54])).
% 11.81/2.00  
% 11.81/2.00  fof(f92,plain,(
% 11.81/2.00    ( ! [X0,X1] : (r2_hidden(X0,k1_ordinal1(X1)) | X0 != X1) )),
% 11.81/2.00    inference(cnf_transformation,[],[f55])).
% 11.81/2.00  
% 11.81/2.00  fof(f112,plain,(
% 11.81/2.00    ( ! [X0,X1] : (r2_hidden(X0,k2_xboole_0(X1,k1_tarski(X1))) | X0 != X1) )),
% 11.81/2.00    inference(definition_unfolding,[],[f92,f81])).
% 11.81/2.00  
% 11.81/2.00  fof(f125,plain,(
% 11.81/2.00    ( ! [X1] : (r2_hidden(X1,k2_xboole_0(X1,k1_tarski(X1)))) )),
% 11.81/2.00    inference(equality_resolution,[],[f112])).
% 11.81/2.00  
% 11.81/2.00  fof(f2,axiom,(
% 11.81/2.00    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 11.81/2.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.81/2.00  
% 11.81/2.00  fof(f40,plain,(
% 11.81/2.00    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 11.81/2.00    inference(nnf_transformation,[],[f2])).
% 11.81/2.00  
% 11.81/2.00  fof(f41,plain,(
% 11.81/2.00    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 11.81/2.00    inference(flattening,[],[f40])).
% 11.81/2.00  
% 11.81/2.00  fof(f73,plain,(
% 11.81/2.00    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 11.81/2.00    inference(cnf_transformation,[],[f41])).
% 11.81/2.00  
% 11.81/2.00  fof(f120,plain,(
% 11.81/2.00    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 11.81/2.00    inference(equality_resolution,[],[f73])).
% 11.81/2.00  
% 11.81/2.00  fof(f91,plain,(
% 11.81/2.00    ( ! [X0,X1] : (r2_hidden(X0,k1_ordinal1(X1)) | ~r2_hidden(X0,X1)) )),
% 11.81/2.00    inference(cnf_transformation,[],[f55])).
% 11.81/2.00  
% 11.81/2.00  fof(f113,plain,(
% 11.81/2.00    ( ! [X0,X1] : (r2_hidden(X0,k2_xboole_0(X1,k1_tarski(X1))) | ~r2_hidden(X0,X1)) )),
% 11.81/2.00    inference(definition_unfolding,[],[f91,f81])).
% 11.81/2.00  
% 11.81/2.00  fof(f12,axiom,(
% 11.81/2.00    ! [X0] : (v3_ordinal1(X0) => v3_ordinal1(k1_ordinal1(X0)))),
% 11.81/2.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.81/2.00  
% 11.81/2.00  fof(f27,plain,(
% 11.81/2.00    ! [X0] : (v3_ordinal1(k1_ordinal1(X0)) | ~v3_ordinal1(X0))),
% 11.81/2.00    inference(ennf_transformation,[],[f12])).
% 11.81/2.00  
% 11.81/2.00  fof(f95,plain,(
% 11.81/2.00    ( ! [X0] : (v3_ordinal1(k1_ordinal1(X0)) | ~v3_ordinal1(X0)) )),
% 11.81/2.00    inference(cnf_transformation,[],[f27])).
% 11.81/2.00  
% 11.81/2.00  fof(f115,plain,(
% 11.81/2.00    ( ! [X0] : (v3_ordinal1(k2_xboole_0(X0,k1_tarski(X0))) | ~v3_ordinal1(X0)) )),
% 11.81/2.00    inference(definition_unfolding,[],[f95,f81])).
% 11.81/2.00  
% 11.81/2.00  fof(f14,axiom,(
% 11.81/2.00    ! [X0] : (! [X1] : (r2_hidden(X1,X0) => v3_ordinal1(X1)) => v3_ordinal1(k3_tarski(X0)))),
% 11.81/2.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.81/2.00  
% 11.81/2.00  fof(f29,plain,(
% 11.81/2.00    ! [X0] : (v3_ordinal1(k3_tarski(X0)) | ? [X1] : (~v3_ordinal1(X1) & r2_hidden(X1,X0)))),
% 11.81/2.00    inference(ennf_transformation,[],[f14])).
% 11.81/2.00  
% 11.81/2.00  fof(f57,plain,(
% 11.81/2.00    ! [X0] : (? [X1] : (~v3_ordinal1(X1) & r2_hidden(X1,X0)) => (~v3_ordinal1(sK5(X0)) & r2_hidden(sK5(X0),X0)))),
% 11.81/2.00    introduced(choice_axiom,[])).
% 11.81/2.00  
% 11.81/2.00  fof(f58,plain,(
% 11.81/2.00    ! [X0] : (v3_ordinal1(k3_tarski(X0)) | (~v3_ordinal1(sK5(X0)) & r2_hidden(sK5(X0),X0)))),
% 11.81/2.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f29,f57])).
% 11.81/2.00  
% 11.81/2.00  fof(f98,plain,(
% 11.81/2.00    ( ! [X0] : (v3_ordinal1(k3_tarski(X0)) | r2_hidden(sK5(X0),X0)) )),
% 11.81/2.00    inference(cnf_transformation,[],[f58])).
% 11.81/2.00  
% 11.81/2.00  fof(f99,plain,(
% 11.81/2.00    ( ! [X0] : (v3_ordinal1(k3_tarski(X0)) | ~v3_ordinal1(sK5(X0))) )),
% 11.81/2.00    inference(cnf_transformation,[],[f58])).
% 11.81/2.00  
% 11.81/2.00  fof(f108,plain,(
% 11.81/2.00    v3_ordinal1(sK9) | ~v4_ordinal1(sK8)),
% 11.81/2.00    inference(cnf_transformation,[],[f68])).
% 11.81/2.00  
% 11.81/2.00  fof(f97,plain,(
% 11.81/2.00    ( ! [X0,X1] : (r2_hidden(X0,k1_ordinal1(X1)) | ~r1_ordinal1(X0,X1) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0)) )),
% 11.81/2.00    inference(cnf_transformation,[],[f56])).
% 11.81/2.00  
% 11.81/2.00  fof(f116,plain,(
% 11.81/2.00    ( ! [X0,X1] : (r2_hidden(X0,k2_xboole_0(X1,k1_tarski(X1))) | ~r1_ordinal1(X0,X1) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0)) )),
% 11.81/2.00    inference(definition_unfolding,[],[f97,f81])).
% 11.81/2.00  
% 11.81/2.00  fof(f16,axiom,(
% 11.81/2.00    ! [X0] : ? [X1] : (! [X2] : (v3_ordinal1(X2) => (~r2_hidden(X2,X0) => r1_ordinal1(X1,X2))) & ~r2_hidden(X1,X0) & v3_ordinal1(X1))),
% 11.81/2.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.81/2.00  
% 11.81/2.00  fof(f31,plain,(
% 11.81/2.00    ! [X0] : ? [X1] : (! [X2] : ((r1_ordinal1(X1,X2) | r2_hidden(X2,X0)) | ~v3_ordinal1(X2)) & ~r2_hidden(X1,X0) & v3_ordinal1(X1))),
% 11.81/2.00    inference(ennf_transformation,[],[f16])).
% 11.81/2.00  
% 11.81/2.00  fof(f32,plain,(
% 11.81/2.00    ! [X0] : ? [X1] : (! [X2] : (r1_ordinal1(X1,X2) | r2_hidden(X2,X0) | ~v3_ordinal1(X2)) & ~r2_hidden(X1,X0) & v3_ordinal1(X1))),
% 11.81/2.00    inference(flattening,[],[f31])).
% 11.81/2.00  
% 11.81/2.00  fof(f61,plain,(
% 11.81/2.00    ! [X0] : (? [X1] : (! [X2] : (r1_ordinal1(X1,X2) | r2_hidden(X2,X0) | ~v3_ordinal1(X2)) & ~r2_hidden(X1,X0) & v3_ordinal1(X1)) => (! [X2] : (r1_ordinal1(sK7(X0),X2) | r2_hidden(X2,X0) | ~v3_ordinal1(X2)) & ~r2_hidden(sK7(X0),X0) & v3_ordinal1(sK7(X0))))),
% 11.81/2.00    introduced(choice_axiom,[])).
% 11.81/2.00  
% 11.81/2.00  fof(f62,plain,(
% 11.81/2.00    ! [X0] : (! [X2] : (r1_ordinal1(sK7(X0),X2) | r2_hidden(X2,X0) | ~v3_ordinal1(X2)) & ~r2_hidden(sK7(X0),X0) & v3_ordinal1(sK7(X0)))),
% 11.81/2.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f32,f61])).
% 11.81/2.00  
% 11.81/2.00  fof(f104,plain,(
% 11.81/2.00    ( ! [X2,X0] : (r1_ordinal1(sK7(X0),X2) | r2_hidden(X2,X0) | ~v3_ordinal1(X2)) )),
% 11.81/2.00    inference(cnf_transformation,[],[f62])).
% 11.81/2.00  
% 11.81/2.00  fof(f102,plain,(
% 11.81/2.00    ( ! [X0] : (v3_ordinal1(sK7(X0))) )),
% 11.81/2.00    inference(cnf_transformation,[],[f62])).
% 11.81/2.00  
% 11.81/2.00  fof(f90,plain,(
% 11.81/2.00    ( ! [X0,X1] : (X0 = X1 | r2_hidden(X0,X1) | ~r2_hidden(X0,k1_ordinal1(X1))) )),
% 11.81/2.00    inference(cnf_transformation,[],[f55])).
% 11.81/2.00  
% 11.81/2.00  fof(f114,plain,(
% 11.81/2.00    ( ! [X0,X1] : (X0 = X1 | r2_hidden(X0,X1) | ~r2_hidden(X0,k2_xboole_0(X1,k1_tarski(X1)))) )),
% 11.81/2.00    inference(definition_unfolding,[],[f90,f81])).
% 11.81/2.00  
% 11.81/2.00  fof(f103,plain,(
% 11.81/2.00    ( ! [X0] : (~r2_hidden(sK7(X0),X0)) )),
% 11.81/2.00    inference(cnf_transformation,[],[f62])).
% 11.81/2.00  
% 11.81/2.00  fof(f71,plain,(
% 11.81/2.00    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r2_hidden(sK0(X0,X1),X1)) )),
% 11.81/2.00    inference(cnf_transformation,[],[f39])).
% 11.81/2.00  
% 11.81/2.00  fof(f110,plain,(
% 11.81/2.00    ~r2_hidden(k1_ordinal1(sK9),sK8) | ~v4_ordinal1(sK8)),
% 11.81/2.00    inference(cnf_transformation,[],[f68])).
% 11.81/2.00  
% 11.81/2.00  fof(f118,plain,(
% 11.81/2.00    ~r2_hidden(k2_xboole_0(sK9,k1_tarski(sK9)),sK8) | ~v4_ordinal1(sK8)),
% 11.81/2.00    inference(definition_unfolding,[],[f110,f81])).
% 11.81/2.00  
% 11.81/2.00  fof(f109,plain,(
% 11.81/2.00    r2_hidden(sK9,sK8) | ~v4_ordinal1(sK8)),
% 11.81/2.00    inference(cnf_transformation,[],[f68])).
% 11.81/2.00  
% 11.81/2.00  fof(f69,plain,(
% 11.81/2.00    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,X1)) )),
% 11.81/2.00    inference(cnf_transformation,[],[f39])).
% 11.81/2.00  
% 11.81/2.00  fof(f82,plain,(
% 11.81/2.00    ( ! [X0] : (k3_tarski(X0) = X0 | ~v4_ordinal1(X0)) )),
% 11.81/2.00    inference(cnf_transformation,[],[f48])).
% 11.81/2.00  
% 11.81/2.00  cnf(c_1,plain,
% 11.81/2.00      ( r2_hidden(sK0(X0,X1),X0) | r1_tarski(X0,X1) ),
% 11.81/2.00      inference(cnf_transformation,[],[f70]) ).
% 11.81/2.00  
% 11.81/2.00  cnf(c_1927,plain,
% 11.81/2.00      ( r2_hidden(sK0(X0,X1),X0) = iProver_top
% 11.81/2.00      | r1_tarski(X0,X1) = iProver_top ),
% 11.81/2.00      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 11.81/2.00  
% 11.81/2.00  cnf(c_18,plain,
% 11.81/2.00      ( r2_hidden(X0,X1) | ~ r2_hidden(X0,sK4(X1)) ),
% 11.81/2.00      inference(cnf_transformation,[],[f86]) ).
% 11.81/2.00  
% 11.81/2.00  cnf(c_1913,plain,
% 11.81/2.00      ( r2_hidden(X0,X1) = iProver_top
% 11.81/2.00      | r2_hidden(X0,sK4(X1)) != iProver_top ),
% 11.81/2.00      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 11.81/2.00  
% 11.81/2.00  cnf(c_3632,plain,
% 11.81/2.00      ( r2_hidden(sK0(sK4(X0),X1),X0) = iProver_top
% 11.81/2.00      | r1_tarski(sK4(X0),X1) = iProver_top ),
% 11.81/2.00      inference(superposition,[status(thm)],[c_1927,c_1913]) ).
% 11.81/2.00  
% 11.81/2.00  cnf(c_7482,plain,
% 11.81/2.00      ( r2_hidden(sK0(sK4(sK4(X0)),X1),X0) = iProver_top
% 11.81/2.00      | r1_tarski(sK4(sK4(X0)),X1) = iProver_top ),
% 11.81/2.00      inference(superposition,[status(thm)],[c_3632,c_1913]) ).
% 11.81/2.00  
% 11.81/2.00  cnf(c_39,negated_conjecture,
% 11.81/2.00      ( ~ r2_hidden(X0,sK8)
% 11.81/2.00      | r2_hidden(k2_xboole_0(X0,k1_tarski(X0)),sK8)
% 11.81/2.00      | ~ v3_ordinal1(X0)
% 11.81/2.00      | v4_ordinal1(sK8) ),
% 11.81/2.00      inference(cnf_transformation,[],[f119]) ).
% 11.81/2.00  
% 11.81/2.00  cnf(c_1896,plain,
% 11.81/2.00      ( r2_hidden(X0,sK8) != iProver_top
% 11.81/2.00      | r2_hidden(k2_xboole_0(X0,k1_tarski(X0)),sK8) = iProver_top
% 11.81/2.00      | v3_ordinal1(X0) != iProver_top
% 11.81/2.00      | v4_ordinal1(sK8) = iProver_top ),
% 11.81/2.00      inference(predicate_to_equality,[status(thm)],[c_39]) ).
% 11.81/2.00  
% 11.81/2.00  cnf(c_9,plain,
% 11.81/2.00      ( ~ r2_hidden(X0,X1)
% 11.81/2.00      | ~ r2_hidden(X2,X0)
% 11.81/2.00      | r2_hidden(X2,k3_tarski(X1)) ),
% 11.81/2.00      inference(cnf_transformation,[],[f122]) ).
% 11.81/2.00  
% 11.81/2.00  cnf(c_1920,plain,
% 11.81/2.00      ( r2_hidden(X0,X1) != iProver_top
% 11.81/2.00      | r2_hidden(X2,X0) != iProver_top
% 11.81/2.00      | r2_hidden(X2,k3_tarski(X1)) = iProver_top ),
% 11.81/2.00      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 11.81/2.00  
% 11.81/2.00  cnf(c_5486,plain,
% 11.81/2.00      ( r2_hidden(X0,k2_xboole_0(X1,k1_tarski(X1))) != iProver_top
% 11.81/2.00      | r2_hidden(X0,k3_tarski(sK8)) = iProver_top
% 11.81/2.00      | r2_hidden(X1,sK8) != iProver_top
% 11.81/2.00      | v3_ordinal1(X1) != iProver_top
% 11.81/2.00      | v4_ordinal1(sK8) = iProver_top ),
% 11.81/2.00      inference(superposition,[status(thm)],[c_1896,c_1920]) ).
% 11.81/2.00  
% 11.81/2.00  cnf(c_12947,plain,
% 11.81/2.00      ( r2_hidden(X0,sK8) != iProver_top
% 11.81/2.00      | r2_hidden(sK0(sK4(sK4(k2_xboole_0(X0,k1_tarski(X0)))),X1),k3_tarski(sK8)) = iProver_top
% 11.81/2.00      | r1_tarski(sK4(sK4(k2_xboole_0(X0,k1_tarski(X0)))),X1) = iProver_top
% 11.81/2.00      | v3_ordinal1(X0) != iProver_top
% 11.81/2.00      | v4_ordinal1(sK8) = iProver_top ),
% 11.81/2.00      inference(superposition,[status(thm)],[c_7482,c_5486]) ).
% 11.81/2.00  
% 11.81/2.00  cnf(c_40,negated_conjecture,
% 11.81/2.00      ( v3_ordinal1(sK8) ),
% 11.81/2.00      inference(cnf_transformation,[],[f106]) ).
% 11.81/2.00  
% 11.81/2.00  cnf(c_41,plain,
% 11.81/2.00      ( v3_ordinal1(sK8) = iProver_top ),
% 11.81/2.00      inference(predicate_to_equality,[status(thm)],[c_40]) ).
% 11.81/2.00  
% 11.81/2.00  cnf(c_12,plain,
% 11.81/2.00      ( v4_ordinal1(X0) | k3_tarski(X0) != X0 ),
% 11.81/2.00      inference(cnf_transformation,[],[f83]) ).
% 11.81/2.00  
% 11.81/2.00  cnf(c_111,plain,
% 11.81/2.00      ( k3_tarski(X0) != X0 | v4_ordinal1(X0) = iProver_top ),
% 11.81/2.00      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 11.81/2.00  
% 11.81/2.00  cnf(c_113,plain,
% 11.81/2.00      ( k3_tarski(sK8) != sK8 | v4_ordinal1(sK8) = iProver_top ),
% 11.81/2.00      inference(instantiation,[status(thm)],[c_111]) ).
% 11.81/2.00  
% 11.81/2.00  cnf(c_10,plain,
% 11.81/2.00      ( ~ r2_hidden(X0,k3_tarski(X1)) | r2_hidden(sK3(X1,X0),X1) ),
% 11.81/2.00      inference(cnf_transformation,[],[f123]) ).
% 11.81/2.00  
% 11.81/2.00  cnf(c_117,plain,
% 11.81/2.00      ( r2_hidden(X0,k3_tarski(X1)) != iProver_top
% 11.81/2.00      | r2_hidden(sK3(X1,X0),X1) = iProver_top ),
% 11.81/2.00      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 11.81/2.00  
% 11.81/2.00  cnf(c_119,plain,
% 11.81/2.00      ( r2_hidden(sK3(sK8,sK8),sK8) = iProver_top
% 11.81/2.00      | r2_hidden(sK8,k3_tarski(sK8)) != iProver_top ),
% 11.81/2.00      inference(instantiation,[status(thm)],[c_117]) ).
% 11.81/2.00  
% 11.81/2.00  cnf(c_24,plain,
% 11.81/2.00      ( r2_hidden(X0,X1)
% 11.81/2.00      | r2_hidden(X1,X0)
% 11.81/2.00      | ~ v3_ordinal1(X1)
% 11.81/2.00      | ~ v3_ordinal1(X0)
% 11.81/2.00      | X1 = X0 ),
% 11.81/2.00      inference(cnf_transformation,[],[f94]) ).
% 11.81/2.00  
% 11.81/2.00  cnf(c_2272,plain,
% 11.81/2.00      ( r2_hidden(k3_tarski(sK8),sK8)
% 11.81/2.00      | r2_hidden(sK8,k3_tarski(sK8))
% 11.81/2.00      | ~ v3_ordinal1(k3_tarski(sK8))
% 11.81/2.00      | ~ v3_ordinal1(sK8)
% 11.81/2.00      | k3_tarski(sK8) = sK8 ),
% 11.81/2.00      inference(instantiation,[status(thm)],[c_24]) ).
% 11.81/2.00  
% 11.81/2.00  cnf(c_2279,plain,
% 11.81/2.00      ( k3_tarski(sK8) = sK8
% 11.81/2.00      | r2_hidden(k3_tarski(sK8),sK8) = iProver_top
% 11.81/2.00      | r2_hidden(sK8,k3_tarski(sK8)) = iProver_top
% 11.81/2.00      | v3_ordinal1(k3_tarski(sK8)) != iProver_top
% 11.81/2.00      | v3_ordinal1(sK8) != iProver_top ),
% 11.81/2.00      inference(predicate_to_equality,[status(thm)],[c_2272]) ).
% 11.81/2.00  
% 11.81/2.00  cnf(c_27,plain,
% 11.81/2.00      ( r1_ordinal1(X0,X1)
% 11.81/2.00      | ~ r2_hidden(X0,k2_xboole_0(X1,k1_tarski(X1)))
% 11.81/2.00      | ~ v3_ordinal1(X1)
% 11.81/2.00      | ~ v3_ordinal1(X0) ),
% 11.81/2.00      inference(cnf_transformation,[],[f117]) ).
% 11.81/2.00  
% 11.81/2.00  cnf(c_15,plain,
% 11.81/2.00      ( ~ r1_ordinal1(X0,X1)
% 11.81/2.00      | r1_tarski(X0,X1)
% 11.81/2.00      | ~ v3_ordinal1(X1)
% 11.81/2.00      | ~ v3_ordinal1(X0) ),
% 11.81/2.00      inference(cnf_transformation,[],[f84]) ).
% 11.81/2.00  
% 11.81/2.00  cnf(c_630,plain,
% 11.81/2.00      ( ~ r2_hidden(X0,k2_xboole_0(X1,k1_tarski(X1)))
% 11.81/2.00      | r1_tarski(X0,X1)
% 11.81/2.00      | ~ v3_ordinal1(X1)
% 11.81/2.00      | ~ v3_ordinal1(X0) ),
% 11.81/2.00      inference(resolution,[status(thm)],[c_27,c_15]) ).
% 11.81/2.00  
% 11.81/2.00  cnf(c_3067,plain,
% 11.81/2.00      ( ~ r2_hidden(sK3(X0,X1),k2_xboole_0(sK8,k1_tarski(sK8)))
% 11.81/2.00      | r1_tarski(sK3(X0,X1),sK8)
% 11.81/2.00      | ~ v3_ordinal1(sK3(X0,X1))
% 11.81/2.00      | ~ v3_ordinal1(sK8) ),
% 11.81/2.00      inference(instantiation,[status(thm)],[c_630]) ).
% 11.81/2.00  
% 11.81/2.00  cnf(c_3078,plain,
% 11.81/2.00      ( r2_hidden(sK3(X0,X1),k2_xboole_0(sK8,k1_tarski(sK8))) != iProver_top
% 11.81/2.00      | r1_tarski(sK3(X0,X1),sK8) = iProver_top
% 11.81/2.00      | v3_ordinal1(sK3(X0,X1)) != iProver_top
% 11.81/2.00      | v3_ordinal1(sK8) != iProver_top ),
% 11.81/2.00      inference(predicate_to_equality,[status(thm)],[c_3067]) ).
% 11.81/2.00  
% 11.81/2.00  cnf(c_3080,plain,
% 11.81/2.00      ( r2_hidden(sK3(sK8,sK8),k2_xboole_0(sK8,k1_tarski(sK8))) != iProver_top
% 11.81/2.00      | r1_tarski(sK3(sK8,sK8),sK8) = iProver_top
% 11.81/2.00      | v3_ordinal1(sK3(sK8,sK8)) != iProver_top
% 11.81/2.00      | v3_ordinal1(sK8) != iProver_top ),
% 11.81/2.00      inference(instantiation,[status(thm)],[c_3078]) ).
% 11.81/2.00  
% 11.81/2.00  cnf(c_3573,plain,
% 11.81/2.00      ( r2_hidden(k2_xboole_0(k3_tarski(sK8),k1_tarski(k3_tarski(sK8))),sK8)
% 11.81/2.00      | ~ r2_hidden(k3_tarski(sK8),sK8)
% 11.81/2.00      | ~ v3_ordinal1(k3_tarski(sK8))
% 11.81/2.00      | v4_ordinal1(sK8) ),
% 11.81/2.00      inference(instantiation,[status(thm)],[c_39]) ).
% 11.81/2.00  
% 11.81/2.00  cnf(c_3574,plain,
% 11.81/2.00      ( r2_hidden(k2_xboole_0(k3_tarski(sK8),k1_tarski(k3_tarski(sK8))),sK8) = iProver_top
% 11.81/2.00      | r2_hidden(k3_tarski(sK8),sK8) != iProver_top
% 11.81/2.00      | v3_ordinal1(k3_tarski(sK8)) != iProver_top
% 11.81/2.00      | v4_ordinal1(sK8) = iProver_top ),
% 11.81/2.00      inference(predicate_to_equality,[status(thm)],[c_3573]) ).
% 11.81/2.00  
% 11.81/2.00  cnf(c_11,plain,
% 11.81/2.00      ( r2_hidden(X0,sK3(X1,X0)) | ~ r2_hidden(X0,k3_tarski(X1)) ),
% 11.81/2.00      inference(cnf_transformation,[],[f124]) ).
% 11.81/2.00  
% 11.81/2.00  cnf(c_1918,plain,
% 11.81/2.00      ( r2_hidden(X0,sK3(X1,X0)) = iProver_top
% 11.81/2.00      | r2_hidden(X0,k3_tarski(X1)) != iProver_top ),
% 11.81/2.00      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 11.81/2.00  
% 11.81/2.00  cnf(c_35,plain,
% 11.81/2.00      ( ~ r2_hidden(X0,X1) | ~ r1_tarski(X1,X0) ),
% 11.81/2.00      inference(cnf_transformation,[],[f105]) ).
% 11.81/2.00  
% 11.81/2.00  cnf(c_1900,plain,
% 11.81/2.00      ( r2_hidden(X0,X1) != iProver_top
% 11.81/2.00      | r1_tarski(X1,X0) != iProver_top ),
% 11.81/2.00      inference(predicate_to_equality,[status(thm)],[c_35]) ).
% 11.81/2.00  
% 11.81/2.00  cnf(c_4011,plain,
% 11.81/2.00      ( r2_hidden(X0,k3_tarski(X1)) != iProver_top
% 11.81/2.00      | r1_tarski(sK3(X1,X0),X0) != iProver_top ),
% 11.81/2.00      inference(superposition,[status(thm)],[c_1918,c_1900]) ).
% 11.81/2.00  
% 11.81/2.00  cnf(c_4013,plain,
% 11.81/2.00      ( r2_hidden(sK8,k3_tarski(sK8)) != iProver_top
% 11.81/2.00      | r1_tarski(sK3(sK8,sK8),sK8) != iProver_top ),
% 11.81/2.00      inference(instantiation,[status(thm)],[c_4011]) ).
% 11.81/2.00  
% 11.81/2.00  cnf(c_1919,plain,
% 11.81/2.00      ( r2_hidden(X0,k3_tarski(X1)) != iProver_top
% 11.81/2.00      | r2_hidden(sK3(X1,X0),X1) = iProver_top ),
% 11.81/2.00      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 11.81/2.00  
% 11.81/2.00  cnf(c_23,plain,
% 11.81/2.00      ( ~ r2_hidden(X0,X1) | ~ v3_ordinal1(X1) | v3_ordinal1(X0) ),
% 11.81/2.00      inference(cnf_transformation,[],[f93]) ).
% 11.81/2.00  
% 11.81/2.00  cnf(c_1909,plain,
% 11.81/2.00      ( r2_hidden(X0,X1) != iProver_top
% 11.81/2.00      | v3_ordinal1(X1) != iProver_top
% 11.81/2.00      | v3_ordinal1(X0) = iProver_top ),
% 11.81/2.00      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 11.81/2.00  
% 11.81/2.00  cnf(c_4250,plain,
% 11.81/2.00      ( r2_hidden(X0,k3_tarski(X1)) != iProver_top
% 11.81/2.00      | v3_ordinal1(X1) != iProver_top
% 11.81/2.00      | v3_ordinal1(sK3(X1,X0)) = iProver_top ),
% 11.81/2.00      inference(superposition,[status(thm)],[c_1919,c_1909]) ).
% 11.81/2.00  
% 11.81/2.00  cnf(c_4261,plain,
% 11.81/2.00      ( r2_hidden(sK8,k3_tarski(sK8)) != iProver_top
% 11.81/2.00      | v3_ordinal1(sK3(sK8,sK8)) = iProver_top
% 11.81/2.00      | v3_ordinal1(sK8) != iProver_top ),
% 11.81/2.00      inference(instantiation,[status(thm)],[c_4250]) ).
% 11.81/2.00  
% 11.81/2.00  cnf(c_20,plain,
% 11.81/2.00      ( r2_hidden(X0,k2_xboole_0(X0,k1_tarski(X0))) ),
% 11.81/2.00      inference(cnf_transformation,[],[f125]) ).
% 11.81/2.00  
% 11.81/2.00  cnf(c_1912,plain,
% 11.81/2.00      ( r2_hidden(X0,k2_xboole_0(X0,k1_tarski(X0))) = iProver_top ),
% 11.81/2.00      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 11.81/2.00  
% 11.81/2.00  cnf(c_6001,plain,
% 11.81/2.00      ( r2_hidden(X0,k3_tarski(sK8)) = iProver_top
% 11.81/2.00      | r2_hidden(X0,sK8) != iProver_top
% 11.81/2.00      | v3_ordinal1(X0) != iProver_top
% 11.81/2.00      | v4_ordinal1(sK8) = iProver_top ),
% 11.81/2.00      inference(superposition,[status(thm)],[c_1912,c_5486]) ).
% 11.81/2.00  
% 11.81/2.00  cnf(c_4,plain,
% 11.81/2.00      ( r1_tarski(X0,X0) ),
% 11.81/2.00      inference(cnf_transformation,[],[f120]) ).
% 11.81/2.00  
% 11.81/2.00  cnf(c_1924,plain,
% 11.81/2.00      ( r1_tarski(X0,X0) = iProver_top ),
% 11.81/2.00      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 11.81/2.00  
% 11.81/2.00  cnf(c_21,plain,
% 11.81/2.00      ( ~ r2_hidden(X0,X1)
% 11.81/2.00      | r2_hidden(X0,k2_xboole_0(X1,k1_tarski(X1))) ),
% 11.81/2.00      inference(cnf_transformation,[],[f113]) ).
% 11.81/2.00  
% 11.81/2.00  cnf(c_1911,plain,
% 11.81/2.00      ( r2_hidden(X0,X1) != iProver_top
% 11.81/2.00      | r2_hidden(X0,k2_xboole_0(X1,k1_tarski(X1))) = iProver_top ),
% 11.81/2.00      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 11.81/2.00  
% 11.81/2.00  cnf(c_3944,plain,
% 11.81/2.00      ( r2_hidden(X0,X1) != iProver_top
% 11.81/2.00      | r1_tarski(k2_xboole_0(X1,k1_tarski(X1)),X0) != iProver_top ),
% 11.81/2.00      inference(superposition,[status(thm)],[c_1911,c_1900]) ).
% 11.81/2.00  
% 11.81/2.00  cnf(c_4709,plain,
% 11.81/2.00      ( r2_hidden(k2_xboole_0(X0,k1_tarski(X0)),X0) != iProver_top ),
% 11.81/2.00      inference(superposition,[status(thm)],[c_1924,c_3944]) ).
% 11.81/2.00  
% 11.81/2.00  cnf(c_7889,plain,
% 11.81/2.00      ( r2_hidden(k2_xboole_0(k3_tarski(sK8),k1_tarski(k3_tarski(sK8))),sK8) != iProver_top
% 11.81/2.00      | v3_ordinal1(k2_xboole_0(k3_tarski(sK8),k1_tarski(k3_tarski(sK8)))) != iProver_top
% 11.81/2.00      | v4_ordinal1(sK8) = iProver_top ),
% 11.81/2.00      inference(superposition,[status(thm)],[c_6001,c_4709]) ).
% 11.81/2.00  
% 11.81/2.00  cnf(c_8497,plain,
% 11.81/2.00      ( ~ r2_hidden(sK3(sK8,X0),X1)
% 11.81/2.00      | r2_hidden(sK3(sK8,X0),k2_xboole_0(X1,k1_tarski(X1))) ),
% 11.81/2.00      inference(instantiation,[status(thm)],[c_21]) ).
% 11.81/2.00  
% 11.81/2.00  cnf(c_8498,plain,
% 11.81/2.00      ( r2_hidden(sK3(sK8,X0),X1) != iProver_top
% 11.81/2.00      | r2_hidden(sK3(sK8,X0),k2_xboole_0(X1,k1_tarski(X1))) = iProver_top ),
% 11.81/2.00      inference(predicate_to_equality,[status(thm)],[c_8497]) ).
% 11.81/2.00  
% 11.81/2.00  cnf(c_8500,plain,
% 11.81/2.00      ( r2_hidden(sK3(sK8,sK8),k2_xboole_0(sK8,k1_tarski(sK8))) = iProver_top
% 11.81/2.00      | r2_hidden(sK3(sK8,sK8),sK8) != iProver_top ),
% 11.81/2.00      inference(instantiation,[status(thm)],[c_8498]) ).
% 11.81/2.00  
% 11.81/2.00  cnf(c_25,plain,
% 11.81/2.00      ( ~ v3_ordinal1(X0) | v3_ordinal1(k2_xboole_0(X0,k1_tarski(X0))) ),
% 11.81/2.00      inference(cnf_transformation,[],[f115]) ).
% 11.81/2.00  
% 11.81/2.00  cnf(c_9468,plain,
% 11.81/2.00      ( v3_ordinal1(k2_xboole_0(k3_tarski(sK8),k1_tarski(k3_tarski(sK8))))
% 11.81/2.00      | ~ v3_ordinal1(k3_tarski(sK8)) ),
% 11.81/2.00      inference(instantiation,[status(thm)],[c_25]) ).
% 11.81/2.00  
% 11.81/2.00  cnf(c_9469,plain,
% 11.81/2.00      ( v3_ordinal1(k2_xboole_0(k3_tarski(sK8),k1_tarski(k3_tarski(sK8)))) = iProver_top
% 11.81/2.00      | v3_ordinal1(k3_tarski(sK8)) != iProver_top ),
% 11.81/2.00      inference(predicate_to_equality,[status(thm)],[c_9468]) ).
% 11.81/2.00  
% 11.81/2.00  cnf(c_29,plain,
% 11.81/2.00      ( r2_hidden(sK5(X0),X0) | v3_ordinal1(k3_tarski(X0)) ),
% 11.81/2.00      inference(cnf_transformation,[],[f98]) ).
% 11.81/2.00  
% 11.81/2.00  cnf(c_1905,plain,
% 11.81/2.00      ( r2_hidden(sK5(X0),X0) = iProver_top
% 11.81/2.00      | v3_ordinal1(k3_tarski(X0)) = iProver_top ),
% 11.81/2.00      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 11.81/2.00  
% 11.81/2.00  cnf(c_4255,plain,
% 11.81/2.00      ( v3_ordinal1(X0) != iProver_top
% 11.81/2.00      | v3_ordinal1(sK5(X0)) = iProver_top
% 11.81/2.00      | v3_ordinal1(k3_tarski(X0)) = iProver_top ),
% 11.81/2.00      inference(superposition,[status(thm)],[c_1905,c_1909]) ).
% 11.81/2.00  
% 11.81/2.00  cnf(c_28,plain,
% 11.81/2.00      ( ~ v3_ordinal1(sK5(X0)) | v3_ordinal1(k3_tarski(X0)) ),
% 11.81/2.00      inference(cnf_transformation,[],[f99]) ).
% 11.81/2.00  
% 11.81/2.00  cnf(c_69,plain,
% 11.81/2.00      ( v3_ordinal1(sK5(X0)) != iProver_top
% 11.81/2.00      | v3_ordinal1(k3_tarski(X0)) = iProver_top ),
% 11.81/2.00      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 11.81/2.00  
% 11.81/2.00  cnf(c_12307,plain,
% 11.81/2.00      ( v3_ordinal1(X0) != iProver_top
% 11.81/2.00      | v3_ordinal1(k3_tarski(X0)) = iProver_top ),
% 11.81/2.00      inference(global_propositional_subsumption,
% 11.81/2.00                [status(thm)],
% 11.81/2.00                [c_4255,c_69]) ).
% 11.81/2.00  
% 11.81/2.00  cnf(c_12310,plain,
% 11.81/2.00      ( v3_ordinal1(k3_tarski(sK8)) = iProver_top
% 11.81/2.00      | v3_ordinal1(sK8) != iProver_top ),
% 11.81/2.00      inference(instantiation,[status(thm)],[c_12307]) ).
% 11.81/2.00  
% 11.81/2.00  cnf(c_12985,plain,
% 11.81/2.00      ( v4_ordinal1(sK8) = iProver_top ),
% 11.81/2.00      inference(global_propositional_subsumption,
% 11.81/2.00                [status(thm)],
% 11.81/2.00                [c_12947,c_41,c_113,c_119,c_2279,c_3080,c_3574,c_4013,
% 11.81/2.00                 c_4261,c_7889,c_8500,c_9469,c_12310]) ).
% 11.81/2.00  
% 11.81/2.00  cnf(c_38,negated_conjecture,
% 11.81/2.00      ( v3_ordinal1(sK9) | ~ v4_ordinal1(sK8) ),
% 11.81/2.00      inference(cnf_transformation,[],[f108]) ).
% 11.81/2.00  
% 11.81/2.00  cnf(c_1897,plain,
% 11.81/2.00      ( v3_ordinal1(sK9) = iProver_top
% 11.81/2.00      | v4_ordinal1(sK8) != iProver_top ),
% 11.81/2.00      inference(predicate_to_equality,[status(thm)],[c_38]) ).
% 11.81/2.00  
% 11.81/2.00  cnf(c_12991,plain,
% 11.81/2.00      ( v3_ordinal1(sK9) = iProver_top ),
% 11.81/2.00      inference(superposition,[status(thm)],[c_12985,c_1897]) ).
% 11.81/2.00  
% 11.81/2.00  cnf(c_26,plain,
% 11.81/2.00      ( ~ r1_ordinal1(X0,X1)
% 11.81/2.00      | r2_hidden(X0,k2_xboole_0(X1,k1_tarski(X1)))
% 11.81/2.00      | ~ v3_ordinal1(X1)
% 11.81/2.00      | ~ v3_ordinal1(X0) ),
% 11.81/2.00      inference(cnf_transformation,[],[f116]) ).
% 11.81/2.00  
% 11.81/2.00  cnf(c_32,plain,
% 11.81/2.00      ( r1_ordinal1(sK7(X0),X1) | r2_hidden(X1,X0) | ~ v3_ordinal1(X1) ),
% 11.81/2.00      inference(cnf_transformation,[],[f104]) ).
% 11.81/2.00  
% 11.81/2.00  cnf(c_661,plain,
% 11.81/2.00      ( r2_hidden(X0,X1)
% 11.81/2.00      | r2_hidden(X2,k2_xboole_0(X3,k1_tarski(X3)))
% 11.81/2.00      | ~ v3_ordinal1(X3)
% 11.81/2.00      | ~ v3_ordinal1(X2)
% 11.81/2.00      | ~ v3_ordinal1(X0)
% 11.81/2.00      | X0 != X3
% 11.81/2.00      | sK7(X1) != X2 ),
% 11.81/2.00      inference(resolution_lifted,[status(thm)],[c_26,c_32]) ).
% 11.81/2.00  
% 11.81/2.00  cnf(c_662,plain,
% 11.81/2.00      ( r2_hidden(X0,X1)
% 11.81/2.00      | r2_hidden(sK7(X1),k2_xboole_0(X0,k1_tarski(X0)))
% 11.81/2.00      | ~ v3_ordinal1(X0)
% 11.81/2.00      | ~ v3_ordinal1(sK7(X1)) ),
% 11.81/2.00      inference(unflattening,[status(thm)],[c_661]) ).
% 11.81/2.00  
% 11.81/2.00  cnf(c_34,plain,
% 11.81/2.00      ( v3_ordinal1(sK7(X0)) ),
% 11.81/2.00      inference(cnf_transformation,[],[f102]) ).
% 11.81/2.00  
% 11.81/2.00  cnf(c_674,plain,
% 11.81/2.00      ( r2_hidden(X0,X1)
% 11.81/2.00      | r2_hidden(sK7(X1),k2_xboole_0(X0,k1_tarski(X0)))
% 11.81/2.00      | ~ v3_ordinal1(X0) ),
% 11.81/2.00      inference(forward_subsumption_resolution,
% 11.81/2.00                [status(thm)],
% 11.81/2.00                [c_662,c_34]) ).
% 11.81/2.00  
% 11.81/2.00  cnf(c_1892,plain,
% 11.81/2.00      ( r2_hidden(X0,X1) = iProver_top
% 11.81/2.00      | r2_hidden(sK7(X1),k2_xboole_0(X0,k1_tarski(X0))) = iProver_top
% 11.81/2.00      | v3_ordinal1(X0) != iProver_top ),
% 11.81/2.00      inference(predicate_to_equality,[status(thm)],[c_674]) ).
% 11.81/2.00  
% 11.81/2.00  cnf(c_22,plain,
% 11.81/2.00      ( r2_hidden(X0,X1)
% 11.81/2.00      | ~ r2_hidden(X0,k2_xboole_0(X1,k1_tarski(X1)))
% 11.81/2.00      | X1 = X0 ),
% 11.81/2.00      inference(cnf_transformation,[],[f114]) ).
% 11.81/2.00  
% 11.81/2.00  cnf(c_1910,plain,
% 11.81/2.00      ( X0 = X1
% 11.81/2.00      | r2_hidden(X1,X0) = iProver_top
% 11.81/2.00      | r2_hidden(X1,k2_xboole_0(X0,k1_tarski(X0))) != iProver_top ),
% 11.81/2.00      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 11.81/2.00  
% 11.81/2.00  cnf(c_4477,plain,
% 11.81/2.00      ( sK7(X0) = X1
% 11.81/2.00      | r2_hidden(X1,X0) = iProver_top
% 11.81/2.00      | r2_hidden(sK7(X0),X1) = iProver_top
% 11.81/2.00      | v3_ordinal1(X1) != iProver_top ),
% 11.81/2.00      inference(superposition,[status(thm)],[c_1892,c_1910]) ).
% 11.81/2.00  
% 11.81/2.00  cnf(c_33,plain,
% 11.81/2.00      ( ~ r2_hidden(sK7(X0),X0) ),
% 11.81/2.00      inference(cnf_transformation,[],[f103]) ).
% 11.81/2.00  
% 11.81/2.00  cnf(c_1902,plain,
% 11.81/2.00      ( r2_hidden(sK7(X0),X0) != iProver_top ),
% 11.81/2.00      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 11.81/2.00  
% 11.81/2.00  cnf(c_27208,plain,
% 11.81/2.00      ( sK7(X0) = X0
% 11.81/2.00      | r2_hidden(X0,X0) = iProver_top
% 11.81/2.00      | v3_ordinal1(X0) != iProver_top ),
% 11.81/2.00      inference(superposition,[status(thm)],[c_4477,c_1902]) ).
% 11.81/2.00  
% 11.81/2.00  cnf(c_3135,plain,
% 11.81/2.00      ( r1_tarski(k2_xboole_0(X0,k1_tarski(X0)),X0) != iProver_top ),
% 11.81/2.00      inference(superposition,[status(thm)],[c_1912,c_1900]) ).
% 11.81/2.00  
% 11.81/2.00  cnf(c_4471,plain,
% 11.81/2.00      ( sK0(k2_xboole_0(X0,k1_tarski(X0)),X1) = X0
% 11.81/2.00      | r2_hidden(sK0(k2_xboole_0(X0,k1_tarski(X0)),X1),X0) = iProver_top
% 11.81/2.00      | r1_tarski(k2_xboole_0(X0,k1_tarski(X0)),X1) = iProver_top ),
% 11.81/2.00      inference(superposition,[status(thm)],[c_1927,c_1910]) ).
% 11.81/2.00  
% 11.81/2.00  cnf(c_0,plain,
% 11.81/2.00      ( ~ r2_hidden(sK0(X0,X1),X1) | r1_tarski(X0,X1) ),
% 11.81/2.00      inference(cnf_transformation,[],[f71]) ).
% 11.81/2.00  
% 11.81/2.00  cnf(c_1928,plain,
% 11.81/2.00      ( r2_hidden(sK0(X0,X1),X1) != iProver_top
% 11.81/2.00      | r1_tarski(X0,X1) = iProver_top ),
% 11.81/2.00      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 11.81/2.00  
% 11.81/2.00  cnf(c_23177,plain,
% 11.81/2.00      ( sK0(k2_xboole_0(X0,k1_tarski(X0)),X0) = X0
% 11.81/2.00      | r1_tarski(k2_xboole_0(X0,k1_tarski(X0)),X0) = iProver_top ),
% 11.81/2.00      inference(superposition,[status(thm)],[c_4471,c_1928]) ).
% 11.81/2.00  
% 11.81/2.00  cnf(c_23293,plain,
% 11.81/2.00      ( sK0(k2_xboole_0(X0,k1_tarski(X0)),X0) = X0 ),
% 11.81/2.00      inference(global_propositional_subsumption,
% 11.81/2.00                [status(thm)],
% 11.81/2.00                [c_23177,c_3135]) ).
% 11.81/2.00  
% 11.81/2.00  cnf(c_23299,plain,
% 11.81/2.00      ( r2_hidden(X0,X0) != iProver_top
% 11.81/2.00      | r1_tarski(k2_xboole_0(X0,k1_tarski(X0)),X0) = iProver_top ),
% 11.81/2.00      inference(superposition,[status(thm)],[c_23293,c_1928]) ).
% 11.81/2.00  
% 11.81/2.00  cnf(c_29259,plain,
% 11.81/2.00      ( sK7(X0) = X0 | v3_ordinal1(X0) != iProver_top ),
% 11.81/2.00      inference(global_propositional_subsumption,
% 11.81/2.00                [status(thm)],
% 11.81/2.00                [c_27208,c_3135,c_23299]) ).
% 11.81/2.00  
% 11.81/2.00  cnf(c_29269,plain,
% 11.81/2.00      ( sK7(sK9) = sK9 ),
% 11.81/2.00      inference(superposition,[status(thm)],[c_12991,c_29259]) ).
% 11.81/2.00  
% 11.81/2.00  cnf(c_29747,plain,
% 11.81/2.00      ( sK7(sK9) = X0
% 11.81/2.00      | r2_hidden(X0,sK9) = iProver_top
% 11.81/2.00      | r2_hidden(sK9,X0) = iProver_top
% 11.81/2.00      | v3_ordinal1(X0) != iProver_top ),
% 11.81/2.00      inference(superposition,[status(thm)],[c_29269,c_4477]) ).
% 11.81/2.00  
% 11.81/2.00  cnf(c_29761,plain,
% 11.81/2.00      ( sK9 = X0
% 11.81/2.00      | r2_hidden(X0,sK9) = iProver_top
% 11.81/2.00      | r2_hidden(sK9,X0) = iProver_top
% 11.81/2.00      | v3_ordinal1(X0) != iProver_top ),
% 11.81/2.00      inference(demodulation,[status(thm)],[c_29747,c_29269]) ).
% 11.81/2.00  
% 11.81/2.00  cnf(c_39633,plain,
% 11.81/2.00      ( k3_tarski(X0) = sK9
% 11.81/2.00      | r2_hidden(k3_tarski(X0),sK9) = iProver_top
% 11.81/2.00      | v3_ordinal1(X0) != iProver_top
% 11.81/2.00      | v3_ordinal1(sK3(X0,sK9)) = iProver_top
% 11.81/2.00      | v3_ordinal1(k3_tarski(X0)) != iProver_top ),
% 11.81/2.00      inference(superposition,[status(thm)],[c_29761,c_4250]) ).
% 11.81/2.00  
% 11.81/2.00  cnf(c_39737,plain,
% 11.81/2.00      ( k3_tarski(sK8) = sK9
% 11.81/2.00      | r2_hidden(k3_tarski(sK8),sK9) = iProver_top
% 11.81/2.00      | v3_ordinal1(sK3(sK8,sK9)) = iProver_top
% 11.81/2.00      | v3_ordinal1(k3_tarski(sK8)) != iProver_top
% 11.81/2.00      | v3_ordinal1(sK8) != iProver_top ),
% 11.81/2.00      inference(instantiation,[status(thm)],[c_39633]) ).
% 11.81/2.00  
% 11.81/2.00  cnf(c_1895,plain,
% 11.81/2.00      ( v3_ordinal1(sK8) = iProver_top ),
% 11.81/2.00      inference(predicate_to_equality,[status(thm)],[c_40]) ).
% 11.81/2.00  
% 11.81/2.00  cnf(c_29270,plain,
% 11.81/2.00      ( sK7(sK8) = sK8 ),
% 11.81/2.00      inference(superposition,[status(thm)],[c_1895,c_29259]) ).
% 11.81/2.00  
% 11.81/2.00  cnf(c_681,plain,
% 11.81/2.00      ( r2_hidden(X0,X1)
% 11.81/2.00      | r1_tarski(X2,X3)
% 11.81/2.00      | ~ v3_ordinal1(X3)
% 11.81/2.00      | ~ v3_ordinal1(X2)
% 11.81/2.00      | ~ v3_ordinal1(X0)
% 11.81/2.00      | X0 != X3
% 11.81/2.00      | sK7(X1) != X2 ),
% 11.81/2.00      inference(resolution_lifted,[status(thm)],[c_15,c_32]) ).
% 11.81/2.00  
% 11.81/2.00  cnf(c_682,plain,
% 11.81/2.00      ( r2_hidden(X0,X1)
% 11.81/2.00      | r1_tarski(sK7(X1),X0)
% 11.81/2.00      | ~ v3_ordinal1(X0)
% 11.81/2.00      | ~ v3_ordinal1(sK7(X1)) ),
% 11.81/2.00      inference(unflattening,[status(thm)],[c_681]) ).
% 11.81/2.00  
% 11.81/2.00  cnf(c_694,plain,
% 11.81/2.00      ( r2_hidden(X0,X1) | r1_tarski(sK7(X1),X0) | ~ v3_ordinal1(X0) ),
% 11.81/2.00      inference(forward_subsumption_resolution,
% 11.81/2.00                [status(thm)],
% 11.81/2.00                [c_682,c_34]) ).
% 11.81/2.00  
% 11.81/2.00  cnf(c_1891,plain,
% 11.81/2.00      ( r2_hidden(X0,X1) = iProver_top
% 11.81/2.00      | r1_tarski(sK7(X1),X0) = iProver_top
% 11.81/2.00      | v3_ordinal1(X0) != iProver_top ),
% 11.81/2.00      inference(predicate_to_equality,[status(thm)],[c_694]) ).
% 11.81/2.00  
% 11.81/2.00  cnf(c_29535,plain,
% 11.81/2.00      ( r2_hidden(X0,sK8) = iProver_top
% 11.81/2.00      | r1_tarski(sK8,X0) = iProver_top
% 11.81/2.00      | v3_ordinal1(X0) != iProver_top ),
% 11.81/2.00      inference(superposition,[status(thm)],[c_29270,c_1891]) ).
% 11.81/2.00  
% 11.81/2.00  cnf(c_1908,plain,
% 11.81/2.00      ( X0 = X1
% 11.81/2.00      | r2_hidden(X1,X0) = iProver_top
% 11.81/2.00      | r2_hidden(X0,X1) = iProver_top
% 11.81/2.00      | v3_ordinal1(X1) != iProver_top
% 11.81/2.00      | v3_ordinal1(X0) != iProver_top ),
% 11.81/2.00      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 11.81/2.00  
% 11.81/2.00  cnf(c_36,negated_conjecture,
% 11.81/2.00      ( ~ r2_hidden(k2_xboole_0(sK9,k1_tarski(sK9)),sK8)
% 11.81/2.00      | ~ v4_ordinal1(sK8) ),
% 11.81/2.00      inference(cnf_transformation,[],[f118]) ).
% 11.81/2.00  
% 11.81/2.00  cnf(c_1899,plain,
% 11.81/2.00      ( r2_hidden(k2_xboole_0(sK9,k1_tarski(sK9)),sK8) != iProver_top
% 11.81/2.00      | v4_ordinal1(sK8) != iProver_top ),
% 11.81/2.00      inference(predicate_to_equality,[status(thm)],[c_36]) ).
% 11.81/2.00  
% 11.81/2.00  cnf(c_6573,plain,
% 11.81/2.00      ( k2_xboole_0(sK9,k1_tarski(sK9)) = sK8
% 11.81/2.00      | r2_hidden(sK8,k2_xboole_0(sK9,k1_tarski(sK9))) = iProver_top
% 11.81/2.00      | v3_ordinal1(k2_xboole_0(sK9,k1_tarski(sK9))) != iProver_top
% 11.81/2.00      | v3_ordinal1(sK8) != iProver_top
% 11.81/2.00      | v4_ordinal1(sK8) != iProver_top ),
% 11.81/2.00      inference(superposition,[status(thm)],[c_1908,c_1899]) ).
% 11.81/2.00  
% 11.81/2.00  cnf(c_45,plain,
% 11.81/2.00      ( v3_ordinal1(sK9) = iProver_top
% 11.81/2.00      | v4_ordinal1(sK8) != iProver_top ),
% 11.81/2.00      inference(predicate_to_equality,[status(thm)],[c_38]) ).
% 11.81/2.00  
% 11.81/2.00  cnf(c_2006,plain,
% 11.81/2.00      ( ~ r2_hidden(sK8,k2_xboole_0(sK9,k1_tarski(sK9)))
% 11.81/2.00      | r1_tarski(sK8,sK9)
% 11.81/2.00      | ~ v3_ordinal1(sK8)
% 11.81/2.00      | ~ v3_ordinal1(sK9) ),
% 11.81/2.00      inference(instantiation,[status(thm)],[c_630]) ).
% 11.81/2.00  
% 11.81/2.00  cnf(c_2013,plain,
% 11.81/2.00      ( r2_hidden(sK8,k2_xboole_0(sK9,k1_tarski(sK9))) != iProver_top
% 11.81/2.00      | r1_tarski(sK8,sK9) = iProver_top
% 11.81/2.00      | v3_ordinal1(sK8) != iProver_top
% 11.81/2.00      | v3_ordinal1(sK9) != iProver_top ),
% 11.81/2.00      inference(predicate_to_equality,[status(thm)],[c_2006]) ).
% 11.81/2.00  
% 11.81/2.00  cnf(c_2112,plain,
% 11.81/2.00      ( v3_ordinal1(k2_xboole_0(sK9,k1_tarski(sK9)))
% 11.81/2.00      | ~ v3_ordinal1(sK9) ),
% 11.81/2.00      inference(instantiation,[status(thm)],[c_25]) ).
% 11.81/2.00  
% 11.81/2.00  cnf(c_2113,plain,
% 11.81/2.00      ( v3_ordinal1(k2_xboole_0(sK9,k1_tarski(sK9))) = iProver_top
% 11.81/2.00      | v3_ordinal1(sK9) != iProver_top ),
% 11.81/2.00      inference(predicate_to_equality,[status(thm)],[c_2112]) ).
% 11.81/2.00  
% 11.81/2.00  cnf(c_37,negated_conjecture,
% 11.81/2.00      ( r2_hidden(sK9,sK8) | ~ v4_ordinal1(sK8) ),
% 11.81/2.00      inference(cnf_transformation,[],[f109]) ).
% 11.81/2.00  
% 11.81/2.00  cnf(c_1898,plain,
% 11.81/2.00      ( r2_hidden(sK9,sK8) = iProver_top
% 11.81/2.00      | v4_ordinal1(sK8) != iProver_top ),
% 11.81/2.00      inference(predicate_to_equality,[status(thm)],[c_37]) ).
% 11.81/2.00  
% 11.81/2.00  cnf(c_3136,plain,
% 11.81/2.00      ( r1_tarski(sK8,sK9) != iProver_top
% 11.81/2.00      | v4_ordinal1(sK8) != iProver_top ),
% 11.81/2.00      inference(superposition,[status(thm)],[c_1898,c_1900]) ).
% 11.81/2.00  
% 11.81/2.00  cnf(c_6773,plain,
% 11.81/2.00      ( k2_xboole_0(sK9,k1_tarski(sK9)) = sK8
% 11.81/2.00      | v4_ordinal1(sK8) != iProver_top ),
% 11.81/2.00      inference(global_propositional_subsumption,
% 11.81/2.00                [status(thm)],
% 11.81/2.00                [c_6573,c_41,c_45,c_2013,c_2113,c_3136]) ).
% 11.81/2.00  
% 11.81/2.00  cnf(c_12990,plain,
% 11.81/2.00      ( k2_xboole_0(sK9,k1_tarski(sK9)) = sK8 ),
% 11.81/2.00      inference(superposition,[status(thm)],[c_12985,c_6773]) ).
% 11.81/2.00  
% 11.81/2.00  cnf(c_1894,plain,
% 11.81/2.00      ( r2_hidden(X0,k2_xboole_0(X1,k1_tarski(X1))) != iProver_top
% 11.81/2.00      | r1_tarski(X0,X1) = iProver_top
% 11.81/2.00      | v3_ordinal1(X0) != iProver_top
% 11.81/2.00      | v3_ordinal1(X1) != iProver_top ),
% 11.81/2.00      inference(predicate_to_equality,[status(thm)],[c_630]) ).
% 11.81/2.00  
% 11.81/2.00  cnf(c_13267,plain,
% 11.81/2.00      ( r2_hidden(X0,sK8) != iProver_top
% 11.81/2.00      | r1_tarski(X0,sK9) = iProver_top
% 11.81/2.00      | v3_ordinal1(X0) != iProver_top
% 11.81/2.00      | v3_ordinal1(sK9) != iProver_top ),
% 11.81/2.00      inference(superposition,[status(thm)],[c_12990,c_1894]) ).
% 11.81/2.00  
% 11.81/2.00  cnf(c_21128,plain,
% 11.81/2.00      ( v3_ordinal1(X0) != iProver_top
% 11.81/2.00      | r1_tarski(X0,sK9) = iProver_top
% 11.81/2.00      | r2_hidden(X0,sK8) != iProver_top ),
% 11.81/2.00      inference(global_propositional_subsumption,
% 11.81/2.00                [status(thm)],
% 11.81/2.00                [c_13267,c_41,c_45,c_113,c_119,c_2279,c_3080,c_3574,
% 11.81/2.00                 c_4013,c_4261,c_7889,c_8500,c_9469,c_12310]) ).
% 11.81/2.00  
% 11.81/2.00  cnf(c_21129,plain,
% 11.81/2.00      ( r2_hidden(X0,sK8) != iProver_top
% 11.81/2.00      | r1_tarski(X0,sK9) = iProver_top
% 11.81/2.00      | v3_ordinal1(X0) != iProver_top ),
% 11.81/2.00      inference(renaming,[status(thm)],[c_21128]) ).
% 11.81/2.00  
% 11.81/2.00  cnf(c_29850,plain,
% 11.81/2.00      ( r1_tarski(X0,sK9) = iProver_top
% 11.81/2.00      | r1_tarski(sK8,X0) = iProver_top
% 11.81/2.00      | v3_ordinal1(X0) != iProver_top ),
% 11.81/2.00      inference(superposition,[status(thm)],[c_29535,c_21129]) ).
% 11.81/2.00  
% 11.81/2.00  cnf(c_39135,plain,
% 11.81/2.00      ( r2_hidden(sK9,k3_tarski(X0)) != iProver_top
% 11.81/2.00      | r1_tarski(sK8,sK3(X0,sK9)) = iProver_top
% 11.81/2.00      | v3_ordinal1(sK3(X0,sK9)) != iProver_top ),
% 11.81/2.00      inference(superposition,[status(thm)],[c_29850,c_4011]) ).
% 11.81/2.00  
% 11.81/2.00  cnf(c_39176,plain,
% 11.81/2.00      ( r2_hidden(sK9,k3_tarski(sK8)) != iProver_top
% 11.81/2.00      | r1_tarski(sK8,sK3(sK8,sK9)) = iProver_top
% 11.81/2.00      | v3_ordinal1(sK3(sK8,sK9)) != iProver_top ),
% 11.81/2.00      inference(instantiation,[status(thm)],[c_39135]) ).
% 11.81/2.00  
% 11.81/2.00  cnf(c_20284,plain,
% 11.81/2.00      ( ~ r2_hidden(sK3(X0,sK9),X0) | ~ r1_tarski(X0,sK3(X0,sK9)) ),
% 11.81/2.00      inference(instantiation,[status(thm)],[c_35]) ).
% 11.81/2.00  
% 11.81/2.00  cnf(c_20285,plain,
% 11.81/2.00      ( r2_hidden(sK3(X0,sK9),X0) != iProver_top
% 11.81/2.00      | r1_tarski(X0,sK3(X0,sK9)) != iProver_top ),
% 11.81/2.00      inference(predicate_to_equality,[status(thm)],[c_20284]) ).
% 11.81/2.00  
% 11.81/2.00  cnf(c_20287,plain,
% 11.81/2.00      ( r2_hidden(sK3(sK8,sK9),sK8) != iProver_top
% 11.81/2.00      | r1_tarski(sK8,sK3(sK8,sK9)) != iProver_top ),
% 11.81/2.00      inference(instantiation,[status(thm)],[c_20285]) ).
% 11.81/2.00  
% 11.81/2.00  cnf(c_10518,plain,
% 11.81/2.00      ( r1_tarski(k3_tarski(sK8),k3_tarski(sK8)) ),
% 11.81/2.00      inference(instantiation,[status(thm)],[c_4]) ).
% 11.81/2.00  
% 11.81/2.00  cnf(c_10519,plain,
% 11.81/2.00      ( r1_tarski(k3_tarski(sK8),k3_tarski(sK8)) = iProver_top ),
% 11.81/2.00      inference(predicate_to_equality,[status(thm)],[c_10518]) ).
% 11.81/2.00  
% 11.81/2.00  cnf(c_1149,plain,
% 11.81/2.00      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,X1) | X2 != X0 ),
% 11.81/2.00      theory(equality) ).
% 11.81/2.00  
% 11.81/2.00  cnf(c_3596,plain,
% 11.81/2.00      ( ~ r1_tarski(X0,k3_tarski(sK8))
% 11.81/2.00      | r1_tarski(sK8,k3_tarski(sK8))
% 11.81/2.00      | sK8 != X0 ),
% 11.81/2.00      inference(instantiation,[status(thm)],[c_1149]) ).
% 11.81/2.00  
% 11.81/2.00  cnf(c_6917,plain,
% 11.81/2.00      ( ~ r1_tarski(k3_tarski(sK8),k3_tarski(sK8))
% 11.81/2.00      | r1_tarski(sK8,k3_tarski(sK8))
% 11.81/2.00      | sK8 != k3_tarski(sK8) ),
% 11.81/2.00      inference(instantiation,[status(thm)],[c_3596]) ).
% 11.81/2.00  
% 11.81/2.00  cnf(c_6918,plain,
% 11.81/2.00      ( sK8 != k3_tarski(sK8)
% 11.81/2.00      | r1_tarski(k3_tarski(sK8),k3_tarski(sK8)) != iProver_top
% 11.81/2.00      | r1_tarski(sK8,k3_tarski(sK8)) = iProver_top ),
% 11.81/2.00      inference(predicate_to_equality,[status(thm)],[c_6917]) ).
% 11.81/2.00  
% 11.81/2.00  cnf(c_5485,plain,
% 11.81/2.00      ( r2_hidden(X0,k3_tarski(sK8)) = iProver_top
% 11.81/2.00      | r2_hidden(X0,sK9) != iProver_top
% 11.81/2.00      | v4_ordinal1(sK8) != iProver_top ),
% 11.81/2.00      inference(superposition,[status(thm)],[c_1898,c_1920]) ).
% 11.81/2.00  
% 11.81/2.00  cnf(c_5778,plain,
% 11.81/2.00      ( r2_hidden(X0,sK9) != iProver_top
% 11.81/2.00      | r1_tarski(k3_tarski(sK8),X0) != iProver_top
% 11.81/2.00      | v4_ordinal1(sK8) != iProver_top ),
% 11.81/2.00      inference(superposition,[status(thm)],[c_5485,c_1900]) ).
% 11.81/2.00  
% 11.81/2.00  cnf(c_6847,plain,
% 11.81/2.00      ( r2_hidden(k3_tarski(sK8),sK9) != iProver_top
% 11.81/2.00      | v4_ordinal1(sK8) != iProver_top ),
% 11.81/2.00      inference(superposition,[status(thm)],[c_1924,c_5778]) ).
% 11.81/2.00  
% 11.81/2.00  cnf(c_2,plain,
% 11.81/2.00      ( ~ r2_hidden(X0,X1) | r2_hidden(X0,X2) | ~ r1_tarski(X1,X2) ),
% 11.81/2.00      inference(cnf_transformation,[],[f69]) ).
% 11.81/2.00  
% 11.81/2.00  cnf(c_3004,plain,
% 11.81/2.00      ( r2_hidden(sK9,X0) | ~ r2_hidden(sK9,sK8) | ~ r1_tarski(sK8,X0) ),
% 11.81/2.00      inference(instantiation,[status(thm)],[c_2]) ).
% 11.81/2.00  
% 11.81/2.00  cnf(c_3756,plain,
% 11.81/2.00      ( r2_hidden(sK9,k3_tarski(X0))
% 11.81/2.00      | ~ r2_hidden(sK9,sK8)
% 11.81/2.00      | ~ r1_tarski(sK8,k3_tarski(X0)) ),
% 11.81/2.00      inference(instantiation,[status(thm)],[c_3004]) ).
% 11.81/2.00  
% 11.81/2.00  cnf(c_3761,plain,
% 11.81/2.00      ( r2_hidden(sK9,k3_tarski(X0)) = iProver_top
% 11.81/2.00      | r2_hidden(sK9,sK8) != iProver_top
% 11.81/2.00      | r1_tarski(sK8,k3_tarski(X0)) != iProver_top ),
% 11.81/2.00      inference(predicate_to_equality,[status(thm)],[c_3756]) ).
% 11.81/2.00  
% 11.81/2.00  cnf(c_3763,plain,
% 11.81/2.00      ( r2_hidden(sK9,k3_tarski(sK8)) = iProver_top
% 11.81/2.00      | r2_hidden(sK9,sK8) != iProver_top
% 11.81/2.00      | r1_tarski(sK8,k3_tarski(sK8)) != iProver_top ),
% 11.81/2.00      inference(instantiation,[status(thm)],[c_3761]) ).
% 11.81/2.00  
% 11.81/2.00  cnf(c_3755,plain,
% 11.81/2.00      ( r2_hidden(sK3(X0,sK9),X0) | ~ r2_hidden(sK9,k3_tarski(X0)) ),
% 11.81/2.00      inference(instantiation,[status(thm)],[c_10]) ).
% 11.81/2.00  
% 11.81/2.00  cnf(c_3757,plain,
% 11.81/2.00      ( r2_hidden(sK3(X0,sK9),X0) = iProver_top
% 11.81/2.00      | r2_hidden(sK9,k3_tarski(X0)) != iProver_top ),
% 11.81/2.00      inference(predicate_to_equality,[status(thm)],[c_3755]) ).
% 11.81/2.00  
% 11.81/2.00  cnf(c_3759,plain,
% 11.81/2.00      ( r2_hidden(sK3(sK8,sK9),sK8) = iProver_top
% 11.81/2.00      | r2_hidden(sK9,k3_tarski(sK8)) != iProver_top ),
% 11.81/2.00      inference(instantiation,[status(thm)],[c_3757]) ).
% 11.81/2.00  
% 11.81/2.00  cnf(c_1150,plain,
% 11.81/2.00      ( ~ r2_hidden(X0,X1) | r2_hidden(X2,X3) | X2 != X0 | X3 != X1 ),
% 11.81/2.00      theory(equality) ).
% 11.81/2.00  
% 11.81/2.00  cnf(c_2147,plain,
% 11.81/2.00      ( ~ r2_hidden(X0,X1) | r2_hidden(X2,sK8) | X2 != X0 | sK8 != X1 ),
% 11.81/2.00      inference(instantiation,[status(thm)],[c_1150]) ).
% 11.81/2.00  
% 11.81/2.00  cnf(c_3552,plain,
% 11.81/2.00      ( r2_hidden(X0,sK8)
% 11.81/2.00      | ~ r2_hidden(k3_tarski(sK8),sK8)
% 11.81/2.00      | X0 != k3_tarski(sK8)
% 11.81/2.00      | sK8 != sK8 ),
% 11.81/2.00      inference(instantiation,[status(thm)],[c_2147]) ).
% 11.81/2.00  
% 11.81/2.00  cnf(c_3555,plain,
% 11.81/2.00      ( ~ r2_hidden(k3_tarski(sK8),sK8)
% 11.81/2.00      | r2_hidden(sK8,sK8)
% 11.81/2.00      | sK8 != k3_tarski(sK8)
% 11.81/2.00      | sK8 != sK8 ),
% 11.81/2.00      inference(instantiation,[status(thm)],[c_3552]) ).
% 11.81/2.00  
% 11.81/2.00  cnf(c_2628,plain,
% 11.81/2.00      ( r2_hidden(X0,sK8)
% 11.81/2.00      | ~ r2_hidden(sK9,sK8)
% 11.81/2.00      | X0 != sK9
% 11.81/2.00      | sK8 != sK8 ),
% 11.81/2.00      inference(instantiation,[status(thm)],[c_2147]) ).
% 11.81/2.00  
% 11.81/2.00  cnf(c_3469,plain,
% 11.81/2.00      ( r2_hidden(k3_tarski(X0),sK8)
% 11.81/2.00      | ~ r2_hidden(sK9,sK8)
% 11.81/2.00      | k3_tarski(X0) != sK9
% 11.81/2.00      | sK8 != sK8 ),
% 11.81/2.00      inference(instantiation,[status(thm)],[c_2628]) ).
% 11.81/2.00  
% 11.81/2.00  cnf(c_3471,plain,
% 11.81/2.00      ( r2_hidden(k3_tarski(sK8),sK8)
% 11.81/2.00      | ~ r2_hidden(sK9,sK8)
% 11.81/2.00      | k3_tarski(sK8) != sK9
% 11.81/2.00      | sK8 != sK8 ),
% 11.81/2.00      inference(instantiation,[status(thm)],[c_3469]) ).
% 11.81/2.00  
% 11.81/2.00  cnf(c_1148,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 11.81/2.00  
% 11.81/2.00  cnf(c_3110,plain,
% 11.81/2.00      ( k3_tarski(X0) != X1 | sK8 != X1 | sK8 = k3_tarski(X0) ),
% 11.81/2.00      inference(instantiation,[status(thm)],[c_1148]) ).
% 11.81/2.00  
% 11.81/2.00  cnf(c_3111,plain,
% 11.81/2.00      ( k3_tarski(sK8) != sK8 | sK8 = k3_tarski(sK8) | sK8 != sK8 ),
% 11.81/2.00      inference(instantiation,[status(thm)],[c_3110]) ).
% 11.81/2.00  
% 11.81/2.00  cnf(c_320,plain,
% 11.81/2.00      ( v4_ordinal1(X0) | k3_tarski(X0) != X0 ),
% 11.81/2.00      inference(prop_impl,[status(thm)],[c_12]) ).
% 11.81/2.00  
% 11.81/2.00  cnf(c_569,plain,
% 11.81/2.00      ( r2_hidden(sK9,sK8) | k3_tarski(X0) != X0 | sK8 != X0 ),
% 11.81/2.00      inference(resolution_lifted,[status(thm)],[c_320,c_37]) ).
% 11.81/2.00  
% 11.81/2.00  cnf(c_570,plain,
% 11.81/2.00      ( r2_hidden(sK9,sK8) | k3_tarski(sK8) != sK8 ),
% 11.81/2.00      inference(unflattening,[status(thm)],[c_569]) ).
% 11.81/2.00  
% 11.81/2.00  cnf(c_13,plain,
% 11.81/2.00      ( ~ v4_ordinal1(X0) | k3_tarski(X0) = X0 ),
% 11.81/2.00      inference(cnf_transformation,[],[f82]) ).
% 11.81/2.00  
% 11.81/2.00  cnf(c_108,plain,
% 11.81/2.00      ( k3_tarski(X0) = X0 | v4_ordinal1(X0) != iProver_top ),
% 11.81/2.00      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 11.81/2.00  
% 11.81/2.00  cnf(c_110,plain,
% 11.81/2.00      ( k3_tarski(sK8) = sK8 | v4_ordinal1(sK8) != iProver_top ),
% 11.81/2.00      inference(instantiation,[status(thm)],[c_108]) ).
% 11.81/2.00  
% 11.81/2.00  cnf(c_103,plain,
% 11.81/2.00      ( ~ r1_ordinal1(sK8,sK8)
% 11.81/2.00      | r1_tarski(sK8,sK8)
% 11.81/2.00      | ~ v3_ordinal1(sK8) ),
% 11.81/2.00      inference(instantiation,[status(thm)],[c_15]) ).
% 11.81/2.00  
% 11.81/2.00  cnf(c_92,plain,
% 11.81/2.00      ( r2_hidden(sK8,k2_xboole_0(sK8,k1_tarski(sK8))) ),
% 11.81/2.00      inference(instantiation,[status(thm)],[c_20]) ).
% 11.81/2.00  
% 11.81/2.00  cnf(c_82,plain,
% 11.81/2.00      ( r2_hidden(sK8,sK8) | ~ v3_ordinal1(sK8) | sK8 = sK8 ),
% 11.81/2.00      inference(instantiation,[status(thm)],[c_24]) ).
% 11.81/2.00  
% 11.81/2.00  cnf(c_73,plain,
% 11.81/2.00      ( r1_ordinal1(sK8,sK8)
% 11.81/2.00      | ~ r2_hidden(sK8,k2_xboole_0(sK8,k1_tarski(sK8)))
% 11.81/2.00      | ~ v3_ordinal1(sK8) ),
% 11.81/2.00      inference(instantiation,[status(thm)],[c_27]) ).
% 11.81/2.00  
% 11.81/2.00  cnf(c_49,plain,
% 11.81/2.00      ( ~ r2_hidden(sK8,sK8) | ~ r1_tarski(sK8,sK8) ),
% 11.81/2.00      inference(instantiation,[status(thm)],[c_35]) ).
% 11.81/2.00  
% 11.81/2.00  cnf(c_46,plain,
% 11.81/2.00      ( r2_hidden(sK9,sK8) = iProver_top
% 11.81/2.00      | v4_ordinal1(sK8) != iProver_top ),
% 11.81/2.00      inference(predicate_to_equality,[status(thm)],[c_37]) ).
% 11.81/2.00  
% 11.81/2.00  cnf(contradiction,plain,
% 11.81/2.00      ( $false ),
% 11.81/2.00      inference(minisat,
% 11.81/2.00                [status(thm)],
% 11.81/2.00                [c_39737,c_39176,c_20287,c_12985,c_12310,c_10519,c_6918,
% 11.81/2.00                 c_6847,c_3763,c_3759,c_3555,c_3471,c_3111,c_570,c_110,
% 11.81/2.00                 c_103,c_92,c_82,c_73,c_49,c_46,c_41,c_40]) ).
% 11.81/2.00  
% 11.81/2.00  
% 11.81/2.00  % SZS output end CNFRefutation for theBenchmark.p
% 11.81/2.00  
% 11.81/2.00  ------                               Statistics
% 11.81/2.00  
% 11.81/2.00  ------ General
% 11.81/2.00  
% 11.81/2.00  abstr_ref_over_cycles:                  0
% 11.81/2.00  abstr_ref_under_cycles:                 0
% 11.81/2.00  gc_basic_clause_elim:                   0
% 11.81/2.00  forced_gc_time:                         0
% 11.81/2.00  parsing_time:                           0.01
% 11.81/2.00  unif_index_cands_time:                  0.
% 11.81/2.00  unif_index_add_time:                    0.
% 11.81/2.00  orderings_time:                         0.
% 11.81/2.00  out_proof_time:                         0.018
% 11.81/2.00  total_time:                             1.263
% 11.81/2.00  num_of_symbols:                         49
% 11.81/2.00  num_of_terms:                           35399
% 11.81/2.00  
% 11.81/2.00  ------ Preprocessing
% 11.81/2.00  
% 11.81/2.00  num_of_splits:                          0
% 11.81/2.00  num_of_split_atoms:                     0
% 11.81/2.00  num_of_reused_defs:                     0
% 11.81/2.00  num_eq_ax_congr_red:                    44
% 11.81/2.00  num_of_sem_filtered_clauses:            1
% 11.81/2.00  num_of_subtypes:                        0
% 11.81/2.00  monotx_restored_types:                  0
% 11.81/2.00  sat_num_of_epr_types:                   0
% 11.81/2.00  sat_num_of_non_cyclic_types:            0
% 11.81/2.00  sat_guarded_non_collapsed_types:        0
% 11.81/2.00  num_pure_diseq_elim:                    0
% 11.81/2.00  simp_replaced_by:                       0
% 11.81/2.00  res_preprocessed:                       170
% 11.81/2.00  prep_upred:                             0
% 11.81/2.00  prep_unflattend:                        12
% 11.81/2.00  smt_new_axioms:                         0
% 11.81/2.00  pred_elim_cands:                        4
% 11.81/2.00  pred_elim:                              1
% 11.81/2.00  pred_elim_cl:                           1
% 11.81/2.00  pred_elim_cycles:                       4
% 11.81/2.00  merged_defs:                            8
% 11.81/2.00  merged_defs_ncl:                        0
% 11.81/2.00  bin_hyper_res:                          8
% 11.81/2.00  prep_cycles:                            4
% 11.81/2.00  pred_elim_time:                         0.007
% 11.81/2.00  splitting_time:                         0.
% 11.81/2.00  sem_filter_time:                        0.
% 11.81/2.00  monotx_time:                            0.001
% 11.81/2.00  subtype_inf_time:                       0.
% 11.81/2.00  
% 11.81/2.00  ------ Problem properties
% 11.81/2.00  
% 11.81/2.00  clauses:                                38
% 11.81/2.00  conjectures:                            5
% 11.81/2.00  epr:                                    9
% 11.81/2.00  horn:                                   29
% 11.81/2.00  ground:                                 4
% 11.81/2.00  unary:                                  7
% 11.81/2.00  binary:                                 16
% 11.81/2.00  lits:                                   90
% 11.81/2.00  lits_eq:                                8
% 11.81/2.00  fd_pure:                                0
% 11.81/2.00  fd_pseudo:                              0
% 11.81/2.00  fd_cond:                                0
% 11.81/2.00  fd_pseudo_cond:                         6
% 11.81/2.00  ac_symbols:                             0
% 11.81/2.00  
% 11.81/2.00  ------ Propositional Solver
% 11.81/2.00  
% 11.81/2.00  prop_solver_calls:                      32
% 11.81/2.00  prop_fast_solver_calls:                 2511
% 11.81/2.00  smt_solver_calls:                       0
% 11.81/2.00  smt_fast_solver_calls:                  0
% 11.81/2.00  prop_num_of_clauses:                    16342
% 11.81/2.00  prop_preprocess_simplified:             32572
% 11.81/2.00  prop_fo_subsumed:                       310
% 11.81/2.00  prop_solver_time:                       0.
% 11.81/2.00  smt_solver_time:                        0.
% 11.81/2.00  smt_fast_solver_time:                   0.
% 11.81/2.00  prop_fast_solver_time:                  0.
% 11.81/2.00  prop_unsat_core_time:                   0.001
% 11.81/2.00  
% 11.81/2.00  ------ QBF
% 11.81/2.00  
% 11.81/2.00  qbf_q_res:                              0
% 11.81/2.00  qbf_num_tautologies:                    0
% 11.81/2.00  qbf_prep_cycles:                        0
% 11.81/2.00  
% 11.81/2.00  ------ BMC1
% 11.81/2.00  
% 11.81/2.00  bmc1_current_bound:                     -1
% 11.81/2.00  bmc1_last_solved_bound:                 -1
% 11.81/2.00  bmc1_unsat_core_size:                   -1
% 11.81/2.00  bmc1_unsat_core_parents_size:           -1
% 11.81/2.00  bmc1_merge_next_fun:                    0
% 11.81/2.00  bmc1_unsat_core_clauses_time:           0.
% 11.81/2.00  
% 11.81/2.00  ------ Instantiation
% 11.81/2.00  
% 11.81/2.00  inst_num_of_clauses:                    4180
% 11.81/2.00  inst_num_in_passive:                    689
% 11.81/2.00  inst_num_in_active:                     1544
% 11.81/2.00  inst_num_in_unprocessed:                1950
% 11.81/2.00  inst_num_of_loops:                      1950
% 11.81/2.00  inst_num_of_learning_restarts:          0
% 11.81/2.00  inst_num_moves_active_passive:          405
% 11.81/2.00  inst_lit_activity:                      0
% 11.81/2.00  inst_lit_activity_moves:                0
% 11.81/2.00  inst_num_tautologies:                   0
% 11.81/2.00  inst_num_prop_implied:                  0
% 11.81/2.00  inst_num_existing_simplified:           0
% 11.81/2.00  inst_num_eq_res_simplified:             0
% 11.81/2.00  inst_num_child_elim:                    0
% 11.81/2.00  inst_num_of_dismatching_blockings:      4108
% 11.81/2.00  inst_num_of_non_proper_insts:           3449
% 11.81/2.00  inst_num_of_duplicates:                 0
% 11.81/2.00  inst_inst_num_from_inst_to_res:         0
% 11.81/2.00  inst_dismatching_checking_time:         0.
% 11.81/2.00  
% 11.81/2.00  ------ Resolution
% 11.81/2.00  
% 11.81/2.00  res_num_of_clauses:                     0
% 11.81/2.00  res_num_in_passive:                     0
% 11.81/2.00  res_num_in_active:                      0
% 11.81/2.00  res_num_of_loops:                       174
% 11.81/2.00  res_forward_subset_subsumed:            192
% 11.81/2.00  res_backward_subset_subsumed:           12
% 11.81/2.00  res_forward_subsumed:                   0
% 11.81/2.00  res_backward_subsumed:                  0
% 11.81/2.00  res_forward_subsumption_resolution:     2
% 11.81/2.00  res_backward_subsumption_resolution:    0
% 11.81/2.00  res_clause_to_clause_subsumption:       10015
% 11.81/2.00  res_orphan_elimination:                 0
% 11.81/2.00  res_tautology_del:                      308
% 11.81/2.00  res_num_eq_res_simplified:              0
% 11.81/2.00  res_num_sel_changes:                    0
% 11.81/2.00  res_moves_from_active_to_pass:          0
% 11.81/2.00  
% 11.81/2.00  ------ Superposition
% 11.81/2.00  
% 11.81/2.00  sup_time_total:                         0.
% 11.81/2.00  sup_time_generating:                    0.
% 11.81/2.00  sup_time_sim_full:                      0.
% 11.81/2.00  sup_time_sim_immed:                     0.
% 11.81/2.00  
% 11.81/2.00  sup_num_of_clauses:                     1736
% 11.81/2.00  sup_num_in_active:                      306
% 11.81/2.00  sup_num_in_passive:                     1430
% 11.81/2.00  sup_num_of_loops:                       389
% 11.81/2.00  sup_fw_superposition:                   995
% 11.81/2.00  sup_bw_superposition:                   1897
% 11.81/2.00  sup_immediate_simplified:               607
% 11.81/2.00  sup_given_eliminated:                   2
% 11.81/2.00  comparisons_done:                       0
% 11.81/2.00  comparisons_avoided:                    0
% 11.81/2.00  
% 11.81/2.00  ------ Simplifications
% 11.81/2.00  
% 11.81/2.00  
% 11.81/2.00  sim_fw_subset_subsumed:                 261
% 11.81/2.00  sim_bw_subset_subsumed:                 46
% 11.81/2.00  sim_fw_subsumed:                        223
% 11.81/2.00  sim_bw_subsumed:                        39
% 11.81/2.00  sim_fw_subsumption_res:                 0
% 11.81/2.00  sim_bw_subsumption_res:                 0
% 11.81/2.00  sim_tautology_del:                      115
% 11.81/2.00  sim_eq_tautology_del:                   41
% 11.81/2.00  sim_eq_res_simp:                        0
% 11.81/2.00  sim_fw_demodulated:                     62
% 11.81/2.00  sim_bw_demodulated:                     36
% 11.81/2.00  sim_light_normalised:                   167
% 11.81/2.00  sim_joinable_taut:                      0
% 11.81/2.00  sim_joinable_simp:                      0
% 11.81/2.00  sim_ac_normalised:                      0
% 11.81/2.00  sim_smt_subsumption:                    0
% 11.81/2.00  
%------------------------------------------------------------------------------
