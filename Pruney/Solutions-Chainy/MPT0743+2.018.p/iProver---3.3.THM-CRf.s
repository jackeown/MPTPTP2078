%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:53:39 EST 2020

% Result     : Theorem 3.39s
% Output     : CNFRefutation 3.39s
% Verified   : 
% Statistics : Number of formulae       :  149 (1453 expanded)
%              Number of clauses        :   57 ( 165 expanded)
%              Number of leaves         :   24 ( 426 expanded)
%              Depth                    :   24
%              Number of atoms          :  467 (3439 expanded)
%              Number of equality atoms :  108 (1087 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal clause size      :   14 (   2 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f20,conjecture,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ! [X1] :
          ( v3_ordinal1(X1)
         => ( r2_hidden(X0,X1)
          <=> r1_ordinal1(k1_ordinal1(X0),X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,negated_conjecture,(
    ~ ! [X0] :
        ( v3_ordinal1(X0)
       => ! [X1] :
            ( v3_ordinal1(X1)
           => ( r2_hidden(X0,X1)
            <=> r1_ordinal1(k1_ordinal1(X0),X1) ) ) ) ),
    inference(negated_conjecture,[],[f20])).

fof(f30,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( r2_hidden(X0,X1)
          <~> r1_ordinal1(k1_ordinal1(X0),X1) )
          & v3_ordinal1(X1) )
      & v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f43,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ r1_ordinal1(k1_ordinal1(X0),X1)
            | ~ r2_hidden(X0,X1) )
          & ( r1_ordinal1(k1_ordinal1(X0),X1)
            | r2_hidden(X0,X1) )
          & v3_ordinal1(X1) )
      & v3_ordinal1(X0) ) ),
    inference(nnf_transformation,[],[f30])).

fof(f44,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ r1_ordinal1(k1_ordinal1(X0),X1)
            | ~ r2_hidden(X0,X1) )
          & ( r1_ordinal1(k1_ordinal1(X0),X1)
            | r2_hidden(X0,X1) )
          & v3_ordinal1(X1) )
      & v3_ordinal1(X0) ) ),
    inference(flattening,[],[f43])).

fof(f46,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ( ~ r1_ordinal1(k1_ordinal1(X0),X1)
            | ~ r2_hidden(X0,X1) )
          & ( r1_ordinal1(k1_ordinal1(X0),X1)
            | r2_hidden(X0,X1) )
          & v3_ordinal1(X1) )
     => ( ( ~ r1_ordinal1(k1_ordinal1(X0),sK3)
          | ~ r2_hidden(X0,sK3) )
        & ( r1_ordinal1(k1_ordinal1(X0),sK3)
          | r2_hidden(X0,sK3) )
        & v3_ordinal1(sK3) ) ) ),
    introduced(choice_axiom,[])).

fof(f45,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( ~ r1_ordinal1(k1_ordinal1(X0),X1)
              | ~ r2_hidden(X0,X1) )
            & ( r1_ordinal1(k1_ordinal1(X0),X1)
              | r2_hidden(X0,X1) )
            & v3_ordinal1(X1) )
        & v3_ordinal1(X0) )
   => ( ? [X1] :
          ( ( ~ r1_ordinal1(k1_ordinal1(sK2),X1)
            | ~ r2_hidden(sK2,X1) )
          & ( r1_ordinal1(k1_ordinal1(sK2),X1)
            | r2_hidden(sK2,X1) )
          & v3_ordinal1(X1) )
      & v3_ordinal1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f47,plain,
    ( ( ~ r1_ordinal1(k1_ordinal1(sK2),sK3)
      | ~ r2_hidden(sK2,sK3) )
    & ( r1_ordinal1(k1_ordinal1(sK2),sK3)
      | r2_hidden(sK2,sK3) )
    & v3_ordinal1(sK3)
    & v3_ordinal1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f44,f46,f45])).

fof(f79,plain,(
    v3_ordinal1(sK2) ),
    inference(cnf_transformation,[],[f47])).

fof(f80,plain,(
    v3_ordinal1(sK3) ),
    inference(cnf_transformation,[],[f47])).

fof(f18,axiom,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => v3_ordinal1(k1_ordinal1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0] :
      ( v3_ordinal1(k1_ordinal1(X0))
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f77,plain,(
    ! [X0] :
      ( v3_ordinal1(k1_ordinal1(X0))
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f14,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_tarski(X0)) = k1_ordinal1(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f72,plain,(
    ! [X0] : k2_xboole_0(X0,k1_tarski(X0)) = k1_ordinal1(X0) ),
    inference(cnf_transformation,[],[f14])).

fof(f13,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f71,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f13])).

fof(f88,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f71,f87])).

fof(f5,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f62,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f6,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f63,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f6])).

fof(f7,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f64,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f7])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f65,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f8])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f66,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f9])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f67,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f10])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f68,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f11])).

fof(f83,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f67,f68])).

fof(f84,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f66,f83])).

fof(f85,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f65,f84])).

fof(f86,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f64,f85])).

fof(f87,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f63,f86])).

fof(f89,plain,(
    ! [X0] : k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f62,f87])).

fof(f90,plain,(
    ! [X0] : k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))) = k1_ordinal1(X0) ),
    inference(definition_unfolding,[],[f72,f88,f89])).

fof(f100,plain,(
    ! [X0] :
      ( v3_ordinal1(k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))))
      | ~ v3_ordinal1(X0) ) ),
    inference(definition_unfolding,[],[f77,f90])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( ( v3_ordinal1(X1)
        & v3_ordinal1(X0) )
     => ( r1_ordinal1(X0,X1)
      <=> r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( r1_ordinal1(X0,X1)
      <=> r1_tarski(X0,X1) )
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( r1_ordinal1(X0,X1)
      <=> r1_tarski(X0,X1) )
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(flattening,[],[f24])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ( ( r1_ordinal1(X0,X1)
          | ~ r1_tarski(X0,X1) )
        & ( r1_tarski(X0,X1)
          | ~ r1_ordinal1(X0,X1) ) )
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(nnf_transformation,[],[f25])).

fof(f73,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r1_ordinal1(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f81,plain,
    ( r1_ordinal1(k1_ordinal1(sK2),sK3)
    | r2_hidden(sK2,sK3) ),
    inference(cnf_transformation,[],[f47])).

fof(f102,plain,
    ( r1_ordinal1(k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))),sK3)
    | r2_hidden(sK2,sK3) ),
    inference(definition_unfolding,[],[f81,f90])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f61,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f17,axiom,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ! [X1] :
          ( v3_ordinal1(X1)
         => ( r2_hidden(X1,X0)
            | r1_ordinal1(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(X1,X0)
          | r1_ordinal1(X0,X1)
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(X1,X0)
          | r1_ordinal1(X0,X1)
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(flattening,[],[f26])).

fof(f76,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,X0)
      | r1_ordinal1(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f82,plain,
    ( ~ r1_ordinal1(k1_ordinal1(sK2),sK3)
    | ~ r2_hidden(sK2,sK3) ),
    inference(cnf_transformation,[],[f47])).

fof(f101,plain,
    ( ~ r1_ordinal1(k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))),sK3)
    | ~ r2_hidden(sK2,sK3) ),
    inference(definition_unfolding,[],[f82,f90])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            | r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) ) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) ) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f31])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( ~ r2_hidden(X4,X1)
                & ~ r2_hidden(X4,X0) ) )
            & ( r2_hidden(X4,X1)
              | r2_hidden(X4,X0)
              | ~ r2_hidden(X4,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f32])).

fof(f34,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ( ~ r2_hidden(X3,X1)
              & ~ r2_hidden(X3,X0) )
            | ~ r2_hidden(X3,X2) )
          & ( r2_hidden(X3,X1)
            | r2_hidden(X3,X0)
            | r2_hidden(X3,X2) ) )
     => ( ( ( ~ r2_hidden(sK0(X0,X1,X2),X1)
            & ~ r2_hidden(sK0(X0,X1,X2),X0) )
          | ~ r2_hidden(sK0(X0,X1,X2),X2) )
        & ( r2_hidden(sK0(X0,X1,X2),X1)
          | r2_hidden(sK0(X0,X1,X2),X0)
          | r2_hidden(sK0(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
        | ( ( ( ~ r2_hidden(sK0(X0,X1,X2),X1)
              & ~ r2_hidden(sK0(X0,X1,X2),X0) )
            | ~ r2_hidden(sK0(X0,X1,X2),X2) )
          & ( r2_hidden(sK0(X0,X1,X2),X1)
            | r2_hidden(sK0(X0,X1,X2),X0)
            | r2_hidden(sK0(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( ~ r2_hidden(X4,X1)
                & ~ r2_hidden(X4,X0) ) )
            & ( r2_hidden(X4,X1)
              | r2_hidden(X4,X0)
              | ~ r2_hidden(X4,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f33,f34])).

fof(f49,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X1)
      | r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f35])).

fof(f96,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X1)
      | r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f49,f88])).

fof(f105,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X1)
      | r2_hidden(X4,X0)
      | ~ r2_hidden(X4,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) ) ),
    inference(equality_resolution,[],[f96])).

fof(f50,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X0)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f35])).

fof(f95,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X0)
      | k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f50,f88])).

fof(f104,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))
      | ~ r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f95])).

fof(f19,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f78,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f51,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X1)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f35])).

fof(f94,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X1)
      | k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f51,f88])).

fof(f103,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))
      | ~ r2_hidden(X4,X1) ) ),
    inference(equality_resolution,[],[f94])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
    <=> r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(k1_tarski(X0),X1)
        | ~ r2_hidden(X0,X1) )
      & ( r2_hidden(X0,X1)
        | ~ r1_tarski(k1_tarski(X0),X1) ) ) ),
    inference(nnf_transformation,[],[f12])).

fof(f70,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f97,plain,(
    ! [X0,X1] :
      ( r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f70,f89])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f36])).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f37])).

fof(f39,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ~ r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( ~ r2_hidden(sK1(X0,X1,X2),X1)
          | ~ r2_hidden(sK1(X0,X1,X2),X0)
          | ~ r2_hidden(sK1(X0,X1,X2),X2) )
        & ( ( r2_hidden(sK1(X0,X1,X2),X1)
            & r2_hidden(sK1(X0,X1,X2),X0) )
          | r2_hidden(sK1(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ( ( ~ r2_hidden(sK1(X0,X1,X2),X1)
            | ~ r2_hidden(sK1(X0,X1,X2),X0)
            | ~ r2_hidden(sK1(X0,X1,X2),X2) )
          & ( ( r2_hidden(sK1(X0,X1,X2),X1)
              & r2_hidden(sK1(X0,X1,X2),X0) )
            | r2_hidden(sK1(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f38,f39])).

fof(f56,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f40])).

fof(f107,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X1)
      | ~ r2_hidden(X4,k3_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f56])).

fof(f16,axiom,(
    ! [X0] : r2_hidden(X0,k1_ordinal1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f75,plain,(
    ! [X0] : r2_hidden(X0,k1_ordinal1(X0)) ),
    inference(cnf_transformation,[],[f16])).

fof(f99,plain,(
    ! [X0] : r2_hidden(X0,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)))) ),
    inference(definition_unfolding,[],[f75,f90])).

cnf(c_25,negated_conjecture,
    ( v3_ordinal1(sK2) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_24,negated_conjecture,
    ( v3_ordinal1(sK3) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_20,plain,
    ( ~ v3_ordinal1(X0)
    | v3_ordinal1(k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)))) ),
    inference(cnf_transformation,[],[f100])).

cnf(c_34,plain,
    ( v3_ordinal1(k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))))
    | ~ v3_ordinal1(sK2) ),
    inference(instantiation,[status(thm)],[c_20])).

cnf(c_17,plain,
    ( ~ r1_ordinal1(X0,X1)
    | r1_tarski(X0,X1)
    | ~ v3_ordinal1(X1)
    | ~ v3_ordinal1(X0) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_23,negated_conjecture,
    ( r1_ordinal1(k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))),sK3)
    | r2_hidden(sK2,sK3) ),
    inference(cnf_transformation,[],[f102])).

cnf(c_210,plain,
    ( r2_hidden(sK2,sK3)
    | r1_ordinal1(k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))),sK3) ),
    inference(prop_impl,[status(thm)],[c_23])).

cnf(c_211,plain,
    ( r1_ordinal1(k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))),sK3)
    | r2_hidden(sK2,sK3) ),
    inference(renaming,[status(thm)],[c_210])).

cnf(c_393,plain,
    ( r1_tarski(X0,X1)
    | r2_hidden(sK2,sK3)
    | ~ v3_ordinal1(X0)
    | ~ v3_ordinal1(X1)
    | k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))) != X0
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_17,c_211])).

cnf(c_394,plain,
    ( r1_tarski(k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))),sK3)
    | r2_hidden(sK2,sK3)
    | ~ v3_ordinal1(k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))))
    | ~ v3_ordinal1(sK3) ),
    inference(unflattening,[status(thm)],[c_393])).

cnf(c_647,plain,
    ( r2_hidden(sK2,sK3)
    | r1_tarski(k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))),sK3) ),
    inference(prop_impl,[status(thm)],[c_25,c_24,c_34,c_394])).

cnf(c_648,plain,
    ( r1_tarski(k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))),sK3)
    | r2_hidden(sK2,sK3) ),
    inference(renaming,[status(thm)],[c_647])).

cnf(c_1479,plain,
    ( r1_tarski(k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))),sK3) = iProver_top
    | r2_hidden(sK2,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_648])).

cnf(c_13,plain,
    ( ~ r1_tarski(X0,X1)
    | k3_xboole_0(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f61])).

cnf(c_1490,plain,
    ( k3_xboole_0(X0,X1) = X0
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_1824,plain,
    ( k3_xboole_0(k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))),sK3) = k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)))
    | r2_hidden(sK2,sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_1479,c_1490])).

cnf(c_396,plain,
    ( r1_tarski(k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))),sK3)
    | r2_hidden(sK2,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_394,c_25,c_24,c_34])).

cnf(c_491,plain,
    ( r2_hidden(sK2,sK3)
    | k3_xboole_0(X0,X1) = X0
    | k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))) != X0
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_396])).

cnf(c_492,plain,
    ( r2_hidden(sK2,sK3)
    | k3_xboole_0(k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))),sK3) = k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))) ),
    inference(unflattening,[status(thm)],[c_491])).

cnf(c_493,plain,
    ( k3_xboole_0(k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))),sK3) = k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)))
    | r2_hidden(sK2,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_492])).

cnf(c_19,plain,
    ( r1_ordinal1(X0,X1)
    | r2_hidden(X1,X0)
    | ~ v3_ordinal1(X1)
    | ~ v3_ordinal1(X0) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_22,negated_conjecture,
    ( ~ r1_ordinal1(k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))),sK3)
    | ~ r2_hidden(sK2,sK3) ),
    inference(cnf_transformation,[],[f101])).

cnf(c_208,plain,
    ( ~ r2_hidden(sK2,sK3)
    | ~ r1_ordinal1(k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))),sK3) ),
    inference(prop_impl,[status(thm)],[c_22])).

cnf(c_209,plain,
    ( ~ r1_ordinal1(k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))),sK3)
    | ~ r2_hidden(sK2,sK3) ),
    inference(renaming,[status(thm)],[c_208])).

cnf(c_365,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(sK2,sK3)
    | ~ v3_ordinal1(X1)
    | ~ v3_ordinal1(X0)
    | k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))) != X1
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_19,c_209])).

cnf(c_366,plain,
    ( r2_hidden(sK3,k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))))
    | ~ r2_hidden(sK2,sK3)
    | ~ v3_ordinal1(k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))))
    | ~ v3_ordinal1(sK3) ),
    inference(unflattening,[status(thm)],[c_365])).

cnf(c_368,plain,
    ( r2_hidden(sK3,k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))))
    | ~ r2_hidden(sK2,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_366,c_25,c_24,c_34])).

cnf(c_1481,plain,
    ( r2_hidden(sK3,k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)))) = iProver_top
    | r2_hidden(sK2,sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_368])).

cnf(c_6,plain,
    ( r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | ~ r2_hidden(X0,k3_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X1))) ),
    inference(cnf_transformation,[],[f105])).

cnf(c_1497,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r2_hidden(X0,X2) = iProver_top
    | r2_hidden(X0,k3_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_4390,plain,
    ( r2_hidden(sK3,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)) = iProver_top
    | r2_hidden(sK3,sK2) = iProver_top
    | r2_hidden(sK2,sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1481,c_1497])).

cnf(c_5,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))) ),
    inference(cnf_transformation,[],[f104])).

cnf(c_1498,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_21,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r2_hidden(X1,X0) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_1485,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r2_hidden(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_1823,plain,
    ( r2_hidden(sK3,k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)))) != iProver_top
    | r2_hidden(sK2,sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_1479,c_1485])).

cnf(c_4412,plain,
    ( r2_hidden(sK3,sK2) != iProver_top
    | r2_hidden(sK2,sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_1498,c_1823])).

cnf(c_0,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X1,X0) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_1675,plain,
    ( ~ r2_hidden(sK3,sK2)
    | ~ r2_hidden(sK2,sK3) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_1676,plain,
    ( r2_hidden(sK3,sK2) != iProver_top
    | r2_hidden(sK2,sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1675])).

cnf(c_4683,plain,
    ( r2_hidden(sK3,sK2) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4412,c_1676])).

cnf(c_4,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,k3_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X1))) ),
    inference(cnf_transformation,[],[f103])).

cnf(c_1499,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,k3_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_4411,plain,
    ( r2_hidden(sK3,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)) != iProver_top
    | r2_hidden(sK2,sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_1499,c_1823])).

cnf(c_14,plain,
    ( r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1)
    | ~ r2_hidden(X0,X1) ),
    inference(cnf_transformation,[],[f97])).

cnf(c_1489,plain,
    ( r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1) = iProver_top
    | r2_hidden(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_1838,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X1,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1489,c_1485])).

cnf(c_4691,plain,
    ( r2_hidden(sK3,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_4411,c_1838])).

cnf(c_8434,plain,
    ( k3_xboole_0(k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))),sK3) = k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1824,c_493,c_1676,c_4390,c_4412,c_4691])).

cnf(c_11,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k3_xboole_0(X2,X1)) ),
    inference(cnf_transformation,[],[f107])).

cnf(c_1492,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r2_hidden(X0,k3_xboole_0(X2,X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_8440,plain,
    ( r2_hidden(X0,k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)))) != iProver_top
    | r2_hidden(X0,sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_8434,c_1492])).

cnf(c_8457,plain,
    ( r2_hidden(sK2,k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)))) != iProver_top
    | r2_hidden(sK2,sK3) = iProver_top ),
    inference(instantiation,[status(thm)],[c_8440])).

cnf(c_18,plain,
    ( r2_hidden(X0,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)))) ),
    inference(cnf_transformation,[],[f99])).

cnf(c_39,plain,
    ( r2_hidden(X0,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_41,plain,
    ( r2_hidden(sK2,k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)))) = iProver_top ),
    inference(instantiation,[status(thm)],[c_39])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_8457,c_4691,c_4683,c_4390,c_41])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : iproveropt_run.sh %d %s
% 0.14/0.34  % Computer   : n024.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 17:11:06 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running in FOF mode
% 3.39/1.00  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.39/1.00  
% 3.39/1.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.39/1.00  
% 3.39/1.00  ------  iProver source info
% 3.39/1.00  
% 3.39/1.00  git: date: 2020-06-30 10:37:57 +0100
% 3.39/1.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.39/1.00  git: non_committed_changes: false
% 3.39/1.00  git: last_make_outside_of_git: false
% 3.39/1.00  
% 3.39/1.00  ------ 
% 3.39/1.00  
% 3.39/1.00  ------ Input Options
% 3.39/1.00  
% 3.39/1.00  --out_options                           all
% 3.39/1.00  --tptp_safe_out                         true
% 3.39/1.00  --problem_path                          ""
% 3.39/1.00  --include_path                          ""
% 3.39/1.00  --clausifier                            res/vclausify_rel
% 3.39/1.00  --clausifier_options                    --mode clausify
% 3.39/1.00  --stdin                                 false
% 3.39/1.00  --stats_out                             all
% 3.39/1.00  
% 3.39/1.00  ------ General Options
% 3.39/1.00  
% 3.39/1.00  --fof                                   false
% 3.39/1.00  --time_out_real                         305.
% 3.39/1.00  --time_out_virtual                      -1.
% 3.39/1.00  --symbol_type_check                     false
% 3.39/1.00  --clausify_out                          false
% 3.39/1.00  --sig_cnt_out                           false
% 3.39/1.00  --trig_cnt_out                          false
% 3.39/1.00  --trig_cnt_out_tolerance                1.
% 3.39/1.00  --trig_cnt_out_sk_spl                   false
% 3.39/1.00  --abstr_cl_out                          false
% 3.39/1.00  
% 3.39/1.00  ------ Global Options
% 3.39/1.00  
% 3.39/1.00  --schedule                              default
% 3.39/1.00  --add_important_lit                     false
% 3.39/1.00  --prop_solver_per_cl                    1000
% 3.39/1.00  --min_unsat_core                        false
% 3.39/1.00  --soft_assumptions                      false
% 3.39/1.00  --soft_lemma_size                       3
% 3.39/1.00  --prop_impl_unit_size                   0
% 3.39/1.00  --prop_impl_unit                        []
% 3.39/1.00  --share_sel_clauses                     true
% 3.39/1.00  --reset_solvers                         false
% 3.39/1.00  --bc_imp_inh                            [conj_cone]
% 3.39/1.00  --conj_cone_tolerance                   3.
% 3.39/1.00  --extra_neg_conj                        none
% 3.39/1.00  --large_theory_mode                     true
% 3.39/1.00  --prolific_symb_bound                   200
% 3.39/1.00  --lt_threshold                          2000
% 3.39/1.00  --clause_weak_htbl                      true
% 3.39/1.00  --gc_record_bc_elim                     false
% 3.39/1.00  
% 3.39/1.00  ------ Preprocessing Options
% 3.39/1.00  
% 3.39/1.00  --preprocessing_flag                    true
% 3.39/1.00  --time_out_prep_mult                    0.1
% 3.39/1.00  --splitting_mode                        input
% 3.39/1.00  --splitting_grd                         true
% 3.39/1.00  --splitting_cvd                         false
% 3.39/1.00  --splitting_cvd_svl                     false
% 3.39/1.00  --splitting_nvd                         32
% 3.39/1.00  --sub_typing                            true
% 3.39/1.00  --prep_gs_sim                           true
% 3.39/1.00  --prep_unflatten                        true
% 3.39/1.00  --prep_res_sim                          true
% 3.39/1.00  --prep_upred                            true
% 3.39/1.00  --prep_sem_filter                       exhaustive
% 3.39/1.00  --prep_sem_filter_out                   false
% 3.39/1.00  --pred_elim                             true
% 3.39/1.00  --res_sim_input                         true
% 3.39/1.00  --eq_ax_congr_red                       true
% 3.39/1.00  --pure_diseq_elim                       true
% 3.39/1.00  --brand_transform                       false
% 3.39/1.00  --non_eq_to_eq                          false
% 3.39/1.00  --prep_def_merge                        true
% 3.39/1.00  --prep_def_merge_prop_impl              false
% 3.39/1.00  --prep_def_merge_mbd                    true
% 3.39/1.00  --prep_def_merge_tr_red                 false
% 3.39/1.00  --prep_def_merge_tr_cl                  false
% 3.39/1.00  --smt_preprocessing                     true
% 3.39/1.00  --smt_ac_axioms                         fast
% 3.39/1.00  --preprocessed_out                      false
% 3.39/1.00  --preprocessed_stats                    false
% 3.39/1.00  
% 3.39/1.00  ------ Abstraction refinement Options
% 3.39/1.00  
% 3.39/1.00  --abstr_ref                             []
% 3.39/1.00  --abstr_ref_prep                        false
% 3.39/1.00  --abstr_ref_until_sat                   false
% 3.39/1.00  --abstr_ref_sig_restrict                funpre
% 3.39/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 3.39/1.00  --abstr_ref_under                       []
% 3.39/1.00  
% 3.39/1.00  ------ SAT Options
% 3.39/1.00  
% 3.39/1.00  --sat_mode                              false
% 3.39/1.00  --sat_fm_restart_options                ""
% 3.39/1.00  --sat_gr_def                            false
% 3.39/1.00  --sat_epr_types                         true
% 3.39/1.00  --sat_non_cyclic_types                  false
% 3.39/1.00  --sat_finite_models                     false
% 3.39/1.00  --sat_fm_lemmas                         false
% 3.39/1.00  --sat_fm_prep                           false
% 3.39/1.00  --sat_fm_uc_incr                        true
% 3.39/1.00  --sat_out_model                         small
% 3.39/1.00  --sat_out_clauses                       false
% 3.39/1.00  
% 3.39/1.00  ------ QBF Options
% 3.39/1.00  
% 3.39/1.00  --qbf_mode                              false
% 3.39/1.00  --qbf_elim_univ                         false
% 3.39/1.00  --qbf_dom_inst                          none
% 3.39/1.00  --qbf_dom_pre_inst                      false
% 3.39/1.00  --qbf_sk_in                             false
% 3.39/1.00  --qbf_pred_elim                         true
% 3.39/1.00  --qbf_split                             512
% 3.39/1.00  
% 3.39/1.00  ------ BMC1 Options
% 3.39/1.00  
% 3.39/1.00  --bmc1_incremental                      false
% 3.39/1.00  --bmc1_axioms                           reachable_all
% 3.39/1.00  --bmc1_min_bound                        0
% 3.39/1.00  --bmc1_max_bound                        -1
% 3.39/1.00  --bmc1_max_bound_default                -1
% 3.39/1.00  --bmc1_symbol_reachability              true
% 3.39/1.00  --bmc1_property_lemmas                  false
% 3.39/1.00  --bmc1_k_induction                      false
% 3.39/1.00  --bmc1_non_equiv_states                 false
% 3.39/1.00  --bmc1_deadlock                         false
% 3.39/1.00  --bmc1_ucm                              false
% 3.39/1.00  --bmc1_add_unsat_core                   none
% 3.39/1.00  --bmc1_unsat_core_children              false
% 3.39/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 3.39/1.00  --bmc1_out_stat                         full
% 3.39/1.00  --bmc1_ground_init                      false
% 3.39/1.00  --bmc1_pre_inst_next_state              false
% 3.39/1.00  --bmc1_pre_inst_state                   false
% 3.39/1.00  --bmc1_pre_inst_reach_state             false
% 3.39/1.00  --bmc1_out_unsat_core                   false
% 3.39/1.00  --bmc1_aig_witness_out                  false
% 3.39/1.00  --bmc1_verbose                          false
% 3.39/1.00  --bmc1_dump_clauses_tptp                false
% 3.39/1.00  --bmc1_dump_unsat_core_tptp             false
% 3.39/1.00  --bmc1_dump_file                        -
% 3.39/1.00  --bmc1_ucm_expand_uc_limit              128
% 3.39/1.00  --bmc1_ucm_n_expand_iterations          6
% 3.39/1.00  --bmc1_ucm_extend_mode                  1
% 3.39/1.00  --bmc1_ucm_init_mode                    2
% 3.39/1.00  --bmc1_ucm_cone_mode                    none
% 3.39/1.00  --bmc1_ucm_reduced_relation_type        0
% 3.39/1.00  --bmc1_ucm_relax_model                  4
% 3.39/1.00  --bmc1_ucm_full_tr_after_sat            true
% 3.39/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 3.39/1.00  --bmc1_ucm_layered_model                none
% 3.39/1.00  --bmc1_ucm_max_lemma_size               10
% 3.39/1.00  
% 3.39/1.00  ------ AIG Options
% 3.39/1.00  
% 3.39/1.00  --aig_mode                              false
% 3.39/1.00  
% 3.39/1.00  ------ Instantiation Options
% 3.39/1.00  
% 3.39/1.00  --instantiation_flag                    true
% 3.39/1.00  --inst_sos_flag                         false
% 3.39/1.00  --inst_sos_phase                        true
% 3.39/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.39/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.39/1.00  --inst_lit_sel_side                     num_symb
% 3.39/1.00  --inst_solver_per_active                1400
% 3.39/1.00  --inst_solver_calls_frac                1.
% 3.39/1.00  --inst_passive_queue_type               priority_queues
% 3.39/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.39/1.00  --inst_passive_queues_freq              [25;2]
% 3.39/1.00  --inst_dismatching                      true
% 3.39/1.00  --inst_eager_unprocessed_to_passive     true
% 3.39/1.00  --inst_prop_sim_given                   true
% 3.39/1.00  --inst_prop_sim_new                     false
% 3.39/1.00  --inst_subs_new                         false
% 3.39/1.00  --inst_eq_res_simp                      false
% 3.39/1.00  --inst_subs_given                       false
% 3.39/1.00  --inst_orphan_elimination               true
% 3.39/1.00  --inst_learning_loop_flag               true
% 3.39/1.00  --inst_learning_start                   3000
% 3.39/1.00  --inst_learning_factor                  2
% 3.39/1.00  --inst_start_prop_sim_after_learn       3
% 3.39/1.00  --inst_sel_renew                        solver
% 3.39/1.00  --inst_lit_activity_flag                true
% 3.39/1.00  --inst_restr_to_given                   false
% 3.39/1.00  --inst_activity_threshold               500
% 3.39/1.00  --inst_out_proof                        true
% 3.39/1.00  
% 3.39/1.00  ------ Resolution Options
% 3.39/1.00  
% 3.39/1.00  --resolution_flag                       true
% 3.39/1.00  --res_lit_sel                           adaptive
% 3.39/1.00  --res_lit_sel_side                      none
% 3.39/1.00  --res_ordering                          kbo
% 3.39/1.00  --res_to_prop_solver                    active
% 3.39/1.00  --res_prop_simpl_new                    false
% 3.39/1.00  --res_prop_simpl_given                  true
% 3.39/1.00  --res_passive_queue_type                priority_queues
% 3.39/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.39/1.00  --res_passive_queues_freq               [15;5]
% 3.39/1.00  --res_forward_subs                      full
% 3.39/1.00  --res_backward_subs                     full
% 3.39/1.00  --res_forward_subs_resolution           true
% 3.39/1.00  --res_backward_subs_resolution          true
% 3.39/1.00  --res_orphan_elimination                true
% 3.39/1.00  --res_time_limit                        2.
% 3.39/1.00  --res_out_proof                         true
% 3.39/1.00  
% 3.39/1.00  ------ Superposition Options
% 3.39/1.00  
% 3.39/1.00  --superposition_flag                    true
% 3.39/1.00  --sup_passive_queue_type                priority_queues
% 3.39/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.39/1.00  --sup_passive_queues_freq               [8;1;4]
% 3.39/1.00  --demod_completeness_check              fast
% 3.39/1.00  --demod_use_ground                      true
% 3.39/1.00  --sup_to_prop_solver                    passive
% 3.39/1.00  --sup_prop_simpl_new                    true
% 3.39/1.00  --sup_prop_simpl_given                  true
% 3.39/1.00  --sup_fun_splitting                     false
% 3.39/1.00  --sup_smt_interval                      50000
% 3.39/1.00  
% 3.39/1.00  ------ Superposition Simplification Setup
% 3.39/1.00  
% 3.39/1.00  --sup_indices_passive                   []
% 3.39/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.39/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.39/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.39/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 3.39/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.39/1.00  --sup_full_bw                           [BwDemod]
% 3.39/1.00  --sup_immed_triv                        [TrivRules]
% 3.39/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.39/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.39/1.00  --sup_immed_bw_main                     []
% 3.39/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.39/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 3.39/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.39/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.39/1.00  
% 3.39/1.00  ------ Combination Options
% 3.39/1.00  
% 3.39/1.00  --comb_res_mult                         3
% 3.39/1.00  --comb_sup_mult                         2
% 3.39/1.00  --comb_inst_mult                        10
% 3.39/1.00  
% 3.39/1.00  ------ Debug Options
% 3.39/1.00  
% 3.39/1.00  --dbg_backtrace                         false
% 3.39/1.00  --dbg_dump_prop_clauses                 false
% 3.39/1.00  --dbg_dump_prop_clauses_file            -
% 3.39/1.00  --dbg_out_stat                          false
% 3.39/1.00  ------ Parsing...
% 3.39/1.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.39/1.00  
% 3.39/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 3.39/1.00  
% 3.39/1.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.39/1.00  
% 3.39/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.39/1.00  ------ Proving...
% 3.39/1.00  ------ Problem Properties 
% 3.39/1.00  
% 3.39/1.00  
% 3.39/1.00  clauses                                 25
% 3.39/1.00  conjectures                             2
% 3.39/1.00  EPR                                     5
% 3.39/1.00  Horn                                    19
% 3.39/1.00  unary                                   3
% 3.39/1.00  binary                                  13
% 3.39/1.00  lits                                    59
% 3.39/1.00  lits eq                                 7
% 3.39/1.00  fd_pure                                 0
% 3.39/1.00  fd_pseudo                               0
% 3.39/1.00  fd_cond                                 0
% 3.39/1.00  fd_pseudo_cond                          6
% 3.39/1.00  AC symbols                              0
% 3.39/1.00  
% 3.39/1.00  ------ Schedule dynamic 5 is on 
% 3.39/1.00  
% 3.39/1.00  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.39/1.00  
% 3.39/1.00  
% 3.39/1.00  ------ 
% 3.39/1.00  Current options:
% 3.39/1.00  ------ 
% 3.39/1.00  
% 3.39/1.00  ------ Input Options
% 3.39/1.00  
% 3.39/1.00  --out_options                           all
% 3.39/1.00  --tptp_safe_out                         true
% 3.39/1.00  --problem_path                          ""
% 3.39/1.00  --include_path                          ""
% 3.39/1.00  --clausifier                            res/vclausify_rel
% 3.39/1.00  --clausifier_options                    --mode clausify
% 3.39/1.00  --stdin                                 false
% 3.39/1.00  --stats_out                             all
% 3.39/1.00  
% 3.39/1.00  ------ General Options
% 3.39/1.00  
% 3.39/1.00  --fof                                   false
% 3.39/1.00  --time_out_real                         305.
% 3.39/1.00  --time_out_virtual                      -1.
% 3.39/1.00  --symbol_type_check                     false
% 3.39/1.00  --clausify_out                          false
% 3.39/1.00  --sig_cnt_out                           false
% 3.39/1.00  --trig_cnt_out                          false
% 3.39/1.00  --trig_cnt_out_tolerance                1.
% 3.39/1.00  --trig_cnt_out_sk_spl                   false
% 3.39/1.00  --abstr_cl_out                          false
% 3.39/1.00  
% 3.39/1.00  ------ Global Options
% 3.39/1.00  
% 3.39/1.00  --schedule                              default
% 3.39/1.00  --add_important_lit                     false
% 3.39/1.00  --prop_solver_per_cl                    1000
% 3.39/1.00  --min_unsat_core                        false
% 3.39/1.00  --soft_assumptions                      false
% 3.39/1.00  --soft_lemma_size                       3
% 3.39/1.00  --prop_impl_unit_size                   0
% 3.39/1.00  --prop_impl_unit                        []
% 3.39/1.00  --share_sel_clauses                     true
% 3.39/1.00  --reset_solvers                         false
% 3.39/1.00  --bc_imp_inh                            [conj_cone]
% 3.39/1.00  --conj_cone_tolerance                   3.
% 3.39/1.00  --extra_neg_conj                        none
% 3.39/1.00  --large_theory_mode                     true
% 3.39/1.00  --prolific_symb_bound                   200
% 3.39/1.00  --lt_threshold                          2000
% 3.39/1.00  --clause_weak_htbl                      true
% 3.39/1.00  --gc_record_bc_elim                     false
% 3.39/1.00  
% 3.39/1.00  ------ Preprocessing Options
% 3.39/1.00  
% 3.39/1.00  --preprocessing_flag                    true
% 3.39/1.00  --time_out_prep_mult                    0.1
% 3.39/1.00  --splitting_mode                        input
% 3.39/1.00  --splitting_grd                         true
% 3.39/1.00  --splitting_cvd                         false
% 3.39/1.00  --splitting_cvd_svl                     false
% 3.39/1.00  --splitting_nvd                         32
% 3.39/1.00  --sub_typing                            true
% 3.39/1.00  --prep_gs_sim                           true
% 3.39/1.00  --prep_unflatten                        true
% 3.39/1.00  --prep_res_sim                          true
% 3.39/1.00  --prep_upred                            true
% 3.39/1.00  --prep_sem_filter                       exhaustive
% 3.39/1.00  --prep_sem_filter_out                   false
% 3.39/1.00  --pred_elim                             true
% 3.39/1.00  --res_sim_input                         true
% 3.39/1.00  --eq_ax_congr_red                       true
% 3.39/1.00  --pure_diseq_elim                       true
% 3.39/1.00  --brand_transform                       false
% 3.39/1.00  --non_eq_to_eq                          false
% 3.39/1.00  --prep_def_merge                        true
% 3.39/1.00  --prep_def_merge_prop_impl              false
% 3.39/1.00  --prep_def_merge_mbd                    true
% 3.39/1.00  --prep_def_merge_tr_red                 false
% 3.39/1.00  --prep_def_merge_tr_cl                  false
% 3.39/1.00  --smt_preprocessing                     true
% 3.39/1.00  --smt_ac_axioms                         fast
% 3.39/1.00  --preprocessed_out                      false
% 3.39/1.00  --preprocessed_stats                    false
% 3.39/1.00  
% 3.39/1.00  ------ Abstraction refinement Options
% 3.39/1.00  
% 3.39/1.00  --abstr_ref                             []
% 3.39/1.00  --abstr_ref_prep                        false
% 3.39/1.00  --abstr_ref_until_sat                   false
% 3.39/1.00  --abstr_ref_sig_restrict                funpre
% 3.39/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 3.39/1.00  --abstr_ref_under                       []
% 3.39/1.00  
% 3.39/1.00  ------ SAT Options
% 3.39/1.00  
% 3.39/1.00  --sat_mode                              false
% 3.39/1.00  --sat_fm_restart_options                ""
% 3.39/1.00  --sat_gr_def                            false
% 3.39/1.00  --sat_epr_types                         true
% 3.39/1.00  --sat_non_cyclic_types                  false
% 3.39/1.00  --sat_finite_models                     false
% 3.39/1.00  --sat_fm_lemmas                         false
% 3.39/1.00  --sat_fm_prep                           false
% 3.39/1.00  --sat_fm_uc_incr                        true
% 3.39/1.00  --sat_out_model                         small
% 3.39/1.00  --sat_out_clauses                       false
% 3.39/1.00  
% 3.39/1.00  ------ QBF Options
% 3.39/1.00  
% 3.39/1.00  --qbf_mode                              false
% 3.39/1.00  --qbf_elim_univ                         false
% 3.39/1.00  --qbf_dom_inst                          none
% 3.39/1.00  --qbf_dom_pre_inst                      false
% 3.39/1.00  --qbf_sk_in                             false
% 3.39/1.00  --qbf_pred_elim                         true
% 3.39/1.00  --qbf_split                             512
% 3.39/1.00  
% 3.39/1.00  ------ BMC1 Options
% 3.39/1.00  
% 3.39/1.00  --bmc1_incremental                      false
% 3.39/1.00  --bmc1_axioms                           reachable_all
% 3.39/1.00  --bmc1_min_bound                        0
% 3.39/1.00  --bmc1_max_bound                        -1
% 3.39/1.00  --bmc1_max_bound_default                -1
% 3.39/1.00  --bmc1_symbol_reachability              true
% 3.39/1.00  --bmc1_property_lemmas                  false
% 3.39/1.00  --bmc1_k_induction                      false
% 3.39/1.00  --bmc1_non_equiv_states                 false
% 3.39/1.00  --bmc1_deadlock                         false
% 3.39/1.00  --bmc1_ucm                              false
% 3.39/1.00  --bmc1_add_unsat_core                   none
% 3.39/1.00  --bmc1_unsat_core_children              false
% 3.39/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 3.39/1.00  --bmc1_out_stat                         full
% 3.39/1.00  --bmc1_ground_init                      false
% 3.39/1.00  --bmc1_pre_inst_next_state              false
% 3.39/1.00  --bmc1_pre_inst_state                   false
% 3.39/1.00  --bmc1_pre_inst_reach_state             false
% 3.39/1.00  --bmc1_out_unsat_core                   false
% 3.39/1.00  --bmc1_aig_witness_out                  false
% 3.39/1.00  --bmc1_verbose                          false
% 3.39/1.00  --bmc1_dump_clauses_tptp                false
% 3.39/1.00  --bmc1_dump_unsat_core_tptp             false
% 3.39/1.00  --bmc1_dump_file                        -
% 3.39/1.00  --bmc1_ucm_expand_uc_limit              128
% 3.39/1.00  --bmc1_ucm_n_expand_iterations          6
% 3.39/1.00  --bmc1_ucm_extend_mode                  1
% 3.39/1.00  --bmc1_ucm_init_mode                    2
% 3.39/1.00  --bmc1_ucm_cone_mode                    none
% 3.39/1.00  --bmc1_ucm_reduced_relation_type        0
% 3.39/1.00  --bmc1_ucm_relax_model                  4
% 3.39/1.00  --bmc1_ucm_full_tr_after_sat            true
% 3.39/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 3.39/1.00  --bmc1_ucm_layered_model                none
% 3.39/1.00  --bmc1_ucm_max_lemma_size               10
% 3.39/1.00  
% 3.39/1.00  ------ AIG Options
% 3.39/1.00  
% 3.39/1.00  --aig_mode                              false
% 3.39/1.00  
% 3.39/1.00  ------ Instantiation Options
% 3.39/1.00  
% 3.39/1.00  --instantiation_flag                    true
% 3.39/1.00  --inst_sos_flag                         false
% 3.39/1.00  --inst_sos_phase                        true
% 3.39/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.39/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.39/1.00  --inst_lit_sel_side                     none
% 3.39/1.00  --inst_solver_per_active                1400
% 3.39/1.00  --inst_solver_calls_frac                1.
% 3.39/1.00  --inst_passive_queue_type               priority_queues
% 3.39/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.39/1.00  --inst_passive_queues_freq              [25;2]
% 3.39/1.00  --inst_dismatching                      true
% 3.39/1.00  --inst_eager_unprocessed_to_passive     true
% 3.39/1.00  --inst_prop_sim_given                   true
% 3.39/1.00  --inst_prop_sim_new                     false
% 3.39/1.00  --inst_subs_new                         false
% 3.39/1.00  --inst_eq_res_simp                      false
% 3.39/1.00  --inst_subs_given                       false
% 3.39/1.00  --inst_orphan_elimination               true
% 3.39/1.00  --inst_learning_loop_flag               true
% 3.39/1.00  --inst_learning_start                   3000
% 3.39/1.00  --inst_learning_factor                  2
% 3.39/1.00  --inst_start_prop_sim_after_learn       3
% 3.39/1.00  --inst_sel_renew                        solver
% 3.39/1.00  --inst_lit_activity_flag                true
% 3.39/1.00  --inst_restr_to_given                   false
% 3.39/1.00  --inst_activity_threshold               500
% 3.39/1.00  --inst_out_proof                        true
% 3.39/1.00  
% 3.39/1.00  ------ Resolution Options
% 3.39/1.00  
% 3.39/1.00  --resolution_flag                       false
% 3.39/1.00  --res_lit_sel                           adaptive
% 3.39/1.00  --res_lit_sel_side                      none
% 3.39/1.00  --res_ordering                          kbo
% 3.39/1.00  --res_to_prop_solver                    active
% 3.39/1.00  --res_prop_simpl_new                    false
% 3.39/1.00  --res_prop_simpl_given                  true
% 3.39/1.00  --res_passive_queue_type                priority_queues
% 3.39/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.39/1.00  --res_passive_queues_freq               [15;5]
% 3.39/1.00  --res_forward_subs                      full
% 3.39/1.00  --res_backward_subs                     full
% 3.39/1.00  --res_forward_subs_resolution           true
% 3.39/1.00  --res_backward_subs_resolution          true
% 3.39/1.00  --res_orphan_elimination                true
% 3.39/1.00  --res_time_limit                        2.
% 3.39/1.00  --res_out_proof                         true
% 3.39/1.00  
% 3.39/1.00  ------ Superposition Options
% 3.39/1.00  
% 3.39/1.00  --superposition_flag                    true
% 3.39/1.00  --sup_passive_queue_type                priority_queues
% 3.39/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.39/1.00  --sup_passive_queues_freq               [8;1;4]
% 3.39/1.00  --demod_completeness_check              fast
% 3.39/1.00  --demod_use_ground                      true
% 3.39/1.00  --sup_to_prop_solver                    passive
% 3.39/1.00  --sup_prop_simpl_new                    true
% 3.39/1.00  --sup_prop_simpl_given                  true
% 3.39/1.00  --sup_fun_splitting                     false
% 3.39/1.00  --sup_smt_interval                      50000
% 3.39/1.00  
% 3.39/1.00  ------ Superposition Simplification Setup
% 3.39/1.00  
% 3.39/1.00  --sup_indices_passive                   []
% 3.39/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.39/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.39/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.39/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 3.39/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.39/1.00  --sup_full_bw                           [BwDemod]
% 3.39/1.00  --sup_immed_triv                        [TrivRules]
% 3.39/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.39/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.39/1.00  --sup_immed_bw_main                     []
% 3.39/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.39/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 3.39/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.39/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.39/1.00  
% 3.39/1.00  ------ Combination Options
% 3.39/1.00  
% 3.39/1.00  --comb_res_mult                         3
% 3.39/1.00  --comb_sup_mult                         2
% 3.39/1.00  --comb_inst_mult                        10
% 3.39/1.00  
% 3.39/1.00  ------ Debug Options
% 3.39/1.00  
% 3.39/1.00  --dbg_backtrace                         false
% 3.39/1.00  --dbg_dump_prop_clauses                 false
% 3.39/1.00  --dbg_dump_prop_clauses_file            -
% 3.39/1.00  --dbg_out_stat                          false
% 3.39/1.00  
% 3.39/1.00  
% 3.39/1.00  
% 3.39/1.00  
% 3.39/1.00  ------ Proving...
% 3.39/1.00  
% 3.39/1.00  
% 3.39/1.00  % SZS status Theorem for theBenchmark.p
% 3.39/1.00  
% 3.39/1.00  % SZS output start CNFRefutation for theBenchmark.p
% 3.39/1.00  
% 3.39/1.00  fof(f20,conjecture,(
% 3.39/1.00    ! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => (r2_hidden(X0,X1) <=> r1_ordinal1(k1_ordinal1(X0),X1))))),
% 3.39/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.39/1.00  
% 3.39/1.00  fof(f21,negated_conjecture,(
% 3.39/1.00    ~! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => (r2_hidden(X0,X1) <=> r1_ordinal1(k1_ordinal1(X0),X1))))),
% 3.39/1.00    inference(negated_conjecture,[],[f20])).
% 3.39/1.00  
% 3.39/1.00  fof(f30,plain,(
% 3.39/1.00    ? [X0] : (? [X1] : ((r2_hidden(X0,X1) <~> r1_ordinal1(k1_ordinal1(X0),X1)) & v3_ordinal1(X1)) & v3_ordinal1(X0))),
% 3.39/1.00    inference(ennf_transformation,[],[f21])).
% 3.39/1.00  
% 3.39/1.00  fof(f43,plain,(
% 3.39/1.00    ? [X0] : (? [X1] : (((~r1_ordinal1(k1_ordinal1(X0),X1) | ~r2_hidden(X0,X1)) & (r1_ordinal1(k1_ordinal1(X0),X1) | r2_hidden(X0,X1))) & v3_ordinal1(X1)) & v3_ordinal1(X0))),
% 3.39/1.00    inference(nnf_transformation,[],[f30])).
% 3.39/1.00  
% 3.39/1.00  fof(f44,plain,(
% 3.39/1.00    ? [X0] : (? [X1] : ((~r1_ordinal1(k1_ordinal1(X0),X1) | ~r2_hidden(X0,X1)) & (r1_ordinal1(k1_ordinal1(X0),X1) | r2_hidden(X0,X1)) & v3_ordinal1(X1)) & v3_ordinal1(X0))),
% 3.39/1.00    inference(flattening,[],[f43])).
% 3.39/1.00  
% 3.39/1.00  fof(f46,plain,(
% 3.39/1.00    ( ! [X0] : (? [X1] : ((~r1_ordinal1(k1_ordinal1(X0),X1) | ~r2_hidden(X0,X1)) & (r1_ordinal1(k1_ordinal1(X0),X1) | r2_hidden(X0,X1)) & v3_ordinal1(X1)) => ((~r1_ordinal1(k1_ordinal1(X0),sK3) | ~r2_hidden(X0,sK3)) & (r1_ordinal1(k1_ordinal1(X0),sK3) | r2_hidden(X0,sK3)) & v3_ordinal1(sK3))) )),
% 3.39/1.00    introduced(choice_axiom,[])).
% 3.39/1.00  
% 3.39/1.00  fof(f45,plain,(
% 3.39/1.00    ? [X0] : (? [X1] : ((~r1_ordinal1(k1_ordinal1(X0),X1) | ~r2_hidden(X0,X1)) & (r1_ordinal1(k1_ordinal1(X0),X1) | r2_hidden(X0,X1)) & v3_ordinal1(X1)) & v3_ordinal1(X0)) => (? [X1] : ((~r1_ordinal1(k1_ordinal1(sK2),X1) | ~r2_hidden(sK2,X1)) & (r1_ordinal1(k1_ordinal1(sK2),X1) | r2_hidden(sK2,X1)) & v3_ordinal1(X1)) & v3_ordinal1(sK2))),
% 3.39/1.00    introduced(choice_axiom,[])).
% 3.39/1.00  
% 3.39/1.00  fof(f47,plain,(
% 3.39/1.00    ((~r1_ordinal1(k1_ordinal1(sK2),sK3) | ~r2_hidden(sK2,sK3)) & (r1_ordinal1(k1_ordinal1(sK2),sK3) | r2_hidden(sK2,sK3)) & v3_ordinal1(sK3)) & v3_ordinal1(sK2)),
% 3.39/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f44,f46,f45])).
% 3.39/1.00  
% 3.39/1.00  fof(f79,plain,(
% 3.39/1.00    v3_ordinal1(sK2)),
% 3.39/1.00    inference(cnf_transformation,[],[f47])).
% 3.39/1.00  
% 3.39/1.00  fof(f80,plain,(
% 3.39/1.00    v3_ordinal1(sK3)),
% 3.39/1.00    inference(cnf_transformation,[],[f47])).
% 3.39/1.00  
% 3.39/1.00  fof(f18,axiom,(
% 3.39/1.00    ! [X0] : (v3_ordinal1(X0) => v3_ordinal1(k1_ordinal1(X0)))),
% 3.39/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.39/1.00  
% 3.39/1.00  fof(f28,plain,(
% 3.39/1.00    ! [X0] : (v3_ordinal1(k1_ordinal1(X0)) | ~v3_ordinal1(X0))),
% 3.39/1.00    inference(ennf_transformation,[],[f18])).
% 3.39/1.00  
% 3.39/1.00  fof(f77,plain,(
% 3.39/1.00    ( ! [X0] : (v3_ordinal1(k1_ordinal1(X0)) | ~v3_ordinal1(X0)) )),
% 3.39/1.00    inference(cnf_transformation,[],[f28])).
% 3.39/1.00  
% 3.39/1.00  fof(f14,axiom,(
% 3.39/1.00    ! [X0] : k2_xboole_0(X0,k1_tarski(X0)) = k1_ordinal1(X0)),
% 3.39/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.39/1.00  
% 3.39/1.00  fof(f72,plain,(
% 3.39/1.00    ( ! [X0] : (k2_xboole_0(X0,k1_tarski(X0)) = k1_ordinal1(X0)) )),
% 3.39/1.00    inference(cnf_transformation,[],[f14])).
% 3.39/1.00  
% 3.39/1.00  fof(f13,axiom,(
% 3.39/1.00    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 3.39/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.39/1.00  
% 3.39/1.00  fof(f71,plain,(
% 3.39/1.00    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 3.39/1.00    inference(cnf_transformation,[],[f13])).
% 3.39/1.00  
% 3.39/1.00  fof(f88,plain,(
% 3.39/1.00    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) )),
% 3.39/1.00    inference(definition_unfolding,[],[f71,f87])).
% 3.39/1.00  
% 3.39/1.00  fof(f5,axiom,(
% 3.39/1.00    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 3.39/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.39/1.00  
% 3.39/1.00  fof(f62,plain,(
% 3.39/1.00    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 3.39/1.00    inference(cnf_transformation,[],[f5])).
% 3.39/1.00  
% 3.39/1.00  fof(f6,axiom,(
% 3.39/1.00    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 3.39/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.39/1.00  
% 3.39/1.00  fof(f63,plain,(
% 3.39/1.00    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 3.39/1.00    inference(cnf_transformation,[],[f6])).
% 3.39/1.00  
% 3.39/1.00  fof(f7,axiom,(
% 3.39/1.00    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 3.39/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.39/1.00  
% 3.39/1.00  fof(f64,plain,(
% 3.39/1.00    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 3.39/1.00    inference(cnf_transformation,[],[f7])).
% 3.39/1.00  
% 3.39/1.00  fof(f8,axiom,(
% 3.39/1.00    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 3.39/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.39/1.00  
% 3.39/1.00  fof(f65,plain,(
% 3.39/1.00    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 3.39/1.00    inference(cnf_transformation,[],[f8])).
% 3.39/1.00  
% 3.39/1.00  fof(f9,axiom,(
% 3.39/1.00    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)),
% 3.39/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.39/1.00  
% 3.39/1.00  fof(f66,plain,(
% 3.39/1.00    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)) )),
% 3.39/1.00    inference(cnf_transformation,[],[f9])).
% 3.39/1.00  
% 3.39/1.00  fof(f10,axiom,(
% 3.39/1.00    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)),
% 3.39/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.39/1.00  
% 3.39/1.00  fof(f67,plain,(
% 3.39/1.00    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)) )),
% 3.39/1.00    inference(cnf_transformation,[],[f10])).
% 3.39/1.00  
% 3.39/1.00  fof(f11,axiom,(
% 3.39/1.00    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)),
% 3.39/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.39/1.00  
% 3.39/1.00  fof(f68,plain,(
% 3.39/1.00    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)) )),
% 3.39/1.00    inference(cnf_transformation,[],[f11])).
% 3.39/1.00  
% 3.39/1.00  fof(f83,plain,(
% 3.39/1.00    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 3.39/1.00    inference(definition_unfolding,[],[f67,f68])).
% 3.39/1.00  
% 3.39/1.00  fof(f84,plain,(
% 3.39/1.00    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 3.39/1.00    inference(definition_unfolding,[],[f66,f83])).
% 3.39/1.00  
% 3.39/1.00  fof(f85,plain,(
% 3.39/1.00    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 3.39/1.00    inference(definition_unfolding,[],[f65,f84])).
% 3.39/1.00  
% 3.39/1.00  fof(f86,plain,(
% 3.39/1.00    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 3.39/1.00    inference(definition_unfolding,[],[f64,f85])).
% 3.39/1.00  
% 3.39/1.00  fof(f87,plain,(
% 3.39/1.00    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 3.39/1.00    inference(definition_unfolding,[],[f63,f86])).
% 3.39/1.00  
% 3.39/1.00  fof(f89,plain,(
% 3.39/1.00    ( ! [X0] : (k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) )),
% 3.39/1.00    inference(definition_unfolding,[],[f62,f87])).
% 3.39/1.00  
% 3.39/1.00  fof(f90,plain,(
% 3.39/1.00    ( ! [X0] : (k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))) = k1_ordinal1(X0)) )),
% 3.39/1.00    inference(definition_unfolding,[],[f72,f88,f89])).
% 3.39/1.00  
% 3.39/1.00  fof(f100,plain,(
% 3.39/1.00    ( ! [X0] : (v3_ordinal1(k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)))) | ~v3_ordinal1(X0)) )),
% 3.39/1.00    inference(definition_unfolding,[],[f77,f90])).
% 3.39/1.00  
% 3.39/1.00  fof(f15,axiom,(
% 3.39/1.00    ! [X0,X1] : ((v3_ordinal1(X1) & v3_ordinal1(X0)) => (r1_ordinal1(X0,X1) <=> r1_tarski(X0,X1)))),
% 3.39/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.39/1.00  
% 3.39/1.00  fof(f24,plain,(
% 3.39/1.00    ! [X0,X1] : ((r1_ordinal1(X0,X1) <=> r1_tarski(X0,X1)) | (~v3_ordinal1(X1) | ~v3_ordinal1(X0)))),
% 3.39/1.00    inference(ennf_transformation,[],[f15])).
% 3.39/1.00  
% 3.39/1.00  fof(f25,plain,(
% 3.39/1.00    ! [X0,X1] : ((r1_ordinal1(X0,X1) <=> r1_tarski(X0,X1)) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0))),
% 3.39/1.00    inference(flattening,[],[f24])).
% 3.39/1.00  
% 3.39/1.00  fof(f42,plain,(
% 3.39/1.00    ! [X0,X1] : (((r1_ordinal1(X0,X1) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~r1_ordinal1(X0,X1))) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0))),
% 3.39/1.00    inference(nnf_transformation,[],[f25])).
% 3.39/1.00  
% 3.39/1.00  fof(f73,plain,(
% 3.39/1.00    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r1_ordinal1(X0,X1) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0)) )),
% 3.39/1.00    inference(cnf_transformation,[],[f42])).
% 3.39/1.00  
% 3.39/1.00  fof(f81,plain,(
% 3.39/1.00    r1_ordinal1(k1_ordinal1(sK2),sK3) | r2_hidden(sK2,sK3)),
% 3.39/1.00    inference(cnf_transformation,[],[f47])).
% 3.39/1.00  
% 3.39/1.00  fof(f102,plain,(
% 3.39/1.00    r1_ordinal1(k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))),sK3) | r2_hidden(sK2,sK3)),
% 3.39/1.00    inference(definition_unfolding,[],[f81,f90])).
% 3.39/1.00  
% 3.39/1.00  fof(f4,axiom,(
% 3.39/1.00    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 3.39/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.39/1.00  
% 3.39/1.00  fof(f23,plain,(
% 3.39/1.00    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 3.39/1.00    inference(ennf_transformation,[],[f4])).
% 3.39/1.00  
% 3.39/1.00  fof(f61,plain,(
% 3.39/1.00    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 3.39/1.00    inference(cnf_transformation,[],[f23])).
% 3.39/1.00  
% 3.39/1.00  fof(f17,axiom,(
% 3.39/1.00    ! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => (r2_hidden(X1,X0) | r1_ordinal1(X0,X1))))),
% 3.39/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.39/1.00  
% 3.39/1.00  fof(f26,plain,(
% 3.39/1.00    ! [X0] : (! [X1] : ((r2_hidden(X1,X0) | r1_ordinal1(X0,X1)) | ~v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 3.39/1.00    inference(ennf_transformation,[],[f17])).
% 3.39/1.00  
% 3.39/1.00  fof(f27,plain,(
% 3.39/1.00    ! [X0] : (! [X1] : (r2_hidden(X1,X0) | r1_ordinal1(X0,X1) | ~v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 3.39/1.00    inference(flattening,[],[f26])).
% 3.39/1.00  
% 3.39/1.00  fof(f76,plain,(
% 3.39/1.00    ( ! [X0,X1] : (r2_hidden(X1,X0) | r1_ordinal1(X0,X1) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0)) )),
% 3.39/1.00    inference(cnf_transformation,[],[f27])).
% 3.39/1.00  
% 3.39/1.00  fof(f82,plain,(
% 3.39/1.00    ~r1_ordinal1(k1_ordinal1(sK2),sK3) | ~r2_hidden(sK2,sK3)),
% 3.39/1.00    inference(cnf_transformation,[],[f47])).
% 3.39/1.00  
% 3.39/1.00  fof(f101,plain,(
% 3.39/1.00    ~r1_ordinal1(k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))),sK3) | ~r2_hidden(sK2,sK3)),
% 3.39/1.00    inference(definition_unfolding,[],[f82,f90])).
% 3.39/1.00  
% 3.39/1.00  fof(f2,axiom,(
% 3.39/1.00    ! [X0,X1,X2] : (k2_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) | r2_hidden(X3,X0))))),
% 3.39/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.39/1.00  
% 3.39/1.00  fof(f31,plain,(
% 3.39/1.00    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) | r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) & ~r2_hidden(X3,X0))) & ((r2_hidden(X3,X1) | r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k2_xboole_0(X0,X1) != X2))),
% 3.39/1.00    inference(nnf_transformation,[],[f2])).
% 3.39/1.00  
% 3.39/1.00  fof(f32,plain,(
% 3.39/1.00    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) & ~r2_hidden(X3,X0))) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | ~r2_hidden(X3,X2))) | k2_xboole_0(X0,X1) != X2))),
% 3.39/1.00    inference(flattening,[],[f31])).
% 3.39/1.00  
% 3.39/1.00  fof(f33,plain,(
% 3.39/1.00    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (~r2_hidden(X4,X1) & ~r2_hidden(X4,X0))) & (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,X2))) | k2_xboole_0(X0,X1) != X2))),
% 3.39/1.00    inference(rectify,[],[f32])).
% 3.39/1.00  
% 3.39/1.00  fof(f34,plain,(
% 3.39/1.00    ! [X2,X1,X0] : (? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2))) => (((~r2_hidden(sK0(X0,X1,X2),X1) & ~r2_hidden(sK0(X0,X1,X2),X0)) | ~r2_hidden(sK0(X0,X1,X2),X2)) & (r2_hidden(sK0(X0,X1,X2),X1) | r2_hidden(sK0(X0,X1,X2),X0) | r2_hidden(sK0(X0,X1,X2),X2))))),
% 3.39/1.00    introduced(choice_axiom,[])).
% 3.39/1.00  
% 3.39/1.00  fof(f35,plain,(
% 3.39/1.00    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | (((~r2_hidden(sK0(X0,X1,X2),X1) & ~r2_hidden(sK0(X0,X1,X2),X0)) | ~r2_hidden(sK0(X0,X1,X2),X2)) & (r2_hidden(sK0(X0,X1,X2),X1) | r2_hidden(sK0(X0,X1,X2),X0) | r2_hidden(sK0(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (~r2_hidden(X4,X1) & ~r2_hidden(X4,X0))) & (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,X2))) | k2_xboole_0(X0,X1) != X2))),
% 3.39/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f33,f34])).
% 3.39/1.00  
% 3.39/1.00  fof(f49,plain,(
% 3.39/1.00    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,X2) | k2_xboole_0(X0,X1) != X2) )),
% 3.39/1.00    inference(cnf_transformation,[],[f35])).
% 3.39/1.00  
% 3.39/1.00  fof(f96,plain,(
% 3.39/1.00    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,X2) | k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) != X2) )),
% 3.39/1.00    inference(definition_unfolding,[],[f49,f88])).
% 3.39/1.00  
% 3.39/1.00  fof(f105,plain,(
% 3.39/1.00    ( ! [X4,X0,X1] : (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) )),
% 3.39/1.00    inference(equality_resolution,[],[f96])).
% 3.39/1.00  
% 3.39/1.00  fof(f50,plain,(
% 3.39/1.00    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | ~r2_hidden(X4,X0) | k2_xboole_0(X0,X1) != X2) )),
% 3.39/1.00    inference(cnf_transformation,[],[f35])).
% 3.39/1.00  
% 3.39/1.00  fof(f95,plain,(
% 3.39/1.00    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | ~r2_hidden(X4,X0) | k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) != X2) )),
% 3.39/1.00    inference(definition_unfolding,[],[f50,f88])).
% 3.39/1.00  
% 3.39/1.00  fof(f104,plain,(
% 3.39/1.00    ( ! [X4,X0,X1] : (r2_hidden(X4,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) | ~r2_hidden(X4,X0)) )),
% 3.39/1.00    inference(equality_resolution,[],[f95])).
% 3.39/1.00  
% 3.39/1.00  fof(f19,axiom,(
% 3.39/1.00    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 3.39/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.39/1.00  
% 3.39/1.00  fof(f29,plain,(
% 3.39/1.00    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 3.39/1.00    inference(ennf_transformation,[],[f19])).
% 3.39/1.00  
% 3.39/1.00  fof(f78,plain,(
% 3.39/1.00    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1)) )),
% 3.39/1.00    inference(cnf_transformation,[],[f29])).
% 3.39/1.00  
% 3.39/1.00  fof(f1,axiom,(
% 3.39/1.00    ! [X0,X1] : (r2_hidden(X0,X1) => ~r2_hidden(X1,X0))),
% 3.39/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.39/1.00  
% 3.39/1.00  fof(f22,plain,(
% 3.39/1.00    ! [X0,X1] : (~r2_hidden(X1,X0) | ~r2_hidden(X0,X1))),
% 3.39/1.00    inference(ennf_transformation,[],[f1])).
% 3.39/1.00  
% 3.39/1.00  fof(f48,plain,(
% 3.39/1.00    ( ! [X0,X1] : (~r2_hidden(X1,X0) | ~r2_hidden(X0,X1)) )),
% 3.39/1.00    inference(cnf_transformation,[],[f22])).
% 3.39/1.00  
% 3.39/1.00  fof(f51,plain,(
% 3.39/1.00    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | k2_xboole_0(X0,X1) != X2) )),
% 3.39/1.00    inference(cnf_transformation,[],[f35])).
% 3.39/1.00  
% 3.39/1.00  fof(f94,plain,(
% 3.39/1.00    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) != X2) )),
% 3.39/1.00    inference(definition_unfolding,[],[f51,f88])).
% 3.39/1.00  
% 3.39/1.00  fof(f103,plain,(
% 3.39/1.00    ( ! [X4,X0,X1] : (r2_hidden(X4,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) | ~r2_hidden(X4,X1)) )),
% 3.39/1.00    inference(equality_resolution,[],[f94])).
% 3.39/1.00  
% 3.39/1.00  fof(f12,axiom,(
% 3.39/1.00    ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) <=> r2_hidden(X0,X1))),
% 3.39/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.39/1.00  
% 3.39/1.00  fof(f41,plain,(
% 3.39/1.00    ! [X0,X1] : ((r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) & (r2_hidden(X0,X1) | ~r1_tarski(k1_tarski(X0),X1)))),
% 3.39/1.00    inference(nnf_transformation,[],[f12])).
% 3.39/1.00  
% 3.39/1.00  fof(f70,plain,(
% 3.39/1.00    ( ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) )),
% 3.39/1.00    inference(cnf_transformation,[],[f41])).
% 3.39/1.00  
% 3.39/1.00  fof(f97,plain,(
% 3.39/1.00    ( ! [X0,X1] : (r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1) | ~r2_hidden(X0,X1)) )),
% 3.39/1.00    inference(definition_unfolding,[],[f70,f89])).
% 3.39/1.00  
% 3.39/1.00  fof(f3,axiom,(
% 3.39/1.00    ! [X0,X1,X2] : (k3_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 3.39/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.39/1.00  
% 3.39/1.00  fof(f36,plain,(
% 3.39/1.00    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k3_xboole_0(X0,X1) != X2))),
% 3.39/1.00    inference(nnf_transformation,[],[f3])).
% 3.39/1.00  
% 3.39/1.00  fof(f37,plain,(
% 3.39/1.00    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ~r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k3_xboole_0(X0,X1) != X2))),
% 3.39/1.00    inference(flattening,[],[f36])).
% 3.39/1.00  
% 3.39/1.00  fof(f38,plain,(
% 3.39/1.00    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k3_xboole_0(X0,X1) != X2))),
% 3.39/1.00    inference(rectify,[],[f37])).
% 3.39/1.00  
% 3.39/1.00  fof(f39,plain,(
% 3.39/1.00    ! [X2,X1,X0] : (? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((~r2_hidden(sK1(X0,X1,X2),X1) | ~r2_hidden(sK1(X0,X1,X2),X0) | ~r2_hidden(sK1(X0,X1,X2),X2)) & ((r2_hidden(sK1(X0,X1,X2),X1) & r2_hidden(sK1(X0,X1,X2),X0)) | r2_hidden(sK1(X0,X1,X2),X2))))),
% 3.39/1.00    introduced(choice_axiom,[])).
% 3.39/1.00  
% 3.39/1.00  fof(f40,plain,(
% 3.39/1.00    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ((~r2_hidden(sK1(X0,X1,X2),X1) | ~r2_hidden(sK1(X0,X1,X2),X0) | ~r2_hidden(sK1(X0,X1,X2),X2)) & ((r2_hidden(sK1(X0,X1,X2),X1) & r2_hidden(sK1(X0,X1,X2),X0)) | r2_hidden(sK1(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k3_xboole_0(X0,X1) != X2))),
% 3.39/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f38,f39])).
% 3.39/1.00  
% 3.39/1.00  fof(f56,plain,(
% 3.39/1.00    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k3_xboole_0(X0,X1) != X2) )),
% 3.39/1.00    inference(cnf_transformation,[],[f40])).
% 3.39/1.00  
% 3.39/1.00  fof(f107,plain,(
% 3.39/1.00    ( ! [X4,X0,X1] : (r2_hidden(X4,X1) | ~r2_hidden(X4,k3_xboole_0(X0,X1))) )),
% 3.39/1.00    inference(equality_resolution,[],[f56])).
% 3.39/1.00  
% 3.39/1.00  fof(f16,axiom,(
% 3.39/1.00    ! [X0] : r2_hidden(X0,k1_ordinal1(X0))),
% 3.39/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.39/1.00  
% 3.39/1.00  fof(f75,plain,(
% 3.39/1.00    ( ! [X0] : (r2_hidden(X0,k1_ordinal1(X0))) )),
% 3.39/1.00    inference(cnf_transformation,[],[f16])).
% 3.39/1.00  
% 3.39/1.00  fof(f99,plain,(
% 3.39/1.00    ( ! [X0] : (r2_hidden(X0,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))))) )),
% 3.39/1.00    inference(definition_unfolding,[],[f75,f90])).
% 3.39/1.00  
% 3.39/1.00  cnf(c_25,negated_conjecture,
% 3.39/1.00      ( v3_ordinal1(sK2) ),
% 3.39/1.00      inference(cnf_transformation,[],[f79]) ).
% 3.39/1.00  
% 3.39/1.00  cnf(c_24,negated_conjecture,
% 3.39/1.00      ( v3_ordinal1(sK3) ),
% 3.39/1.00      inference(cnf_transformation,[],[f80]) ).
% 3.39/1.00  
% 3.39/1.00  cnf(c_20,plain,
% 3.39/1.00      ( ~ v3_ordinal1(X0)
% 3.39/1.00      | v3_ordinal1(k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)))) ),
% 3.39/1.00      inference(cnf_transformation,[],[f100]) ).
% 3.39/1.00  
% 3.39/1.00  cnf(c_34,plain,
% 3.39/1.00      ( v3_ordinal1(k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))))
% 3.39/1.00      | ~ v3_ordinal1(sK2) ),
% 3.39/1.00      inference(instantiation,[status(thm)],[c_20]) ).
% 3.39/1.00  
% 3.39/1.00  cnf(c_17,plain,
% 3.39/1.00      ( ~ r1_ordinal1(X0,X1)
% 3.39/1.00      | r1_tarski(X0,X1)
% 3.39/1.00      | ~ v3_ordinal1(X1)
% 3.39/1.00      | ~ v3_ordinal1(X0) ),
% 3.39/1.00      inference(cnf_transformation,[],[f73]) ).
% 3.39/1.00  
% 3.39/1.00  cnf(c_23,negated_conjecture,
% 3.39/1.00      ( r1_ordinal1(k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))),sK3)
% 3.39/1.00      | r2_hidden(sK2,sK3) ),
% 3.39/1.00      inference(cnf_transformation,[],[f102]) ).
% 3.39/1.00  
% 3.39/1.00  cnf(c_210,plain,
% 3.39/1.00      ( r2_hidden(sK2,sK3)
% 3.39/1.00      | r1_ordinal1(k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))),sK3) ),
% 3.39/1.00      inference(prop_impl,[status(thm)],[c_23]) ).
% 3.39/1.00  
% 3.39/1.00  cnf(c_211,plain,
% 3.39/1.00      ( r1_ordinal1(k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))),sK3)
% 3.39/1.00      | r2_hidden(sK2,sK3) ),
% 3.39/1.00      inference(renaming,[status(thm)],[c_210]) ).
% 3.39/1.00  
% 3.39/1.00  cnf(c_393,plain,
% 3.39/1.00      ( r1_tarski(X0,X1)
% 3.39/1.00      | r2_hidden(sK2,sK3)
% 3.39/1.00      | ~ v3_ordinal1(X0)
% 3.39/1.00      | ~ v3_ordinal1(X1)
% 3.39/1.00      | k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))) != X0
% 3.39/1.00      | sK3 != X1 ),
% 3.39/1.00      inference(resolution_lifted,[status(thm)],[c_17,c_211]) ).
% 3.39/1.00  
% 3.39/1.00  cnf(c_394,plain,
% 3.39/1.00      ( r1_tarski(k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))),sK3)
% 3.39/1.00      | r2_hidden(sK2,sK3)
% 3.39/1.00      | ~ v3_ordinal1(k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))))
% 3.39/1.00      | ~ v3_ordinal1(sK3) ),
% 3.39/1.00      inference(unflattening,[status(thm)],[c_393]) ).
% 3.39/1.00  
% 3.39/1.00  cnf(c_647,plain,
% 3.39/1.00      ( r2_hidden(sK2,sK3)
% 3.39/1.00      | r1_tarski(k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))),sK3) ),
% 3.39/1.00      inference(prop_impl,[status(thm)],[c_25,c_24,c_34,c_394]) ).
% 3.39/1.00  
% 3.39/1.00  cnf(c_648,plain,
% 3.39/1.00      ( r1_tarski(k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))),sK3)
% 3.39/1.00      | r2_hidden(sK2,sK3) ),
% 3.39/1.00      inference(renaming,[status(thm)],[c_647]) ).
% 3.39/1.00  
% 3.39/1.00  cnf(c_1479,plain,
% 3.39/1.00      ( r1_tarski(k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))),sK3) = iProver_top
% 3.39/1.00      | r2_hidden(sK2,sK3) = iProver_top ),
% 3.39/1.00      inference(predicate_to_equality,[status(thm)],[c_648]) ).
% 3.39/1.00  
% 3.39/1.00  cnf(c_13,plain,
% 3.39/1.00      ( ~ r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0 ),
% 3.39/1.00      inference(cnf_transformation,[],[f61]) ).
% 3.39/1.00  
% 3.39/1.00  cnf(c_1490,plain,
% 3.39/1.00      ( k3_xboole_0(X0,X1) = X0 | r1_tarski(X0,X1) != iProver_top ),
% 3.39/1.00      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 3.39/1.00  
% 3.39/1.00  cnf(c_1824,plain,
% 3.39/1.00      ( k3_xboole_0(k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))),sK3) = k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)))
% 3.39/1.00      | r2_hidden(sK2,sK3) = iProver_top ),
% 3.39/1.00      inference(superposition,[status(thm)],[c_1479,c_1490]) ).
% 3.39/1.00  
% 3.39/1.00  cnf(c_396,plain,
% 3.39/1.00      ( r1_tarski(k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))),sK3)
% 3.39/1.00      | r2_hidden(sK2,sK3) ),
% 3.39/1.00      inference(global_propositional_subsumption,
% 3.39/1.00                [status(thm)],
% 3.39/1.00                [c_394,c_25,c_24,c_34]) ).
% 3.39/1.00  
% 3.39/1.00  cnf(c_491,plain,
% 3.39/1.00      ( r2_hidden(sK2,sK3)
% 3.39/1.00      | k3_xboole_0(X0,X1) = X0
% 3.39/1.00      | k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))) != X0
% 3.39/1.00      | sK3 != X1 ),
% 3.39/1.00      inference(resolution_lifted,[status(thm)],[c_13,c_396]) ).
% 3.39/1.00  
% 3.39/1.00  cnf(c_492,plain,
% 3.39/1.00      ( r2_hidden(sK2,sK3)
% 3.39/1.00      | k3_xboole_0(k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))),sK3) = k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))) ),
% 3.39/1.00      inference(unflattening,[status(thm)],[c_491]) ).
% 3.39/1.00  
% 3.39/1.00  cnf(c_493,plain,
% 3.39/1.00      ( k3_xboole_0(k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))),sK3) = k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)))
% 3.39/1.00      | r2_hidden(sK2,sK3) = iProver_top ),
% 3.39/1.00      inference(predicate_to_equality,[status(thm)],[c_492]) ).
% 3.39/1.00  
% 3.39/1.00  cnf(c_19,plain,
% 3.39/1.00      ( r1_ordinal1(X0,X1)
% 3.39/1.00      | r2_hidden(X1,X0)
% 3.39/1.00      | ~ v3_ordinal1(X1)
% 3.39/1.00      | ~ v3_ordinal1(X0) ),
% 3.39/1.00      inference(cnf_transformation,[],[f76]) ).
% 3.39/1.00  
% 3.39/1.00  cnf(c_22,negated_conjecture,
% 3.39/1.00      ( ~ r1_ordinal1(k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))),sK3)
% 3.39/1.00      | ~ r2_hidden(sK2,sK3) ),
% 3.39/1.00      inference(cnf_transformation,[],[f101]) ).
% 3.39/1.00  
% 3.39/1.00  cnf(c_208,plain,
% 3.39/1.00      ( ~ r2_hidden(sK2,sK3)
% 3.39/1.00      | ~ r1_ordinal1(k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))),sK3) ),
% 3.39/1.00      inference(prop_impl,[status(thm)],[c_22]) ).
% 3.39/1.00  
% 3.39/1.00  cnf(c_209,plain,
% 3.39/1.00      ( ~ r1_ordinal1(k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))),sK3)
% 3.39/1.00      | ~ r2_hidden(sK2,sK3) ),
% 3.39/1.00      inference(renaming,[status(thm)],[c_208]) ).
% 3.39/1.00  
% 3.39/1.00  cnf(c_365,plain,
% 3.39/1.00      ( r2_hidden(X0,X1)
% 3.39/1.00      | ~ r2_hidden(sK2,sK3)
% 3.39/1.00      | ~ v3_ordinal1(X1)
% 3.39/1.00      | ~ v3_ordinal1(X0)
% 3.39/1.00      | k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))) != X1
% 3.39/1.00      | sK3 != X0 ),
% 3.39/1.00      inference(resolution_lifted,[status(thm)],[c_19,c_209]) ).
% 3.39/1.00  
% 3.39/1.00  cnf(c_366,plain,
% 3.39/1.00      ( r2_hidden(sK3,k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))))
% 3.39/1.00      | ~ r2_hidden(sK2,sK3)
% 3.39/1.00      | ~ v3_ordinal1(k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))))
% 3.39/1.00      | ~ v3_ordinal1(sK3) ),
% 3.39/1.00      inference(unflattening,[status(thm)],[c_365]) ).
% 3.39/1.00  
% 3.39/1.00  cnf(c_368,plain,
% 3.39/1.00      ( r2_hidden(sK3,k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))))
% 3.39/1.00      | ~ r2_hidden(sK2,sK3) ),
% 3.39/1.00      inference(global_propositional_subsumption,
% 3.39/1.00                [status(thm)],
% 3.39/1.00                [c_366,c_25,c_24,c_34]) ).
% 3.39/1.00  
% 3.39/1.00  cnf(c_1481,plain,
% 3.39/1.00      ( r2_hidden(sK3,k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)))) = iProver_top
% 3.39/1.00      | r2_hidden(sK2,sK3) != iProver_top ),
% 3.39/1.00      inference(predicate_to_equality,[status(thm)],[c_368]) ).
% 3.39/1.00  
% 3.39/1.00  cnf(c_6,plain,
% 3.39/1.00      ( r2_hidden(X0,X1)
% 3.39/1.00      | r2_hidden(X0,X2)
% 3.39/1.00      | ~ r2_hidden(X0,k3_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X1))) ),
% 3.39/1.00      inference(cnf_transformation,[],[f105]) ).
% 3.39/1.00  
% 3.39/1.00  cnf(c_1497,plain,
% 3.39/1.00      ( r2_hidden(X0,X1) = iProver_top
% 3.39/1.00      | r2_hidden(X0,X2) = iProver_top
% 3.39/1.00      | r2_hidden(X0,k3_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X1))) != iProver_top ),
% 3.39/1.00      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 3.39/1.01  
% 3.39/1.01  cnf(c_4390,plain,
% 3.39/1.01      ( r2_hidden(sK3,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)) = iProver_top
% 3.39/1.01      | r2_hidden(sK3,sK2) = iProver_top
% 3.39/1.01      | r2_hidden(sK2,sK3) != iProver_top ),
% 3.39/1.01      inference(superposition,[status(thm)],[c_1481,c_1497]) ).
% 3.39/1.01  
% 3.39/1.01  cnf(c_5,plain,
% 3.39/1.01      ( ~ r2_hidden(X0,X1)
% 3.39/1.01      | r2_hidden(X0,k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))) ),
% 3.39/1.01      inference(cnf_transformation,[],[f104]) ).
% 3.39/1.01  
% 3.39/1.01  cnf(c_1498,plain,
% 3.39/1.01      ( r2_hidden(X0,X1) != iProver_top
% 3.39/1.01      | r2_hidden(X0,k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))) = iProver_top ),
% 3.39/1.01      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 3.39/1.01  
% 3.39/1.01  cnf(c_21,plain,
% 3.39/1.01      ( ~ r1_tarski(X0,X1) | ~ r2_hidden(X1,X0) ),
% 3.39/1.01      inference(cnf_transformation,[],[f78]) ).
% 3.39/1.01  
% 3.39/1.01  cnf(c_1485,plain,
% 3.39/1.01      ( r1_tarski(X0,X1) != iProver_top
% 3.39/1.01      | r2_hidden(X1,X0) != iProver_top ),
% 3.39/1.01      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 3.39/1.01  
% 3.39/1.01  cnf(c_1823,plain,
% 3.39/1.01      ( r2_hidden(sK3,k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)))) != iProver_top
% 3.39/1.01      | r2_hidden(sK2,sK3) = iProver_top ),
% 3.39/1.01      inference(superposition,[status(thm)],[c_1479,c_1485]) ).
% 3.39/1.01  
% 3.39/1.01  cnf(c_4412,plain,
% 3.39/1.01      ( r2_hidden(sK3,sK2) != iProver_top
% 3.39/1.01      | r2_hidden(sK2,sK3) = iProver_top ),
% 3.39/1.01      inference(superposition,[status(thm)],[c_1498,c_1823]) ).
% 3.39/1.01  
% 3.39/1.01  cnf(c_0,plain,
% 3.39/1.01      ( ~ r2_hidden(X0,X1) | ~ r2_hidden(X1,X0) ),
% 3.39/1.01      inference(cnf_transformation,[],[f48]) ).
% 3.39/1.01  
% 3.39/1.01  cnf(c_1675,plain,
% 3.39/1.01      ( ~ r2_hidden(sK3,sK2) | ~ r2_hidden(sK2,sK3) ),
% 3.39/1.01      inference(instantiation,[status(thm)],[c_0]) ).
% 3.39/1.01  
% 3.39/1.01  cnf(c_1676,plain,
% 3.39/1.01      ( r2_hidden(sK3,sK2) != iProver_top
% 3.39/1.01      | r2_hidden(sK2,sK3) != iProver_top ),
% 3.39/1.01      inference(predicate_to_equality,[status(thm)],[c_1675]) ).
% 3.39/1.01  
% 3.39/1.01  cnf(c_4683,plain,
% 3.39/1.01      ( r2_hidden(sK3,sK2) != iProver_top ),
% 3.39/1.01      inference(global_propositional_subsumption,
% 3.39/1.01                [status(thm)],
% 3.39/1.01                [c_4412,c_1676]) ).
% 3.39/1.01  
% 3.39/1.01  cnf(c_4,plain,
% 3.39/1.01      ( ~ r2_hidden(X0,X1)
% 3.39/1.01      | r2_hidden(X0,k3_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X1))) ),
% 3.39/1.01      inference(cnf_transformation,[],[f103]) ).
% 3.39/1.01  
% 3.39/1.01  cnf(c_1499,plain,
% 3.39/1.01      ( r2_hidden(X0,X1) != iProver_top
% 3.39/1.01      | r2_hidden(X0,k3_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X1))) = iProver_top ),
% 3.39/1.01      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 3.39/1.01  
% 3.39/1.01  cnf(c_4411,plain,
% 3.39/1.01      ( r2_hidden(sK3,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)) != iProver_top
% 3.39/1.01      | r2_hidden(sK2,sK3) = iProver_top ),
% 3.39/1.01      inference(superposition,[status(thm)],[c_1499,c_1823]) ).
% 3.39/1.01  
% 3.39/1.01  cnf(c_14,plain,
% 3.39/1.01      ( r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1)
% 3.39/1.01      | ~ r2_hidden(X0,X1) ),
% 3.39/1.01      inference(cnf_transformation,[],[f97]) ).
% 3.39/1.01  
% 3.39/1.01  cnf(c_1489,plain,
% 3.39/1.01      ( r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1) = iProver_top
% 3.39/1.01      | r2_hidden(X0,X1) != iProver_top ),
% 3.39/1.01      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 3.39/1.01  
% 3.39/1.01  cnf(c_1838,plain,
% 3.39/1.01      ( r2_hidden(X0,X1) != iProver_top
% 3.39/1.01      | r2_hidden(X1,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) != iProver_top ),
% 3.39/1.01      inference(superposition,[status(thm)],[c_1489,c_1485]) ).
% 3.39/1.01  
% 3.39/1.01  cnf(c_4691,plain,
% 3.39/1.01      ( r2_hidden(sK3,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)) != iProver_top ),
% 3.39/1.01      inference(forward_subsumption_resolution,
% 3.39/1.01                [status(thm)],
% 3.39/1.01                [c_4411,c_1838]) ).
% 3.39/1.01  
% 3.39/1.01  cnf(c_8434,plain,
% 3.39/1.01      ( k3_xboole_0(k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))),sK3) = k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))) ),
% 3.39/1.01      inference(global_propositional_subsumption,
% 3.39/1.01                [status(thm)],
% 3.39/1.01                [c_1824,c_493,c_1676,c_4390,c_4412,c_4691]) ).
% 3.39/1.01  
% 3.39/1.01  cnf(c_11,plain,
% 3.39/1.01      ( r2_hidden(X0,X1) | ~ r2_hidden(X0,k3_xboole_0(X2,X1)) ),
% 3.39/1.01      inference(cnf_transformation,[],[f107]) ).
% 3.39/1.01  
% 3.39/1.01  cnf(c_1492,plain,
% 3.39/1.01      ( r2_hidden(X0,X1) = iProver_top
% 3.39/1.01      | r2_hidden(X0,k3_xboole_0(X2,X1)) != iProver_top ),
% 3.39/1.01      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 3.39/1.01  
% 3.39/1.01  cnf(c_8440,plain,
% 3.39/1.01      ( r2_hidden(X0,k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)))) != iProver_top
% 3.39/1.01      | r2_hidden(X0,sK3) = iProver_top ),
% 3.39/1.01      inference(superposition,[status(thm)],[c_8434,c_1492]) ).
% 3.39/1.01  
% 3.39/1.01  cnf(c_8457,plain,
% 3.39/1.01      ( r2_hidden(sK2,k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)))) != iProver_top
% 3.39/1.01      | r2_hidden(sK2,sK3) = iProver_top ),
% 3.39/1.01      inference(instantiation,[status(thm)],[c_8440]) ).
% 3.39/1.01  
% 3.39/1.01  cnf(c_18,plain,
% 3.39/1.01      ( r2_hidden(X0,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)))) ),
% 3.39/1.01      inference(cnf_transformation,[],[f99]) ).
% 3.39/1.01  
% 3.39/1.01  cnf(c_39,plain,
% 3.39/1.01      ( r2_hidden(X0,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)))) = iProver_top ),
% 3.39/1.01      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 3.39/1.01  
% 3.39/1.01  cnf(c_41,plain,
% 3.39/1.01      ( r2_hidden(sK2,k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)))) = iProver_top ),
% 3.39/1.01      inference(instantiation,[status(thm)],[c_39]) ).
% 3.39/1.01  
% 3.39/1.01  cnf(contradiction,plain,
% 3.39/1.01      ( $false ),
% 3.39/1.01      inference(minisat,[status(thm)],[c_8457,c_4691,c_4683,c_4390,c_41]) ).
% 3.39/1.01  
% 3.39/1.01  
% 3.39/1.01  % SZS output end CNFRefutation for theBenchmark.p
% 3.39/1.01  
% 3.39/1.01  ------                               Statistics
% 3.39/1.01  
% 3.39/1.01  ------ General
% 3.39/1.01  
% 3.39/1.01  abstr_ref_over_cycles:                  0
% 3.39/1.01  abstr_ref_under_cycles:                 0
% 3.39/1.01  gc_basic_clause_elim:                   0
% 3.39/1.01  forced_gc_time:                         0
% 3.39/1.01  parsing_time:                           0.008
% 3.39/1.01  unif_index_cands_time:                  0.
% 3.39/1.01  unif_index_add_time:                    0.
% 3.39/1.01  orderings_time:                         0.
% 3.39/1.01  out_proof_time:                         0.01
% 3.39/1.01  total_time:                             0.36
% 3.39/1.01  num_of_symbols:                         42
% 3.39/1.01  num_of_terms:                           10742
% 3.39/1.01  
% 3.39/1.01  ------ Preprocessing
% 3.39/1.01  
% 3.39/1.01  num_of_splits:                          0
% 3.39/1.01  num_of_split_atoms:                     0
% 3.39/1.01  num_of_reused_defs:                     0
% 3.39/1.01  num_eq_ax_congr_red:                    25
% 3.39/1.01  num_of_sem_filtered_clauses:            1
% 3.39/1.01  num_of_subtypes:                        0
% 3.39/1.01  monotx_restored_types:                  0
% 3.39/1.01  sat_num_of_epr_types:                   0
% 3.39/1.01  sat_num_of_non_cyclic_types:            0
% 3.39/1.01  sat_guarded_non_collapsed_types:        0
% 3.39/1.01  num_pure_diseq_elim:                    0
% 3.39/1.01  simp_replaced_by:                       0
% 3.39/1.01  res_preprocessed:                       116
% 3.39/1.01  prep_upred:                             0
% 3.39/1.01  prep_unflattend:                        34
% 3.39/1.01  smt_new_axioms:                         0
% 3.39/1.01  pred_elim_cands:                        3
% 3.39/1.01  pred_elim:                              1
% 3.39/1.01  pred_elim_cl:                           1
% 3.39/1.01  pred_elim_cycles:                       3
% 3.39/1.01  merged_defs:                            16
% 3.39/1.01  merged_defs_ncl:                        0
% 3.39/1.01  bin_hyper_res:                          16
% 3.39/1.01  prep_cycles:                            4
% 3.39/1.01  pred_elim_time:                         0.003
% 3.39/1.01  splitting_time:                         0.
% 3.39/1.01  sem_filter_time:                        0.
% 3.39/1.01  monotx_time:                            0.
% 3.39/1.01  subtype_inf_time:                       0.
% 3.39/1.01  
% 3.39/1.01  ------ Problem properties
% 3.39/1.01  
% 3.39/1.01  clauses:                                25
% 3.39/1.01  conjectures:                            2
% 3.39/1.01  epr:                                    5
% 3.39/1.01  horn:                                   19
% 3.39/1.01  ground:                                 5
% 3.39/1.01  unary:                                  3
% 3.39/1.01  binary:                                 13
% 3.39/1.01  lits:                                   59
% 3.39/1.01  lits_eq:                                7
% 3.39/1.01  fd_pure:                                0
% 3.39/1.01  fd_pseudo:                              0
% 3.39/1.01  fd_cond:                                0
% 3.39/1.01  fd_pseudo_cond:                         6
% 3.39/1.01  ac_symbols:                             0
% 3.39/1.01  
% 3.39/1.01  ------ Propositional Solver
% 3.39/1.01  
% 3.39/1.01  prop_solver_calls:                      27
% 3.39/1.01  prop_fast_solver_calls:                 765
% 3.39/1.01  smt_solver_calls:                       0
% 3.39/1.01  smt_fast_solver_calls:                  0
% 3.39/1.01  prop_num_of_clauses:                    3039
% 3.39/1.01  prop_preprocess_simplified:             10858
% 3.39/1.01  prop_fo_subsumed:                       9
% 3.39/1.01  prop_solver_time:                       0.
% 3.39/1.01  smt_solver_time:                        0.
% 3.39/1.01  smt_fast_solver_time:                   0.
% 3.39/1.01  prop_fast_solver_time:                  0.
% 3.39/1.01  prop_unsat_core_time:                   0.
% 3.39/1.01  
% 3.39/1.01  ------ QBF
% 3.39/1.01  
% 3.39/1.01  qbf_q_res:                              0
% 3.39/1.01  qbf_num_tautologies:                    0
% 3.39/1.01  qbf_prep_cycles:                        0
% 3.39/1.01  
% 3.39/1.01  ------ BMC1
% 3.39/1.01  
% 3.39/1.01  bmc1_current_bound:                     -1
% 3.39/1.01  bmc1_last_solved_bound:                 -1
% 3.39/1.01  bmc1_unsat_core_size:                   -1
% 3.39/1.01  bmc1_unsat_core_parents_size:           -1
% 3.39/1.01  bmc1_merge_next_fun:                    0
% 3.39/1.01  bmc1_unsat_core_clauses_time:           0.
% 3.39/1.01  
% 3.39/1.01  ------ Instantiation
% 3.39/1.01  
% 3.39/1.01  inst_num_of_clauses:                    1020
% 3.39/1.01  inst_num_in_passive:                    408
% 3.39/1.01  inst_num_in_active:                     222
% 3.39/1.01  inst_num_in_unprocessed:                390
% 3.39/1.01  inst_num_of_loops:                      230
% 3.39/1.01  inst_num_of_learning_restarts:          0
% 3.39/1.01  inst_num_moves_active_passive:          7
% 3.39/1.01  inst_lit_activity:                      0
% 3.39/1.01  inst_lit_activity_moves:                0
% 3.39/1.01  inst_num_tautologies:                   0
% 3.39/1.01  inst_num_prop_implied:                  0
% 3.39/1.01  inst_num_existing_simplified:           0
% 3.39/1.01  inst_num_eq_res_simplified:             0
% 3.39/1.01  inst_num_child_elim:                    0
% 3.39/1.01  inst_num_of_dismatching_blockings:      176
% 3.39/1.01  inst_num_of_non_proper_insts:           537
% 3.39/1.01  inst_num_of_duplicates:                 0
% 3.39/1.01  inst_inst_num_from_inst_to_res:         0
% 3.39/1.01  inst_dismatching_checking_time:         0.
% 3.39/1.01  
% 3.39/1.01  ------ Resolution
% 3.39/1.01  
% 3.39/1.01  res_num_of_clauses:                     0
% 3.39/1.01  res_num_in_passive:                     0
% 3.39/1.01  res_num_in_active:                      0
% 3.39/1.01  res_num_of_loops:                       120
% 3.39/1.01  res_forward_subset_subsumed:            13
% 3.39/1.01  res_backward_subset_subsumed:           0
% 3.39/1.01  res_forward_subsumed:                   0
% 3.39/1.01  res_backward_subsumed:                  0
% 3.39/1.01  res_forward_subsumption_resolution:     0
% 3.39/1.01  res_backward_subsumption_resolution:    0
% 3.39/1.01  res_clause_to_clause_subsumption:       1209
% 3.39/1.01  res_orphan_elimination:                 0
% 3.39/1.01  res_tautology_del:                      73
% 3.39/1.01  res_num_eq_res_simplified:              0
% 3.39/1.01  res_num_sel_changes:                    0
% 3.39/1.01  res_moves_from_active_to_pass:          0
% 3.39/1.01  
% 3.39/1.01  ------ Superposition
% 3.39/1.01  
% 3.39/1.01  sup_time_total:                         0.
% 3.39/1.01  sup_time_generating:                    0.
% 3.39/1.01  sup_time_sim_full:                      0.
% 3.39/1.01  sup_time_sim_immed:                     0.
% 3.39/1.01  
% 3.39/1.01  sup_num_of_clauses:                     173
% 3.39/1.01  sup_num_in_active:                      46
% 3.39/1.01  sup_num_in_passive:                     127
% 3.39/1.01  sup_num_of_loops:                       45
% 3.39/1.01  sup_fw_superposition:                   103
% 3.39/1.01  sup_bw_superposition:                   80
% 3.39/1.01  sup_immediate_simplified:               9
% 3.39/1.01  sup_given_eliminated:                   0
% 3.39/1.01  comparisons_done:                       0
% 3.39/1.01  comparisons_avoided:                    0
% 3.39/1.01  
% 3.39/1.01  ------ Simplifications
% 3.39/1.01  
% 3.39/1.01  
% 3.39/1.01  sim_fw_subset_subsumed:                 7
% 3.39/1.01  sim_bw_subset_subsumed:                 1
% 3.39/1.01  sim_fw_subsumed:                        6
% 3.39/1.01  sim_bw_subsumed:                        0
% 3.39/1.01  sim_fw_subsumption_res:                 3
% 3.39/1.01  sim_bw_subsumption_res:                 0
% 3.39/1.01  sim_tautology_del:                      21
% 3.39/1.01  sim_eq_tautology_del:                   0
% 3.39/1.01  sim_eq_res_simp:                        8
% 3.39/1.01  sim_fw_demodulated:                     0
% 3.39/1.01  sim_bw_demodulated:                     0
% 3.39/1.01  sim_light_normalised:                   2
% 3.39/1.01  sim_joinable_taut:                      0
% 3.39/1.01  sim_joinable_simp:                      0
% 3.39/1.01  sim_ac_normalised:                      0
% 3.39/1.01  sim_smt_subsumption:                    0
% 3.39/1.01  
%------------------------------------------------------------------------------
