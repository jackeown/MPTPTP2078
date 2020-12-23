%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:53:42 EST 2020

% Result     : Theorem 2.29s
% Output     : CNFRefutation 2.29s
% Verified   : 
% Statistics : Number of formulae       :  173 (1299 expanded)
%              Number of clauses        :   85 ( 232 expanded)
%              Number of leaves         :   25 ( 348 expanded)
%              Depth                    :   23
%              Number of atoms          :  528 (3592 expanded)
%              Number of equality atoms :  212 ( 967 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal clause size      :   14 (   3 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f15,axiom,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ! [X1] :
          ( v3_ordinal1(X1)
         => ~ ( ~ r2_hidden(X1,X0)
              & X0 != X1
              & ~ r2_hidden(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(X1,X0)
          | X0 = X1
          | r2_hidden(X0,X1)
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(X1,X0)
          | X0 = X1
          | r2_hidden(X0,X1)
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(flattening,[],[f25])).

fof(f71,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,X0)
      | X0 = X1
      | r2_hidden(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f16,axiom,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ! [X1] :
          ( v3_ordinal1(X1)
         => ( r2_hidden(X1,X0)
            | r1_ordinal1(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(X1,X0)
          | r1_ordinal1(X0,X1)
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(X1,X0)
          | r1_ordinal1(X0,X1)
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(flattening,[],[f27])).

fof(f72,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,X0)
      | r1_ordinal1(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f19,conjecture,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ! [X1] :
          ( v3_ordinal1(X1)
         => ( r2_hidden(X0,X1)
          <=> r1_ordinal1(k1_ordinal1(X0),X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,negated_conjecture,(
    ~ ! [X0] :
        ( v3_ordinal1(X0)
       => ! [X1] :
            ( v3_ordinal1(X1)
           => ( r2_hidden(X0,X1)
            <=> r1_ordinal1(k1_ordinal1(X0),X1) ) ) ) ),
    inference(negated_conjecture,[],[f19])).

fof(f31,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( r2_hidden(X0,X1)
          <~> r1_ordinal1(k1_ordinal1(X0),X1) )
          & v3_ordinal1(X1) )
      & v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f42,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ r1_ordinal1(k1_ordinal1(X0),X1)
            | ~ r2_hidden(X0,X1) )
          & ( r1_ordinal1(k1_ordinal1(X0),X1)
            | r2_hidden(X0,X1) )
          & v3_ordinal1(X1) )
      & v3_ordinal1(X0) ) ),
    inference(nnf_transformation,[],[f31])).

fof(f43,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ r1_ordinal1(k1_ordinal1(X0),X1)
            | ~ r2_hidden(X0,X1) )
          & ( r1_ordinal1(k1_ordinal1(X0),X1)
            | r2_hidden(X0,X1) )
          & v3_ordinal1(X1) )
      & v3_ordinal1(X0) ) ),
    inference(flattening,[],[f42])).

fof(f45,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ( ~ r1_ordinal1(k1_ordinal1(X0),X1)
            | ~ r2_hidden(X0,X1) )
          & ( r1_ordinal1(k1_ordinal1(X0),X1)
            | r2_hidden(X0,X1) )
          & v3_ordinal1(X1) )
     => ( ( ~ r1_ordinal1(k1_ordinal1(X0),sK2)
          | ~ r2_hidden(X0,sK2) )
        & ( r1_ordinal1(k1_ordinal1(X0),sK2)
          | r2_hidden(X0,sK2) )
        & v3_ordinal1(sK2) ) ) ),
    introduced(choice_axiom,[])).

fof(f44,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( ~ r1_ordinal1(k1_ordinal1(X0),X1)
              | ~ r2_hidden(X0,X1) )
            & ( r1_ordinal1(k1_ordinal1(X0),X1)
              | r2_hidden(X0,X1) )
            & v3_ordinal1(X1) )
        & v3_ordinal1(X0) )
   => ( ? [X1] :
          ( ( ~ r1_ordinal1(k1_ordinal1(sK1),X1)
            | ~ r2_hidden(sK1,X1) )
          & ( r1_ordinal1(k1_ordinal1(sK1),X1)
            | r2_hidden(sK1,X1) )
          & v3_ordinal1(X1) )
      & v3_ordinal1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f46,plain,
    ( ( ~ r1_ordinal1(k1_ordinal1(sK1),sK2)
      | ~ r2_hidden(sK1,sK2) )
    & ( r1_ordinal1(k1_ordinal1(sK1),sK2)
      | r2_hidden(sK1,sK2) )
    & v3_ordinal1(sK2)
    & v3_ordinal1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f43,f45,f44])).

fof(f78,plain,
    ( ~ r1_ordinal1(k1_ordinal1(sK1),sK2)
    | ~ r2_hidden(sK1,sK2) ),
    inference(cnf_transformation,[],[f46])).

fof(f12,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_tarski(X0)) = k1_ordinal1(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f65,plain,(
    ! [X0] : k2_xboole_0(X0,k1_tarski(X0)) = k1_ordinal1(X0) ),
    inference(cnf_transformation,[],[f12])).

fof(f10,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f63,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f10])).

fof(f84,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f63,f83])).

fof(f3,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f56,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f4,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f57,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f5,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f58,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f5])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f59,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f6])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f60,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f7])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f61,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f8])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f62,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f9])).

fof(f79,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f61,f62])).

fof(f80,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f60,f79])).

fof(f81,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f59,f80])).

fof(f82,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f58,f81])).

fof(f83,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f57,f82])).

fof(f85,plain,(
    ! [X0] : k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f56,f83])).

fof(f86,plain,(
    ! [X0] : k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))) = k1_ordinal1(X0) ),
    inference(definition_unfolding,[],[f65,f84,f85])).

fof(f97,plain,
    ( ~ r1_ordinal1(k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))),sK2)
    | ~ r2_hidden(sK1,sK2) ),
    inference(definition_unfolding,[],[f78,f86])).

fof(f75,plain,(
    v3_ordinal1(sK1) ),
    inference(cnf_transformation,[],[f46])).

fof(f76,plain,(
    v3_ordinal1(sK2) ),
    inference(cnf_transformation,[],[f46])).

fof(f17,axiom,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => v3_ordinal1(k1_ordinal1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0] :
      ( v3_ordinal1(k1_ordinal1(X0))
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f73,plain,(
    ! [X0] :
      ( v3_ordinal1(k1_ordinal1(X0))
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f96,plain,(
    ! [X0] :
      ( v3_ordinal1(k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))))
      | ~ v3_ordinal1(X0) ) ),
    inference(definition_unfolding,[],[f73,f86])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,k1_ordinal1(X1))
    <=> ( X0 = X1
        | r2_hidden(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( r2_hidden(X0,k1_ordinal1(X1))
        | ( X0 != X1
          & ~ r2_hidden(X0,X1) ) )
      & ( X0 = X1
        | r2_hidden(X0,X1)
        | ~ r2_hidden(X0,k1_ordinal1(X1)) ) ) ),
    inference(nnf_transformation,[],[f14])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ( r2_hidden(X0,k1_ordinal1(X1))
        | ( X0 != X1
          & ~ r2_hidden(X0,X1) ) )
      & ( X0 = X1
        | r2_hidden(X0,X1)
        | ~ r2_hidden(X0,k1_ordinal1(X1)) ) ) ),
    inference(flattening,[],[f40])).

fof(f68,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | r2_hidden(X0,X1)
      | ~ r2_hidden(X0,k1_ordinal1(X1)) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f95,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | r2_hidden(X0,X1)
      | ~ r2_hidden(X0,k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)))) ) ),
    inference(definition_unfolding,[],[f68,f86])).

fof(f18,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f74,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f13,axiom,(
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
    inference(ennf_transformation,[],[f13])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( r1_ordinal1(X0,X1)
      <=> r1_tarski(X0,X1) )
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(flattening,[],[f23])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( ( r1_ordinal1(X0,X1)
          | ~ r1_tarski(X0,X1) )
        & ( r1_tarski(X0,X1)
          | ~ r1_ordinal1(X0,X1) ) )
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(nnf_transformation,[],[f24])).

fof(f66,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r1_ordinal1(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( ( v3_ordinal1(X1)
        & v3_ordinal1(X0) )
     => ( r1_ordinal1(X1,X0)
        | r1_ordinal1(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] :
      ( r1_ordinal1(X1,X0)
      | r1_ordinal1(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f22,plain,(
    ! [X0,X1] :
      ( r1_ordinal1(X1,X0)
      | r1_ordinal1(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(flattening,[],[f21])).

fof(f64,plain,(
    ! [X0,X1] :
      ( r1_ordinal1(X1,X0)
      | r1_ordinal1(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            | r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

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
    inference(nnf_transformation,[],[f1])).

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
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) ) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f32])).

fof(f34,plain,(
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
    inference(rectify,[],[f33])).

fof(f35,plain,(
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

fof(f36,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f34,f35])).

fof(f48,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X0)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f36])).

fof(f91,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X0)
      | k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f48,f84])).

fof(f100,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))
      | ~ r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f91])).

fof(f77,plain,
    ( r1_ordinal1(k1_ordinal1(sK1),sK2)
    | r2_hidden(sK1,sK2) ),
    inference(cnf_transformation,[],[f46])).

fof(f98,plain,
    ( r1_ordinal1(k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))),sK2)
    | r2_hidden(sK1,sK2) ),
    inference(definition_unfolding,[],[f77,f86])).

fof(f69,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,k1_ordinal1(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f94,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))))
      | ~ r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f69,f86])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f37])).

fof(f54,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f38])).

fof(f102,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f54])).

fof(f70,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,k1_ordinal1(X1))
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f41])).

fof(f93,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))))
      | X0 != X1 ) ),
    inference(definition_unfolding,[],[f70,f86])).

fof(f104,plain,(
    ! [X1] : r2_hidden(X1,k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)))) ),
    inference(equality_resolution,[],[f93])).

cnf(c_15,plain,
    ( r2_hidden(X0,X1)
    | r2_hidden(X1,X0)
    | ~ v3_ordinal1(X1)
    | ~ v3_ordinal1(X0)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f71])).

cnf(c_987,plain,
    ( X0 = X1
    | r2_hidden(X0,X1) = iProver_top
    | r2_hidden(X1,X0) = iProver_top
    | v3_ordinal1(X1) != iProver_top
    | v3_ordinal1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_16,plain,
    ( r1_ordinal1(X0,X1)
    | r2_hidden(X1,X0)
    | ~ v3_ordinal1(X1)
    | ~ v3_ordinal1(X0) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_986,plain,
    ( r1_ordinal1(X0,X1) = iProver_top
    | r2_hidden(X1,X0) = iProver_top
    | v3_ordinal1(X0) != iProver_top
    | v3_ordinal1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_19,negated_conjecture,
    ( ~ r1_ordinal1(k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))),sK2)
    | ~ r2_hidden(sK1,sK2) ),
    inference(cnf_transformation,[],[f97])).

cnf(c_983,plain,
    ( r1_ordinal1(k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))),sK2) != iProver_top
    | r2_hidden(sK1,sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_2360,plain,
    ( r2_hidden(sK2,k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)))) = iProver_top
    | r2_hidden(sK1,sK2) != iProver_top
    | v3_ordinal1(k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)))) != iProver_top
    | v3_ordinal1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_986,c_983])).

cnf(c_22,negated_conjecture,
    ( v3_ordinal1(sK1) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_23,plain,
    ( v3_ordinal1(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_21,negated_conjecture,
    ( v3_ordinal1(sK2) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_24,plain,
    ( v3_ordinal1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_17,plain,
    ( ~ v3_ordinal1(X0)
    | v3_ordinal1(k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)))) ),
    inference(cnf_transformation,[],[f96])).

cnf(c_30,plain,
    ( v3_ordinal1(X0) != iProver_top
    | v3_ordinal1(k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_32,plain,
    ( v3_ordinal1(k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)))) = iProver_top
    | v3_ordinal1(sK1) != iProver_top ),
    inference(instantiation,[status(thm)],[c_30])).

cnf(c_3058,plain,
    ( r2_hidden(sK2,k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)))) = iProver_top
    | r2_hidden(sK1,sK2) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2360,c_23,c_24,c_32])).

cnf(c_14,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))))
    | X1 = X0 ),
    inference(cnf_transformation,[],[f95])).

cnf(c_988,plain,
    ( X0 = X1
    | r2_hidden(X1,X0) = iProver_top
    | r2_hidden(X1,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_3995,plain,
    ( sK2 = sK1
    | r2_hidden(sK2,sK1) = iProver_top
    | r2_hidden(sK1,sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_3058,c_988])).

cnf(c_18,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r2_hidden(X1,X0) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_28,plain,
    ( ~ r1_tarski(sK1,sK1)
    | ~ r2_hidden(sK1,sK1) ),
    inference(instantiation,[status(thm)],[c_18])).

cnf(c_37,plain,
    ( r2_hidden(sK1,sK1)
    | ~ v3_ordinal1(sK1)
    | sK1 = sK1 ),
    inference(instantiation,[status(thm)],[c_15])).

cnf(c_11,plain,
    ( ~ r1_ordinal1(X0,X1)
    | r1_tarski(X0,X1)
    | ~ v3_ordinal1(X1)
    | ~ v3_ordinal1(X0) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_49,plain,
    ( ~ r1_ordinal1(sK1,sK1)
    | r1_tarski(sK1,sK1)
    | ~ v3_ordinal1(sK1) ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_9,plain,
    ( r1_ordinal1(X0,X1)
    | r1_ordinal1(X1,X0)
    | ~ v3_ordinal1(X1)
    | ~ v3_ordinal1(X0) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_55,plain,
    ( r1_ordinal1(sK1,sK1)
    | ~ v3_ordinal1(sK1) ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_54,plain,
    ( r1_ordinal1(X0,X1) = iProver_top
    | r1_ordinal1(X1,X0) = iProver_top
    | v3_ordinal1(X0) != iProver_top
    | v3_ordinal1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_56,plain,
    ( r1_ordinal1(sK1,sK1) = iProver_top
    | v3_ordinal1(sK1) != iProver_top ),
    inference(instantiation,[status(thm)],[c_54])).

cnf(c_1687,plain,
    ( ~ r1_tarski(sK2,sK1)
    | ~ r2_hidden(sK1,sK2) ),
    inference(instantiation,[status(thm)],[c_18])).

cnf(c_1688,plain,
    ( r1_tarski(sK2,sK1) != iProver_top
    | r2_hidden(sK1,sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1687])).

cnf(c_2643,plain,
    ( ~ r1_ordinal1(sK2,sK1)
    | r1_tarski(sK2,sK1)
    | ~ v3_ordinal1(sK2)
    | ~ v3_ordinal1(sK1) ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_2644,plain,
    ( r1_ordinal1(sK2,sK1) != iProver_top
    | r1_tarski(sK2,sK1) = iProver_top
    | v3_ordinal1(sK2) != iProver_top
    | v3_ordinal1(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2643])).

cnf(c_487,plain,
    ( ~ r1_ordinal1(X0,X1)
    | r1_ordinal1(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_4825,plain,
    ( ~ r1_ordinal1(X0,X1)
    | r1_ordinal1(sK2,sK1)
    | sK2 != X0
    | sK1 != X1 ),
    inference(instantiation,[status(thm)],[c_487])).

cnf(c_4826,plain,
    ( sK2 != X0
    | sK1 != X1
    | r1_ordinal1(X0,X1) != iProver_top
    | r1_ordinal1(sK2,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4825])).

cnf(c_4828,plain,
    ( sK2 != sK1
    | sK1 != sK1
    | r1_ordinal1(sK2,sK1) = iProver_top
    | r1_ordinal1(sK1,sK1) != iProver_top ),
    inference(instantiation,[status(thm)],[c_4826])).

cnf(c_4887,plain,
    ( r2_hidden(sK2,sK1) = iProver_top
    | r2_hidden(sK1,sK2) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3995,c_22,c_23,c_24,c_28,c_37,c_49,c_55,c_56,c_1688,c_2644,c_4828])).

cnf(c_4893,plain,
    ( sK2 = sK1
    | r2_hidden(sK2,sK1) = iProver_top
    | v3_ordinal1(sK2) != iProver_top
    | v3_ordinal1(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_987,c_4887])).

cnf(c_4897,plain,
    ( sK2 = sK1
    | r2_hidden(sK2,sK1) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4893,c_23,c_24])).

cnf(c_4,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))) ),
    inference(cnf_transformation,[],[f100])).

cnf(c_997,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_20,negated_conjecture,
    ( r1_ordinal1(k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))),sK2)
    | r2_hidden(sK1,sK2) ),
    inference(cnf_transformation,[],[f98])).

cnf(c_982,plain,
    ( r1_ordinal1(k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))),sK2) = iProver_top
    | r2_hidden(sK1,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_991,plain,
    ( r1_ordinal1(X0,X1) != iProver_top
    | r1_tarski(X0,X1) = iProver_top
    | v3_ordinal1(X0) != iProver_top
    | v3_ordinal1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_2001,plain,
    ( r1_tarski(k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))),sK2) = iProver_top
    | r2_hidden(sK1,sK2) = iProver_top
    | v3_ordinal1(k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)))) != iProver_top
    | v3_ordinal1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_982,c_991])).

cnf(c_2004,plain,
    ( r1_tarski(k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))),sK2) = iProver_top
    | r2_hidden(sK1,sK2) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2001,c_23,c_24,c_32])).

cnf(c_984,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r2_hidden(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_2011,plain,
    ( r2_hidden(sK2,k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)))) != iProver_top
    | r2_hidden(sK1,sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_2004,c_984])).

cnf(c_2252,plain,
    ( r2_hidden(sK2,sK1) != iProver_top
    | r2_hidden(sK1,sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_997,c_2011])).

cnf(c_4903,plain,
    ( sK2 = sK1
    | r2_hidden(sK1,sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_4897,c_2252])).

cnf(c_993,plain,
    ( r1_ordinal1(X0,X1) = iProver_top
    | r1_ordinal1(X1,X0) = iProver_top
    | v3_ordinal1(X0) != iProver_top
    | v3_ordinal1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_2653,plain,
    ( r1_ordinal1(X0,X1) = iProver_top
    | r1_tarski(X1,X0) = iProver_top
    | v3_ordinal1(X0) != iProver_top
    | v3_ordinal1(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_993,c_991])).

cnf(c_6478,plain,
    ( r1_tarski(X0,X1) = iProver_top
    | r1_tarski(X1,X0) = iProver_top
    | v3_ordinal1(X0) != iProver_top
    | v3_ordinal1(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_2653,c_991])).

cnf(c_6722,plain,
    ( r1_tarski(X0,X1) = iProver_top
    | r2_hidden(X0,X1) != iProver_top
    | v3_ordinal1(X0) != iProver_top
    | v3_ordinal1(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_6478,c_984])).

cnf(c_6758,plain,
    ( sK2 = sK1
    | r1_tarski(sK2,sK1) = iProver_top
    | v3_ordinal1(sK2) != iProver_top
    | v3_ordinal1(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_4897,c_6722])).

cnf(c_7168,plain,
    ( r1_tarski(sK2,sK1) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6758,c_22,c_23,c_24,c_28,c_37,c_49,c_55,c_56,c_2644,c_4828])).

cnf(c_7175,plain,
    ( r2_hidden(sK1,sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_7168,c_984])).

cnf(c_7195,plain,
    ( sK2 = sK1 ),
    inference(superposition,[status(thm)],[c_4903,c_7175])).

cnf(c_2799,plain,
    ( k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))) = sK2
    | r2_hidden(k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))),sK2) = iProver_top
    | r2_hidden(sK1,sK2) = iProver_top
    | v3_ordinal1(k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)))) != iProver_top
    | v3_ordinal1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_987,c_2011])).

cnf(c_3758,plain,
    ( k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))) = sK2
    | r2_hidden(k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))),sK2) = iProver_top
    | r2_hidden(sK1,sK2) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2799,c_23,c_24,c_32])).

cnf(c_7545,plain,
    ( k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))) = sK1
    | r2_hidden(k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))),sK1) = iProver_top
    | r2_hidden(sK1,sK1) = iProver_top ),
    inference(demodulation,[status(thm)],[c_7195,c_3758])).

cnf(c_13,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)))) ),
    inference(cnf_transformation,[],[f94])).

cnf(c_2493,plain,
    ( ~ r2_hidden(k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))),X0)
    | r2_hidden(k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)))) ),
    inference(instantiation,[status(thm)],[c_13])).

cnf(c_2494,plain,
    ( r2_hidden(k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))),X0) != iProver_top
    | r2_hidden(k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2493])).

cnf(c_2496,plain,
    ( r2_hidden(k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))),k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)))) = iProver_top
    | r2_hidden(k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))),sK1) != iProver_top ),
    inference(instantiation,[status(thm)],[c_2494])).

cnf(c_483,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_1301,plain,
    ( X0 != X1
    | X0 = k3_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2)))
    | k3_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2))) != X1 ),
    inference(instantiation,[status(thm)],[c_483])).

cnf(c_1302,plain,
    ( k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))) != sK1
    | sK1 = k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)))
    | sK1 != sK1 ),
    inference(instantiation,[status(thm)],[c_1301])).

cnf(c_7,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f102])).

cnf(c_1260,plain,
    ( r1_tarski(k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)))) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_1265,plain,
    ( r1_tarski(k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1260])).

cnf(c_1267,plain,
    ( r1_tarski(k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))),k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)))) = iProver_top ),
    inference(instantiation,[status(thm)],[c_1265])).

cnf(c_1209,plain,
    ( ~ r1_tarski(k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))),X1)
    | ~ r2_hidden(X1,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)))) ),
    inference(instantiation,[status(thm)],[c_18])).

cnf(c_1259,plain,
    ( ~ r1_tarski(k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))))
    | ~ r2_hidden(k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)))) ),
    inference(instantiation,[status(thm)],[c_1209])).

cnf(c_1261,plain,
    ( r1_tarski(k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)))) != iProver_top
    | r2_hidden(k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1259])).

cnf(c_1263,plain,
    ( r1_tarski(k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))),k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)))) != iProver_top
    | r2_hidden(k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))),k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)))) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1261])).

cnf(c_486,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_1166,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(X2,k3_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2))))
    | X0 != X2
    | X1 != k3_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2))) ),
    inference(instantiation,[status(thm)],[c_486])).

cnf(c_1168,plain,
    ( ~ r2_hidden(sK1,k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))))
    | r2_hidden(sK1,sK1)
    | sK1 != k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)))
    | sK1 != sK1 ),
    inference(instantiation,[status(thm)],[c_1166])).

cnf(c_48,plain,
    ( r1_ordinal1(X0,X1) != iProver_top
    | r1_tarski(X0,X1) = iProver_top
    | v3_ordinal1(X0) != iProver_top
    | v3_ordinal1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_50,plain,
    ( r1_ordinal1(sK1,sK1) != iProver_top
    | r1_tarski(sK1,sK1) = iProver_top
    | v3_ordinal1(sK1) != iProver_top ),
    inference(instantiation,[status(thm)],[c_48])).

cnf(c_12,plain,
    ( r2_hidden(X0,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)))) ),
    inference(cnf_transformation,[],[f104])).

cnf(c_46,plain,
    ( r2_hidden(sK1,k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)))) ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_27,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r2_hidden(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_29,plain,
    ( r1_tarski(sK1,sK1) != iProver_top
    | r2_hidden(sK1,sK1) != iProver_top ),
    inference(instantiation,[status(thm)],[c_27])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_7545,c_2496,c_1302,c_1267,c_1263,c_1168,c_56,c_55,c_50,c_49,c_46,c_37,c_29,c_28,c_23,c_22])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 11:28:17 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 2.29/1.03  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.29/1.03  
% 2.29/1.03  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.29/1.03  
% 2.29/1.03  ------  iProver source info
% 2.29/1.03  
% 2.29/1.03  git: date: 2020-06-30 10:37:57 +0100
% 2.29/1.03  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.29/1.03  git: non_committed_changes: false
% 2.29/1.03  git: last_make_outside_of_git: false
% 2.29/1.03  
% 2.29/1.03  ------ 
% 2.29/1.03  
% 2.29/1.03  ------ Input Options
% 2.29/1.03  
% 2.29/1.03  --out_options                           all
% 2.29/1.03  --tptp_safe_out                         true
% 2.29/1.03  --problem_path                          ""
% 2.29/1.03  --include_path                          ""
% 2.29/1.03  --clausifier                            res/vclausify_rel
% 2.29/1.03  --clausifier_options                    --mode clausify
% 2.29/1.03  --stdin                                 false
% 2.29/1.03  --stats_out                             all
% 2.29/1.03  
% 2.29/1.03  ------ General Options
% 2.29/1.03  
% 2.29/1.03  --fof                                   false
% 2.29/1.03  --time_out_real                         305.
% 2.29/1.03  --time_out_virtual                      -1.
% 2.29/1.03  --symbol_type_check                     false
% 2.29/1.03  --clausify_out                          false
% 2.29/1.03  --sig_cnt_out                           false
% 2.29/1.03  --trig_cnt_out                          false
% 2.29/1.03  --trig_cnt_out_tolerance                1.
% 2.29/1.03  --trig_cnt_out_sk_spl                   false
% 2.29/1.03  --abstr_cl_out                          false
% 2.29/1.03  
% 2.29/1.03  ------ Global Options
% 2.29/1.03  
% 2.29/1.03  --schedule                              default
% 2.29/1.03  --add_important_lit                     false
% 2.29/1.03  --prop_solver_per_cl                    1000
% 2.29/1.03  --min_unsat_core                        false
% 2.29/1.03  --soft_assumptions                      false
% 2.29/1.03  --soft_lemma_size                       3
% 2.29/1.03  --prop_impl_unit_size                   0
% 2.29/1.03  --prop_impl_unit                        []
% 2.29/1.03  --share_sel_clauses                     true
% 2.29/1.03  --reset_solvers                         false
% 2.29/1.03  --bc_imp_inh                            [conj_cone]
% 2.29/1.03  --conj_cone_tolerance                   3.
% 2.29/1.03  --extra_neg_conj                        none
% 2.29/1.03  --large_theory_mode                     true
% 2.29/1.03  --prolific_symb_bound                   200
% 2.29/1.03  --lt_threshold                          2000
% 2.29/1.03  --clause_weak_htbl                      true
% 2.29/1.03  --gc_record_bc_elim                     false
% 2.29/1.03  
% 2.29/1.03  ------ Preprocessing Options
% 2.29/1.03  
% 2.29/1.03  --preprocessing_flag                    true
% 2.29/1.03  --time_out_prep_mult                    0.1
% 2.29/1.03  --splitting_mode                        input
% 2.29/1.03  --splitting_grd                         true
% 2.29/1.03  --splitting_cvd                         false
% 2.29/1.03  --splitting_cvd_svl                     false
% 2.29/1.03  --splitting_nvd                         32
% 2.29/1.03  --sub_typing                            true
% 2.29/1.03  --prep_gs_sim                           true
% 2.29/1.03  --prep_unflatten                        true
% 2.29/1.03  --prep_res_sim                          true
% 2.29/1.03  --prep_upred                            true
% 2.29/1.03  --prep_sem_filter                       exhaustive
% 2.29/1.03  --prep_sem_filter_out                   false
% 2.29/1.03  --pred_elim                             true
% 2.29/1.03  --res_sim_input                         true
% 2.29/1.03  --eq_ax_congr_red                       true
% 2.29/1.03  --pure_diseq_elim                       true
% 2.29/1.03  --brand_transform                       false
% 2.29/1.03  --non_eq_to_eq                          false
% 2.29/1.03  --prep_def_merge                        true
% 2.29/1.03  --prep_def_merge_prop_impl              false
% 2.29/1.03  --prep_def_merge_mbd                    true
% 2.29/1.03  --prep_def_merge_tr_red                 false
% 2.29/1.03  --prep_def_merge_tr_cl                  false
% 2.29/1.03  --smt_preprocessing                     true
% 2.29/1.03  --smt_ac_axioms                         fast
% 2.29/1.03  --preprocessed_out                      false
% 2.29/1.03  --preprocessed_stats                    false
% 2.29/1.03  
% 2.29/1.03  ------ Abstraction refinement Options
% 2.29/1.03  
% 2.29/1.03  --abstr_ref                             []
% 2.29/1.03  --abstr_ref_prep                        false
% 2.29/1.03  --abstr_ref_until_sat                   false
% 2.29/1.03  --abstr_ref_sig_restrict                funpre
% 2.29/1.03  --abstr_ref_af_restrict_to_split_sk     false
% 2.29/1.03  --abstr_ref_under                       []
% 2.29/1.03  
% 2.29/1.03  ------ SAT Options
% 2.29/1.03  
% 2.29/1.03  --sat_mode                              false
% 2.29/1.03  --sat_fm_restart_options                ""
% 2.29/1.03  --sat_gr_def                            false
% 2.29/1.03  --sat_epr_types                         true
% 2.29/1.03  --sat_non_cyclic_types                  false
% 2.29/1.03  --sat_finite_models                     false
% 2.29/1.03  --sat_fm_lemmas                         false
% 2.29/1.03  --sat_fm_prep                           false
% 2.29/1.03  --sat_fm_uc_incr                        true
% 2.29/1.03  --sat_out_model                         small
% 2.29/1.03  --sat_out_clauses                       false
% 2.29/1.03  
% 2.29/1.03  ------ QBF Options
% 2.29/1.03  
% 2.29/1.03  --qbf_mode                              false
% 2.29/1.03  --qbf_elim_univ                         false
% 2.29/1.03  --qbf_dom_inst                          none
% 2.29/1.03  --qbf_dom_pre_inst                      false
% 2.29/1.03  --qbf_sk_in                             false
% 2.29/1.03  --qbf_pred_elim                         true
% 2.29/1.03  --qbf_split                             512
% 2.29/1.03  
% 2.29/1.03  ------ BMC1 Options
% 2.29/1.03  
% 2.29/1.03  --bmc1_incremental                      false
% 2.29/1.03  --bmc1_axioms                           reachable_all
% 2.29/1.03  --bmc1_min_bound                        0
% 2.29/1.03  --bmc1_max_bound                        -1
% 2.29/1.03  --bmc1_max_bound_default                -1
% 2.29/1.03  --bmc1_symbol_reachability              true
% 2.29/1.03  --bmc1_property_lemmas                  false
% 2.29/1.03  --bmc1_k_induction                      false
% 2.29/1.03  --bmc1_non_equiv_states                 false
% 2.29/1.03  --bmc1_deadlock                         false
% 2.29/1.03  --bmc1_ucm                              false
% 2.29/1.03  --bmc1_add_unsat_core                   none
% 2.29/1.03  --bmc1_unsat_core_children              false
% 2.29/1.03  --bmc1_unsat_core_extrapolate_axioms    false
% 2.29/1.03  --bmc1_out_stat                         full
% 2.29/1.03  --bmc1_ground_init                      false
% 2.29/1.03  --bmc1_pre_inst_next_state              false
% 2.29/1.03  --bmc1_pre_inst_state                   false
% 2.29/1.03  --bmc1_pre_inst_reach_state             false
% 2.29/1.03  --bmc1_out_unsat_core                   false
% 2.29/1.03  --bmc1_aig_witness_out                  false
% 2.29/1.03  --bmc1_verbose                          false
% 2.29/1.03  --bmc1_dump_clauses_tptp                false
% 2.29/1.03  --bmc1_dump_unsat_core_tptp             false
% 2.29/1.03  --bmc1_dump_file                        -
% 2.29/1.03  --bmc1_ucm_expand_uc_limit              128
% 2.29/1.03  --bmc1_ucm_n_expand_iterations          6
% 2.29/1.03  --bmc1_ucm_extend_mode                  1
% 2.29/1.03  --bmc1_ucm_init_mode                    2
% 2.29/1.03  --bmc1_ucm_cone_mode                    none
% 2.29/1.03  --bmc1_ucm_reduced_relation_type        0
% 2.29/1.03  --bmc1_ucm_relax_model                  4
% 2.29/1.03  --bmc1_ucm_full_tr_after_sat            true
% 2.29/1.03  --bmc1_ucm_expand_neg_assumptions       false
% 2.29/1.03  --bmc1_ucm_layered_model                none
% 2.29/1.03  --bmc1_ucm_max_lemma_size               10
% 2.29/1.03  
% 2.29/1.03  ------ AIG Options
% 2.29/1.03  
% 2.29/1.03  --aig_mode                              false
% 2.29/1.03  
% 2.29/1.03  ------ Instantiation Options
% 2.29/1.03  
% 2.29/1.03  --instantiation_flag                    true
% 2.29/1.03  --inst_sos_flag                         false
% 2.29/1.03  --inst_sos_phase                        true
% 2.29/1.03  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.29/1.03  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.29/1.03  --inst_lit_sel_side                     num_symb
% 2.29/1.03  --inst_solver_per_active                1400
% 2.29/1.03  --inst_solver_calls_frac                1.
% 2.29/1.03  --inst_passive_queue_type               priority_queues
% 2.29/1.03  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.29/1.03  --inst_passive_queues_freq              [25;2]
% 2.29/1.03  --inst_dismatching                      true
% 2.29/1.03  --inst_eager_unprocessed_to_passive     true
% 2.29/1.03  --inst_prop_sim_given                   true
% 2.29/1.03  --inst_prop_sim_new                     false
% 2.29/1.03  --inst_subs_new                         false
% 2.29/1.03  --inst_eq_res_simp                      false
% 2.29/1.03  --inst_subs_given                       false
% 2.29/1.03  --inst_orphan_elimination               true
% 2.29/1.03  --inst_learning_loop_flag               true
% 2.29/1.03  --inst_learning_start                   3000
% 2.29/1.03  --inst_learning_factor                  2
% 2.29/1.03  --inst_start_prop_sim_after_learn       3
% 2.29/1.03  --inst_sel_renew                        solver
% 2.29/1.03  --inst_lit_activity_flag                true
% 2.29/1.03  --inst_restr_to_given                   false
% 2.29/1.03  --inst_activity_threshold               500
% 2.29/1.03  --inst_out_proof                        true
% 2.29/1.03  
% 2.29/1.03  ------ Resolution Options
% 2.29/1.03  
% 2.29/1.03  --resolution_flag                       true
% 2.29/1.03  --res_lit_sel                           adaptive
% 2.29/1.03  --res_lit_sel_side                      none
% 2.29/1.03  --res_ordering                          kbo
% 2.29/1.03  --res_to_prop_solver                    active
% 2.29/1.03  --res_prop_simpl_new                    false
% 2.29/1.03  --res_prop_simpl_given                  true
% 2.29/1.03  --res_passive_queue_type                priority_queues
% 2.29/1.03  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.29/1.03  --res_passive_queues_freq               [15;5]
% 2.29/1.03  --res_forward_subs                      full
% 2.29/1.03  --res_backward_subs                     full
% 2.29/1.03  --res_forward_subs_resolution           true
% 2.29/1.03  --res_backward_subs_resolution          true
% 2.29/1.03  --res_orphan_elimination                true
% 2.29/1.03  --res_time_limit                        2.
% 2.29/1.03  --res_out_proof                         true
% 2.29/1.03  
% 2.29/1.03  ------ Superposition Options
% 2.29/1.03  
% 2.29/1.03  --superposition_flag                    true
% 2.29/1.03  --sup_passive_queue_type                priority_queues
% 2.29/1.03  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.29/1.03  --sup_passive_queues_freq               [8;1;4]
% 2.29/1.03  --demod_completeness_check              fast
% 2.29/1.03  --demod_use_ground                      true
% 2.29/1.03  --sup_to_prop_solver                    passive
% 2.29/1.03  --sup_prop_simpl_new                    true
% 2.29/1.03  --sup_prop_simpl_given                  true
% 2.29/1.03  --sup_fun_splitting                     false
% 2.29/1.03  --sup_smt_interval                      50000
% 2.29/1.03  
% 2.29/1.03  ------ Superposition Simplification Setup
% 2.29/1.03  
% 2.29/1.03  --sup_indices_passive                   []
% 2.29/1.03  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.29/1.03  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.29/1.03  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.29/1.03  --sup_full_triv                         [TrivRules;PropSubs]
% 2.29/1.03  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.29/1.03  --sup_full_bw                           [BwDemod]
% 2.29/1.03  --sup_immed_triv                        [TrivRules]
% 2.29/1.03  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.29/1.03  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.29/1.03  --sup_immed_bw_main                     []
% 2.29/1.03  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.29/1.03  --sup_input_triv                        [Unflattening;TrivRules]
% 2.29/1.03  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.29/1.03  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.29/1.03  
% 2.29/1.03  ------ Combination Options
% 2.29/1.03  
% 2.29/1.03  --comb_res_mult                         3
% 2.29/1.03  --comb_sup_mult                         2
% 2.29/1.03  --comb_inst_mult                        10
% 2.29/1.03  
% 2.29/1.03  ------ Debug Options
% 2.29/1.03  
% 2.29/1.03  --dbg_backtrace                         false
% 2.29/1.03  --dbg_dump_prop_clauses                 false
% 2.29/1.03  --dbg_dump_prop_clauses_file            -
% 2.29/1.03  --dbg_out_stat                          false
% 2.29/1.03  ------ Parsing...
% 2.29/1.03  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.29/1.03  
% 2.29/1.03  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e  sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 2.29/1.03  
% 2.29/1.03  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.29/1.03  
% 2.29/1.03  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.29/1.03  ------ Proving...
% 2.29/1.03  ------ Problem Properties 
% 2.29/1.03  
% 2.29/1.03  
% 2.29/1.03  clauses                                 22
% 2.29/1.03  conjectures                             4
% 2.29/1.03  EPR                                     10
% 2.29/1.03  Horn                                    15
% 2.29/1.03  unary                                   4
% 2.29/1.03  binary                                  7
% 2.29/1.03  lits                                    58
% 2.29/1.03  lits eq                                 6
% 2.29/1.03  fd_pure                                 0
% 2.29/1.03  fd_pseudo                               0
% 2.29/1.03  fd_cond                                 0
% 2.29/1.03  fd_pseudo_cond                          6
% 2.29/1.03  AC symbols                              0
% 2.29/1.03  
% 2.29/1.03  ------ Schedule dynamic 5 is on 
% 2.29/1.03  
% 2.29/1.03  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.29/1.03  
% 2.29/1.03  
% 2.29/1.03  ------ 
% 2.29/1.03  Current options:
% 2.29/1.03  ------ 
% 2.29/1.03  
% 2.29/1.03  ------ Input Options
% 2.29/1.03  
% 2.29/1.03  --out_options                           all
% 2.29/1.03  --tptp_safe_out                         true
% 2.29/1.03  --problem_path                          ""
% 2.29/1.03  --include_path                          ""
% 2.29/1.03  --clausifier                            res/vclausify_rel
% 2.29/1.03  --clausifier_options                    --mode clausify
% 2.29/1.03  --stdin                                 false
% 2.29/1.03  --stats_out                             all
% 2.29/1.03  
% 2.29/1.03  ------ General Options
% 2.29/1.03  
% 2.29/1.03  --fof                                   false
% 2.29/1.03  --time_out_real                         305.
% 2.29/1.03  --time_out_virtual                      -1.
% 2.29/1.03  --symbol_type_check                     false
% 2.29/1.03  --clausify_out                          false
% 2.29/1.03  --sig_cnt_out                           false
% 2.29/1.03  --trig_cnt_out                          false
% 2.29/1.03  --trig_cnt_out_tolerance                1.
% 2.29/1.03  --trig_cnt_out_sk_spl                   false
% 2.29/1.03  --abstr_cl_out                          false
% 2.29/1.03  
% 2.29/1.03  ------ Global Options
% 2.29/1.03  
% 2.29/1.03  --schedule                              default
% 2.29/1.03  --add_important_lit                     false
% 2.29/1.03  --prop_solver_per_cl                    1000
% 2.29/1.03  --min_unsat_core                        false
% 2.29/1.03  --soft_assumptions                      false
% 2.29/1.03  --soft_lemma_size                       3
% 2.29/1.03  --prop_impl_unit_size                   0
% 2.29/1.03  --prop_impl_unit                        []
% 2.29/1.03  --share_sel_clauses                     true
% 2.29/1.03  --reset_solvers                         false
% 2.29/1.03  --bc_imp_inh                            [conj_cone]
% 2.29/1.03  --conj_cone_tolerance                   3.
% 2.29/1.03  --extra_neg_conj                        none
% 2.29/1.03  --large_theory_mode                     true
% 2.29/1.03  --prolific_symb_bound                   200
% 2.29/1.03  --lt_threshold                          2000
% 2.29/1.03  --clause_weak_htbl                      true
% 2.29/1.03  --gc_record_bc_elim                     false
% 2.29/1.03  
% 2.29/1.03  ------ Preprocessing Options
% 2.29/1.03  
% 2.29/1.03  --preprocessing_flag                    true
% 2.29/1.03  --time_out_prep_mult                    0.1
% 2.29/1.03  --splitting_mode                        input
% 2.29/1.03  --splitting_grd                         true
% 2.29/1.03  --splitting_cvd                         false
% 2.29/1.03  --splitting_cvd_svl                     false
% 2.29/1.03  --splitting_nvd                         32
% 2.29/1.03  --sub_typing                            true
% 2.29/1.03  --prep_gs_sim                           true
% 2.29/1.03  --prep_unflatten                        true
% 2.29/1.03  --prep_res_sim                          true
% 2.29/1.03  --prep_upred                            true
% 2.29/1.03  --prep_sem_filter                       exhaustive
% 2.29/1.03  --prep_sem_filter_out                   false
% 2.29/1.03  --pred_elim                             true
% 2.29/1.03  --res_sim_input                         true
% 2.29/1.03  --eq_ax_congr_red                       true
% 2.29/1.03  --pure_diseq_elim                       true
% 2.29/1.03  --brand_transform                       false
% 2.29/1.03  --non_eq_to_eq                          false
% 2.29/1.03  --prep_def_merge                        true
% 2.29/1.03  --prep_def_merge_prop_impl              false
% 2.29/1.03  --prep_def_merge_mbd                    true
% 2.29/1.03  --prep_def_merge_tr_red                 false
% 2.29/1.03  --prep_def_merge_tr_cl                  false
% 2.29/1.03  --smt_preprocessing                     true
% 2.29/1.03  --smt_ac_axioms                         fast
% 2.29/1.03  --preprocessed_out                      false
% 2.29/1.03  --preprocessed_stats                    false
% 2.29/1.03  
% 2.29/1.03  ------ Abstraction refinement Options
% 2.29/1.03  
% 2.29/1.03  --abstr_ref                             []
% 2.29/1.03  --abstr_ref_prep                        false
% 2.29/1.03  --abstr_ref_until_sat                   false
% 2.29/1.03  --abstr_ref_sig_restrict                funpre
% 2.29/1.03  --abstr_ref_af_restrict_to_split_sk     false
% 2.29/1.03  --abstr_ref_under                       []
% 2.29/1.03  
% 2.29/1.03  ------ SAT Options
% 2.29/1.03  
% 2.29/1.03  --sat_mode                              false
% 2.29/1.03  --sat_fm_restart_options                ""
% 2.29/1.03  --sat_gr_def                            false
% 2.29/1.03  --sat_epr_types                         true
% 2.29/1.03  --sat_non_cyclic_types                  false
% 2.29/1.03  --sat_finite_models                     false
% 2.29/1.03  --sat_fm_lemmas                         false
% 2.29/1.03  --sat_fm_prep                           false
% 2.29/1.03  --sat_fm_uc_incr                        true
% 2.29/1.03  --sat_out_model                         small
% 2.29/1.03  --sat_out_clauses                       false
% 2.29/1.03  
% 2.29/1.03  ------ QBF Options
% 2.29/1.03  
% 2.29/1.03  --qbf_mode                              false
% 2.29/1.03  --qbf_elim_univ                         false
% 2.29/1.03  --qbf_dom_inst                          none
% 2.29/1.03  --qbf_dom_pre_inst                      false
% 2.29/1.03  --qbf_sk_in                             false
% 2.29/1.03  --qbf_pred_elim                         true
% 2.29/1.03  --qbf_split                             512
% 2.29/1.03  
% 2.29/1.03  ------ BMC1 Options
% 2.29/1.03  
% 2.29/1.03  --bmc1_incremental                      false
% 2.29/1.03  --bmc1_axioms                           reachable_all
% 2.29/1.03  --bmc1_min_bound                        0
% 2.29/1.03  --bmc1_max_bound                        -1
% 2.29/1.03  --bmc1_max_bound_default                -1
% 2.29/1.03  --bmc1_symbol_reachability              true
% 2.29/1.03  --bmc1_property_lemmas                  false
% 2.29/1.03  --bmc1_k_induction                      false
% 2.29/1.03  --bmc1_non_equiv_states                 false
% 2.29/1.03  --bmc1_deadlock                         false
% 2.29/1.03  --bmc1_ucm                              false
% 2.29/1.03  --bmc1_add_unsat_core                   none
% 2.29/1.03  --bmc1_unsat_core_children              false
% 2.29/1.03  --bmc1_unsat_core_extrapolate_axioms    false
% 2.29/1.03  --bmc1_out_stat                         full
% 2.29/1.03  --bmc1_ground_init                      false
% 2.29/1.03  --bmc1_pre_inst_next_state              false
% 2.29/1.03  --bmc1_pre_inst_state                   false
% 2.29/1.03  --bmc1_pre_inst_reach_state             false
% 2.29/1.03  --bmc1_out_unsat_core                   false
% 2.29/1.03  --bmc1_aig_witness_out                  false
% 2.29/1.03  --bmc1_verbose                          false
% 2.29/1.03  --bmc1_dump_clauses_tptp                false
% 2.29/1.03  --bmc1_dump_unsat_core_tptp             false
% 2.29/1.03  --bmc1_dump_file                        -
% 2.29/1.03  --bmc1_ucm_expand_uc_limit              128
% 2.29/1.03  --bmc1_ucm_n_expand_iterations          6
% 2.29/1.03  --bmc1_ucm_extend_mode                  1
% 2.29/1.03  --bmc1_ucm_init_mode                    2
% 2.29/1.03  --bmc1_ucm_cone_mode                    none
% 2.29/1.03  --bmc1_ucm_reduced_relation_type        0
% 2.29/1.03  --bmc1_ucm_relax_model                  4
% 2.29/1.03  --bmc1_ucm_full_tr_after_sat            true
% 2.29/1.03  --bmc1_ucm_expand_neg_assumptions       false
% 2.29/1.03  --bmc1_ucm_layered_model                none
% 2.29/1.03  --bmc1_ucm_max_lemma_size               10
% 2.29/1.03  
% 2.29/1.03  ------ AIG Options
% 2.29/1.03  
% 2.29/1.03  --aig_mode                              false
% 2.29/1.03  
% 2.29/1.03  ------ Instantiation Options
% 2.29/1.03  
% 2.29/1.03  --instantiation_flag                    true
% 2.29/1.03  --inst_sos_flag                         false
% 2.29/1.03  --inst_sos_phase                        true
% 2.29/1.03  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.29/1.03  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.29/1.03  --inst_lit_sel_side                     none
% 2.29/1.03  --inst_solver_per_active                1400
% 2.29/1.03  --inst_solver_calls_frac                1.
% 2.29/1.03  --inst_passive_queue_type               priority_queues
% 2.29/1.03  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.29/1.03  --inst_passive_queues_freq              [25;2]
% 2.29/1.03  --inst_dismatching                      true
% 2.29/1.03  --inst_eager_unprocessed_to_passive     true
% 2.29/1.03  --inst_prop_sim_given                   true
% 2.29/1.03  --inst_prop_sim_new                     false
% 2.29/1.03  --inst_subs_new                         false
% 2.29/1.03  --inst_eq_res_simp                      false
% 2.29/1.03  --inst_subs_given                       false
% 2.29/1.03  --inst_orphan_elimination               true
% 2.29/1.03  --inst_learning_loop_flag               true
% 2.29/1.03  --inst_learning_start                   3000
% 2.29/1.03  --inst_learning_factor                  2
% 2.29/1.03  --inst_start_prop_sim_after_learn       3
% 2.29/1.03  --inst_sel_renew                        solver
% 2.29/1.03  --inst_lit_activity_flag                true
% 2.29/1.03  --inst_restr_to_given                   false
% 2.29/1.03  --inst_activity_threshold               500
% 2.29/1.03  --inst_out_proof                        true
% 2.29/1.03  
% 2.29/1.03  ------ Resolution Options
% 2.29/1.03  
% 2.29/1.03  --resolution_flag                       false
% 2.29/1.03  --res_lit_sel                           adaptive
% 2.29/1.03  --res_lit_sel_side                      none
% 2.29/1.03  --res_ordering                          kbo
% 2.29/1.03  --res_to_prop_solver                    active
% 2.29/1.03  --res_prop_simpl_new                    false
% 2.29/1.03  --res_prop_simpl_given                  true
% 2.29/1.03  --res_passive_queue_type                priority_queues
% 2.29/1.03  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.29/1.03  --res_passive_queues_freq               [15;5]
% 2.29/1.03  --res_forward_subs                      full
% 2.29/1.03  --res_backward_subs                     full
% 2.29/1.03  --res_forward_subs_resolution           true
% 2.29/1.03  --res_backward_subs_resolution          true
% 2.29/1.03  --res_orphan_elimination                true
% 2.29/1.03  --res_time_limit                        2.
% 2.29/1.03  --res_out_proof                         true
% 2.29/1.03  
% 2.29/1.03  ------ Superposition Options
% 2.29/1.03  
% 2.29/1.03  --superposition_flag                    true
% 2.29/1.03  --sup_passive_queue_type                priority_queues
% 2.29/1.03  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.29/1.03  --sup_passive_queues_freq               [8;1;4]
% 2.29/1.03  --demod_completeness_check              fast
% 2.29/1.03  --demod_use_ground                      true
% 2.29/1.03  --sup_to_prop_solver                    passive
% 2.29/1.03  --sup_prop_simpl_new                    true
% 2.29/1.03  --sup_prop_simpl_given                  true
% 2.29/1.03  --sup_fun_splitting                     false
% 2.29/1.03  --sup_smt_interval                      50000
% 2.29/1.03  
% 2.29/1.03  ------ Superposition Simplification Setup
% 2.29/1.03  
% 2.29/1.03  --sup_indices_passive                   []
% 2.29/1.03  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.29/1.03  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.29/1.03  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.29/1.03  --sup_full_triv                         [TrivRules;PropSubs]
% 2.29/1.03  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.29/1.03  --sup_full_bw                           [BwDemod]
% 2.29/1.03  --sup_immed_triv                        [TrivRules]
% 2.29/1.03  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.29/1.03  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.29/1.03  --sup_immed_bw_main                     []
% 2.29/1.03  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.29/1.03  --sup_input_triv                        [Unflattening;TrivRules]
% 2.29/1.03  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.29/1.03  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.29/1.03  
% 2.29/1.03  ------ Combination Options
% 2.29/1.03  
% 2.29/1.03  --comb_res_mult                         3
% 2.29/1.03  --comb_sup_mult                         2
% 2.29/1.03  --comb_inst_mult                        10
% 2.29/1.03  
% 2.29/1.03  ------ Debug Options
% 2.29/1.03  
% 2.29/1.03  --dbg_backtrace                         false
% 2.29/1.03  --dbg_dump_prop_clauses                 false
% 2.29/1.03  --dbg_dump_prop_clauses_file            -
% 2.29/1.03  --dbg_out_stat                          false
% 2.29/1.03  
% 2.29/1.03  
% 2.29/1.03  
% 2.29/1.03  
% 2.29/1.03  ------ Proving...
% 2.29/1.03  
% 2.29/1.03  
% 2.29/1.03  % SZS status Theorem for theBenchmark.p
% 2.29/1.03  
% 2.29/1.03  % SZS output start CNFRefutation for theBenchmark.p
% 2.29/1.03  
% 2.29/1.03  fof(f15,axiom,(
% 2.29/1.03    ! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => ~(~r2_hidden(X1,X0) & X0 != X1 & ~r2_hidden(X0,X1))))),
% 2.29/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.29/1.03  
% 2.29/1.03  fof(f25,plain,(
% 2.29/1.03    ! [X0] : (! [X1] : ((r2_hidden(X1,X0) | X0 = X1 | r2_hidden(X0,X1)) | ~v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 2.29/1.03    inference(ennf_transformation,[],[f15])).
% 2.29/1.03  
% 2.29/1.03  fof(f26,plain,(
% 2.29/1.03    ! [X0] : (! [X1] : (r2_hidden(X1,X0) | X0 = X1 | r2_hidden(X0,X1) | ~v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 2.29/1.03    inference(flattening,[],[f25])).
% 2.29/1.03  
% 2.29/1.03  fof(f71,plain,(
% 2.29/1.03    ( ! [X0,X1] : (r2_hidden(X1,X0) | X0 = X1 | r2_hidden(X0,X1) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0)) )),
% 2.29/1.03    inference(cnf_transformation,[],[f26])).
% 2.29/1.03  
% 2.29/1.03  fof(f16,axiom,(
% 2.29/1.03    ! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => (r2_hidden(X1,X0) | r1_ordinal1(X0,X1))))),
% 2.29/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.29/1.03  
% 2.29/1.03  fof(f27,plain,(
% 2.29/1.03    ! [X0] : (! [X1] : ((r2_hidden(X1,X0) | r1_ordinal1(X0,X1)) | ~v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 2.29/1.03    inference(ennf_transformation,[],[f16])).
% 2.29/1.03  
% 2.29/1.03  fof(f28,plain,(
% 2.29/1.03    ! [X0] : (! [X1] : (r2_hidden(X1,X0) | r1_ordinal1(X0,X1) | ~v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 2.29/1.03    inference(flattening,[],[f27])).
% 2.29/1.03  
% 2.29/1.03  fof(f72,plain,(
% 2.29/1.03    ( ! [X0,X1] : (r2_hidden(X1,X0) | r1_ordinal1(X0,X1) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0)) )),
% 2.29/1.03    inference(cnf_transformation,[],[f28])).
% 2.29/1.03  
% 2.29/1.03  fof(f19,conjecture,(
% 2.29/1.03    ! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => (r2_hidden(X0,X1) <=> r1_ordinal1(k1_ordinal1(X0),X1))))),
% 2.29/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.29/1.03  
% 2.29/1.03  fof(f20,negated_conjecture,(
% 2.29/1.03    ~! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => (r2_hidden(X0,X1) <=> r1_ordinal1(k1_ordinal1(X0),X1))))),
% 2.29/1.03    inference(negated_conjecture,[],[f19])).
% 2.29/1.03  
% 2.29/1.03  fof(f31,plain,(
% 2.29/1.03    ? [X0] : (? [X1] : ((r2_hidden(X0,X1) <~> r1_ordinal1(k1_ordinal1(X0),X1)) & v3_ordinal1(X1)) & v3_ordinal1(X0))),
% 2.29/1.03    inference(ennf_transformation,[],[f20])).
% 2.29/1.03  
% 2.29/1.03  fof(f42,plain,(
% 2.29/1.03    ? [X0] : (? [X1] : (((~r1_ordinal1(k1_ordinal1(X0),X1) | ~r2_hidden(X0,X1)) & (r1_ordinal1(k1_ordinal1(X0),X1) | r2_hidden(X0,X1))) & v3_ordinal1(X1)) & v3_ordinal1(X0))),
% 2.29/1.03    inference(nnf_transformation,[],[f31])).
% 2.29/1.03  
% 2.29/1.03  fof(f43,plain,(
% 2.29/1.03    ? [X0] : (? [X1] : ((~r1_ordinal1(k1_ordinal1(X0),X1) | ~r2_hidden(X0,X1)) & (r1_ordinal1(k1_ordinal1(X0),X1) | r2_hidden(X0,X1)) & v3_ordinal1(X1)) & v3_ordinal1(X0))),
% 2.29/1.03    inference(flattening,[],[f42])).
% 2.29/1.03  
% 2.29/1.03  fof(f45,plain,(
% 2.29/1.03    ( ! [X0] : (? [X1] : ((~r1_ordinal1(k1_ordinal1(X0),X1) | ~r2_hidden(X0,X1)) & (r1_ordinal1(k1_ordinal1(X0),X1) | r2_hidden(X0,X1)) & v3_ordinal1(X1)) => ((~r1_ordinal1(k1_ordinal1(X0),sK2) | ~r2_hidden(X0,sK2)) & (r1_ordinal1(k1_ordinal1(X0),sK2) | r2_hidden(X0,sK2)) & v3_ordinal1(sK2))) )),
% 2.29/1.03    introduced(choice_axiom,[])).
% 2.29/1.03  
% 2.29/1.03  fof(f44,plain,(
% 2.29/1.03    ? [X0] : (? [X1] : ((~r1_ordinal1(k1_ordinal1(X0),X1) | ~r2_hidden(X0,X1)) & (r1_ordinal1(k1_ordinal1(X0),X1) | r2_hidden(X0,X1)) & v3_ordinal1(X1)) & v3_ordinal1(X0)) => (? [X1] : ((~r1_ordinal1(k1_ordinal1(sK1),X1) | ~r2_hidden(sK1,X1)) & (r1_ordinal1(k1_ordinal1(sK1),X1) | r2_hidden(sK1,X1)) & v3_ordinal1(X1)) & v3_ordinal1(sK1))),
% 2.29/1.03    introduced(choice_axiom,[])).
% 2.29/1.03  
% 2.29/1.03  fof(f46,plain,(
% 2.29/1.03    ((~r1_ordinal1(k1_ordinal1(sK1),sK2) | ~r2_hidden(sK1,sK2)) & (r1_ordinal1(k1_ordinal1(sK1),sK2) | r2_hidden(sK1,sK2)) & v3_ordinal1(sK2)) & v3_ordinal1(sK1)),
% 2.29/1.03    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f43,f45,f44])).
% 2.29/1.03  
% 2.29/1.03  fof(f78,plain,(
% 2.29/1.03    ~r1_ordinal1(k1_ordinal1(sK1),sK2) | ~r2_hidden(sK1,sK2)),
% 2.29/1.03    inference(cnf_transformation,[],[f46])).
% 2.29/1.03  
% 2.29/1.03  fof(f12,axiom,(
% 2.29/1.03    ! [X0] : k2_xboole_0(X0,k1_tarski(X0)) = k1_ordinal1(X0)),
% 2.29/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.29/1.03  
% 2.29/1.03  fof(f65,plain,(
% 2.29/1.03    ( ! [X0] : (k2_xboole_0(X0,k1_tarski(X0)) = k1_ordinal1(X0)) )),
% 2.29/1.03    inference(cnf_transformation,[],[f12])).
% 2.29/1.03  
% 2.29/1.03  fof(f10,axiom,(
% 2.29/1.03    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 2.29/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.29/1.03  
% 2.29/1.03  fof(f63,plain,(
% 2.29/1.03    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 2.29/1.03    inference(cnf_transformation,[],[f10])).
% 2.29/1.03  
% 2.29/1.03  fof(f84,plain,(
% 2.29/1.03    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) )),
% 2.29/1.03    inference(definition_unfolding,[],[f63,f83])).
% 2.29/1.03  
% 2.29/1.03  fof(f3,axiom,(
% 2.29/1.03    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 2.29/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.29/1.03  
% 2.29/1.03  fof(f56,plain,(
% 2.29/1.03    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 2.29/1.03    inference(cnf_transformation,[],[f3])).
% 2.29/1.03  
% 2.29/1.03  fof(f4,axiom,(
% 2.29/1.03    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 2.29/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.29/1.03  
% 2.29/1.03  fof(f57,plain,(
% 2.29/1.03    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 2.29/1.03    inference(cnf_transformation,[],[f4])).
% 2.29/1.03  
% 2.29/1.03  fof(f5,axiom,(
% 2.29/1.03    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 2.29/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.29/1.03  
% 2.29/1.03  fof(f58,plain,(
% 2.29/1.03    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 2.29/1.03    inference(cnf_transformation,[],[f5])).
% 2.29/1.03  
% 2.29/1.03  fof(f6,axiom,(
% 2.29/1.03    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 2.29/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.29/1.03  
% 2.29/1.03  fof(f59,plain,(
% 2.29/1.03    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 2.29/1.03    inference(cnf_transformation,[],[f6])).
% 2.29/1.03  
% 2.29/1.03  fof(f7,axiom,(
% 2.29/1.03    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)),
% 2.29/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.29/1.03  
% 2.29/1.03  fof(f60,plain,(
% 2.29/1.03    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)) )),
% 2.29/1.03    inference(cnf_transformation,[],[f7])).
% 2.29/1.03  
% 2.29/1.03  fof(f8,axiom,(
% 2.29/1.03    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)),
% 2.29/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.29/1.03  
% 2.29/1.03  fof(f61,plain,(
% 2.29/1.03    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)) )),
% 2.29/1.03    inference(cnf_transformation,[],[f8])).
% 2.29/1.03  
% 2.29/1.03  fof(f9,axiom,(
% 2.29/1.03    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)),
% 2.29/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.29/1.03  
% 2.29/1.03  fof(f62,plain,(
% 2.29/1.03    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)) )),
% 2.29/1.03    inference(cnf_transformation,[],[f9])).
% 2.29/1.03  
% 2.29/1.03  fof(f79,plain,(
% 2.29/1.03    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 2.29/1.03    inference(definition_unfolding,[],[f61,f62])).
% 2.29/1.03  
% 2.29/1.03  fof(f80,plain,(
% 2.29/1.03    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 2.29/1.03    inference(definition_unfolding,[],[f60,f79])).
% 2.29/1.03  
% 2.29/1.03  fof(f81,plain,(
% 2.29/1.03    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 2.29/1.03    inference(definition_unfolding,[],[f59,f80])).
% 2.29/1.03  
% 2.29/1.03  fof(f82,plain,(
% 2.29/1.03    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 2.29/1.03    inference(definition_unfolding,[],[f58,f81])).
% 2.29/1.03  
% 2.29/1.03  fof(f83,plain,(
% 2.29/1.03    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 2.29/1.03    inference(definition_unfolding,[],[f57,f82])).
% 2.29/1.03  
% 2.29/1.03  fof(f85,plain,(
% 2.29/1.03    ( ! [X0] : (k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) )),
% 2.29/1.03    inference(definition_unfolding,[],[f56,f83])).
% 2.29/1.03  
% 2.29/1.03  fof(f86,plain,(
% 2.29/1.03    ( ! [X0] : (k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))) = k1_ordinal1(X0)) )),
% 2.29/1.03    inference(definition_unfolding,[],[f65,f84,f85])).
% 2.29/1.03  
% 2.29/1.03  fof(f97,plain,(
% 2.29/1.03    ~r1_ordinal1(k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))),sK2) | ~r2_hidden(sK1,sK2)),
% 2.29/1.03    inference(definition_unfolding,[],[f78,f86])).
% 2.29/1.03  
% 2.29/1.03  fof(f75,plain,(
% 2.29/1.03    v3_ordinal1(sK1)),
% 2.29/1.03    inference(cnf_transformation,[],[f46])).
% 2.29/1.03  
% 2.29/1.03  fof(f76,plain,(
% 2.29/1.03    v3_ordinal1(sK2)),
% 2.29/1.03    inference(cnf_transformation,[],[f46])).
% 2.29/1.03  
% 2.29/1.03  fof(f17,axiom,(
% 2.29/1.03    ! [X0] : (v3_ordinal1(X0) => v3_ordinal1(k1_ordinal1(X0)))),
% 2.29/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.29/1.03  
% 2.29/1.03  fof(f29,plain,(
% 2.29/1.03    ! [X0] : (v3_ordinal1(k1_ordinal1(X0)) | ~v3_ordinal1(X0))),
% 2.29/1.03    inference(ennf_transformation,[],[f17])).
% 2.29/1.03  
% 2.29/1.03  fof(f73,plain,(
% 2.29/1.03    ( ! [X0] : (v3_ordinal1(k1_ordinal1(X0)) | ~v3_ordinal1(X0)) )),
% 2.29/1.03    inference(cnf_transformation,[],[f29])).
% 2.29/1.03  
% 2.29/1.03  fof(f96,plain,(
% 2.29/1.03    ( ! [X0] : (v3_ordinal1(k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)))) | ~v3_ordinal1(X0)) )),
% 2.29/1.03    inference(definition_unfolding,[],[f73,f86])).
% 2.29/1.03  
% 2.29/1.03  fof(f14,axiom,(
% 2.29/1.03    ! [X0,X1] : (r2_hidden(X0,k1_ordinal1(X1)) <=> (X0 = X1 | r2_hidden(X0,X1)))),
% 2.29/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.29/1.03  
% 2.29/1.03  fof(f40,plain,(
% 2.29/1.03    ! [X0,X1] : ((r2_hidden(X0,k1_ordinal1(X1)) | (X0 != X1 & ~r2_hidden(X0,X1))) & ((X0 = X1 | r2_hidden(X0,X1)) | ~r2_hidden(X0,k1_ordinal1(X1))))),
% 2.29/1.03    inference(nnf_transformation,[],[f14])).
% 2.29/1.03  
% 2.29/1.03  fof(f41,plain,(
% 2.29/1.03    ! [X0,X1] : ((r2_hidden(X0,k1_ordinal1(X1)) | (X0 != X1 & ~r2_hidden(X0,X1))) & (X0 = X1 | r2_hidden(X0,X1) | ~r2_hidden(X0,k1_ordinal1(X1))))),
% 2.29/1.03    inference(flattening,[],[f40])).
% 2.29/1.03  
% 2.29/1.03  fof(f68,plain,(
% 2.29/1.03    ( ! [X0,X1] : (X0 = X1 | r2_hidden(X0,X1) | ~r2_hidden(X0,k1_ordinal1(X1))) )),
% 2.29/1.03    inference(cnf_transformation,[],[f41])).
% 2.29/1.03  
% 2.29/1.03  fof(f95,plain,(
% 2.29/1.03    ( ! [X0,X1] : (X0 = X1 | r2_hidden(X0,X1) | ~r2_hidden(X0,k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))))) )),
% 2.29/1.03    inference(definition_unfolding,[],[f68,f86])).
% 2.29/1.03  
% 2.29/1.03  fof(f18,axiom,(
% 2.29/1.03    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 2.29/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.29/1.03  
% 2.29/1.03  fof(f30,plain,(
% 2.29/1.03    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 2.29/1.03    inference(ennf_transformation,[],[f18])).
% 2.29/1.03  
% 2.29/1.03  fof(f74,plain,(
% 2.29/1.03    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1)) )),
% 2.29/1.03    inference(cnf_transformation,[],[f30])).
% 2.29/1.03  
% 2.29/1.03  fof(f13,axiom,(
% 2.29/1.03    ! [X0,X1] : ((v3_ordinal1(X1) & v3_ordinal1(X0)) => (r1_ordinal1(X0,X1) <=> r1_tarski(X0,X1)))),
% 2.29/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.29/1.03  
% 2.29/1.03  fof(f23,plain,(
% 2.29/1.03    ! [X0,X1] : ((r1_ordinal1(X0,X1) <=> r1_tarski(X0,X1)) | (~v3_ordinal1(X1) | ~v3_ordinal1(X0)))),
% 2.29/1.03    inference(ennf_transformation,[],[f13])).
% 2.29/1.03  
% 2.29/1.03  fof(f24,plain,(
% 2.29/1.03    ! [X0,X1] : ((r1_ordinal1(X0,X1) <=> r1_tarski(X0,X1)) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0))),
% 2.29/1.03    inference(flattening,[],[f23])).
% 2.29/1.03  
% 2.29/1.03  fof(f39,plain,(
% 2.29/1.03    ! [X0,X1] : (((r1_ordinal1(X0,X1) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~r1_ordinal1(X0,X1))) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0))),
% 2.29/1.03    inference(nnf_transformation,[],[f24])).
% 2.29/1.03  
% 2.29/1.03  fof(f66,plain,(
% 2.29/1.03    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r1_ordinal1(X0,X1) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0)) )),
% 2.29/1.03    inference(cnf_transformation,[],[f39])).
% 2.29/1.03  
% 2.29/1.03  fof(f11,axiom,(
% 2.29/1.03    ! [X0,X1] : ((v3_ordinal1(X1) & v3_ordinal1(X0)) => (r1_ordinal1(X1,X0) | r1_ordinal1(X0,X1)))),
% 2.29/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.29/1.03  
% 2.29/1.03  fof(f21,plain,(
% 2.29/1.03    ! [X0,X1] : ((r1_ordinal1(X1,X0) | r1_ordinal1(X0,X1)) | (~v3_ordinal1(X1) | ~v3_ordinal1(X0)))),
% 2.29/1.03    inference(ennf_transformation,[],[f11])).
% 2.29/1.03  
% 2.29/1.03  fof(f22,plain,(
% 2.29/1.03    ! [X0,X1] : (r1_ordinal1(X1,X0) | r1_ordinal1(X0,X1) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0))),
% 2.29/1.03    inference(flattening,[],[f21])).
% 2.29/1.03  
% 2.29/1.03  fof(f64,plain,(
% 2.29/1.03    ( ! [X0,X1] : (r1_ordinal1(X1,X0) | r1_ordinal1(X0,X1) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0)) )),
% 2.29/1.03    inference(cnf_transformation,[],[f22])).
% 2.29/1.03  
% 2.29/1.03  fof(f1,axiom,(
% 2.29/1.03    ! [X0,X1,X2] : (k2_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) | r2_hidden(X3,X0))))),
% 2.29/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.29/1.03  
% 2.29/1.03  fof(f32,plain,(
% 2.29/1.03    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) | r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) & ~r2_hidden(X3,X0))) & ((r2_hidden(X3,X1) | r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k2_xboole_0(X0,X1) != X2))),
% 2.29/1.03    inference(nnf_transformation,[],[f1])).
% 2.29/1.03  
% 2.29/1.03  fof(f33,plain,(
% 2.29/1.03    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) & ~r2_hidden(X3,X0))) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | ~r2_hidden(X3,X2))) | k2_xboole_0(X0,X1) != X2))),
% 2.29/1.03    inference(flattening,[],[f32])).
% 2.29/1.03  
% 2.29/1.03  fof(f34,plain,(
% 2.29/1.03    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (~r2_hidden(X4,X1) & ~r2_hidden(X4,X0))) & (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,X2))) | k2_xboole_0(X0,X1) != X2))),
% 2.29/1.03    inference(rectify,[],[f33])).
% 2.29/1.03  
% 2.29/1.03  fof(f35,plain,(
% 2.29/1.03    ! [X2,X1,X0] : (? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2))) => (((~r2_hidden(sK0(X0,X1,X2),X1) & ~r2_hidden(sK0(X0,X1,X2),X0)) | ~r2_hidden(sK0(X0,X1,X2),X2)) & (r2_hidden(sK0(X0,X1,X2),X1) | r2_hidden(sK0(X0,X1,X2),X0) | r2_hidden(sK0(X0,X1,X2),X2))))),
% 2.29/1.03    introduced(choice_axiom,[])).
% 2.29/1.03  
% 2.29/1.03  fof(f36,plain,(
% 2.29/1.03    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | (((~r2_hidden(sK0(X0,X1,X2),X1) & ~r2_hidden(sK0(X0,X1,X2),X0)) | ~r2_hidden(sK0(X0,X1,X2),X2)) & (r2_hidden(sK0(X0,X1,X2),X1) | r2_hidden(sK0(X0,X1,X2),X0) | r2_hidden(sK0(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (~r2_hidden(X4,X1) & ~r2_hidden(X4,X0))) & (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,X2))) | k2_xboole_0(X0,X1) != X2))),
% 2.29/1.03    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f34,f35])).
% 2.29/1.03  
% 2.29/1.03  fof(f48,plain,(
% 2.29/1.03    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | ~r2_hidden(X4,X0) | k2_xboole_0(X0,X1) != X2) )),
% 2.29/1.03    inference(cnf_transformation,[],[f36])).
% 2.29/1.03  
% 2.29/1.03  fof(f91,plain,(
% 2.29/1.03    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | ~r2_hidden(X4,X0) | k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) != X2) )),
% 2.29/1.03    inference(definition_unfolding,[],[f48,f84])).
% 2.29/1.03  
% 2.29/1.03  fof(f100,plain,(
% 2.29/1.03    ( ! [X4,X0,X1] : (r2_hidden(X4,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) | ~r2_hidden(X4,X0)) )),
% 2.29/1.03    inference(equality_resolution,[],[f91])).
% 2.29/1.03  
% 2.29/1.03  fof(f77,plain,(
% 2.29/1.03    r1_ordinal1(k1_ordinal1(sK1),sK2) | r2_hidden(sK1,sK2)),
% 2.29/1.03    inference(cnf_transformation,[],[f46])).
% 2.29/1.03  
% 2.29/1.03  fof(f98,plain,(
% 2.29/1.03    r1_ordinal1(k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))),sK2) | r2_hidden(sK1,sK2)),
% 2.29/1.03    inference(definition_unfolding,[],[f77,f86])).
% 2.29/1.03  
% 2.29/1.03  fof(f69,plain,(
% 2.29/1.03    ( ! [X0,X1] : (r2_hidden(X0,k1_ordinal1(X1)) | ~r2_hidden(X0,X1)) )),
% 2.29/1.03    inference(cnf_transformation,[],[f41])).
% 2.29/1.03  
% 2.29/1.03  fof(f94,plain,(
% 2.29/1.03    ( ! [X0,X1] : (r2_hidden(X0,k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)))) | ~r2_hidden(X0,X1)) )),
% 2.29/1.03    inference(definition_unfolding,[],[f69,f86])).
% 2.29/1.03  
% 2.29/1.03  fof(f2,axiom,(
% 2.29/1.03    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 2.29/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.29/1.03  
% 2.29/1.03  fof(f37,plain,(
% 2.29/1.03    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.29/1.03    inference(nnf_transformation,[],[f2])).
% 2.29/1.03  
% 2.29/1.03  fof(f38,plain,(
% 2.29/1.03    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.29/1.03    inference(flattening,[],[f37])).
% 2.29/1.03  
% 2.29/1.03  fof(f54,plain,(
% 2.29/1.03    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 2.29/1.03    inference(cnf_transformation,[],[f38])).
% 2.29/1.03  
% 2.29/1.03  fof(f102,plain,(
% 2.29/1.03    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 2.29/1.03    inference(equality_resolution,[],[f54])).
% 2.29/1.03  
% 2.29/1.03  fof(f70,plain,(
% 2.29/1.03    ( ! [X0,X1] : (r2_hidden(X0,k1_ordinal1(X1)) | X0 != X1) )),
% 2.29/1.03    inference(cnf_transformation,[],[f41])).
% 2.29/1.03  
% 2.29/1.03  fof(f93,plain,(
% 2.29/1.03    ( ! [X0,X1] : (r2_hidden(X0,k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)))) | X0 != X1) )),
% 2.29/1.03    inference(definition_unfolding,[],[f70,f86])).
% 2.29/1.03  
% 2.29/1.03  fof(f104,plain,(
% 2.29/1.03    ( ! [X1] : (r2_hidden(X1,k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))))) )),
% 2.29/1.03    inference(equality_resolution,[],[f93])).
% 2.29/1.03  
% 2.29/1.03  cnf(c_15,plain,
% 2.29/1.03      ( r2_hidden(X0,X1)
% 2.29/1.03      | r2_hidden(X1,X0)
% 2.29/1.03      | ~ v3_ordinal1(X1)
% 2.29/1.03      | ~ v3_ordinal1(X0)
% 2.29/1.03      | X1 = X0 ),
% 2.29/1.03      inference(cnf_transformation,[],[f71]) ).
% 2.29/1.03  
% 2.29/1.03  cnf(c_987,plain,
% 2.29/1.03      ( X0 = X1
% 2.29/1.03      | r2_hidden(X0,X1) = iProver_top
% 2.29/1.03      | r2_hidden(X1,X0) = iProver_top
% 2.29/1.03      | v3_ordinal1(X1) != iProver_top
% 2.29/1.03      | v3_ordinal1(X0) != iProver_top ),
% 2.29/1.03      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 2.29/1.03  
% 2.29/1.03  cnf(c_16,plain,
% 2.29/1.03      ( r1_ordinal1(X0,X1)
% 2.29/1.03      | r2_hidden(X1,X0)
% 2.29/1.03      | ~ v3_ordinal1(X1)
% 2.29/1.03      | ~ v3_ordinal1(X0) ),
% 2.29/1.03      inference(cnf_transformation,[],[f72]) ).
% 2.29/1.03  
% 2.29/1.03  cnf(c_986,plain,
% 2.29/1.03      ( r1_ordinal1(X0,X1) = iProver_top
% 2.29/1.03      | r2_hidden(X1,X0) = iProver_top
% 2.29/1.03      | v3_ordinal1(X0) != iProver_top
% 2.29/1.03      | v3_ordinal1(X1) != iProver_top ),
% 2.29/1.03      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 2.29/1.03  
% 2.29/1.03  cnf(c_19,negated_conjecture,
% 2.29/1.03      ( ~ r1_ordinal1(k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))),sK2)
% 2.29/1.03      | ~ r2_hidden(sK1,sK2) ),
% 2.29/1.03      inference(cnf_transformation,[],[f97]) ).
% 2.29/1.03  
% 2.29/1.03  cnf(c_983,plain,
% 2.29/1.03      ( r1_ordinal1(k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))),sK2) != iProver_top
% 2.29/1.03      | r2_hidden(sK1,sK2) != iProver_top ),
% 2.29/1.03      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 2.29/1.03  
% 2.29/1.03  cnf(c_2360,plain,
% 2.29/1.03      ( r2_hidden(sK2,k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)))) = iProver_top
% 2.29/1.03      | r2_hidden(sK1,sK2) != iProver_top
% 2.29/1.03      | v3_ordinal1(k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)))) != iProver_top
% 2.29/1.03      | v3_ordinal1(sK2) != iProver_top ),
% 2.29/1.03      inference(superposition,[status(thm)],[c_986,c_983]) ).
% 2.29/1.03  
% 2.29/1.03  cnf(c_22,negated_conjecture,
% 2.29/1.03      ( v3_ordinal1(sK1) ),
% 2.29/1.03      inference(cnf_transformation,[],[f75]) ).
% 2.29/1.03  
% 2.29/1.03  cnf(c_23,plain,
% 2.29/1.03      ( v3_ordinal1(sK1) = iProver_top ),
% 2.29/1.03      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 2.29/1.03  
% 2.29/1.03  cnf(c_21,negated_conjecture,
% 2.29/1.03      ( v3_ordinal1(sK2) ),
% 2.29/1.03      inference(cnf_transformation,[],[f76]) ).
% 2.29/1.03  
% 2.29/1.03  cnf(c_24,plain,
% 2.29/1.03      ( v3_ordinal1(sK2) = iProver_top ),
% 2.29/1.03      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 2.29/1.03  
% 2.29/1.03  cnf(c_17,plain,
% 2.29/1.03      ( ~ v3_ordinal1(X0)
% 2.29/1.03      | v3_ordinal1(k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)))) ),
% 2.29/1.03      inference(cnf_transformation,[],[f96]) ).
% 2.29/1.03  
% 2.29/1.03  cnf(c_30,plain,
% 2.29/1.03      ( v3_ordinal1(X0) != iProver_top
% 2.29/1.03      | v3_ordinal1(k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)))) = iProver_top ),
% 2.29/1.03      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 2.29/1.03  
% 2.29/1.03  cnf(c_32,plain,
% 2.29/1.03      ( v3_ordinal1(k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)))) = iProver_top
% 2.29/1.03      | v3_ordinal1(sK1) != iProver_top ),
% 2.29/1.03      inference(instantiation,[status(thm)],[c_30]) ).
% 2.29/1.03  
% 2.29/1.03  cnf(c_3058,plain,
% 2.29/1.03      ( r2_hidden(sK2,k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)))) = iProver_top
% 2.29/1.03      | r2_hidden(sK1,sK2) != iProver_top ),
% 2.29/1.03      inference(global_propositional_subsumption,
% 2.29/1.03                [status(thm)],
% 2.29/1.03                [c_2360,c_23,c_24,c_32]) ).
% 2.29/1.03  
% 2.29/1.03  cnf(c_14,plain,
% 2.29/1.03      ( r2_hidden(X0,X1)
% 2.29/1.03      | ~ r2_hidden(X0,k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))))
% 2.29/1.03      | X1 = X0 ),
% 2.29/1.03      inference(cnf_transformation,[],[f95]) ).
% 2.29/1.03  
% 2.29/1.03  cnf(c_988,plain,
% 2.29/1.03      ( X0 = X1
% 2.29/1.03      | r2_hidden(X1,X0) = iProver_top
% 2.29/1.03      | r2_hidden(X1,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)))) != iProver_top ),
% 2.29/1.03      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 2.29/1.03  
% 2.29/1.03  cnf(c_3995,plain,
% 2.29/1.03      ( sK2 = sK1
% 2.29/1.03      | r2_hidden(sK2,sK1) = iProver_top
% 2.29/1.03      | r2_hidden(sK1,sK2) != iProver_top ),
% 2.29/1.03      inference(superposition,[status(thm)],[c_3058,c_988]) ).
% 2.29/1.03  
% 2.29/1.03  cnf(c_18,plain,
% 2.29/1.03      ( ~ r1_tarski(X0,X1) | ~ r2_hidden(X1,X0) ),
% 2.29/1.03      inference(cnf_transformation,[],[f74]) ).
% 2.29/1.03  
% 2.29/1.03  cnf(c_28,plain,
% 2.29/1.03      ( ~ r1_tarski(sK1,sK1) | ~ r2_hidden(sK1,sK1) ),
% 2.29/1.03      inference(instantiation,[status(thm)],[c_18]) ).
% 2.29/1.03  
% 2.29/1.03  cnf(c_37,plain,
% 2.29/1.03      ( r2_hidden(sK1,sK1) | ~ v3_ordinal1(sK1) | sK1 = sK1 ),
% 2.29/1.03      inference(instantiation,[status(thm)],[c_15]) ).
% 2.29/1.03  
% 2.29/1.03  cnf(c_11,plain,
% 2.29/1.03      ( ~ r1_ordinal1(X0,X1)
% 2.29/1.03      | r1_tarski(X0,X1)
% 2.29/1.03      | ~ v3_ordinal1(X1)
% 2.29/1.03      | ~ v3_ordinal1(X0) ),
% 2.29/1.03      inference(cnf_transformation,[],[f66]) ).
% 2.29/1.03  
% 2.29/1.03  cnf(c_49,plain,
% 2.29/1.03      ( ~ r1_ordinal1(sK1,sK1)
% 2.29/1.03      | r1_tarski(sK1,sK1)
% 2.29/1.03      | ~ v3_ordinal1(sK1) ),
% 2.29/1.03      inference(instantiation,[status(thm)],[c_11]) ).
% 2.29/1.03  
% 2.29/1.03  cnf(c_9,plain,
% 2.29/1.03      ( r1_ordinal1(X0,X1)
% 2.29/1.03      | r1_ordinal1(X1,X0)
% 2.29/1.03      | ~ v3_ordinal1(X1)
% 2.29/1.03      | ~ v3_ordinal1(X0) ),
% 2.29/1.03      inference(cnf_transformation,[],[f64]) ).
% 2.29/1.03  
% 2.29/1.03  cnf(c_55,plain,
% 2.29/1.03      ( r1_ordinal1(sK1,sK1) | ~ v3_ordinal1(sK1) ),
% 2.29/1.03      inference(instantiation,[status(thm)],[c_9]) ).
% 2.29/1.03  
% 2.29/1.03  cnf(c_54,plain,
% 2.29/1.03      ( r1_ordinal1(X0,X1) = iProver_top
% 2.29/1.03      | r1_ordinal1(X1,X0) = iProver_top
% 2.29/1.03      | v3_ordinal1(X0) != iProver_top
% 2.29/1.03      | v3_ordinal1(X1) != iProver_top ),
% 2.29/1.03      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 2.29/1.03  
% 2.29/1.03  cnf(c_56,plain,
% 2.29/1.03      ( r1_ordinal1(sK1,sK1) = iProver_top
% 2.29/1.03      | v3_ordinal1(sK1) != iProver_top ),
% 2.29/1.03      inference(instantiation,[status(thm)],[c_54]) ).
% 2.29/1.03  
% 2.29/1.03  cnf(c_1687,plain,
% 2.29/1.03      ( ~ r1_tarski(sK2,sK1) | ~ r2_hidden(sK1,sK2) ),
% 2.29/1.03      inference(instantiation,[status(thm)],[c_18]) ).
% 2.29/1.03  
% 2.29/1.03  cnf(c_1688,plain,
% 2.29/1.03      ( r1_tarski(sK2,sK1) != iProver_top
% 2.29/1.03      | r2_hidden(sK1,sK2) != iProver_top ),
% 2.29/1.03      inference(predicate_to_equality,[status(thm)],[c_1687]) ).
% 2.29/1.03  
% 2.29/1.03  cnf(c_2643,plain,
% 2.29/1.03      ( ~ r1_ordinal1(sK2,sK1)
% 2.29/1.03      | r1_tarski(sK2,sK1)
% 2.29/1.03      | ~ v3_ordinal1(sK2)
% 2.29/1.03      | ~ v3_ordinal1(sK1) ),
% 2.29/1.03      inference(instantiation,[status(thm)],[c_11]) ).
% 2.29/1.03  
% 2.29/1.03  cnf(c_2644,plain,
% 2.29/1.03      ( r1_ordinal1(sK2,sK1) != iProver_top
% 2.29/1.03      | r1_tarski(sK2,sK1) = iProver_top
% 2.29/1.03      | v3_ordinal1(sK2) != iProver_top
% 2.29/1.03      | v3_ordinal1(sK1) != iProver_top ),
% 2.29/1.03      inference(predicate_to_equality,[status(thm)],[c_2643]) ).
% 2.29/1.03  
% 2.29/1.03  cnf(c_487,plain,
% 2.29/1.03      ( ~ r1_ordinal1(X0,X1) | r1_ordinal1(X2,X3) | X2 != X0 | X3 != X1 ),
% 2.29/1.03      theory(equality) ).
% 2.29/1.03  
% 2.29/1.03  cnf(c_4825,plain,
% 2.29/1.03      ( ~ r1_ordinal1(X0,X1)
% 2.29/1.03      | r1_ordinal1(sK2,sK1)
% 2.29/1.03      | sK2 != X0
% 2.29/1.03      | sK1 != X1 ),
% 2.29/1.03      inference(instantiation,[status(thm)],[c_487]) ).
% 2.29/1.03  
% 2.29/1.03  cnf(c_4826,plain,
% 2.29/1.03      ( sK2 != X0
% 2.29/1.03      | sK1 != X1
% 2.29/1.03      | r1_ordinal1(X0,X1) != iProver_top
% 2.29/1.03      | r1_ordinal1(sK2,sK1) = iProver_top ),
% 2.29/1.03      inference(predicate_to_equality,[status(thm)],[c_4825]) ).
% 2.29/1.03  
% 2.29/1.03  cnf(c_4828,plain,
% 2.29/1.03      ( sK2 != sK1
% 2.29/1.03      | sK1 != sK1
% 2.29/1.03      | r1_ordinal1(sK2,sK1) = iProver_top
% 2.29/1.03      | r1_ordinal1(sK1,sK1) != iProver_top ),
% 2.29/1.03      inference(instantiation,[status(thm)],[c_4826]) ).
% 2.29/1.03  
% 2.29/1.03  cnf(c_4887,plain,
% 2.29/1.03      ( r2_hidden(sK2,sK1) = iProver_top
% 2.29/1.03      | r2_hidden(sK1,sK2) != iProver_top ),
% 2.29/1.03      inference(global_propositional_subsumption,
% 2.29/1.03                [status(thm)],
% 2.29/1.03                [c_3995,c_22,c_23,c_24,c_28,c_37,c_49,c_55,c_56,c_1688,
% 2.29/1.03                 c_2644,c_4828]) ).
% 2.29/1.03  
% 2.29/1.03  cnf(c_4893,plain,
% 2.29/1.03      ( sK2 = sK1
% 2.29/1.03      | r2_hidden(sK2,sK1) = iProver_top
% 2.29/1.03      | v3_ordinal1(sK2) != iProver_top
% 2.29/1.03      | v3_ordinal1(sK1) != iProver_top ),
% 2.29/1.03      inference(superposition,[status(thm)],[c_987,c_4887]) ).
% 2.29/1.03  
% 2.29/1.03  cnf(c_4897,plain,
% 2.29/1.03      ( sK2 = sK1 | r2_hidden(sK2,sK1) = iProver_top ),
% 2.29/1.03      inference(global_propositional_subsumption,
% 2.29/1.03                [status(thm)],
% 2.29/1.03                [c_4893,c_23,c_24]) ).
% 2.29/1.03  
% 2.29/1.03  cnf(c_4,plain,
% 2.29/1.03      ( ~ r2_hidden(X0,X1)
% 2.29/1.03      | r2_hidden(X0,k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))) ),
% 2.29/1.03      inference(cnf_transformation,[],[f100]) ).
% 2.29/1.03  
% 2.29/1.03  cnf(c_997,plain,
% 2.29/1.03      ( r2_hidden(X0,X1) != iProver_top
% 2.29/1.03      | r2_hidden(X0,k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))) = iProver_top ),
% 2.29/1.03      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 2.29/1.03  
% 2.29/1.03  cnf(c_20,negated_conjecture,
% 2.29/1.03      ( r1_ordinal1(k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))),sK2)
% 2.29/1.03      | r2_hidden(sK1,sK2) ),
% 2.29/1.03      inference(cnf_transformation,[],[f98]) ).
% 2.29/1.03  
% 2.29/1.03  cnf(c_982,plain,
% 2.29/1.03      ( r1_ordinal1(k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))),sK2) = iProver_top
% 2.29/1.03      | r2_hidden(sK1,sK2) = iProver_top ),
% 2.29/1.03      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 2.29/1.03  
% 2.29/1.03  cnf(c_991,plain,
% 2.29/1.03      ( r1_ordinal1(X0,X1) != iProver_top
% 2.29/1.03      | r1_tarski(X0,X1) = iProver_top
% 2.29/1.03      | v3_ordinal1(X0) != iProver_top
% 2.29/1.03      | v3_ordinal1(X1) != iProver_top ),
% 2.29/1.03      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 2.29/1.03  
% 2.29/1.03  cnf(c_2001,plain,
% 2.29/1.03      ( r1_tarski(k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))),sK2) = iProver_top
% 2.29/1.03      | r2_hidden(sK1,sK2) = iProver_top
% 2.29/1.03      | v3_ordinal1(k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)))) != iProver_top
% 2.29/1.03      | v3_ordinal1(sK2) != iProver_top ),
% 2.29/1.03      inference(superposition,[status(thm)],[c_982,c_991]) ).
% 2.29/1.03  
% 2.29/1.03  cnf(c_2004,plain,
% 2.29/1.03      ( r1_tarski(k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))),sK2) = iProver_top
% 2.29/1.03      | r2_hidden(sK1,sK2) = iProver_top ),
% 2.29/1.03      inference(global_propositional_subsumption,
% 2.29/1.03                [status(thm)],
% 2.29/1.03                [c_2001,c_23,c_24,c_32]) ).
% 2.29/1.03  
% 2.29/1.03  cnf(c_984,plain,
% 2.29/1.03      ( r1_tarski(X0,X1) != iProver_top
% 2.29/1.03      | r2_hidden(X1,X0) != iProver_top ),
% 2.29/1.03      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 2.29/1.03  
% 2.29/1.03  cnf(c_2011,plain,
% 2.29/1.03      ( r2_hidden(sK2,k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)))) != iProver_top
% 2.29/1.03      | r2_hidden(sK1,sK2) = iProver_top ),
% 2.29/1.03      inference(superposition,[status(thm)],[c_2004,c_984]) ).
% 2.29/1.03  
% 2.29/1.03  cnf(c_2252,plain,
% 2.29/1.03      ( r2_hidden(sK2,sK1) != iProver_top
% 2.29/1.03      | r2_hidden(sK1,sK2) = iProver_top ),
% 2.29/1.03      inference(superposition,[status(thm)],[c_997,c_2011]) ).
% 2.29/1.03  
% 2.29/1.03  cnf(c_4903,plain,
% 2.29/1.03      ( sK2 = sK1 | r2_hidden(sK1,sK2) = iProver_top ),
% 2.29/1.03      inference(superposition,[status(thm)],[c_4897,c_2252]) ).
% 2.29/1.03  
% 2.29/1.03  cnf(c_993,plain,
% 2.29/1.03      ( r1_ordinal1(X0,X1) = iProver_top
% 2.29/1.03      | r1_ordinal1(X1,X0) = iProver_top
% 2.29/1.03      | v3_ordinal1(X0) != iProver_top
% 2.29/1.03      | v3_ordinal1(X1) != iProver_top ),
% 2.29/1.03      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 2.29/1.03  
% 2.29/1.03  cnf(c_2653,plain,
% 2.29/1.03      ( r1_ordinal1(X0,X1) = iProver_top
% 2.29/1.03      | r1_tarski(X1,X0) = iProver_top
% 2.29/1.03      | v3_ordinal1(X0) != iProver_top
% 2.29/1.03      | v3_ordinal1(X1) != iProver_top ),
% 2.29/1.03      inference(superposition,[status(thm)],[c_993,c_991]) ).
% 2.29/1.03  
% 2.29/1.03  cnf(c_6478,plain,
% 2.29/1.03      ( r1_tarski(X0,X1) = iProver_top
% 2.29/1.03      | r1_tarski(X1,X0) = iProver_top
% 2.29/1.03      | v3_ordinal1(X0) != iProver_top
% 2.29/1.03      | v3_ordinal1(X1) != iProver_top ),
% 2.29/1.03      inference(superposition,[status(thm)],[c_2653,c_991]) ).
% 2.29/1.03  
% 2.29/1.03  cnf(c_6722,plain,
% 2.29/1.03      ( r1_tarski(X0,X1) = iProver_top
% 2.29/1.03      | r2_hidden(X0,X1) != iProver_top
% 2.29/1.03      | v3_ordinal1(X0) != iProver_top
% 2.29/1.03      | v3_ordinal1(X1) != iProver_top ),
% 2.29/1.03      inference(superposition,[status(thm)],[c_6478,c_984]) ).
% 2.29/1.03  
% 2.29/1.03  cnf(c_6758,plain,
% 2.29/1.03      ( sK2 = sK1
% 2.29/1.03      | r1_tarski(sK2,sK1) = iProver_top
% 2.29/1.03      | v3_ordinal1(sK2) != iProver_top
% 2.29/1.03      | v3_ordinal1(sK1) != iProver_top ),
% 2.29/1.03      inference(superposition,[status(thm)],[c_4897,c_6722]) ).
% 2.29/1.03  
% 2.29/1.03  cnf(c_7168,plain,
% 2.29/1.03      ( r1_tarski(sK2,sK1) = iProver_top ),
% 2.29/1.03      inference(global_propositional_subsumption,
% 2.29/1.03                [status(thm)],
% 2.29/1.03                [c_6758,c_22,c_23,c_24,c_28,c_37,c_49,c_55,c_56,c_2644,
% 2.29/1.03                 c_4828]) ).
% 2.29/1.03  
% 2.29/1.03  cnf(c_7175,plain,
% 2.29/1.03      ( r2_hidden(sK1,sK2) != iProver_top ),
% 2.29/1.03      inference(superposition,[status(thm)],[c_7168,c_984]) ).
% 2.29/1.03  
% 2.29/1.03  cnf(c_7195,plain,
% 2.29/1.03      ( sK2 = sK1 ),
% 2.29/1.03      inference(superposition,[status(thm)],[c_4903,c_7175]) ).
% 2.29/1.03  
% 2.29/1.03  cnf(c_2799,plain,
% 2.29/1.03      ( k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))) = sK2
% 2.29/1.03      | r2_hidden(k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))),sK2) = iProver_top
% 2.29/1.03      | r2_hidden(sK1,sK2) = iProver_top
% 2.29/1.03      | v3_ordinal1(k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)))) != iProver_top
% 2.29/1.03      | v3_ordinal1(sK2) != iProver_top ),
% 2.29/1.03      inference(superposition,[status(thm)],[c_987,c_2011]) ).
% 2.29/1.03  
% 2.29/1.03  cnf(c_3758,plain,
% 2.29/1.03      ( k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))) = sK2
% 2.29/1.03      | r2_hidden(k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))),sK2) = iProver_top
% 2.29/1.03      | r2_hidden(sK1,sK2) = iProver_top ),
% 2.29/1.03      inference(global_propositional_subsumption,
% 2.29/1.03                [status(thm)],
% 2.29/1.03                [c_2799,c_23,c_24,c_32]) ).
% 2.29/1.03  
% 2.29/1.03  cnf(c_7545,plain,
% 2.29/1.03      ( k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))) = sK1
% 2.29/1.03      | r2_hidden(k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))),sK1) = iProver_top
% 2.29/1.03      | r2_hidden(sK1,sK1) = iProver_top ),
% 2.29/1.03      inference(demodulation,[status(thm)],[c_7195,c_3758]) ).
% 2.29/1.03  
% 2.29/1.03  cnf(c_13,plain,
% 2.29/1.03      ( ~ r2_hidden(X0,X1)
% 2.29/1.03      | r2_hidden(X0,k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)))) ),
% 2.29/1.03      inference(cnf_transformation,[],[f94]) ).
% 2.29/1.03  
% 2.29/1.03  cnf(c_2493,plain,
% 2.29/1.03      ( ~ r2_hidden(k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))),X0)
% 2.29/1.03      | r2_hidden(k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)))) ),
% 2.29/1.03      inference(instantiation,[status(thm)],[c_13]) ).
% 2.29/1.03  
% 2.29/1.03  cnf(c_2494,plain,
% 2.29/1.03      ( r2_hidden(k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))),X0) != iProver_top
% 2.29/1.03      | r2_hidden(k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)))) = iProver_top ),
% 2.29/1.03      inference(predicate_to_equality,[status(thm)],[c_2493]) ).
% 2.29/1.03  
% 2.29/1.03  cnf(c_2496,plain,
% 2.29/1.03      ( r2_hidden(k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))),k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)))) = iProver_top
% 2.29/1.03      | r2_hidden(k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))),sK1) != iProver_top ),
% 2.29/1.03      inference(instantiation,[status(thm)],[c_2494]) ).
% 2.29/1.03  
% 2.29/1.03  cnf(c_483,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 2.29/1.03  
% 2.29/1.03  cnf(c_1301,plain,
% 2.29/1.03      ( X0 != X1
% 2.29/1.03      | X0 = k3_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2)))
% 2.29/1.03      | k3_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2))) != X1 ),
% 2.29/1.03      inference(instantiation,[status(thm)],[c_483]) ).
% 2.29/1.03  
% 2.29/1.03  cnf(c_1302,plain,
% 2.29/1.03      ( k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))) != sK1
% 2.29/1.03      | sK1 = k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)))
% 2.29/1.03      | sK1 != sK1 ),
% 2.29/1.03      inference(instantiation,[status(thm)],[c_1301]) ).
% 2.29/1.03  
% 2.29/1.03  cnf(c_7,plain,
% 2.29/1.03      ( r1_tarski(X0,X0) ),
% 2.29/1.03      inference(cnf_transformation,[],[f102]) ).
% 2.29/1.03  
% 2.29/1.03  cnf(c_1260,plain,
% 2.29/1.03      ( r1_tarski(k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)))) ),
% 2.29/1.03      inference(instantiation,[status(thm)],[c_7]) ).
% 2.29/1.03  
% 2.29/1.03  cnf(c_1265,plain,
% 2.29/1.03      ( r1_tarski(k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)))) = iProver_top ),
% 2.29/1.03      inference(predicate_to_equality,[status(thm)],[c_1260]) ).
% 2.29/1.03  
% 2.29/1.03  cnf(c_1267,plain,
% 2.29/1.03      ( r1_tarski(k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))),k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)))) = iProver_top ),
% 2.29/1.03      inference(instantiation,[status(thm)],[c_1265]) ).
% 2.29/1.03  
% 2.29/1.03  cnf(c_1209,plain,
% 2.29/1.03      ( ~ r1_tarski(k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))),X1)
% 2.29/1.03      | ~ r2_hidden(X1,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)))) ),
% 2.29/1.03      inference(instantiation,[status(thm)],[c_18]) ).
% 2.29/1.03  
% 2.29/1.03  cnf(c_1259,plain,
% 2.29/1.03      ( ~ r1_tarski(k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))))
% 2.29/1.03      | ~ r2_hidden(k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)))) ),
% 2.29/1.03      inference(instantiation,[status(thm)],[c_1209]) ).
% 2.29/1.03  
% 2.29/1.03  cnf(c_1261,plain,
% 2.29/1.03      ( r1_tarski(k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)))) != iProver_top
% 2.29/1.03      | r2_hidden(k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)))) != iProver_top ),
% 2.29/1.03      inference(predicate_to_equality,[status(thm)],[c_1259]) ).
% 2.29/1.03  
% 2.29/1.03  cnf(c_1263,plain,
% 2.29/1.03      ( r1_tarski(k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))),k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)))) != iProver_top
% 2.29/1.03      | r2_hidden(k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))),k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)))) != iProver_top ),
% 2.29/1.03      inference(instantiation,[status(thm)],[c_1261]) ).
% 2.29/1.03  
% 2.29/1.03  cnf(c_486,plain,
% 2.29/1.03      ( ~ r2_hidden(X0,X1) | r2_hidden(X2,X3) | X2 != X0 | X3 != X1 ),
% 2.29/1.03      theory(equality) ).
% 2.29/1.03  
% 2.29/1.03  cnf(c_1166,plain,
% 2.29/1.03      ( r2_hidden(X0,X1)
% 2.29/1.03      | ~ r2_hidden(X2,k3_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2))))
% 2.29/1.03      | X0 != X2
% 2.29/1.03      | X1 != k3_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2))) ),
% 2.29/1.03      inference(instantiation,[status(thm)],[c_486]) ).
% 2.29/1.03  
% 2.29/1.03  cnf(c_1168,plain,
% 2.29/1.03      ( ~ r2_hidden(sK1,k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))))
% 2.29/1.03      | r2_hidden(sK1,sK1)
% 2.29/1.03      | sK1 != k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)))
% 2.29/1.03      | sK1 != sK1 ),
% 2.29/1.03      inference(instantiation,[status(thm)],[c_1166]) ).
% 2.29/1.03  
% 2.29/1.03  cnf(c_48,plain,
% 2.29/1.03      ( r1_ordinal1(X0,X1) != iProver_top
% 2.29/1.03      | r1_tarski(X0,X1) = iProver_top
% 2.29/1.03      | v3_ordinal1(X0) != iProver_top
% 2.29/1.03      | v3_ordinal1(X1) != iProver_top ),
% 2.29/1.03      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 2.29/1.03  
% 2.29/1.03  cnf(c_50,plain,
% 2.29/1.03      ( r1_ordinal1(sK1,sK1) != iProver_top
% 2.29/1.03      | r1_tarski(sK1,sK1) = iProver_top
% 2.29/1.03      | v3_ordinal1(sK1) != iProver_top ),
% 2.29/1.03      inference(instantiation,[status(thm)],[c_48]) ).
% 2.29/1.03  
% 2.29/1.03  cnf(c_12,plain,
% 2.29/1.03      ( r2_hidden(X0,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)))) ),
% 2.29/1.03      inference(cnf_transformation,[],[f104]) ).
% 2.29/1.03  
% 2.29/1.03  cnf(c_46,plain,
% 2.29/1.03      ( r2_hidden(sK1,k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)))) ),
% 2.29/1.03      inference(instantiation,[status(thm)],[c_12]) ).
% 2.29/1.03  
% 2.29/1.03  cnf(c_27,plain,
% 2.29/1.03      ( r1_tarski(X0,X1) != iProver_top
% 2.29/1.03      | r2_hidden(X1,X0) != iProver_top ),
% 2.29/1.03      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 2.29/1.03  
% 2.29/1.03  cnf(c_29,plain,
% 2.29/1.03      ( r1_tarski(sK1,sK1) != iProver_top
% 2.29/1.03      | r2_hidden(sK1,sK1) != iProver_top ),
% 2.29/1.03      inference(instantiation,[status(thm)],[c_27]) ).
% 2.29/1.03  
% 2.29/1.03  cnf(contradiction,plain,
% 2.29/1.03      ( $false ),
% 2.29/1.03      inference(minisat,
% 2.29/1.03                [status(thm)],
% 2.29/1.03                [c_7545,c_2496,c_1302,c_1267,c_1263,c_1168,c_56,c_55,
% 2.29/1.03                 c_50,c_49,c_46,c_37,c_29,c_28,c_23,c_22]) ).
% 2.29/1.03  
% 2.29/1.03  
% 2.29/1.03  % SZS output end CNFRefutation for theBenchmark.p
% 2.29/1.03  
% 2.29/1.03  ------                               Statistics
% 2.29/1.03  
% 2.29/1.03  ------ General
% 2.29/1.03  
% 2.29/1.03  abstr_ref_over_cycles:                  0
% 2.29/1.03  abstr_ref_under_cycles:                 0
% 2.29/1.03  gc_basic_clause_elim:                   0
% 2.29/1.03  forced_gc_time:                         0
% 2.29/1.03  parsing_time:                           0.012
% 2.29/1.03  unif_index_cands_time:                  0.
% 2.29/1.03  unif_index_add_time:                    0.
% 2.29/1.03  orderings_time:                         0.
% 2.29/1.03  out_proof_time:                         0.009
% 2.29/1.03  total_time:                             0.447
% 2.29/1.03  num_of_symbols:                         37
% 2.29/1.03  num_of_terms:                           10202
% 2.29/1.03  
% 2.29/1.03  ------ Preprocessing
% 2.29/1.03  
% 2.29/1.03  num_of_splits:                          0
% 2.29/1.03  num_of_split_atoms:                     0
% 2.29/1.03  num_of_reused_defs:                     0
% 2.29/1.03  num_eq_ax_congr_red:                    15
% 2.29/1.03  num_of_sem_filtered_clauses:            1
% 2.29/1.03  num_of_subtypes:                        0
% 2.29/1.03  monotx_restored_types:                  0
% 2.29/1.03  sat_num_of_epr_types:                   0
% 2.29/1.03  sat_num_of_non_cyclic_types:            0
% 2.29/1.03  sat_guarded_non_collapsed_types:        0
% 2.29/1.03  num_pure_diseq_elim:                    0
% 2.29/1.03  simp_replaced_by:                       0
% 2.29/1.03  res_preprocessed:                       103
% 2.29/1.03  prep_upred:                             0
% 2.29/1.03  prep_unflattend:                        0
% 2.29/1.03  smt_new_axioms:                         0
% 2.29/1.03  pred_elim_cands:                        4
% 2.29/1.03  pred_elim:                              0
% 2.29/1.03  pred_elim_cl:                           0
% 2.29/1.03  pred_elim_cycles:                       2
% 2.29/1.03  merged_defs:                            8
% 2.29/1.03  merged_defs_ncl:                        0
% 2.29/1.03  bin_hyper_res:                          8
% 2.29/1.03  prep_cycles:                            4
% 2.29/1.03  pred_elim_time:                         0.002
% 2.29/1.03  splitting_time:                         0.
% 2.29/1.03  sem_filter_time:                        0.
% 2.29/1.03  monotx_time:                            0.001
% 2.29/1.03  subtype_inf_time:                       0.
% 2.29/1.03  
% 2.29/1.03  ------ Problem properties
% 2.29/1.03  
% 2.29/1.03  clauses:                                22
% 2.29/1.03  conjectures:                            4
% 2.29/1.03  epr:                                    10
% 2.29/1.03  horn:                                   15
% 2.29/1.03  ground:                                 4
% 2.29/1.03  unary:                                  4
% 2.29/1.03  binary:                                 7
% 2.29/1.03  lits:                                   58
% 2.29/1.03  lits_eq:                                6
% 2.29/1.03  fd_pure:                                0
% 2.29/1.03  fd_pseudo:                              0
% 2.29/1.03  fd_cond:                                0
% 2.29/1.03  fd_pseudo_cond:                         6
% 2.29/1.03  ac_symbols:                             0
% 2.29/1.03  
% 2.29/1.03  ------ Propositional Solver
% 2.29/1.03  
% 2.29/1.03  prop_solver_calls:                      27
% 2.29/1.03  prop_fast_solver_calls:                 735
% 2.29/1.03  smt_solver_calls:                       0
% 2.29/1.03  smt_fast_solver_calls:                  0
% 2.29/1.03  prop_num_of_clauses:                    2779
% 2.29/1.03  prop_preprocess_simplified:             8607
% 2.29/1.03  prop_fo_subsumed:                       19
% 2.29/1.03  prop_solver_time:                       0.
% 2.29/1.03  smt_solver_time:                        0.
% 2.29/1.03  smt_fast_solver_time:                   0.
% 2.29/1.03  prop_fast_solver_time:                  0.
% 2.29/1.03  prop_unsat_core_time:                   0.
% 2.29/1.03  
% 2.29/1.03  ------ QBF
% 2.29/1.03  
% 2.29/1.03  qbf_q_res:                              0
% 2.29/1.03  qbf_num_tautologies:                    0
% 2.29/1.03  qbf_prep_cycles:                        0
% 2.29/1.03  
% 2.29/1.03  ------ BMC1
% 2.29/1.03  
% 2.29/1.03  bmc1_current_bound:                     -1
% 2.29/1.03  bmc1_last_solved_bound:                 -1
% 2.29/1.03  bmc1_unsat_core_size:                   -1
% 2.29/1.03  bmc1_unsat_core_parents_size:           -1
% 2.29/1.03  bmc1_merge_next_fun:                    0
% 2.29/1.03  bmc1_unsat_core_clauses_time:           0.
% 2.29/1.03  
% 2.29/1.03  ------ Instantiation
% 2.29/1.03  
% 2.29/1.03  inst_num_of_clauses:                    859
% 2.29/1.03  inst_num_in_passive:                    283
% 2.29/1.03  inst_num_in_active:                     242
% 2.29/1.03  inst_num_in_unprocessed:                334
% 2.29/1.03  inst_num_of_loops:                      270
% 2.29/1.03  inst_num_of_learning_restarts:          0
% 2.29/1.03  inst_num_moves_active_passive:          27
% 2.29/1.03  inst_lit_activity:                      0
% 2.29/1.03  inst_lit_activity_moves:                0
% 2.29/1.03  inst_num_tautologies:                   0
% 2.29/1.03  inst_num_prop_implied:                  0
% 2.29/1.03  inst_num_existing_simplified:           0
% 2.29/1.03  inst_num_eq_res_simplified:             0
% 2.29/1.03  inst_num_child_elim:                    0
% 2.29/1.03  inst_num_of_dismatching_blockings:      467
% 2.29/1.03  inst_num_of_non_proper_insts:           727
% 2.29/1.03  inst_num_of_duplicates:                 0
% 2.29/1.03  inst_inst_num_from_inst_to_res:         0
% 2.29/1.03  inst_dismatching_checking_time:         0.
% 2.29/1.03  
% 2.29/1.03  ------ Resolution
% 2.29/1.03  
% 2.29/1.03  res_num_of_clauses:                     0
% 2.29/1.03  res_num_in_passive:                     0
% 2.29/1.03  res_num_in_active:                      0
% 2.29/1.03  res_num_of_loops:                       107
% 2.29/1.03  res_forward_subset_subsumed:            71
% 2.29/1.03  res_backward_subset_subsumed:           0
% 2.29/1.03  res_forward_subsumed:                   0
% 2.29/1.03  res_backward_subsumed:                  0
% 2.29/1.03  res_forward_subsumption_resolution:     0
% 2.29/1.03  res_backward_subsumption_resolution:    0
% 2.29/1.03  res_clause_to_clause_subsumption:       717
% 2.29/1.03  res_orphan_elimination:                 0
% 2.29/1.03  res_tautology_del:                      63
% 2.29/1.03  res_num_eq_res_simplified:              0
% 2.29/1.03  res_num_sel_changes:                    0
% 2.29/1.03  res_moves_from_active_to_pass:          0
% 2.29/1.03  
% 2.29/1.03  ------ Superposition
% 2.29/1.03  
% 2.29/1.03  sup_time_total:                         0.
% 2.29/1.03  sup_time_generating:                    0.
% 2.29/1.03  sup_time_sim_full:                      0.
% 2.29/1.03  sup_time_sim_immed:                     0.
% 2.29/1.03  
% 2.29/1.03  sup_num_of_clauses:                     78
% 2.29/1.03  sup_num_in_active:                      31
% 2.29/1.03  sup_num_in_passive:                     47
% 2.29/1.03  sup_num_of_loops:                       52
% 2.29/1.03  sup_fw_superposition:                   72
% 2.29/1.03  sup_bw_superposition:                   64
% 2.29/1.03  sup_immediate_simplified:               14
% 2.29/1.03  sup_given_eliminated:                   1
% 2.29/1.03  comparisons_done:                       0
% 2.29/1.03  comparisons_avoided:                    0
% 2.29/1.03  
% 2.29/1.03  ------ Simplifications
% 2.29/1.03  
% 2.29/1.03  
% 2.29/1.03  sim_fw_subset_subsumed:                 11
% 2.29/1.03  sim_bw_subset_subsumed:                 6
% 2.29/1.03  sim_fw_subsumed:                        12
% 2.29/1.03  sim_bw_subsumed:                        0
% 2.29/1.03  sim_fw_subsumption_res:                 0
% 2.29/1.03  sim_bw_subsumption_res:                 0
% 2.29/1.03  sim_tautology_del:                      17
% 2.29/1.03  sim_eq_tautology_del:                   5
% 2.29/1.03  sim_eq_res_simp:                        8
% 2.29/1.03  sim_fw_demodulated:                     0
% 2.29/1.03  sim_bw_demodulated:                     19
% 2.29/1.03  sim_light_normalised:                   0
% 2.29/1.03  sim_joinable_taut:                      0
% 2.29/1.03  sim_joinable_simp:                      0
% 2.29/1.03  sim_ac_normalised:                      0
% 2.29/1.03  sim_smt_subsumption:                    0
% 2.29/1.03  
%------------------------------------------------------------------------------
