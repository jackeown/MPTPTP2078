%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:53:42 EST 2020

% Result     : Theorem 11.42s
% Output     : CNFRefutation 11.42s
% Verified   : 
% Statistics : Number of formulae       :  181 (3815 expanded)
%              Number of clauses        :   91 ( 436 expanded)
%              Number of leaves         :   27 (1127 expanded)
%              Depth                    :   25
%              Number of atoms          :  567 (9736 expanded)
%              Number of equality atoms :  114 (2682 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal clause size      :   14 (   3 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f35])).

fof(f52,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            | r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
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
    inference(flattening,[],[f30])).

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
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( ~ r2_hidden(X4,X1)
                & ~ r2_hidden(X4,X0) ) )
            & ( r2_hidden(X4,X1)
              | r2_hidden(X4,X0)
              | ~ r2_hidden(X4,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f31])).

fof(f33,plain,(
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

fof(f34,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f32,f33])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( k2_xboole_0(X0,X1) = X2
      | r2_hidden(sK0(X0,X1,X2),X1)
      | r2_hidden(sK0(X0,X1,X2),X0)
      | r2_hidden(sK0(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f11,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f62,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f11])).

fof(f4,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f54,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f5,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f55,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f5])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f56,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f6])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f57,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f7])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f58,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f8])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f59,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f9])).

fof(f75,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f58,f59])).

fof(f76,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f57,f75])).

fof(f77,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f56,f76])).

fof(f78,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f55,f77])).

fof(f79,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f54,f78])).

fof(f80,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f62,f79])).

fof(f85,plain,(
    ! [X2,X0,X1] :
      ( k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = X2
      | r2_hidden(sK0(X0,X1,X2),X1)
      | r2_hidden(sK0(X0,X1,X2),X0)
      | r2_hidden(sK0(X0,X1,X2),X2) ) ),
    inference(definition_unfolding,[],[f47,f80])).

fof(f14,axiom,(
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
    inference(ennf_transformation,[],[f14])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( r1_ordinal1(X0,X1)
      <=> r1_tarski(X0,X1) )
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(flattening,[],[f23])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( ( r1_ordinal1(X0,X1)
          | ~ r1_tarski(X0,X1) )
        & ( r1_tarski(X0,X1)
          | ~ r1_ordinal1(X0,X1) ) )
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(nnf_transformation,[],[f24])).

fof(f65,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r1_ordinal1(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f38])).

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

fof(f29,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( r2_hidden(X0,X1)
          <~> r1_ordinal1(k1_ordinal1(X0),X1) )
          & v3_ordinal1(X1) )
      & v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f39,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ r1_ordinal1(k1_ordinal1(X0),X1)
            | ~ r2_hidden(X0,X1) )
          & ( r1_ordinal1(k1_ordinal1(X0),X1)
            | r2_hidden(X0,X1) )
          & v3_ordinal1(X1) )
      & v3_ordinal1(X0) ) ),
    inference(nnf_transformation,[],[f29])).

fof(f40,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ r1_ordinal1(k1_ordinal1(X0),X1)
            | ~ r2_hidden(X0,X1) )
          & ( r1_ordinal1(k1_ordinal1(X0),X1)
            | r2_hidden(X0,X1) )
          & v3_ordinal1(X1) )
      & v3_ordinal1(X0) ) ),
    inference(flattening,[],[f39])).

fof(f42,plain,(
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

fof(f41,plain,
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

fof(f43,plain,
    ( ( ~ r1_ordinal1(k1_ordinal1(sK1),sK2)
      | ~ r2_hidden(sK1,sK2) )
    & ( r1_ordinal1(k1_ordinal1(sK1),sK2)
      | r2_hidden(sK1,sK2) )
    & v3_ordinal1(sK2)
    & v3_ordinal1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f40,f42,f41])).

fof(f73,plain,
    ( r1_ordinal1(k1_ordinal1(sK1),sK2)
    | r2_hidden(sK1,sK2) ),
    inference(cnf_transformation,[],[f43])).

fof(f13,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_tarski(X0)) = k1_ordinal1(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f64,plain,(
    ! [X0] : k2_xboole_0(X0,k1_tarski(X0)) = k1_ordinal1(X0) ),
    inference(cnf_transformation,[],[f13])).

fof(f3,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f53,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f81,plain,(
    ! [X0] : k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f53,f79])).

fof(f82,plain,(
    ! [X0] : k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))) = k1_ordinal1(X0) ),
    inference(definition_unfolding,[],[f64,f80,f81])).

fof(f94,plain,
    ( r1_ordinal1(k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))),sK2)
    | r2_hidden(sK1,sK2) ),
    inference(definition_unfolding,[],[f73,f82])).

fof(f71,plain,(
    v3_ordinal1(sK1) ),
    inference(cnf_transformation,[],[f43])).

fof(f72,plain,(
    v3_ordinal1(sK2) ),
    inference(cnf_transformation,[],[f43])).

fof(f17,axiom,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => v3_ordinal1(k1_ordinal1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0] :
      ( v3_ordinal1(k1_ordinal1(X0))
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f69,plain,(
    ! [X0] :
      ( v3_ordinal1(k1_ordinal1(X0))
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f92,plain,(
    ! [X0] :
      ( v3_ordinal1(k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))))
      | ~ v3_ordinal1(X0) ) ),
    inference(definition_unfolding,[],[f69,f82])).

fof(f15,axiom,(
    ! [X0] : r2_hidden(X0,k1_ordinal1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f67,plain,(
    ! [X0] : r2_hidden(X0,k1_ordinal1(X0)) ),
    inference(cnf_transformation,[],[f15])).

fof(f91,plain,(
    ! [X0] : r2_hidden(X0,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)))) ),
    inference(definition_unfolding,[],[f67,f82])).

fof(f12,axiom,(
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
    inference(ennf_transformation,[],[f12])).

fof(f22,plain,(
    ! [X0,X1] :
      ( r1_ordinal1(X1,X0)
      | r1_ordinal1(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(flattening,[],[f21])).

fof(f63,plain,(
    ! [X0,X1] :
      ( r1_ordinal1(X1,X0)
      | r1_ordinal1(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f16,axiom,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ! [X1] :
          ( v3_ordinal1(X1)
         => ( r2_hidden(X1,X0)
            | r1_ordinal1(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(X1,X0)
          | r1_ordinal1(X0,X1)
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(X1,X0)
          | r1_ordinal1(X0,X1)
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(flattening,[],[f25])).

fof(f68,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,X0)
      | r1_ordinal1(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f18,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f70,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f51,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f36])).

fof(f98,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f51])).

fof(f46,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X1)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f34])).

fof(f86,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X1)
      | k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f46,f80])).

fof(f95,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))
      | ~ r2_hidden(X4,X1) ) ),
    inference(equality_resolution,[],[f86])).

fof(f45,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X0)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f34])).

fof(f87,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X0)
      | k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f45,f80])).

fof(f96,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))
      | ~ r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f87])).

fof(f44,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X1)
      | r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f34])).

fof(f88,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X1)
      | r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f44,f80])).

fof(f97,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X1)
      | r2_hidden(X4,X0)
      | ~ r2_hidden(X4,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) ) ),
    inference(equality_resolution,[],[f88])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
    <=> r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(k1_tarski(X0),X1)
        | ~ r2_hidden(X0,X1) )
      & ( r2_hidden(X0,X1)
        | ~ r1_tarski(k1_tarski(X0),X1) ) ) ),
    inference(nnf_transformation,[],[f10])).

fof(f61,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f89,plain,(
    ! [X0,X1] :
      ( r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f61,f81])).

fof(f74,plain,
    ( ~ r1_ordinal1(k1_ordinal1(sK1),sK2)
    | ~ r2_hidden(sK1,sK2) ),
    inference(cnf_transformation,[],[f43])).

fof(f93,plain,
    ( ~ r1_ordinal1(k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))),sK2)
    | ~ r2_hidden(sK1,sK2) ),
    inference(definition_unfolding,[],[f74,f82])).

cnf(c_398,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_6,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f52])).

cnf(c_4079,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | ~ r2_hidden(X2,X0)
    | r2_hidden(X3,X1)
    | X3 != X2 ),
    inference(resolution,[status(thm)],[c_398,c_6])).

cnf(c_394,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_8579,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | ~ r2_hidden(X2,X1)
    | r2_hidden(X2,X0) ),
    inference(resolution,[status(thm)],[c_4079,c_394])).

cnf(c_2,plain,
    ( r2_hidden(sK0(X0,X1,X2),X1)
    | r2_hidden(sK0(X0,X1,X2),X2)
    | r2_hidden(sK0(X0,X1,X2),X0)
    | k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = X2 ),
    inference(cnf_transformation,[],[f85])).

cnf(c_399,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X1)
    | X2 != X0 ),
    theory(equality)).

cnf(c_6172,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k3_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X3)),X1)
    | r2_hidden(sK0(X2,X3,X0),X3)
    | r2_hidden(sK0(X2,X3,X0),X0)
    | r2_hidden(sK0(X2,X3,X0),X2) ),
    inference(resolution,[status(thm)],[c_2,c_399])).

cnf(c_13,plain,
    ( ~ r1_ordinal1(X0,X1)
    | r1_tarski(X0,X1)
    | ~ v3_ordinal1(X1)
    | ~ v3_ordinal1(X0) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_19,negated_conjecture,
    ( r1_ordinal1(k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))),sK2)
    | r2_hidden(sK1,sK2) ),
    inference(cnf_transformation,[],[f94])).

cnf(c_1215,plain,
    ( r1_tarski(k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))),sK2)
    | r2_hidden(sK1,sK2)
    | ~ v3_ordinal1(k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))))
    | ~ v3_ordinal1(sK2) ),
    inference(resolution,[status(thm)],[c_13,c_19])).

cnf(c_21,negated_conjecture,
    ( v3_ordinal1(sK1) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_20,negated_conjecture,
    ( v3_ordinal1(sK2) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_16,plain,
    ( ~ v3_ordinal1(X0)
    | v3_ordinal1(k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)))) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_30,plain,
    ( v3_ordinal1(k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))))
    | ~ v3_ordinal1(sK1) ),
    inference(instantiation,[status(thm)],[c_16])).

cnf(c_1356,plain,
    ( r1_tarski(k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))),sK2)
    | r2_hidden(sK1,sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1215,c_21,c_20,c_30])).

cnf(c_10576,plain,
    ( r1_tarski(k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),sK2)
    | r2_hidden(sK0(X0,X1,k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)))),X1)
    | r2_hidden(sK0(X0,X1,k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)))),X0)
    | r2_hidden(sK0(X0,X1,k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)))),k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))))
    | r2_hidden(sK1,sK2) ),
    inference(resolution,[status(thm)],[c_6172,c_1356])).

cnf(c_400,plain,
    ( ~ r1_ordinal1(X0,X1)
    | r1_ordinal1(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_4097,plain,
    ( ~ r1_ordinal1(X0,X1)
    | r1_ordinal1(X2,X1)
    | X2 != X0 ),
    inference(resolution,[status(thm)],[c_400,c_394])).

cnf(c_4486,plain,
    ( ~ r1_ordinal1(X0,X1)
    | r1_ordinal1(X2,X1)
    | ~ r1_tarski(X2,X0)
    | ~ r1_tarski(X0,X2) ),
    inference(resolution,[status(thm)],[c_4097,c_6])).

cnf(c_11350,plain,
    ( ~ r1_ordinal1(k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),X2)
    | r1_ordinal1(sK2,X2)
    | ~ r1_tarski(sK2,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))
    | r2_hidden(sK0(X0,X1,k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)))),X1)
    | r2_hidden(sK0(X0,X1,k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)))),X0)
    | r2_hidden(sK0(X0,X1,k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)))),k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))))
    | r2_hidden(sK1,sK2) ),
    inference(resolution,[status(thm)],[c_10576,c_4486])).

cnf(c_12169,plain,
    ( r1_ordinal1(sK2,sK2)
    | ~ r1_tarski(sK2,k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))))
    | r2_hidden(sK0(sK1,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)))),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))
    | r2_hidden(sK0(sK1,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)))),k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))))
    | r2_hidden(sK0(sK1,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)))),sK1)
    | r2_hidden(sK1,sK2) ),
    inference(resolution,[status(thm)],[c_11350,c_19])).

cnf(c_14,plain,
    ( r2_hidden(X0,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)))) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_36,plain,
    ( r2_hidden(sK1,k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)))) ),
    inference(instantiation,[status(thm)],[c_14])).

cnf(c_39,plain,
    ( ~ r1_ordinal1(sK1,sK1)
    | r1_tarski(sK1,sK1)
    | ~ v3_ordinal1(sK1) ),
    inference(instantiation,[status(thm)],[c_13])).

cnf(c_11,plain,
    ( r1_ordinal1(X0,X1)
    | r1_ordinal1(X1,X0)
    | ~ v3_ordinal1(X1)
    | ~ v3_ordinal1(X0) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_45,plain,
    ( r1_ordinal1(sK1,sK1)
    | ~ v3_ordinal1(sK1) ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_58,plain,
    ( ~ r1_tarski(sK1,sK1)
    | sK1 = sK1 ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_1286,plain,
    ( ~ r1_tarski(X0,k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))))
    | ~ r1_tarski(k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))),X0)
    | X0 = k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_2849,plain,
    ( ~ r1_tarski(k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))),sK2)
    | ~ r1_tarski(sK2,k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))))
    | sK2 = k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))) ),
    inference(instantiation,[status(thm)],[c_1286])).

cnf(c_1099,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(X2,k3_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2))))
    | X0 != X2
    | X1 != k3_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2))) ),
    inference(instantiation,[status(thm)],[c_398])).

cnf(c_12209,plain,
    ( ~ r2_hidden(X0,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))))
    | r2_hidden(X1,sK2)
    | X1 != X0
    | sK2 != k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))) ),
    inference(instantiation,[status(thm)],[c_1099])).

cnf(c_12212,plain,
    ( ~ r2_hidden(sK1,k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))))
    | r2_hidden(sK1,sK2)
    | sK2 != k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)))
    | sK1 != sK1 ),
    inference(instantiation,[status(thm)],[c_12209])).

cnf(c_12981,plain,
    ( ~ r1_tarski(sK2,k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))))
    | r2_hidden(sK1,sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_12169,c_21,c_20,c_30,c_36,c_39,c_45,c_58,c_1215,c_2849,c_12212])).

cnf(c_15,plain,
    ( r1_ordinal1(X0,X1)
    | r2_hidden(X1,X0)
    | ~ v3_ordinal1(X1)
    | ~ v3_ordinal1(X0) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_1211,plain,
    ( r1_tarski(X0,X1)
    | r2_hidden(X1,X0)
    | ~ v3_ordinal1(X1)
    | ~ v3_ordinal1(X0) ),
    inference(resolution,[status(thm)],[c_13,c_15])).

cnf(c_12998,plain,
    ( r2_hidden(k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))),sK2)
    | r2_hidden(sK1,sK2)
    | ~ v3_ordinal1(k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))))
    | ~ v3_ordinal1(sK2) ),
    inference(resolution,[status(thm)],[c_12981,c_1211])).

cnf(c_13003,plain,
    ( r2_hidden(k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))),sK2)
    | r2_hidden(sK1,sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_12998,c_21,c_20,c_30])).

cnf(c_23666,plain,
    ( ~ r1_tarski(X0,sK2)
    | ~ r1_tarski(sK2,X0)
    | r2_hidden(k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))),X0)
    | r2_hidden(sK1,sK2) ),
    inference(resolution,[status(thm)],[c_8579,c_13003])).

cnf(c_17,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r2_hidden(X1,X0) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_7,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f98])).

cnf(c_2443,plain,
    ( ~ r2_hidden(X0,X0) ),
    inference(resolution,[status(thm)],[c_17,c_7])).

cnf(c_3,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,k3_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X1))) ),
    inference(cnf_transformation,[],[f95])).

cnf(c_3115,plain,
    ( ~ r2_hidden(k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),X1) ),
    inference(resolution,[status(thm)],[c_2443,c_3])).

cnf(c_24296,plain,
    ( ~ r1_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),sK2)
    | ~ r1_tarski(sK2,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))
    | r2_hidden(sK1,sK2) ),
    inference(resolution,[status(thm)],[c_23666,c_3115])).

cnf(c_2445,plain,
    ( ~ r2_hidden(sK2,k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))))
    | r2_hidden(sK1,sK2) ),
    inference(resolution,[status(thm)],[c_17,c_1356])).

cnf(c_4,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))) ),
    inference(cnf_transformation,[],[f96])).

cnf(c_2915,plain,
    ( ~ r2_hidden(sK2,sK1)
    | r2_hidden(sK1,sK2) ),
    inference(resolution,[status(thm)],[c_2445,c_4])).

cnf(c_3117,plain,
    ( ~ r2_hidden(k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),X0) ),
    inference(resolution,[status(thm)],[c_2443,c_4])).

cnf(c_24294,plain,
    ( ~ r1_tarski(sK2,sK1)
    | ~ r1_tarski(sK1,sK2)
    | r2_hidden(sK1,sK2) ),
    inference(resolution,[status(thm)],[c_23666,c_3117])).

cnf(c_27,plain,
    ( ~ r1_tarski(sK1,sK1)
    | ~ r2_hidden(sK1,sK1) ),
    inference(instantiation,[status(thm)],[c_17])).

cnf(c_396,plain,
    ( X0 != X1
    | X2 != X3
    | X4 != X5
    | X6 != X7
    | X8 != X9
    | X10 != X11
    | X12 != X13
    | X14 != X15
    | k6_enumset1(X0,X2,X4,X6,X8,X10,X12,X14) = k6_enumset1(X1,X3,X5,X7,X9,X11,X13,X15) ),
    theory(equality)).

cnf(c_402,plain,
    ( k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) = k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)
    | sK1 != sK1 ),
    inference(instantiation,[status(thm)],[c_396])).

cnf(c_5,plain,
    ( r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | ~ r2_hidden(X0,k3_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X1))) ),
    inference(cnf_transformation,[],[f97])).

cnf(c_1116,plain,
    ( r2_hidden(X0,X0)
    | r2_hidden(X0,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))
    | ~ r2_hidden(X0,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)))) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_1118,plain,
    ( r2_hidden(sK1,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))
    | ~ r2_hidden(sK1,k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))))
    | r2_hidden(sK1,sK1) ),
    inference(instantiation,[status(thm)],[c_1116])).

cnf(c_1771,plain,
    ( ~ r1_tarski(X0,sK2)
    | ~ r1_tarski(sK2,X0)
    | sK2 = X0 ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_1773,plain,
    ( ~ r1_tarski(sK2,sK1)
    | ~ r1_tarski(sK1,sK2)
    | sK2 = sK1 ),
    inference(instantiation,[status(thm)],[c_1771])).

cnf(c_2859,plain,
    ( ~ r1_ordinal1(sK2,X0)
    | r1_tarski(sK2,X0)
    | ~ v3_ordinal1(X0)
    | ~ v3_ordinal1(sK2) ),
    inference(instantiation,[status(thm)],[c_13])).

cnf(c_2861,plain,
    ( ~ r1_ordinal1(sK2,sK1)
    | r1_tarski(sK2,sK1)
    | ~ v3_ordinal1(sK2)
    | ~ v3_ordinal1(sK1) ),
    inference(instantiation,[status(thm)],[c_2859])).

cnf(c_2913,plain,
    ( ~ r2_hidden(sK2,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))
    | r2_hidden(sK1,sK2) ),
    inference(resolution,[status(thm)],[c_2445,c_3])).

cnf(c_9,plain,
    ( r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1)
    | ~ r2_hidden(X0,X1) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_2677,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X1,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) ),
    inference(resolution,[status(thm)],[c_9,c_17])).

cnf(c_3103,plain,
    ( ~ r2_hidden(sK2,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_2913,c_2677])).

cnf(c_5554,plain,
    ( r1_ordinal1(sK2,X0)
    | r2_hidden(X0,sK2)
    | ~ v3_ordinal1(X0)
    | ~ v3_ordinal1(sK2) ),
    inference(instantiation,[status(thm)],[c_15])).

cnf(c_5561,plain,
    ( r1_ordinal1(sK2,sK1)
    | r2_hidden(sK1,sK2)
    | ~ v3_ordinal1(sK2)
    | ~ v3_ordinal1(sK1) ),
    inference(instantiation,[status(thm)],[c_5554])).

cnf(c_1232,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(X2,k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2))
    | X0 != X2
    | X1 != k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2) ),
    inference(instantiation,[status(thm)],[c_398])).

cnf(c_1417,plain,
    ( ~ r2_hidden(X0,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))
    | r2_hidden(X1,k6_enumset1(X2,X3,X4,X5,X6,X7,X8,X9))
    | X1 != X0
    | k6_enumset1(X2,X3,X4,X5,X6,X7,X8,X9) != k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
    inference(instantiation,[status(thm)],[c_1232])).

cnf(c_26057,plain,
    ( ~ r2_hidden(X0,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))
    | r2_hidden(sK2,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))
    | k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) != k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)
    | sK2 != X0 ),
    inference(instantiation,[status(thm)],[c_1417])).

cnf(c_26059,plain,
    ( r2_hidden(sK2,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))
    | ~ r2_hidden(sK1,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))
    | k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) != k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)
    | sK2 != sK1 ),
    inference(instantiation,[status(thm)],[c_26057])).

cnf(c_26373,plain,
    ( ~ r1_tarski(sK1,sK2)
    | r2_hidden(sK1,sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_24294,c_21,c_20,c_27,c_36,c_39,c_45,c_58,c_402,c_1118,c_1773,c_2861,c_3103,c_5561,c_26059])).

cnf(c_27071,plain,
    ( r2_hidden(sK2,sK1)
    | r2_hidden(sK1,sK2)
    | ~ v3_ordinal1(sK2)
    | ~ v3_ordinal1(sK1) ),
    inference(resolution,[status(thm)],[c_26373,c_1211])).

cnf(c_27076,plain,
    ( r2_hidden(sK1,sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_24296,c_21,c_20,c_2915,c_27071])).

cnf(c_1210,plain,
    ( r1_ordinal1(X0,X1)
    | r1_tarski(X1,X0)
    | ~ v3_ordinal1(X1)
    | ~ v3_ordinal1(X0) ),
    inference(resolution,[status(thm)],[c_13,c_11])).

cnf(c_1769,plain,
    ( r1_tarski(X0,X1)
    | r1_tarski(X1,X0)
    | ~ v3_ordinal1(X0)
    | ~ v3_ordinal1(X1) ),
    inference(resolution,[status(thm)],[c_1210,c_13])).

cnf(c_2439,plain,
    ( r1_tarski(X0,X1)
    | ~ r2_hidden(X0,X1)
    | ~ v3_ordinal1(X1)
    | ~ v3_ordinal1(X0) ),
    inference(resolution,[status(thm)],[c_17,c_1769])).

cnf(c_3341,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X1,X0)
    | ~ v3_ordinal1(X1)
    | ~ v3_ordinal1(X0) ),
    inference(resolution,[status(thm)],[c_2439,c_17])).

cnf(c_27090,plain,
    ( ~ r2_hidden(sK2,sK1)
    | ~ v3_ordinal1(sK2)
    | ~ v3_ordinal1(sK1) ),
    inference(resolution,[status(thm)],[c_27076,c_3341])).

cnf(c_888,plain,
    ( r1_ordinal1(X0,X1) = iProver_top
    | r2_hidden(X1,X0) = iProver_top
    | v3_ordinal1(X0) != iProver_top
    | v3_ordinal1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_18,negated_conjecture,
    ( ~ r1_ordinal1(k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))),sK2)
    | ~ r2_hidden(sK1,sK2) ),
    inference(cnf_transformation,[],[f93])).

cnf(c_885,plain,
    ( r1_ordinal1(k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))),sK2) != iProver_top
    | r2_hidden(sK1,sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_2203,plain,
    ( r2_hidden(sK2,k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)))) = iProver_top
    | r2_hidden(sK1,sK2) != iProver_top
    | v3_ordinal1(k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)))) != iProver_top
    | v3_ordinal1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_888,c_885])).

cnf(c_22,plain,
    ( v3_ordinal1(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_23,plain,
    ( v3_ordinal1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_29,plain,
    ( v3_ordinal1(X0) != iProver_top
    | v3_ordinal1(k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_31,plain,
    ( v3_ordinal1(k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)))) = iProver_top
    | v3_ordinal1(sK1) != iProver_top ),
    inference(instantiation,[status(thm)],[c_29])).

cnf(c_2885,plain,
    ( r2_hidden(sK2,k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)))) = iProver_top
    | r2_hidden(sK1,sK2) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2203,c_22,c_23,c_31])).

cnf(c_897,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r2_hidden(X0,X2) = iProver_top
    | r2_hidden(X0,k3_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_2891,plain,
    ( r2_hidden(sK2,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)) = iProver_top
    | r2_hidden(sK2,sK1) = iProver_top
    | r2_hidden(sK1,sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_2885,c_897])).

cnf(c_2892,plain,
    ( r2_hidden(sK2,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))
    | r2_hidden(sK2,sK1)
    | ~ r2_hidden(sK1,sK2) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_2891])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_27090,c_27076,c_3103,c_2892,c_20,c_21])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 20:58:36 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 11.42/1.99  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 11.42/1.99  
% 11.42/1.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 11.42/1.99  
% 11.42/1.99  ------  iProver source info
% 11.42/1.99  
% 11.42/1.99  git: date: 2020-06-30 10:37:57 +0100
% 11.42/1.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 11.42/1.99  git: non_committed_changes: false
% 11.42/1.99  git: last_make_outside_of_git: false
% 11.42/1.99  
% 11.42/1.99  ------ 
% 11.42/1.99  ------ Parsing...
% 11.42/1.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 11.42/1.99  
% 11.42/1.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 1 0s  sf_e 
% 11.42/1.99  
% 11.42/1.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 11.42/1.99  
% 11.42/1.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 11.42/1.99  ------ Proving...
% 11.42/1.99  ------ Problem Properties 
% 11.42/1.99  
% 11.42/1.99  
% 11.42/1.99  clauses                                 21
% 11.42/1.99  conjectures                             4
% 11.42/1.99  EPR                                     9
% 11.42/1.99  Horn                                    16
% 11.42/1.99  unary                                   4
% 11.42/1.99  binary                                  8
% 11.42/1.99  lits                                    52
% 11.42/1.99  lits eq                                 4
% 11.42/1.99  fd_pure                                 0
% 11.42/1.99  fd_pseudo                               0
% 11.42/1.99  fd_cond                                 0
% 11.42/1.99  fd_pseudo_cond                          4
% 11.42/1.99  AC symbols                              0
% 11.42/1.99  
% 11.42/1.99  ------ Input Options Time Limit: Unbounded
% 11.42/1.99  
% 11.42/1.99  
% 11.42/1.99  ------ 
% 11.42/1.99  Current options:
% 11.42/1.99  ------ 
% 11.42/1.99  
% 11.42/1.99  
% 11.42/1.99  
% 11.42/1.99  
% 11.42/1.99  ------ Proving...
% 11.42/1.99  
% 11.42/1.99  
% 11.42/1.99  % SZS status Theorem for theBenchmark.p
% 11.42/1.99  
% 11.42/1.99  % SZS output start CNFRefutation for theBenchmark.p
% 11.42/1.99  
% 11.42/1.99  fof(f2,axiom,(
% 11.42/1.99    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 11.42/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.42/1.99  
% 11.42/1.99  fof(f35,plain,(
% 11.42/1.99    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 11.42/1.99    inference(nnf_transformation,[],[f2])).
% 11.42/1.99  
% 11.42/1.99  fof(f36,plain,(
% 11.42/1.99    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 11.42/1.99    inference(flattening,[],[f35])).
% 11.42/1.99  
% 11.42/1.99  fof(f52,plain,(
% 11.42/1.99    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 11.42/1.99    inference(cnf_transformation,[],[f36])).
% 11.42/1.99  
% 11.42/1.99  fof(f1,axiom,(
% 11.42/1.99    ! [X0,X1,X2] : (k2_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) | r2_hidden(X3,X0))))),
% 11.42/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.42/1.99  
% 11.42/1.99  fof(f30,plain,(
% 11.42/1.99    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) | r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) & ~r2_hidden(X3,X0))) & ((r2_hidden(X3,X1) | r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k2_xboole_0(X0,X1) != X2))),
% 11.42/1.99    inference(nnf_transformation,[],[f1])).
% 11.42/1.99  
% 11.42/1.99  fof(f31,plain,(
% 11.42/1.99    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) & ~r2_hidden(X3,X0))) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | ~r2_hidden(X3,X2))) | k2_xboole_0(X0,X1) != X2))),
% 11.42/1.99    inference(flattening,[],[f30])).
% 11.42/1.99  
% 11.42/1.99  fof(f32,plain,(
% 11.42/1.99    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (~r2_hidden(X4,X1) & ~r2_hidden(X4,X0))) & (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,X2))) | k2_xboole_0(X0,X1) != X2))),
% 11.42/1.99    inference(rectify,[],[f31])).
% 11.42/1.99  
% 11.42/1.99  fof(f33,plain,(
% 11.42/1.99    ! [X2,X1,X0] : (? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2))) => (((~r2_hidden(sK0(X0,X1,X2),X1) & ~r2_hidden(sK0(X0,X1,X2),X0)) | ~r2_hidden(sK0(X0,X1,X2),X2)) & (r2_hidden(sK0(X0,X1,X2),X1) | r2_hidden(sK0(X0,X1,X2),X0) | r2_hidden(sK0(X0,X1,X2),X2))))),
% 11.42/1.99    introduced(choice_axiom,[])).
% 11.42/1.99  
% 11.42/1.99  fof(f34,plain,(
% 11.42/1.99    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | (((~r2_hidden(sK0(X0,X1,X2),X1) & ~r2_hidden(sK0(X0,X1,X2),X0)) | ~r2_hidden(sK0(X0,X1,X2),X2)) & (r2_hidden(sK0(X0,X1,X2),X1) | r2_hidden(sK0(X0,X1,X2),X0) | r2_hidden(sK0(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (~r2_hidden(X4,X1) & ~r2_hidden(X4,X0))) & (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,X2))) | k2_xboole_0(X0,X1) != X2))),
% 11.42/1.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f32,f33])).
% 11.42/1.99  
% 11.42/1.99  fof(f47,plain,(
% 11.42/1.99    ( ! [X2,X0,X1] : (k2_xboole_0(X0,X1) = X2 | r2_hidden(sK0(X0,X1,X2),X1) | r2_hidden(sK0(X0,X1,X2),X0) | r2_hidden(sK0(X0,X1,X2),X2)) )),
% 11.42/1.99    inference(cnf_transformation,[],[f34])).
% 11.42/1.99  
% 11.42/1.99  fof(f11,axiom,(
% 11.42/1.99    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 11.42/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.42/1.99  
% 11.42/1.99  fof(f62,plain,(
% 11.42/1.99    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 11.42/1.99    inference(cnf_transformation,[],[f11])).
% 11.42/1.99  
% 11.42/1.99  fof(f4,axiom,(
% 11.42/1.99    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 11.42/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.42/1.99  
% 11.42/1.99  fof(f54,plain,(
% 11.42/1.99    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 11.42/1.99    inference(cnf_transformation,[],[f4])).
% 11.42/1.99  
% 11.42/1.99  fof(f5,axiom,(
% 11.42/1.99    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 11.42/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.42/1.99  
% 11.42/1.99  fof(f55,plain,(
% 11.42/1.99    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 11.42/1.99    inference(cnf_transformation,[],[f5])).
% 11.42/1.99  
% 11.42/1.99  fof(f6,axiom,(
% 11.42/1.99    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 11.42/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.42/1.99  
% 11.42/1.99  fof(f56,plain,(
% 11.42/1.99    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 11.42/1.99    inference(cnf_transformation,[],[f6])).
% 11.42/1.99  
% 11.42/1.99  fof(f7,axiom,(
% 11.42/1.99    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)),
% 11.42/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.42/1.99  
% 11.42/1.99  fof(f57,plain,(
% 11.42/1.99    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)) )),
% 11.42/1.99    inference(cnf_transformation,[],[f7])).
% 11.42/1.99  
% 11.42/1.99  fof(f8,axiom,(
% 11.42/1.99    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)),
% 11.42/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.42/1.99  
% 11.42/1.99  fof(f58,plain,(
% 11.42/1.99    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)) )),
% 11.42/1.99    inference(cnf_transformation,[],[f8])).
% 11.42/1.99  
% 11.42/1.99  fof(f9,axiom,(
% 11.42/1.99    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)),
% 11.42/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.42/1.99  
% 11.42/1.99  fof(f59,plain,(
% 11.42/1.99    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)) )),
% 11.42/1.99    inference(cnf_transformation,[],[f9])).
% 11.42/1.99  
% 11.42/1.99  fof(f75,plain,(
% 11.42/1.99    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 11.42/1.99    inference(definition_unfolding,[],[f58,f59])).
% 11.42/1.99  
% 11.42/1.99  fof(f76,plain,(
% 11.42/1.99    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 11.42/1.99    inference(definition_unfolding,[],[f57,f75])).
% 11.42/1.99  
% 11.42/1.99  fof(f77,plain,(
% 11.42/1.99    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 11.42/1.99    inference(definition_unfolding,[],[f56,f76])).
% 11.42/1.99  
% 11.42/1.99  fof(f78,plain,(
% 11.42/1.99    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 11.42/1.99    inference(definition_unfolding,[],[f55,f77])).
% 11.42/1.99  
% 11.42/1.99  fof(f79,plain,(
% 11.42/1.99    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 11.42/1.99    inference(definition_unfolding,[],[f54,f78])).
% 11.42/1.99  
% 11.42/1.99  fof(f80,plain,(
% 11.42/1.99    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) )),
% 11.42/1.99    inference(definition_unfolding,[],[f62,f79])).
% 11.42/1.99  
% 11.42/1.99  fof(f85,plain,(
% 11.42/1.99    ( ! [X2,X0,X1] : (k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = X2 | r2_hidden(sK0(X0,X1,X2),X1) | r2_hidden(sK0(X0,X1,X2),X0) | r2_hidden(sK0(X0,X1,X2),X2)) )),
% 11.42/1.99    inference(definition_unfolding,[],[f47,f80])).
% 11.42/1.99  
% 11.42/1.99  fof(f14,axiom,(
% 11.42/1.99    ! [X0,X1] : ((v3_ordinal1(X1) & v3_ordinal1(X0)) => (r1_ordinal1(X0,X1) <=> r1_tarski(X0,X1)))),
% 11.42/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.42/1.99  
% 11.42/1.99  fof(f23,plain,(
% 11.42/1.99    ! [X0,X1] : ((r1_ordinal1(X0,X1) <=> r1_tarski(X0,X1)) | (~v3_ordinal1(X1) | ~v3_ordinal1(X0)))),
% 11.42/1.99    inference(ennf_transformation,[],[f14])).
% 11.42/1.99  
% 11.42/1.99  fof(f24,plain,(
% 11.42/1.99    ! [X0,X1] : ((r1_ordinal1(X0,X1) <=> r1_tarski(X0,X1)) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0))),
% 11.42/1.99    inference(flattening,[],[f23])).
% 11.42/1.99  
% 11.42/1.99  fof(f38,plain,(
% 11.42/1.99    ! [X0,X1] : (((r1_ordinal1(X0,X1) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~r1_ordinal1(X0,X1))) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0))),
% 11.42/1.99    inference(nnf_transformation,[],[f24])).
% 11.42/1.99  
% 11.42/1.99  fof(f65,plain,(
% 11.42/1.99    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r1_ordinal1(X0,X1) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0)) )),
% 11.42/1.99    inference(cnf_transformation,[],[f38])).
% 11.42/1.99  
% 11.42/1.99  fof(f19,conjecture,(
% 11.42/1.99    ! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => (r2_hidden(X0,X1) <=> r1_ordinal1(k1_ordinal1(X0),X1))))),
% 11.42/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.42/1.99  
% 11.42/1.99  fof(f20,negated_conjecture,(
% 11.42/1.99    ~! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => (r2_hidden(X0,X1) <=> r1_ordinal1(k1_ordinal1(X0),X1))))),
% 11.42/1.99    inference(negated_conjecture,[],[f19])).
% 11.42/1.99  
% 11.42/1.99  fof(f29,plain,(
% 11.42/1.99    ? [X0] : (? [X1] : ((r2_hidden(X0,X1) <~> r1_ordinal1(k1_ordinal1(X0),X1)) & v3_ordinal1(X1)) & v3_ordinal1(X0))),
% 11.42/1.99    inference(ennf_transformation,[],[f20])).
% 11.42/1.99  
% 11.42/1.99  fof(f39,plain,(
% 11.42/1.99    ? [X0] : (? [X1] : (((~r1_ordinal1(k1_ordinal1(X0),X1) | ~r2_hidden(X0,X1)) & (r1_ordinal1(k1_ordinal1(X0),X1) | r2_hidden(X0,X1))) & v3_ordinal1(X1)) & v3_ordinal1(X0))),
% 11.42/1.99    inference(nnf_transformation,[],[f29])).
% 11.42/1.99  
% 11.42/1.99  fof(f40,plain,(
% 11.42/1.99    ? [X0] : (? [X1] : ((~r1_ordinal1(k1_ordinal1(X0),X1) | ~r2_hidden(X0,X1)) & (r1_ordinal1(k1_ordinal1(X0),X1) | r2_hidden(X0,X1)) & v3_ordinal1(X1)) & v3_ordinal1(X0))),
% 11.42/1.99    inference(flattening,[],[f39])).
% 11.42/1.99  
% 11.42/1.99  fof(f42,plain,(
% 11.42/1.99    ( ! [X0] : (? [X1] : ((~r1_ordinal1(k1_ordinal1(X0),X1) | ~r2_hidden(X0,X1)) & (r1_ordinal1(k1_ordinal1(X0),X1) | r2_hidden(X0,X1)) & v3_ordinal1(X1)) => ((~r1_ordinal1(k1_ordinal1(X0),sK2) | ~r2_hidden(X0,sK2)) & (r1_ordinal1(k1_ordinal1(X0),sK2) | r2_hidden(X0,sK2)) & v3_ordinal1(sK2))) )),
% 11.42/1.99    introduced(choice_axiom,[])).
% 11.42/1.99  
% 11.42/1.99  fof(f41,plain,(
% 11.42/1.99    ? [X0] : (? [X1] : ((~r1_ordinal1(k1_ordinal1(X0),X1) | ~r2_hidden(X0,X1)) & (r1_ordinal1(k1_ordinal1(X0),X1) | r2_hidden(X0,X1)) & v3_ordinal1(X1)) & v3_ordinal1(X0)) => (? [X1] : ((~r1_ordinal1(k1_ordinal1(sK1),X1) | ~r2_hidden(sK1,X1)) & (r1_ordinal1(k1_ordinal1(sK1),X1) | r2_hidden(sK1,X1)) & v3_ordinal1(X1)) & v3_ordinal1(sK1))),
% 11.42/1.99    introduced(choice_axiom,[])).
% 11.42/1.99  
% 11.42/1.99  fof(f43,plain,(
% 11.42/1.99    ((~r1_ordinal1(k1_ordinal1(sK1),sK2) | ~r2_hidden(sK1,sK2)) & (r1_ordinal1(k1_ordinal1(sK1),sK2) | r2_hidden(sK1,sK2)) & v3_ordinal1(sK2)) & v3_ordinal1(sK1)),
% 11.42/1.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f40,f42,f41])).
% 11.42/1.99  
% 11.42/1.99  fof(f73,plain,(
% 11.42/1.99    r1_ordinal1(k1_ordinal1(sK1),sK2) | r2_hidden(sK1,sK2)),
% 11.42/1.99    inference(cnf_transformation,[],[f43])).
% 11.42/1.99  
% 11.42/1.99  fof(f13,axiom,(
% 11.42/1.99    ! [X0] : k2_xboole_0(X0,k1_tarski(X0)) = k1_ordinal1(X0)),
% 11.42/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.42/1.99  
% 11.42/1.99  fof(f64,plain,(
% 11.42/1.99    ( ! [X0] : (k2_xboole_0(X0,k1_tarski(X0)) = k1_ordinal1(X0)) )),
% 11.42/1.99    inference(cnf_transformation,[],[f13])).
% 11.42/1.99  
% 11.42/1.99  fof(f3,axiom,(
% 11.42/1.99    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 11.42/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.42/1.99  
% 11.42/1.99  fof(f53,plain,(
% 11.42/1.99    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 11.42/1.99    inference(cnf_transformation,[],[f3])).
% 11.42/1.99  
% 11.42/1.99  fof(f81,plain,(
% 11.42/1.99    ( ! [X0] : (k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) )),
% 11.42/1.99    inference(definition_unfolding,[],[f53,f79])).
% 11.42/1.99  
% 11.42/1.99  fof(f82,plain,(
% 11.42/1.99    ( ! [X0] : (k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))) = k1_ordinal1(X0)) )),
% 11.42/1.99    inference(definition_unfolding,[],[f64,f80,f81])).
% 11.42/1.99  
% 11.42/1.99  fof(f94,plain,(
% 11.42/1.99    r1_ordinal1(k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))),sK2) | r2_hidden(sK1,sK2)),
% 11.42/1.99    inference(definition_unfolding,[],[f73,f82])).
% 11.42/1.99  
% 11.42/1.99  fof(f71,plain,(
% 11.42/1.99    v3_ordinal1(sK1)),
% 11.42/1.99    inference(cnf_transformation,[],[f43])).
% 11.42/1.99  
% 11.42/1.99  fof(f72,plain,(
% 11.42/1.99    v3_ordinal1(sK2)),
% 11.42/1.99    inference(cnf_transformation,[],[f43])).
% 11.42/1.99  
% 11.42/1.99  fof(f17,axiom,(
% 11.42/1.99    ! [X0] : (v3_ordinal1(X0) => v3_ordinal1(k1_ordinal1(X0)))),
% 11.42/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.42/1.99  
% 11.42/1.99  fof(f27,plain,(
% 11.42/1.99    ! [X0] : (v3_ordinal1(k1_ordinal1(X0)) | ~v3_ordinal1(X0))),
% 11.42/1.99    inference(ennf_transformation,[],[f17])).
% 11.42/1.99  
% 11.42/1.99  fof(f69,plain,(
% 11.42/1.99    ( ! [X0] : (v3_ordinal1(k1_ordinal1(X0)) | ~v3_ordinal1(X0)) )),
% 11.42/1.99    inference(cnf_transformation,[],[f27])).
% 11.42/1.99  
% 11.42/1.99  fof(f92,plain,(
% 11.42/1.99    ( ! [X0] : (v3_ordinal1(k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)))) | ~v3_ordinal1(X0)) )),
% 11.42/1.99    inference(definition_unfolding,[],[f69,f82])).
% 11.42/1.99  
% 11.42/1.99  fof(f15,axiom,(
% 11.42/1.99    ! [X0] : r2_hidden(X0,k1_ordinal1(X0))),
% 11.42/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.42/1.99  
% 11.42/1.99  fof(f67,plain,(
% 11.42/1.99    ( ! [X0] : (r2_hidden(X0,k1_ordinal1(X0))) )),
% 11.42/1.99    inference(cnf_transformation,[],[f15])).
% 11.42/1.99  
% 11.42/1.99  fof(f91,plain,(
% 11.42/1.99    ( ! [X0] : (r2_hidden(X0,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))))) )),
% 11.42/1.99    inference(definition_unfolding,[],[f67,f82])).
% 11.42/1.99  
% 11.42/1.99  fof(f12,axiom,(
% 11.42/1.99    ! [X0,X1] : ((v3_ordinal1(X1) & v3_ordinal1(X0)) => (r1_ordinal1(X1,X0) | r1_ordinal1(X0,X1)))),
% 11.42/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.42/1.99  
% 11.42/1.99  fof(f21,plain,(
% 11.42/1.99    ! [X0,X1] : ((r1_ordinal1(X1,X0) | r1_ordinal1(X0,X1)) | (~v3_ordinal1(X1) | ~v3_ordinal1(X0)))),
% 11.42/1.99    inference(ennf_transformation,[],[f12])).
% 11.42/1.99  
% 11.42/1.99  fof(f22,plain,(
% 11.42/1.99    ! [X0,X1] : (r1_ordinal1(X1,X0) | r1_ordinal1(X0,X1) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0))),
% 11.42/1.99    inference(flattening,[],[f21])).
% 11.42/1.99  
% 11.42/1.99  fof(f63,plain,(
% 11.42/1.99    ( ! [X0,X1] : (r1_ordinal1(X1,X0) | r1_ordinal1(X0,X1) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0)) )),
% 11.42/1.99    inference(cnf_transformation,[],[f22])).
% 11.42/1.99  
% 11.42/1.99  fof(f16,axiom,(
% 11.42/1.99    ! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => (r2_hidden(X1,X0) | r1_ordinal1(X0,X1))))),
% 11.42/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.42/1.99  
% 11.42/1.99  fof(f25,plain,(
% 11.42/1.99    ! [X0] : (! [X1] : ((r2_hidden(X1,X0) | r1_ordinal1(X0,X1)) | ~v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 11.42/1.99    inference(ennf_transformation,[],[f16])).
% 11.42/1.99  
% 11.42/1.99  fof(f26,plain,(
% 11.42/1.99    ! [X0] : (! [X1] : (r2_hidden(X1,X0) | r1_ordinal1(X0,X1) | ~v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 11.42/1.99    inference(flattening,[],[f25])).
% 11.42/1.99  
% 11.42/1.99  fof(f68,plain,(
% 11.42/1.99    ( ! [X0,X1] : (r2_hidden(X1,X0) | r1_ordinal1(X0,X1) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0)) )),
% 11.42/1.99    inference(cnf_transformation,[],[f26])).
% 11.42/1.99  
% 11.42/1.99  fof(f18,axiom,(
% 11.42/1.99    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 11.42/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.42/1.99  
% 11.42/1.99  fof(f28,plain,(
% 11.42/1.99    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 11.42/1.99    inference(ennf_transformation,[],[f18])).
% 11.42/1.99  
% 11.42/1.99  fof(f70,plain,(
% 11.42/1.99    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1)) )),
% 11.42/1.99    inference(cnf_transformation,[],[f28])).
% 11.42/1.99  
% 11.42/1.99  fof(f51,plain,(
% 11.42/1.99    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 11.42/1.99    inference(cnf_transformation,[],[f36])).
% 11.42/1.99  
% 11.42/1.99  fof(f98,plain,(
% 11.42/1.99    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 11.42/1.99    inference(equality_resolution,[],[f51])).
% 11.42/1.99  
% 11.42/1.99  fof(f46,plain,(
% 11.42/1.99    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | k2_xboole_0(X0,X1) != X2) )),
% 11.42/1.99    inference(cnf_transformation,[],[f34])).
% 11.42/1.99  
% 11.42/1.99  fof(f86,plain,(
% 11.42/1.99    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) != X2) )),
% 11.42/1.99    inference(definition_unfolding,[],[f46,f80])).
% 11.42/1.99  
% 11.42/1.99  fof(f95,plain,(
% 11.42/1.99    ( ! [X4,X0,X1] : (r2_hidden(X4,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) | ~r2_hidden(X4,X1)) )),
% 11.42/1.99    inference(equality_resolution,[],[f86])).
% 11.42/1.99  
% 11.42/1.99  fof(f45,plain,(
% 11.42/1.99    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | ~r2_hidden(X4,X0) | k2_xboole_0(X0,X1) != X2) )),
% 11.42/1.99    inference(cnf_transformation,[],[f34])).
% 11.42/1.99  
% 11.42/1.99  fof(f87,plain,(
% 11.42/1.99    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | ~r2_hidden(X4,X0) | k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) != X2) )),
% 11.42/1.99    inference(definition_unfolding,[],[f45,f80])).
% 11.42/1.99  
% 11.42/1.99  fof(f96,plain,(
% 11.42/1.99    ( ! [X4,X0,X1] : (r2_hidden(X4,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) | ~r2_hidden(X4,X0)) )),
% 11.42/1.99    inference(equality_resolution,[],[f87])).
% 11.42/1.99  
% 11.42/1.99  fof(f44,plain,(
% 11.42/1.99    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,X2) | k2_xboole_0(X0,X1) != X2) )),
% 11.42/1.99    inference(cnf_transformation,[],[f34])).
% 11.42/1.99  
% 11.42/1.99  fof(f88,plain,(
% 11.42/1.99    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,X2) | k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) != X2) )),
% 11.42/1.99    inference(definition_unfolding,[],[f44,f80])).
% 11.42/1.99  
% 11.42/1.99  fof(f97,plain,(
% 11.42/1.99    ( ! [X4,X0,X1] : (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) )),
% 11.42/1.99    inference(equality_resolution,[],[f88])).
% 11.42/1.99  
% 11.42/1.99  fof(f10,axiom,(
% 11.42/1.99    ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) <=> r2_hidden(X0,X1))),
% 11.42/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.42/1.99  
% 11.42/1.99  fof(f37,plain,(
% 11.42/1.99    ! [X0,X1] : ((r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) & (r2_hidden(X0,X1) | ~r1_tarski(k1_tarski(X0),X1)))),
% 11.42/1.99    inference(nnf_transformation,[],[f10])).
% 11.42/1.99  
% 11.42/1.99  fof(f61,plain,(
% 11.42/1.99    ( ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) )),
% 11.42/1.99    inference(cnf_transformation,[],[f37])).
% 11.42/1.99  
% 11.42/1.99  fof(f89,plain,(
% 11.42/1.99    ( ! [X0,X1] : (r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1) | ~r2_hidden(X0,X1)) )),
% 11.42/1.99    inference(definition_unfolding,[],[f61,f81])).
% 11.42/1.99  
% 11.42/1.99  fof(f74,plain,(
% 11.42/1.99    ~r1_ordinal1(k1_ordinal1(sK1),sK2) | ~r2_hidden(sK1,sK2)),
% 11.42/1.99    inference(cnf_transformation,[],[f43])).
% 11.42/1.99  
% 11.42/1.99  fof(f93,plain,(
% 11.42/1.99    ~r1_ordinal1(k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))),sK2) | ~r2_hidden(sK1,sK2)),
% 11.42/1.99    inference(definition_unfolding,[],[f74,f82])).
% 11.42/1.99  
% 11.42/1.99  cnf(c_398,plain,
% 11.42/1.99      ( ~ r2_hidden(X0,X1) | r2_hidden(X2,X3) | X2 != X0 | X3 != X1 ),
% 11.42/1.99      theory(equality) ).
% 11.42/1.99  
% 11.42/1.99  cnf(c_6,plain,
% 11.42/1.99      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 11.42/1.99      inference(cnf_transformation,[],[f52]) ).
% 11.42/1.99  
% 11.42/1.99  cnf(c_4079,plain,
% 11.42/1.99      ( ~ r1_tarski(X0,X1)
% 11.42/1.99      | ~ r1_tarski(X1,X0)
% 11.42/1.99      | ~ r2_hidden(X2,X0)
% 11.42/1.99      | r2_hidden(X3,X1)
% 11.42/1.99      | X3 != X2 ),
% 11.42/1.99      inference(resolution,[status(thm)],[c_398,c_6]) ).
% 11.42/1.99  
% 11.42/1.99  cnf(c_394,plain,( X0 = X0 ),theory(equality) ).
% 11.42/1.99  
% 11.42/1.99  cnf(c_8579,plain,
% 11.42/1.99      ( ~ r1_tarski(X0,X1)
% 11.42/1.99      | ~ r1_tarski(X1,X0)
% 11.42/1.99      | ~ r2_hidden(X2,X1)
% 11.42/1.99      | r2_hidden(X2,X0) ),
% 11.42/1.99      inference(resolution,[status(thm)],[c_4079,c_394]) ).
% 11.42/1.99  
% 11.42/1.99  cnf(c_2,plain,
% 11.42/1.99      ( r2_hidden(sK0(X0,X1,X2),X1)
% 11.42/1.99      | r2_hidden(sK0(X0,X1,X2),X2)
% 11.42/1.99      | r2_hidden(sK0(X0,X1,X2),X0)
% 11.42/1.99      | k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = X2 ),
% 11.42/1.99      inference(cnf_transformation,[],[f85]) ).
% 11.42/1.99  
% 11.42/1.99  cnf(c_399,plain,
% 11.42/1.99      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,X1) | X2 != X0 ),
% 11.42/1.99      theory(equality) ).
% 11.42/1.99  
% 11.42/1.99  cnf(c_6172,plain,
% 11.42/1.99      ( ~ r1_tarski(X0,X1)
% 11.42/1.99      | r1_tarski(k3_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X3)),X1)
% 11.42/1.99      | r2_hidden(sK0(X2,X3,X0),X3)
% 11.42/1.99      | r2_hidden(sK0(X2,X3,X0),X0)
% 11.42/1.99      | r2_hidden(sK0(X2,X3,X0),X2) ),
% 11.42/1.99      inference(resolution,[status(thm)],[c_2,c_399]) ).
% 11.42/1.99  
% 11.42/1.99  cnf(c_13,plain,
% 11.42/1.99      ( ~ r1_ordinal1(X0,X1)
% 11.42/1.99      | r1_tarski(X0,X1)
% 11.42/1.99      | ~ v3_ordinal1(X1)
% 11.42/1.99      | ~ v3_ordinal1(X0) ),
% 11.42/1.99      inference(cnf_transformation,[],[f65]) ).
% 11.42/1.99  
% 11.42/1.99  cnf(c_19,negated_conjecture,
% 11.42/1.99      ( r1_ordinal1(k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))),sK2)
% 11.42/1.99      | r2_hidden(sK1,sK2) ),
% 11.42/1.99      inference(cnf_transformation,[],[f94]) ).
% 11.42/1.99  
% 11.42/1.99  cnf(c_1215,plain,
% 11.42/1.99      ( r1_tarski(k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))),sK2)
% 11.42/1.99      | r2_hidden(sK1,sK2)
% 11.42/1.99      | ~ v3_ordinal1(k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))))
% 11.42/1.99      | ~ v3_ordinal1(sK2) ),
% 11.42/1.99      inference(resolution,[status(thm)],[c_13,c_19]) ).
% 11.42/1.99  
% 11.42/1.99  cnf(c_21,negated_conjecture,
% 11.42/1.99      ( v3_ordinal1(sK1) ),
% 11.42/1.99      inference(cnf_transformation,[],[f71]) ).
% 11.42/1.99  
% 11.42/1.99  cnf(c_20,negated_conjecture,
% 11.42/1.99      ( v3_ordinal1(sK2) ),
% 11.42/1.99      inference(cnf_transformation,[],[f72]) ).
% 11.42/1.99  
% 11.42/1.99  cnf(c_16,plain,
% 11.42/1.99      ( ~ v3_ordinal1(X0)
% 11.42/1.99      | v3_ordinal1(k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)))) ),
% 11.42/1.99      inference(cnf_transformation,[],[f92]) ).
% 11.42/1.99  
% 11.42/1.99  cnf(c_30,plain,
% 11.42/1.99      ( v3_ordinal1(k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))))
% 11.42/1.99      | ~ v3_ordinal1(sK1) ),
% 11.42/1.99      inference(instantiation,[status(thm)],[c_16]) ).
% 11.42/1.99  
% 11.42/1.99  cnf(c_1356,plain,
% 11.42/1.99      ( r1_tarski(k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))),sK2)
% 11.42/1.99      | r2_hidden(sK1,sK2) ),
% 11.42/1.99      inference(global_propositional_subsumption,
% 11.42/1.99                [status(thm)],
% 11.42/1.99                [c_1215,c_21,c_20,c_30]) ).
% 11.42/1.99  
% 11.42/1.99  cnf(c_10576,plain,
% 11.42/2.00      ( r1_tarski(k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),sK2)
% 11.42/2.00      | r2_hidden(sK0(X0,X1,k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)))),X1)
% 11.42/2.00      | r2_hidden(sK0(X0,X1,k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)))),X0)
% 11.42/2.00      | r2_hidden(sK0(X0,X1,k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)))),k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))))
% 11.42/2.00      | r2_hidden(sK1,sK2) ),
% 11.42/2.00      inference(resolution,[status(thm)],[c_6172,c_1356]) ).
% 11.42/2.00  
% 11.42/2.00  cnf(c_400,plain,
% 11.42/2.00      ( ~ r1_ordinal1(X0,X1) | r1_ordinal1(X2,X3) | X2 != X0 | X3 != X1 ),
% 11.42/2.00      theory(equality) ).
% 11.42/2.00  
% 11.42/2.00  cnf(c_4097,plain,
% 11.42/2.00      ( ~ r1_ordinal1(X0,X1) | r1_ordinal1(X2,X1) | X2 != X0 ),
% 11.42/2.00      inference(resolution,[status(thm)],[c_400,c_394]) ).
% 11.42/2.00  
% 11.42/2.00  cnf(c_4486,plain,
% 11.42/2.00      ( ~ r1_ordinal1(X0,X1)
% 11.42/2.00      | r1_ordinal1(X2,X1)
% 11.42/2.00      | ~ r1_tarski(X2,X0)
% 11.42/2.00      | ~ r1_tarski(X0,X2) ),
% 11.42/2.00      inference(resolution,[status(thm)],[c_4097,c_6]) ).
% 11.42/2.00  
% 11.42/2.00  cnf(c_11350,plain,
% 11.42/2.00      ( ~ r1_ordinal1(k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),X2)
% 11.42/2.00      | r1_ordinal1(sK2,X2)
% 11.42/2.00      | ~ r1_tarski(sK2,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))
% 11.42/2.00      | r2_hidden(sK0(X0,X1,k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)))),X1)
% 11.42/2.00      | r2_hidden(sK0(X0,X1,k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)))),X0)
% 11.42/2.00      | r2_hidden(sK0(X0,X1,k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)))),k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))))
% 11.42/2.00      | r2_hidden(sK1,sK2) ),
% 11.42/2.00      inference(resolution,[status(thm)],[c_10576,c_4486]) ).
% 11.42/2.00  
% 11.42/2.00  cnf(c_12169,plain,
% 11.42/2.00      ( r1_ordinal1(sK2,sK2)
% 11.42/2.00      | ~ r1_tarski(sK2,k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))))
% 11.42/2.00      | r2_hidden(sK0(sK1,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)))),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))
% 11.42/2.00      | r2_hidden(sK0(sK1,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)))),k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))))
% 11.42/2.00      | r2_hidden(sK0(sK1,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)))),sK1)
% 11.42/2.00      | r2_hidden(sK1,sK2) ),
% 11.42/2.00      inference(resolution,[status(thm)],[c_11350,c_19]) ).
% 11.42/2.00  
% 11.42/2.00  cnf(c_14,plain,
% 11.42/2.00      ( r2_hidden(X0,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)))) ),
% 11.42/2.00      inference(cnf_transformation,[],[f91]) ).
% 11.42/2.00  
% 11.42/2.00  cnf(c_36,plain,
% 11.42/2.00      ( r2_hidden(sK1,k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)))) ),
% 11.42/2.00      inference(instantiation,[status(thm)],[c_14]) ).
% 11.42/2.00  
% 11.42/2.00  cnf(c_39,plain,
% 11.42/2.00      ( ~ r1_ordinal1(sK1,sK1)
% 11.42/2.00      | r1_tarski(sK1,sK1)
% 11.42/2.00      | ~ v3_ordinal1(sK1) ),
% 11.42/2.00      inference(instantiation,[status(thm)],[c_13]) ).
% 11.42/2.00  
% 11.42/2.00  cnf(c_11,plain,
% 11.42/2.00      ( r1_ordinal1(X0,X1)
% 11.42/2.00      | r1_ordinal1(X1,X0)
% 11.42/2.00      | ~ v3_ordinal1(X1)
% 11.42/2.00      | ~ v3_ordinal1(X0) ),
% 11.42/2.00      inference(cnf_transformation,[],[f63]) ).
% 11.42/2.00  
% 11.42/2.00  cnf(c_45,plain,
% 11.42/2.00      ( r1_ordinal1(sK1,sK1) | ~ v3_ordinal1(sK1) ),
% 11.42/2.00      inference(instantiation,[status(thm)],[c_11]) ).
% 11.42/2.00  
% 11.42/2.00  cnf(c_58,plain,
% 11.42/2.00      ( ~ r1_tarski(sK1,sK1) | sK1 = sK1 ),
% 11.42/2.00      inference(instantiation,[status(thm)],[c_6]) ).
% 11.42/2.00  
% 11.42/2.00  cnf(c_1286,plain,
% 11.42/2.00      ( ~ r1_tarski(X0,k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))))
% 11.42/2.00      | ~ r1_tarski(k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))),X0)
% 11.42/2.00      | X0 = k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))) ),
% 11.42/2.00      inference(instantiation,[status(thm)],[c_6]) ).
% 11.42/2.00  
% 11.42/2.00  cnf(c_2849,plain,
% 11.42/2.00      ( ~ r1_tarski(k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))),sK2)
% 11.42/2.00      | ~ r1_tarski(sK2,k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))))
% 11.42/2.00      | sK2 = k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))) ),
% 11.42/2.00      inference(instantiation,[status(thm)],[c_1286]) ).
% 11.42/2.00  
% 11.42/2.00  cnf(c_1099,plain,
% 11.42/2.00      ( r2_hidden(X0,X1)
% 11.42/2.00      | ~ r2_hidden(X2,k3_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2))))
% 11.42/2.00      | X0 != X2
% 11.42/2.00      | X1 != k3_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2))) ),
% 11.42/2.00      inference(instantiation,[status(thm)],[c_398]) ).
% 11.42/2.00  
% 11.42/2.00  cnf(c_12209,plain,
% 11.42/2.00      ( ~ r2_hidden(X0,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))))
% 11.42/2.00      | r2_hidden(X1,sK2)
% 11.42/2.00      | X1 != X0
% 11.42/2.00      | sK2 != k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))) ),
% 11.42/2.00      inference(instantiation,[status(thm)],[c_1099]) ).
% 11.42/2.00  
% 11.42/2.00  cnf(c_12212,plain,
% 11.42/2.00      ( ~ r2_hidden(sK1,k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))))
% 11.42/2.00      | r2_hidden(sK1,sK2)
% 11.42/2.00      | sK2 != k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)))
% 11.42/2.00      | sK1 != sK1 ),
% 11.42/2.00      inference(instantiation,[status(thm)],[c_12209]) ).
% 11.42/2.00  
% 11.42/2.00  cnf(c_12981,plain,
% 11.42/2.00      ( ~ r1_tarski(sK2,k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))))
% 11.42/2.00      | r2_hidden(sK1,sK2) ),
% 11.42/2.00      inference(global_propositional_subsumption,
% 11.42/2.00                [status(thm)],
% 11.42/2.00                [c_12169,c_21,c_20,c_30,c_36,c_39,c_45,c_58,c_1215,
% 11.42/2.00                 c_2849,c_12212]) ).
% 11.42/2.00  
% 11.42/2.00  cnf(c_15,plain,
% 11.42/2.00      ( r1_ordinal1(X0,X1)
% 11.42/2.00      | r2_hidden(X1,X0)
% 11.42/2.00      | ~ v3_ordinal1(X1)
% 11.42/2.00      | ~ v3_ordinal1(X0) ),
% 11.42/2.00      inference(cnf_transformation,[],[f68]) ).
% 11.42/2.00  
% 11.42/2.00  cnf(c_1211,plain,
% 11.42/2.00      ( r1_tarski(X0,X1)
% 11.42/2.00      | r2_hidden(X1,X0)
% 11.42/2.00      | ~ v3_ordinal1(X1)
% 11.42/2.00      | ~ v3_ordinal1(X0) ),
% 11.42/2.00      inference(resolution,[status(thm)],[c_13,c_15]) ).
% 11.42/2.00  
% 11.42/2.00  cnf(c_12998,plain,
% 11.42/2.00      ( r2_hidden(k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))),sK2)
% 11.42/2.00      | r2_hidden(sK1,sK2)
% 11.42/2.00      | ~ v3_ordinal1(k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))))
% 11.42/2.00      | ~ v3_ordinal1(sK2) ),
% 11.42/2.00      inference(resolution,[status(thm)],[c_12981,c_1211]) ).
% 11.42/2.00  
% 11.42/2.00  cnf(c_13003,plain,
% 11.42/2.00      ( r2_hidden(k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))),sK2)
% 11.42/2.00      | r2_hidden(sK1,sK2) ),
% 11.42/2.00      inference(global_propositional_subsumption,
% 11.42/2.00                [status(thm)],
% 11.42/2.00                [c_12998,c_21,c_20,c_30]) ).
% 11.42/2.00  
% 11.42/2.00  cnf(c_23666,plain,
% 11.42/2.00      ( ~ r1_tarski(X0,sK2)
% 11.42/2.00      | ~ r1_tarski(sK2,X0)
% 11.42/2.00      | r2_hidden(k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))),X0)
% 11.42/2.00      | r2_hidden(sK1,sK2) ),
% 11.42/2.00      inference(resolution,[status(thm)],[c_8579,c_13003]) ).
% 11.42/2.00  
% 11.42/2.00  cnf(c_17,plain,
% 11.42/2.00      ( ~ r1_tarski(X0,X1) | ~ r2_hidden(X1,X0) ),
% 11.42/2.00      inference(cnf_transformation,[],[f70]) ).
% 11.42/2.00  
% 11.42/2.00  cnf(c_7,plain,
% 11.42/2.00      ( r1_tarski(X0,X0) ),
% 11.42/2.00      inference(cnf_transformation,[],[f98]) ).
% 11.42/2.00  
% 11.42/2.00  cnf(c_2443,plain,
% 11.42/2.00      ( ~ r2_hidden(X0,X0) ),
% 11.42/2.00      inference(resolution,[status(thm)],[c_17,c_7]) ).
% 11.42/2.00  
% 11.42/2.00  cnf(c_3,plain,
% 11.42/2.00      ( ~ r2_hidden(X0,X1)
% 11.42/2.00      | r2_hidden(X0,k3_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X1))) ),
% 11.42/2.00      inference(cnf_transformation,[],[f95]) ).
% 11.42/2.00  
% 11.42/2.00  cnf(c_3115,plain,
% 11.42/2.00      ( ~ r2_hidden(k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),X1) ),
% 11.42/2.00      inference(resolution,[status(thm)],[c_2443,c_3]) ).
% 11.42/2.00  
% 11.42/2.00  cnf(c_24296,plain,
% 11.42/2.00      ( ~ r1_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),sK2)
% 11.42/2.00      | ~ r1_tarski(sK2,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))
% 11.42/2.00      | r2_hidden(sK1,sK2) ),
% 11.42/2.00      inference(resolution,[status(thm)],[c_23666,c_3115]) ).
% 11.42/2.00  
% 11.42/2.00  cnf(c_2445,plain,
% 11.42/2.00      ( ~ r2_hidden(sK2,k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))))
% 11.42/2.00      | r2_hidden(sK1,sK2) ),
% 11.42/2.00      inference(resolution,[status(thm)],[c_17,c_1356]) ).
% 11.42/2.00  
% 11.42/2.00  cnf(c_4,plain,
% 11.42/2.00      ( ~ r2_hidden(X0,X1)
% 11.42/2.00      | r2_hidden(X0,k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))) ),
% 11.42/2.00      inference(cnf_transformation,[],[f96]) ).
% 11.42/2.00  
% 11.42/2.00  cnf(c_2915,plain,
% 11.42/2.00      ( ~ r2_hidden(sK2,sK1) | r2_hidden(sK1,sK2) ),
% 11.42/2.00      inference(resolution,[status(thm)],[c_2445,c_4]) ).
% 11.42/2.00  
% 11.42/2.00  cnf(c_3117,plain,
% 11.42/2.00      ( ~ r2_hidden(k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),X0) ),
% 11.42/2.00      inference(resolution,[status(thm)],[c_2443,c_4]) ).
% 11.42/2.00  
% 11.42/2.00  cnf(c_24294,plain,
% 11.42/2.00      ( ~ r1_tarski(sK2,sK1)
% 11.42/2.00      | ~ r1_tarski(sK1,sK2)
% 11.42/2.00      | r2_hidden(sK1,sK2) ),
% 11.42/2.00      inference(resolution,[status(thm)],[c_23666,c_3117]) ).
% 11.42/2.00  
% 11.42/2.00  cnf(c_27,plain,
% 11.42/2.00      ( ~ r1_tarski(sK1,sK1) | ~ r2_hidden(sK1,sK1) ),
% 11.42/2.00      inference(instantiation,[status(thm)],[c_17]) ).
% 11.42/2.00  
% 11.42/2.00  cnf(c_396,plain,
% 11.42/2.00      ( X0 != X1
% 11.42/2.00      | X2 != X3
% 11.42/2.00      | X4 != X5
% 11.42/2.00      | X6 != X7
% 11.42/2.00      | X8 != X9
% 11.42/2.00      | X10 != X11
% 11.42/2.00      | X12 != X13
% 11.42/2.00      | X14 != X15
% 11.42/2.00      | k6_enumset1(X0,X2,X4,X6,X8,X10,X12,X14) = k6_enumset1(X1,X3,X5,X7,X9,X11,X13,X15) ),
% 11.42/2.00      theory(equality) ).
% 11.42/2.00  
% 11.42/2.00  cnf(c_402,plain,
% 11.42/2.00      ( k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) = k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)
% 11.42/2.00      | sK1 != sK1 ),
% 11.42/2.00      inference(instantiation,[status(thm)],[c_396]) ).
% 11.42/2.00  
% 11.42/2.00  cnf(c_5,plain,
% 11.42/2.00      ( r2_hidden(X0,X1)
% 11.42/2.00      | r2_hidden(X0,X2)
% 11.42/2.00      | ~ r2_hidden(X0,k3_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X1))) ),
% 11.42/2.00      inference(cnf_transformation,[],[f97]) ).
% 11.42/2.00  
% 11.42/2.00  cnf(c_1116,plain,
% 11.42/2.00      ( r2_hidden(X0,X0)
% 11.42/2.00      | r2_hidden(X0,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))
% 11.42/2.00      | ~ r2_hidden(X0,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)))) ),
% 11.42/2.00      inference(instantiation,[status(thm)],[c_5]) ).
% 11.42/2.00  
% 11.42/2.00  cnf(c_1118,plain,
% 11.42/2.00      ( r2_hidden(sK1,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))
% 11.42/2.00      | ~ r2_hidden(sK1,k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))))
% 11.42/2.00      | r2_hidden(sK1,sK1) ),
% 11.42/2.00      inference(instantiation,[status(thm)],[c_1116]) ).
% 11.42/2.00  
% 11.42/2.00  cnf(c_1771,plain,
% 11.42/2.00      ( ~ r1_tarski(X0,sK2) | ~ r1_tarski(sK2,X0) | sK2 = X0 ),
% 11.42/2.00      inference(instantiation,[status(thm)],[c_6]) ).
% 11.42/2.00  
% 11.42/2.00  cnf(c_1773,plain,
% 11.42/2.00      ( ~ r1_tarski(sK2,sK1) | ~ r1_tarski(sK1,sK2) | sK2 = sK1 ),
% 11.42/2.00      inference(instantiation,[status(thm)],[c_1771]) ).
% 11.42/2.00  
% 11.42/2.00  cnf(c_2859,plain,
% 11.42/2.00      ( ~ r1_ordinal1(sK2,X0)
% 11.42/2.00      | r1_tarski(sK2,X0)
% 11.42/2.00      | ~ v3_ordinal1(X0)
% 11.42/2.00      | ~ v3_ordinal1(sK2) ),
% 11.42/2.00      inference(instantiation,[status(thm)],[c_13]) ).
% 11.42/2.00  
% 11.42/2.00  cnf(c_2861,plain,
% 11.42/2.00      ( ~ r1_ordinal1(sK2,sK1)
% 11.42/2.00      | r1_tarski(sK2,sK1)
% 11.42/2.00      | ~ v3_ordinal1(sK2)
% 11.42/2.00      | ~ v3_ordinal1(sK1) ),
% 11.42/2.00      inference(instantiation,[status(thm)],[c_2859]) ).
% 11.42/2.00  
% 11.42/2.00  cnf(c_2913,plain,
% 11.42/2.00      ( ~ r2_hidden(sK2,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))
% 11.42/2.00      | r2_hidden(sK1,sK2) ),
% 11.42/2.00      inference(resolution,[status(thm)],[c_2445,c_3]) ).
% 11.42/2.00  
% 11.42/2.00  cnf(c_9,plain,
% 11.42/2.00      ( r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1)
% 11.42/2.00      | ~ r2_hidden(X0,X1) ),
% 11.42/2.00      inference(cnf_transformation,[],[f89]) ).
% 11.42/2.00  
% 11.42/2.00  cnf(c_2677,plain,
% 11.42/2.00      ( ~ r2_hidden(X0,X1)
% 11.42/2.00      | ~ r2_hidden(X1,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) ),
% 11.42/2.00      inference(resolution,[status(thm)],[c_9,c_17]) ).
% 11.42/2.00  
% 11.42/2.00  cnf(c_3103,plain,
% 11.42/2.00      ( ~ r2_hidden(sK2,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)) ),
% 11.42/2.00      inference(forward_subsumption_resolution,
% 11.42/2.00                [status(thm)],
% 11.42/2.00                [c_2913,c_2677]) ).
% 11.42/2.00  
% 11.42/2.00  cnf(c_5554,plain,
% 11.42/2.00      ( r1_ordinal1(sK2,X0)
% 11.42/2.00      | r2_hidden(X0,sK2)
% 11.42/2.00      | ~ v3_ordinal1(X0)
% 11.42/2.00      | ~ v3_ordinal1(sK2) ),
% 11.42/2.00      inference(instantiation,[status(thm)],[c_15]) ).
% 11.42/2.00  
% 11.42/2.00  cnf(c_5561,plain,
% 11.42/2.00      ( r1_ordinal1(sK2,sK1)
% 11.42/2.00      | r2_hidden(sK1,sK2)
% 11.42/2.00      | ~ v3_ordinal1(sK2)
% 11.42/2.00      | ~ v3_ordinal1(sK1) ),
% 11.42/2.00      inference(instantiation,[status(thm)],[c_5554]) ).
% 11.42/2.00  
% 11.42/2.00  cnf(c_1232,plain,
% 11.42/2.00      ( r2_hidden(X0,X1)
% 11.42/2.00      | ~ r2_hidden(X2,k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2))
% 11.42/2.00      | X0 != X2
% 11.42/2.00      | X1 != k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2) ),
% 11.42/2.00      inference(instantiation,[status(thm)],[c_398]) ).
% 11.42/2.00  
% 11.42/2.00  cnf(c_1417,plain,
% 11.42/2.00      ( ~ r2_hidden(X0,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))
% 11.42/2.00      | r2_hidden(X1,k6_enumset1(X2,X3,X4,X5,X6,X7,X8,X9))
% 11.42/2.00      | X1 != X0
% 11.42/2.00      | k6_enumset1(X2,X3,X4,X5,X6,X7,X8,X9) != k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
% 11.42/2.00      inference(instantiation,[status(thm)],[c_1232]) ).
% 11.42/2.00  
% 11.42/2.00  cnf(c_26057,plain,
% 11.42/2.00      ( ~ r2_hidden(X0,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))
% 11.42/2.00      | r2_hidden(sK2,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))
% 11.42/2.00      | k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) != k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)
% 11.42/2.00      | sK2 != X0 ),
% 11.42/2.00      inference(instantiation,[status(thm)],[c_1417]) ).
% 11.42/2.00  
% 11.42/2.00  cnf(c_26059,plain,
% 11.42/2.00      ( r2_hidden(sK2,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))
% 11.42/2.00      | ~ r2_hidden(sK1,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))
% 11.42/2.00      | k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) != k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)
% 11.42/2.00      | sK2 != sK1 ),
% 11.42/2.00      inference(instantiation,[status(thm)],[c_26057]) ).
% 11.42/2.00  
% 11.42/2.00  cnf(c_26373,plain,
% 11.42/2.00      ( ~ r1_tarski(sK1,sK2) | r2_hidden(sK1,sK2) ),
% 11.42/2.00      inference(global_propositional_subsumption,
% 11.42/2.00                [status(thm)],
% 11.42/2.00                [c_24294,c_21,c_20,c_27,c_36,c_39,c_45,c_58,c_402,c_1118,
% 11.42/2.00                 c_1773,c_2861,c_3103,c_5561,c_26059]) ).
% 11.42/2.00  
% 11.42/2.00  cnf(c_27071,plain,
% 11.42/2.00      ( r2_hidden(sK2,sK1)
% 11.42/2.00      | r2_hidden(sK1,sK2)
% 11.42/2.00      | ~ v3_ordinal1(sK2)
% 11.42/2.00      | ~ v3_ordinal1(sK1) ),
% 11.42/2.00      inference(resolution,[status(thm)],[c_26373,c_1211]) ).
% 11.42/2.00  
% 11.42/2.00  cnf(c_27076,plain,
% 11.42/2.00      ( r2_hidden(sK1,sK2) ),
% 11.42/2.00      inference(global_propositional_subsumption,
% 11.42/2.00                [status(thm)],
% 11.42/2.00                [c_24296,c_21,c_20,c_2915,c_27071]) ).
% 11.42/2.00  
% 11.42/2.00  cnf(c_1210,plain,
% 11.42/2.00      ( r1_ordinal1(X0,X1)
% 11.42/2.00      | r1_tarski(X1,X0)
% 11.42/2.00      | ~ v3_ordinal1(X1)
% 11.42/2.00      | ~ v3_ordinal1(X0) ),
% 11.42/2.00      inference(resolution,[status(thm)],[c_13,c_11]) ).
% 11.42/2.00  
% 11.42/2.00  cnf(c_1769,plain,
% 11.42/2.00      ( r1_tarski(X0,X1)
% 11.42/2.00      | r1_tarski(X1,X0)
% 11.42/2.00      | ~ v3_ordinal1(X0)
% 11.42/2.00      | ~ v3_ordinal1(X1) ),
% 11.42/2.00      inference(resolution,[status(thm)],[c_1210,c_13]) ).
% 11.42/2.00  
% 11.42/2.00  cnf(c_2439,plain,
% 11.42/2.00      ( r1_tarski(X0,X1)
% 11.42/2.00      | ~ r2_hidden(X0,X1)
% 11.42/2.00      | ~ v3_ordinal1(X1)
% 11.42/2.00      | ~ v3_ordinal1(X0) ),
% 11.42/2.00      inference(resolution,[status(thm)],[c_17,c_1769]) ).
% 11.42/2.00  
% 11.42/2.00  cnf(c_3341,plain,
% 11.42/2.00      ( ~ r2_hidden(X0,X1)
% 11.42/2.00      | ~ r2_hidden(X1,X0)
% 11.42/2.00      | ~ v3_ordinal1(X1)
% 11.42/2.00      | ~ v3_ordinal1(X0) ),
% 11.42/2.00      inference(resolution,[status(thm)],[c_2439,c_17]) ).
% 11.42/2.00  
% 11.42/2.00  cnf(c_27090,plain,
% 11.42/2.00      ( ~ r2_hidden(sK2,sK1) | ~ v3_ordinal1(sK2) | ~ v3_ordinal1(sK1) ),
% 11.42/2.00      inference(resolution,[status(thm)],[c_27076,c_3341]) ).
% 11.42/2.00  
% 11.42/2.00  cnf(c_888,plain,
% 11.42/2.00      ( r1_ordinal1(X0,X1) = iProver_top
% 11.42/2.00      | r2_hidden(X1,X0) = iProver_top
% 11.42/2.00      | v3_ordinal1(X0) != iProver_top
% 11.42/2.00      | v3_ordinal1(X1) != iProver_top ),
% 11.42/2.00      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 11.42/2.00  
% 11.42/2.00  cnf(c_18,negated_conjecture,
% 11.42/2.00      ( ~ r1_ordinal1(k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))),sK2)
% 11.42/2.00      | ~ r2_hidden(sK1,sK2) ),
% 11.42/2.00      inference(cnf_transformation,[],[f93]) ).
% 11.42/2.00  
% 11.42/2.00  cnf(c_885,plain,
% 11.42/2.00      ( r1_ordinal1(k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))),sK2) != iProver_top
% 11.42/2.00      | r2_hidden(sK1,sK2) != iProver_top ),
% 11.42/2.00      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 11.42/2.00  
% 11.42/2.00  cnf(c_2203,plain,
% 11.42/2.00      ( r2_hidden(sK2,k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)))) = iProver_top
% 11.42/2.00      | r2_hidden(sK1,sK2) != iProver_top
% 11.42/2.00      | v3_ordinal1(k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)))) != iProver_top
% 11.42/2.00      | v3_ordinal1(sK2) != iProver_top ),
% 11.42/2.00      inference(superposition,[status(thm)],[c_888,c_885]) ).
% 11.42/2.00  
% 11.42/2.00  cnf(c_22,plain,
% 11.42/2.00      ( v3_ordinal1(sK1) = iProver_top ),
% 11.42/2.00      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 11.42/2.00  
% 11.42/2.00  cnf(c_23,plain,
% 11.42/2.00      ( v3_ordinal1(sK2) = iProver_top ),
% 11.42/2.00      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 11.42/2.00  
% 11.42/2.00  cnf(c_29,plain,
% 11.42/2.00      ( v3_ordinal1(X0) != iProver_top
% 11.42/2.00      | v3_ordinal1(k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)))) = iProver_top ),
% 11.42/2.00      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 11.42/2.00  
% 11.42/2.00  cnf(c_31,plain,
% 11.42/2.00      ( v3_ordinal1(k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)))) = iProver_top
% 11.42/2.00      | v3_ordinal1(sK1) != iProver_top ),
% 11.42/2.00      inference(instantiation,[status(thm)],[c_29]) ).
% 11.42/2.00  
% 11.42/2.00  cnf(c_2885,plain,
% 11.42/2.00      ( r2_hidden(sK2,k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)))) = iProver_top
% 11.42/2.00      | r2_hidden(sK1,sK2) != iProver_top ),
% 11.42/2.00      inference(global_propositional_subsumption,
% 11.42/2.00                [status(thm)],
% 11.42/2.00                [c_2203,c_22,c_23,c_31]) ).
% 11.42/2.00  
% 11.42/2.00  cnf(c_897,plain,
% 11.42/2.00      ( r2_hidden(X0,X1) = iProver_top
% 11.42/2.00      | r2_hidden(X0,X2) = iProver_top
% 11.42/2.00      | r2_hidden(X0,k3_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X1))) != iProver_top ),
% 11.42/2.00      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 11.42/2.00  
% 11.42/2.00  cnf(c_2891,plain,
% 11.42/2.00      ( r2_hidden(sK2,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)) = iProver_top
% 11.42/2.00      | r2_hidden(sK2,sK1) = iProver_top
% 11.42/2.00      | r2_hidden(sK1,sK2) != iProver_top ),
% 11.42/2.00      inference(superposition,[status(thm)],[c_2885,c_897]) ).
% 11.42/2.00  
% 11.42/2.00  cnf(c_2892,plain,
% 11.42/2.00      ( r2_hidden(sK2,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))
% 11.42/2.00      | r2_hidden(sK2,sK1)
% 11.42/2.00      | ~ r2_hidden(sK1,sK2) ),
% 11.42/2.00      inference(predicate_to_equality_rev,[status(thm)],[c_2891]) ).
% 11.42/2.00  
% 11.42/2.00  cnf(contradiction,plain,
% 11.42/2.00      ( $false ),
% 11.42/2.00      inference(minisat,
% 11.42/2.00                [status(thm)],
% 11.42/2.00                [c_27090,c_27076,c_3103,c_2892,c_20,c_21]) ).
% 11.42/2.00  
% 11.42/2.00  
% 11.42/2.00  % SZS output end CNFRefutation for theBenchmark.p
% 11.42/2.00  
% 11.42/2.00  ------                               Statistics
% 11.42/2.00  
% 11.42/2.00  ------ Selected
% 11.96/2.00  
% 11.96/2.00  total_time:                             1.452
% 11.96/2.00  
%------------------------------------------------------------------------------
