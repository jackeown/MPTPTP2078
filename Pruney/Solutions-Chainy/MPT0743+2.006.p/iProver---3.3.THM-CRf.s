%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:53:37 EST 2020

% Result     : Theorem 2.40s
% Output     : CNFRefutation 2.40s
% Verified   : 
% Statistics : Number of formulae       :  157 ( 599 expanded)
%              Number of clauses        :   75 ( 133 expanded)
%              Number of leaves         :   21 ( 152 expanded)
%              Depth                    :   18
%              Number of atoms          :  563 (2199 expanded)
%              Number of equality atoms :  189 ( 448 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal clause size      :   18 (   3 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f32])).

fof(f55,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f12,axiom,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ! [X1] :
          ( v3_ordinal1(X1)
         => ( r2_hidden(X1,X0)
            | r1_ordinal1(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(X1,X0)
          | r1_ordinal1(X0,X1)
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(X1,X0)
          | r1_ordinal1(X0,X1)
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(flattening,[],[f22])).

fof(f73,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,X0)
      | r1_ordinal1(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f15,conjecture,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ! [X1] :
          ( v3_ordinal1(X1)
         => ( r2_hidden(X0,X1)
          <=> r1_ordinal1(k1_ordinal1(X0),X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,negated_conjecture,(
    ~ ! [X0] :
        ( v3_ordinal1(X0)
       => ! [X1] :
            ( v3_ordinal1(X1)
           => ( r2_hidden(X0,X1)
            <=> r1_ordinal1(k1_ordinal1(X0),X1) ) ) ) ),
    inference(negated_conjecture,[],[f15])).

fof(f26,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( r2_hidden(X0,X1)
          <~> r1_ordinal1(k1_ordinal1(X0),X1) )
          & v3_ordinal1(X1) )
      & v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f41,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ r1_ordinal1(k1_ordinal1(X0),X1)
            | ~ r2_hidden(X0,X1) )
          & ( r1_ordinal1(k1_ordinal1(X0),X1)
            | r2_hidden(X0,X1) )
          & v3_ordinal1(X1) )
      & v3_ordinal1(X0) ) ),
    inference(nnf_transformation,[],[f26])).

fof(f42,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ r1_ordinal1(k1_ordinal1(X0),X1)
            | ~ r2_hidden(X0,X1) )
          & ( r1_ordinal1(k1_ordinal1(X0),X1)
            | r2_hidden(X0,X1) )
          & v3_ordinal1(X1) )
      & v3_ordinal1(X0) ) ),
    inference(flattening,[],[f41])).

fof(f44,plain,(
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

fof(f43,plain,
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

fof(f45,plain,
    ( ( ~ r1_ordinal1(k1_ordinal1(sK2),sK3)
      | ~ r2_hidden(sK2,sK3) )
    & ( r1_ordinal1(k1_ordinal1(sK2),sK3)
      | r2_hidden(sK2,sK3) )
    & v3_ordinal1(sK3)
    & v3_ordinal1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f42,f44,f43])).

fof(f79,plain,
    ( ~ r1_ordinal1(k1_ordinal1(sK2),sK3)
    | ~ r2_hidden(sK2,sK3) ),
    inference(cnf_transformation,[],[f45])).

fof(f10,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_tarski(X0)) = k1_ordinal1(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f70,plain,(
    ! [X0] : k2_xboole_0(X0,k1_tarski(X0)) = k1_ordinal1(X0) ),
    inference(cnf_transformation,[],[f10])).

fof(f9,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f69,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f80,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k1_enumset1(X0,X0,X1)) ),
    inference(definition_unfolding,[],[f69,f66])).

fof(f6,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f65,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f7,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f66,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f7])).

fof(f81,plain,(
    ! [X0] : k1_enumset1(X0,X0,X0) = k1_tarski(X0) ),
    inference(definition_unfolding,[],[f65,f66])).

fof(f82,plain,(
    ! [X0] : k3_tarski(k1_enumset1(X0,X0,k1_enumset1(X0,X0,X0))) = k1_ordinal1(X0) ),
    inference(definition_unfolding,[],[f70,f80,f81])).

fof(f93,plain,
    ( ~ r1_ordinal1(k3_tarski(k1_enumset1(sK2,sK2,k1_enumset1(sK2,sK2,sK2))),sK3)
    | ~ r2_hidden(sK2,sK3) ),
    inference(definition_unfolding,[],[f79,f82])).

fof(f76,plain,(
    v3_ordinal1(sK2) ),
    inference(cnf_transformation,[],[f45])).

fof(f77,plain,(
    v3_ordinal1(sK3) ),
    inference(cnf_transformation,[],[f45])).

fof(f13,axiom,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => v3_ordinal1(k1_ordinal1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0] :
      ( v3_ordinal1(k1_ordinal1(X0))
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f74,plain,(
    ! [X0] :
      ( v3_ordinal1(k1_ordinal1(X0))
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f92,plain,(
    ! [X0] :
      ( v3_ordinal1(k3_tarski(k1_enumset1(X0,X0,k1_enumset1(X0,X0,X0))))
      | ~ v3_ordinal1(X0) ) ),
    inference(definition_unfolding,[],[f74,f82])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
    <=> r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(k1_tarski(X0),X1)
        | ~ r2_hidden(X0,X1) )
      & ( r2_hidden(X0,X1)
        | ~ r1_tarski(k1_tarski(X0),X1) ) ) ),
    inference(nnf_transformation,[],[f8])).

fof(f68,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f90,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_enumset1(X0,X0,X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f68,f81])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            | r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
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

fof(f28,plain,(
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
    inference(flattening,[],[f27])).

fof(f29,plain,(
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
    inference(rectify,[],[f28])).

fof(f30,plain,(
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

fof(f31,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f29,f30])).

fof(f47,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X1)
      | r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f31])).

fof(f88,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X1)
      | r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k3_tarski(k1_enumset1(X0,X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f47,f80])).

fof(f97,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X1)
      | r2_hidden(X4,X0)
      | ~ r2_hidden(X4,k3_tarski(k1_enumset1(X0,X0,X1))) ) ),
    inference(equality_resolution,[],[f88])).

fof(f14,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f75,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f49,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X1)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f31])).

fof(f86,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X1)
      | k3_tarski(k1_enumset1(X0,X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f49,f80])).

fof(f95,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k3_tarski(k1_enumset1(X0,X0,X1)))
      | ~ r2_hidden(X4,X1) ) ),
    inference(equality_resolution,[],[f86])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( ( v3_ordinal1(X1)
        & v3_ordinal1(X0) )
     => ( r1_ordinal1(X0,X1)
      <=> r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( r1_ordinal1(X0,X1)
      <=> r1_tarski(X0,X1) )
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( r1_ordinal1(X0,X1)
      <=> r1_tarski(X0,X1) )
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(flattening,[],[f20])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( ( r1_ordinal1(X0,X1)
          | ~ r1_tarski(X0,X1) )
        & ( r1_tarski(X0,X1)
          | ~ r1_ordinal1(X0,X1) ) )
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(nnf_transformation,[],[f21])).

fof(f71,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r1_ordinal1(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f78,plain,
    ( r1_ordinal1(k1_ordinal1(sK2),sK3)
    | r2_hidden(sK2,sK3) ),
    inference(cnf_transformation,[],[f45])).

fof(f94,plain,
    ( r1_ordinal1(k3_tarski(k1_enumset1(sK2,sK2,k1_enumset1(sK2,sK2,sK2))),sK3)
    | r2_hidden(sK2,sK3) ),
    inference(definition_unfolding,[],[f78,f82])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X1),X2)
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(k2_xboole_0(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(k2_xboole_0(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f89,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(k3_tarski(k1_enumset1(X0,X0,X1)),X2) ) ),
    inference(definition_unfolding,[],[f56,f80])).

fof(f53,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f33])).

fof(f99,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f53])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ~ ( X2 != X4
              & X1 != X4
              & X0 != X4 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( X2 = X4
            | X1 = X4
            | X0 = X4 ) ) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f34,plain,(
    ! [X0,X1,X2,X3] :
      ( ( k1_enumset1(X0,X1,X2) = X3
        | ? [X4] :
            ( ( ( X2 != X4
                & X1 != X4
                & X0 != X4 )
              | ~ r2_hidden(X4,X3) )
            & ( X2 = X4
              | X1 = X4
              | X0 = X4
              | r2_hidden(X4,X3) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X3)
              | ( X2 != X4
                & X1 != X4
                & X0 != X4 ) )
            & ( X2 = X4
              | X1 = X4
              | X0 = X4
              | ~ r2_hidden(X4,X3) ) )
        | k1_enumset1(X0,X1,X2) != X3 ) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f35,plain,(
    ! [X0,X1,X2,X3] :
      ( ( k1_enumset1(X0,X1,X2) = X3
        | ? [X4] :
            ( ( ( X2 != X4
                & X1 != X4
                & X0 != X4 )
              | ~ r2_hidden(X4,X3) )
            & ( X2 = X4
              | X1 = X4
              | X0 = X4
              | r2_hidden(X4,X3) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X3)
              | ( X2 != X4
                & X1 != X4
                & X0 != X4 ) )
            & ( X2 = X4
              | X1 = X4
              | X0 = X4
              | ~ r2_hidden(X4,X3) ) )
        | k1_enumset1(X0,X1,X2) != X3 ) ) ),
    inference(flattening,[],[f34])).

fof(f36,plain,(
    ! [X0,X1,X2,X3] :
      ( ( k1_enumset1(X0,X1,X2) = X3
        | ? [X4] :
            ( ( ( X2 != X4
                & X1 != X4
                & X0 != X4 )
              | ~ r2_hidden(X4,X3) )
            & ( X2 = X4
              | X1 = X4
              | X0 = X4
              | r2_hidden(X4,X3) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X3)
              | ( X2 != X5
                & X1 != X5
                & X0 != X5 ) )
            & ( X2 = X5
              | X1 = X5
              | X0 = X5
              | ~ r2_hidden(X5,X3) ) )
        | k1_enumset1(X0,X1,X2) != X3 ) ) ),
    inference(rectify,[],[f35])).

fof(f37,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X4] :
          ( ( ( X2 != X4
              & X1 != X4
              & X0 != X4 )
            | ~ r2_hidden(X4,X3) )
          & ( X2 = X4
            | X1 = X4
            | X0 = X4
            | r2_hidden(X4,X3) ) )
     => ( ( ( sK1(X0,X1,X2,X3) != X2
            & sK1(X0,X1,X2,X3) != X1
            & sK1(X0,X1,X2,X3) != X0 )
          | ~ r2_hidden(sK1(X0,X1,X2,X3),X3) )
        & ( sK1(X0,X1,X2,X3) = X2
          | sK1(X0,X1,X2,X3) = X1
          | sK1(X0,X1,X2,X3) = X0
          | r2_hidden(sK1(X0,X1,X2,X3),X3) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,(
    ! [X0,X1,X2,X3] :
      ( ( k1_enumset1(X0,X1,X2) = X3
        | ( ( ( sK1(X0,X1,X2,X3) != X2
              & sK1(X0,X1,X2,X3) != X1
              & sK1(X0,X1,X2,X3) != X0 )
            | ~ r2_hidden(sK1(X0,X1,X2,X3),X3) )
          & ( sK1(X0,X1,X2,X3) = X2
            | sK1(X0,X1,X2,X3) = X1
            | sK1(X0,X1,X2,X3) = X0
            | r2_hidden(sK1(X0,X1,X2,X3),X3) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X3)
              | ( X2 != X5
                & X1 != X5
                & X0 != X5 ) )
            & ( X2 = X5
              | X1 = X5
              | X0 = X5
              | ~ r2_hidden(X5,X3) ) )
        | k1_enumset1(X0,X1,X2) != X3 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f36,f37])).

fof(f58,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X0 != X5
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f38])).

fof(f104,plain,(
    ! [X2,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | k1_enumset1(X5,X1,X2) != X3 ) ),
    inference(equality_resolution,[],[f58])).

fof(f105,plain,(
    ! [X2,X5,X1] : r2_hidden(X5,k1_enumset1(X5,X1,X2)) ),
    inference(equality_resolution,[],[f104])).

fof(f57,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( X2 = X5
      | X1 = X5
      | X0 = X5
      | ~ r2_hidden(X5,X3)
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f38])).

fof(f106,plain,(
    ! [X2,X0,X5,X1] :
      ( X2 = X5
      | X1 = X5
      | X0 = X5
      | ~ r2_hidden(X5,k1_enumset1(X0,X1,X2)) ) ),
    inference(equality_resolution,[],[f57])).

cnf(c_7,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f55])).

cnf(c_6792,plain,
    ( ~ r1_tarski(X0,sK3)
    | ~ r1_tarski(sK3,X0)
    | sK3 = X0 ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_6794,plain,
    ( ~ r1_tarski(sK3,sK2)
    | ~ r1_tarski(sK2,sK3)
    | sK3 = sK2 ),
    inference(instantiation,[status(thm)],[c_6792])).

cnf(c_709,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_1664,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(X2,k1_enumset1(X3,X4,X2))
    | X0 != X2
    | X1 != k1_enumset1(X3,X4,X2) ),
    inference(instantiation,[status(thm)],[c_709])).

cnf(c_2050,plain,
    ( ~ r2_hidden(X0,k1_enumset1(X1,X2,X0))
    | r2_hidden(X3,k1_enumset1(X1,X2,X0))
    | X3 != X0
    | k1_enumset1(X1,X2,X0) != k1_enumset1(X1,X2,X0) ),
    inference(instantiation,[status(thm)],[c_1664])).

cnf(c_5561,plain,
    ( r2_hidden(sK3,k1_enumset1(sK2,sK2,sK2))
    | ~ r2_hidden(sK2,k1_enumset1(sK2,sK2,sK2))
    | k1_enumset1(sK2,sK2,sK2) != k1_enumset1(sK2,sK2,sK2)
    | sK3 != sK2 ),
    inference(instantiation,[status(thm)],[c_2050])).

cnf(c_23,plain,
    ( r1_ordinal1(X0,X1)
    | r2_hidden(X1,X0)
    | ~ v3_ordinal1(X1)
    | ~ v3_ordinal1(X0) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_26,negated_conjecture,
    ( ~ r1_ordinal1(k3_tarski(k1_enumset1(sK2,sK2,k1_enumset1(sK2,sK2,sK2))),sK3)
    | ~ r2_hidden(sK2,sK3) ),
    inference(cnf_transformation,[],[f93])).

cnf(c_231,plain,
    ( ~ r2_hidden(sK2,sK3)
    | ~ r1_ordinal1(k3_tarski(k1_enumset1(sK2,sK2,k1_enumset1(sK2,sK2,sK2))),sK3) ),
    inference(prop_impl,[status(thm)],[c_26])).

cnf(c_232,plain,
    ( ~ r1_ordinal1(k3_tarski(k1_enumset1(sK2,sK2,k1_enumset1(sK2,sK2,sK2))),sK3)
    | ~ r2_hidden(sK2,sK3) ),
    inference(renaming,[status(thm)],[c_231])).

cnf(c_402,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(sK2,sK3)
    | ~ v3_ordinal1(X1)
    | ~ v3_ordinal1(X0)
    | k3_tarski(k1_enumset1(sK2,sK2,k1_enumset1(sK2,sK2,sK2))) != X1
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_23,c_232])).

cnf(c_403,plain,
    ( r2_hidden(sK3,k3_tarski(k1_enumset1(sK2,sK2,k1_enumset1(sK2,sK2,sK2))))
    | ~ r2_hidden(sK2,sK3)
    | ~ v3_ordinal1(k3_tarski(k1_enumset1(sK2,sK2,k1_enumset1(sK2,sK2,sK2))))
    | ~ v3_ordinal1(sK3) ),
    inference(unflattening,[status(thm)],[c_402])).

cnf(c_29,negated_conjecture,
    ( v3_ordinal1(sK2) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_28,negated_conjecture,
    ( v3_ordinal1(sK3) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_24,plain,
    ( ~ v3_ordinal1(X0)
    | v3_ordinal1(k3_tarski(k1_enumset1(X0,X0,k1_enumset1(X0,X0,X0)))) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_38,plain,
    ( v3_ordinal1(k3_tarski(k1_enumset1(sK2,sK2,k1_enumset1(sK2,sK2,sK2))))
    | ~ v3_ordinal1(sK2) ),
    inference(instantiation,[status(thm)],[c_24])).

cnf(c_405,plain,
    ( r2_hidden(sK3,k3_tarski(k1_enumset1(sK2,sK2,k1_enumset1(sK2,sK2,sK2))))
    | ~ r2_hidden(sK2,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_403,c_29,c_28,c_38])).

cnf(c_1327,plain,
    ( r2_hidden(sK3,k3_tarski(k1_enumset1(sK2,sK2,k1_enumset1(sK2,sK2,sK2)))) = iProver_top
    | r2_hidden(sK2,sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_405])).

cnf(c_30,plain,
    ( v3_ordinal1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_31,plain,
    ( v3_ordinal1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_37,plain,
    ( v3_ordinal1(X0) != iProver_top
    | v3_ordinal1(k3_tarski(k1_enumset1(X0,X0,k1_enumset1(X0,X0,X0)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_39,plain,
    ( v3_ordinal1(k3_tarski(k1_enumset1(sK2,sK2,k1_enumset1(sK2,sK2,sK2)))) = iProver_top
    | v3_ordinal1(sK2) != iProver_top ),
    inference(instantiation,[status(thm)],[c_37])).

cnf(c_404,plain,
    ( r2_hidden(sK3,k3_tarski(k1_enumset1(sK2,sK2,k1_enumset1(sK2,sK2,sK2)))) = iProver_top
    | r2_hidden(sK2,sK3) != iProver_top
    | v3_ordinal1(k3_tarski(k1_enumset1(sK2,sK2,k1_enumset1(sK2,sK2,sK2)))) != iProver_top
    | v3_ordinal1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_403])).

cnf(c_0,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X1,X0) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_1544,plain,
    ( ~ r2_hidden(sK3,sK2)
    | ~ r2_hidden(sK2,sK3) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_1545,plain,
    ( r2_hidden(sK3,sK2) != iProver_top
    | r2_hidden(sK2,sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1544])).

cnf(c_19,plain,
    ( r1_tarski(k1_enumset1(X0,X0,X0),X1)
    | ~ r2_hidden(X0,X1) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_1640,plain,
    ( r1_tarski(k1_enumset1(sK2,sK2,sK2),sK3)
    | ~ r2_hidden(sK2,sK3) ),
    inference(instantiation,[status(thm)],[c_19])).

cnf(c_1641,plain,
    ( r1_tarski(k1_enumset1(sK2,sK2,sK2),sK3) = iProver_top
    | r2_hidden(sK2,sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1640])).

cnf(c_6,plain,
    ( r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | ~ r2_hidden(X0,k3_tarski(k1_enumset1(X2,X2,X1))) ),
    inference(cnf_transformation,[],[f97])).

cnf(c_1657,plain,
    ( r2_hidden(sK3,k1_enumset1(sK2,sK2,sK2))
    | ~ r2_hidden(sK3,k3_tarski(k1_enumset1(sK2,sK2,k1_enumset1(sK2,sK2,sK2))))
    | r2_hidden(sK3,sK2) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_1658,plain,
    ( r2_hidden(sK3,k1_enumset1(sK2,sK2,sK2)) = iProver_top
    | r2_hidden(sK3,k3_tarski(k1_enumset1(sK2,sK2,k1_enumset1(sK2,sK2,sK2)))) != iProver_top
    | r2_hidden(sK3,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1657])).

cnf(c_25,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r2_hidden(X1,X0) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_1996,plain,
    ( ~ r1_tarski(k1_enumset1(X0,X0,X0),X1)
    | ~ r2_hidden(X1,k1_enumset1(X0,X0,X0)) ),
    inference(instantiation,[status(thm)],[c_25])).

cnf(c_3177,plain,
    ( ~ r1_tarski(k1_enumset1(sK2,sK2,sK2),sK3)
    | ~ r2_hidden(sK3,k1_enumset1(sK2,sK2,sK2)) ),
    inference(instantiation,[status(thm)],[c_1996])).

cnf(c_3181,plain,
    ( r1_tarski(k1_enumset1(sK2,sK2,sK2),sK3) != iProver_top
    | r2_hidden(sK3,k1_enumset1(sK2,sK2,sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3177])).

cnf(c_4396,plain,
    ( r2_hidden(sK2,sK3) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1327,c_30,c_31,c_39,c_404,c_1545,c_1641,c_1658,c_3181])).

cnf(c_3469,plain,
    ( ~ r1_tarski(X0,sK3)
    | ~ r1_tarski(sK3,X0)
    | X0 = sK3 ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_3470,plain,
    ( X0 = sK3
    | r1_tarski(X0,sK3) != iProver_top
    | r1_tarski(sK3,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3469])).

cnf(c_3472,plain,
    ( sK2 = sK3
    | r1_tarski(sK3,sK2) != iProver_top
    | r1_tarski(sK2,sK3) != iProver_top ),
    inference(instantiation,[status(thm)],[c_3470])).

cnf(c_4,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,k3_tarski(k1_enumset1(X2,X2,X1))) ),
    inference(cnf_transformation,[],[f95])).

cnf(c_1984,plain,
    ( ~ r2_hidden(X0,k1_enumset1(X1,X1,X1))
    | r2_hidden(X0,k3_tarski(k1_enumset1(X2,X2,k1_enumset1(X1,X1,X1)))) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_2273,plain,
    ( ~ r2_hidden(sK3,k1_enumset1(sK2,sK2,sK2))
    | r2_hidden(sK3,k3_tarski(k1_enumset1(sK2,sK2,k1_enumset1(sK2,sK2,sK2)))) ),
    inference(instantiation,[status(thm)],[c_1984])).

cnf(c_22,plain,
    ( ~ r1_ordinal1(X0,X1)
    | r1_tarski(X0,X1)
    | ~ v3_ordinal1(X1)
    | ~ v3_ordinal1(X0) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_27,negated_conjecture,
    ( r1_ordinal1(k3_tarski(k1_enumset1(sK2,sK2,k1_enumset1(sK2,sK2,sK2))),sK3)
    | r2_hidden(sK2,sK3) ),
    inference(cnf_transformation,[],[f94])).

cnf(c_233,plain,
    ( r2_hidden(sK2,sK3)
    | r1_ordinal1(k3_tarski(k1_enumset1(sK2,sK2,k1_enumset1(sK2,sK2,sK2))),sK3) ),
    inference(prop_impl,[status(thm)],[c_27])).

cnf(c_234,plain,
    ( r1_ordinal1(k3_tarski(k1_enumset1(sK2,sK2,k1_enumset1(sK2,sK2,sK2))),sK3)
    | r2_hidden(sK2,sK3) ),
    inference(renaming,[status(thm)],[c_233])).

cnf(c_430,plain,
    ( r1_tarski(X0,X1)
    | r2_hidden(sK2,sK3)
    | ~ v3_ordinal1(X0)
    | ~ v3_ordinal1(X1)
    | k3_tarski(k1_enumset1(sK2,sK2,k1_enumset1(sK2,sK2,sK2))) != X0
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_22,c_234])).

cnf(c_431,plain,
    ( r1_tarski(k3_tarski(k1_enumset1(sK2,sK2,k1_enumset1(sK2,sK2,sK2))),sK3)
    | r2_hidden(sK2,sK3)
    | ~ v3_ordinal1(k3_tarski(k1_enumset1(sK2,sK2,k1_enumset1(sK2,sK2,sK2))))
    | ~ v3_ordinal1(sK3) ),
    inference(unflattening,[status(thm)],[c_430])).

cnf(c_559,plain,
    ( r2_hidden(sK2,sK3)
    | r1_tarski(k3_tarski(k1_enumset1(sK2,sK2,k1_enumset1(sK2,sK2,sK2))),sK3) ),
    inference(prop_impl,[status(thm)],[c_29,c_28,c_38,c_431])).

cnf(c_560,plain,
    ( r1_tarski(k3_tarski(k1_enumset1(sK2,sK2,k1_enumset1(sK2,sK2,sK2))),sK3)
    | r2_hidden(sK2,sK3) ),
    inference(renaming,[status(thm)],[c_559])).

cnf(c_1325,plain,
    ( r1_tarski(k3_tarski(k1_enumset1(sK2,sK2,k1_enumset1(sK2,sK2,sK2))),sK3) = iProver_top
    | r2_hidden(sK2,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_560])).

cnf(c_10,plain,
    ( r1_tarski(X0,X1)
    | ~ r1_tarski(k3_tarski(k1_enumset1(X0,X0,X2)),X1) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_1343,plain,
    ( r1_tarski(X0,X1) = iProver_top
    | r1_tarski(k3_tarski(k1_enumset1(X0,X0,X2)),X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_2136,plain,
    ( r1_tarski(sK2,sK3) = iProver_top
    | r2_hidden(sK2,sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_1325,c_1343])).

cnf(c_2146,plain,
    ( r1_tarski(sK2,sK3)
    | r2_hidden(sK2,sK3) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_2136])).

cnf(c_1331,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r2_hidden(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_1759,plain,
    ( r2_hidden(sK3,k3_tarski(k1_enumset1(sK2,sK2,k1_enumset1(sK2,sK2,sK2)))) != iProver_top
    | r2_hidden(sK2,sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_1325,c_1331])).

cnf(c_1760,plain,
    ( ~ r2_hidden(sK3,k3_tarski(k1_enumset1(sK2,sK2,k1_enumset1(sK2,sK2,sK2))))
    | r2_hidden(sK2,sK3) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_1759])).

cnf(c_385,plain,
    ( r1_tarski(X0,X1)
    | r2_hidden(X1,X0)
    | ~ v3_ordinal1(X0)
    | ~ v3_ordinal1(X1) ),
    inference(resolution,[status(thm)],[c_23,c_22])).

cnf(c_1730,plain,
    ( r1_tarski(sK3,sK2)
    | r2_hidden(sK2,sK3)
    | ~ v3_ordinal1(sK3)
    | ~ v3_ordinal1(sK2) ),
    inference(instantiation,[status(thm)],[c_385])).

cnf(c_1736,plain,
    ( r1_tarski(sK3,sK2) = iProver_top
    | r2_hidden(sK2,sK3) = iProver_top
    | v3_ordinal1(sK3) != iProver_top
    | v3_ordinal1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1730])).

cnf(c_1675,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(sK2,sK3)
    | X1 != sK3
    | X0 != sK2 ),
    inference(instantiation,[status(thm)],[c_709])).

cnf(c_1677,plain,
    ( ~ r2_hidden(sK2,sK3)
    | r2_hidden(sK2,sK2)
    | sK2 != sK3
    | sK2 != sK2 ),
    inference(instantiation,[status(thm)],[c_1675])).

cnf(c_710,plain,
    ( X0 != X1
    | X2 != X3
    | X4 != X5
    | k1_enumset1(X0,X2,X4) = k1_enumset1(X1,X3,X5) ),
    theory(equality)).

cnf(c_715,plain,
    ( k1_enumset1(sK2,sK2,sK2) = k1_enumset1(sK2,sK2,sK2)
    | sK2 != sK2 ),
    inference(instantiation,[status(thm)],[c_710])).

cnf(c_9,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f99])).

cnf(c_75,plain,
    ( r1_tarski(sK2,sK2) ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_17,plain,
    ( r2_hidden(X0,k1_enumset1(X0,X1,X2)) ),
    inference(cnf_transformation,[],[f105])).

cnf(c_59,plain,
    ( r2_hidden(sK2,k1_enumset1(sK2,sK2,sK2)) ),
    inference(instantiation,[status(thm)],[c_17])).

cnf(c_18,plain,
    ( ~ r2_hidden(X0,k1_enumset1(X1,X2,X3))
    | X0 = X1
    | X0 = X2
    | X0 = X3 ),
    inference(cnf_transformation,[],[f106])).

cnf(c_56,plain,
    ( ~ r2_hidden(sK2,k1_enumset1(sK2,sK2,sK2))
    | sK2 = sK2 ),
    inference(instantiation,[status(thm)],[c_18])).

cnf(c_35,plain,
    ( ~ r1_tarski(sK2,sK2)
    | ~ r2_hidden(sK2,sK2) ),
    inference(instantiation,[status(thm)],[c_25])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_6794,c_5561,c_4396,c_3472,c_2273,c_2146,c_2136,c_1760,c_1736,c_1730,c_1677,c_715,c_75,c_59,c_56,c_35,c_31,c_28,c_30,c_29])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 18:50:04 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  % Running in FOF mode
% 2.40/0.99  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.40/0.99  
% 2.40/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.40/0.99  
% 2.40/0.99  ------  iProver source info
% 2.40/0.99  
% 2.40/0.99  git: date: 2020-06-30 10:37:57 +0100
% 2.40/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.40/0.99  git: non_committed_changes: false
% 2.40/0.99  git: last_make_outside_of_git: false
% 2.40/0.99  
% 2.40/0.99  ------ 
% 2.40/0.99  
% 2.40/0.99  ------ Input Options
% 2.40/0.99  
% 2.40/0.99  --out_options                           all
% 2.40/0.99  --tptp_safe_out                         true
% 2.40/0.99  --problem_path                          ""
% 2.40/0.99  --include_path                          ""
% 2.40/0.99  --clausifier                            res/vclausify_rel
% 2.40/0.99  --clausifier_options                    --mode clausify
% 2.40/0.99  --stdin                                 false
% 2.40/0.99  --stats_out                             all
% 2.40/0.99  
% 2.40/0.99  ------ General Options
% 2.40/0.99  
% 2.40/0.99  --fof                                   false
% 2.40/0.99  --time_out_real                         305.
% 2.40/0.99  --time_out_virtual                      -1.
% 2.40/0.99  --symbol_type_check                     false
% 2.40/0.99  --clausify_out                          false
% 2.40/0.99  --sig_cnt_out                           false
% 2.40/0.99  --trig_cnt_out                          false
% 2.40/0.99  --trig_cnt_out_tolerance                1.
% 2.40/0.99  --trig_cnt_out_sk_spl                   false
% 2.40/0.99  --abstr_cl_out                          false
% 2.40/0.99  
% 2.40/0.99  ------ Global Options
% 2.40/0.99  
% 2.40/0.99  --schedule                              default
% 2.40/0.99  --add_important_lit                     false
% 2.40/0.99  --prop_solver_per_cl                    1000
% 2.40/0.99  --min_unsat_core                        false
% 2.40/0.99  --soft_assumptions                      false
% 2.40/0.99  --soft_lemma_size                       3
% 2.40/0.99  --prop_impl_unit_size                   0
% 2.40/0.99  --prop_impl_unit                        []
% 2.40/0.99  --share_sel_clauses                     true
% 2.40/0.99  --reset_solvers                         false
% 2.40/0.99  --bc_imp_inh                            [conj_cone]
% 2.40/0.99  --conj_cone_tolerance                   3.
% 2.40/0.99  --extra_neg_conj                        none
% 2.40/0.99  --large_theory_mode                     true
% 2.40/0.99  --prolific_symb_bound                   200
% 2.40/0.99  --lt_threshold                          2000
% 2.40/0.99  --clause_weak_htbl                      true
% 2.40/0.99  --gc_record_bc_elim                     false
% 2.40/0.99  
% 2.40/0.99  ------ Preprocessing Options
% 2.40/0.99  
% 2.40/0.99  --preprocessing_flag                    true
% 2.40/0.99  --time_out_prep_mult                    0.1
% 2.40/0.99  --splitting_mode                        input
% 2.40/0.99  --splitting_grd                         true
% 2.40/0.99  --splitting_cvd                         false
% 2.40/0.99  --splitting_cvd_svl                     false
% 2.40/0.99  --splitting_nvd                         32
% 2.40/0.99  --sub_typing                            true
% 2.40/0.99  --prep_gs_sim                           true
% 2.40/0.99  --prep_unflatten                        true
% 2.40/0.99  --prep_res_sim                          true
% 2.40/0.99  --prep_upred                            true
% 2.40/0.99  --prep_sem_filter                       exhaustive
% 2.40/0.99  --prep_sem_filter_out                   false
% 2.40/0.99  --pred_elim                             true
% 2.40/0.99  --res_sim_input                         true
% 2.40/0.99  --eq_ax_congr_red                       true
% 2.40/0.99  --pure_diseq_elim                       true
% 2.40/0.99  --brand_transform                       false
% 2.40/0.99  --non_eq_to_eq                          false
% 2.40/0.99  --prep_def_merge                        true
% 2.40/0.99  --prep_def_merge_prop_impl              false
% 2.40/0.99  --prep_def_merge_mbd                    true
% 2.40/0.99  --prep_def_merge_tr_red                 false
% 2.40/0.99  --prep_def_merge_tr_cl                  false
% 2.40/0.99  --smt_preprocessing                     true
% 2.40/0.99  --smt_ac_axioms                         fast
% 2.40/0.99  --preprocessed_out                      false
% 2.40/0.99  --preprocessed_stats                    false
% 2.40/0.99  
% 2.40/0.99  ------ Abstraction refinement Options
% 2.40/0.99  
% 2.40/0.99  --abstr_ref                             []
% 2.40/0.99  --abstr_ref_prep                        false
% 2.40/0.99  --abstr_ref_until_sat                   false
% 2.40/0.99  --abstr_ref_sig_restrict                funpre
% 2.40/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 2.40/0.99  --abstr_ref_under                       []
% 2.40/0.99  
% 2.40/0.99  ------ SAT Options
% 2.40/0.99  
% 2.40/0.99  --sat_mode                              false
% 2.40/0.99  --sat_fm_restart_options                ""
% 2.40/0.99  --sat_gr_def                            false
% 2.40/0.99  --sat_epr_types                         true
% 2.40/0.99  --sat_non_cyclic_types                  false
% 2.40/0.99  --sat_finite_models                     false
% 2.40/0.99  --sat_fm_lemmas                         false
% 2.40/0.99  --sat_fm_prep                           false
% 2.40/0.99  --sat_fm_uc_incr                        true
% 2.40/0.99  --sat_out_model                         small
% 2.40/0.99  --sat_out_clauses                       false
% 2.40/0.99  
% 2.40/0.99  ------ QBF Options
% 2.40/0.99  
% 2.40/0.99  --qbf_mode                              false
% 2.40/0.99  --qbf_elim_univ                         false
% 2.40/0.99  --qbf_dom_inst                          none
% 2.40/0.99  --qbf_dom_pre_inst                      false
% 2.40/0.99  --qbf_sk_in                             false
% 2.40/0.99  --qbf_pred_elim                         true
% 2.40/0.99  --qbf_split                             512
% 2.40/0.99  
% 2.40/0.99  ------ BMC1 Options
% 2.40/0.99  
% 2.40/0.99  --bmc1_incremental                      false
% 2.40/0.99  --bmc1_axioms                           reachable_all
% 2.40/0.99  --bmc1_min_bound                        0
% 2.40/0.99  --bmc1_max_bound                        -1
% 2.40/0.99  --bmc1_max_bound_default                -1
% 2.40/0.99  --bmc1_symbol_reachability              true
% 2.40/0.99  --bmc1_property_lemmas                  false
% 2.40/0.99  --bmc1_k_induction                      false
% 2.40/0.99  --bmc1_non_equiv_states                 false
% 2.40/0.99  --bmc1_deadlock                         false
% 2.40/0.99  --bmc1_ucm                              false
% 2.40/0.99  --bmc1_add_unsat_core                   none
% 2.40/0.99  --bmc1_unsat_core_children              false
% 2.40/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 2.40/0.99  --bmc1_out_stat                         full
% 2.40/0.99  --bmc1_ground_init                      false
% 2.40/0.99  --bmc1_pre_inst_next_state              false
% 2.40/0.99  --bmc1_pre_inst_state                   false
% 2.40/0.99  --bmc1_pre_inst_reach_state             false
% 2.40/0.99  --bmc1_out_unsat_core                   false
% 2.40/0.99  --bmc1_aig_witness_out                  false
% 2.40/0.99  --bmc1_verbose                          false
% 2.40/0.99  --bmc1_dump_clauses_tptp                false
% 2.40/0.99  --bmc1_dump_unsat_core_tptp             false
% 2.40/0.99  --bmc1_dump_file                        -
% 2.40/0.99  --bmc1_ucm_expand_uc_limit              128
% 2.40/0.99  --bmc1_ucm_n_expand_iterations          6
% 2.40/0.99  --bmc1_ucm_extend_mode                  1
% 2.40/0.99  --bmc1_ucm_init_mode                    2
% 2.40/0.99  --bmc1_ucm_cone_mode                    none
% 2.40/0.99  --bmc1_ucm_reduced_relation_type        0
% 2.40/0.99  --bmc1_ucm_relax_model                  4
% 2.40/0.99  --bmc1_ucm_full_tr_after_sat            true
% 2.40/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 2.40/0.99  --bmc1_ucm_layered_model                none
% 2.40/0.99  --bmc1_ucm_max_lemma_size               10
% 2.40/0.99  
% 2.40/0.99  ------ AIG Options
% 2.40/0.99  
% 2.40/0.99  --aig_mode                              false
% 2.40/0.99  
% 2.40/0.99  ------ Instantiation Options
% 2.40/0.99  
% 2.40/0.99  --instantiation_flag                    true
% 2.40/0.99  --inst_sos_flag                         false
% 2.40/0.99  --inst_sos_phase                        true
% 2.40/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.40/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.40/0.99  --inst_lit_sel_side                     num_symb
% 2.40/0.99  --inst_solver_per_active                1400
% 2.40/0.99  --inst_solver_calls_frac                1.
% 2.40/0.99  --inst_passive_queue_type               priority_queues
% 2.40/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.40/0.99  --inst_passive_queues_freq              [25;2]
% 2.40/0.99  --inst_dismatching                      true
% 2.40/0.99  --inst_eager_unprocessed_to_passive     true
% 2.40/0.99  --inst_prop_sim_given                   true
% 2.40/0.99  --inst_prop_sim_new                     false
% 2.40/0.99  --inst_subs_new                         false
% 2.40/0.99  --inst_eq_res_simp                      false
% 2.40/0.99  --inst_subs_given                       false
% 2.40/0.99  --inst_orphan_elimination               true
% 2.40/0.99  --inst_learning_loop_flag               true
% 2.40/0.99  --inst_learning_start                   3000
% 2.40/0.99  --inst_learning_factor                  2
% 2.40/0.99  --inst_start_prop_sim_after_learn       3
% 2.40/0.99  --inst_sel_renew                        solver
% 2.40/0.99  --inst_lit_activity_flag                true
% 2.40/0.99  --inst_restr_to_given                   false
% 2.40/0.99  --inst_activity_threshold               500
% 2.40/0.99  --inst_out_proof                        true
% 2.40/0.99  
% 2.40/0.99  ------ Resolution Options
% 2.40/0.99  
% 2.40/0.99  --resolution_flag                       true
% 2.40/0.99  --res_lit_sel                           adaptive
% 2.40/0.99  --res_lit_sel_side                      none
% 2.40/0.99  --res_ordering                          kbo
% 2.40/0.99  --res_to_prop_solver                    active
% 2.40/0.99  --res_prop_simpl_new                    false
% 2.40/0.99  --res_prop_simpl_given                  true
% 2.40/0.99  --res_passive_queue_type                priority_queues
% 2.40/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.40/0.99  --res_passive_queues_freq               [15;5]
% 2.40/0.99  --res_forward_subs                      full
% 2.40/0.99  --res_backward_subs                     full
% 2.40/0.99  --res_forward_subs_resolution           true
% 2.40/0.99  --res_backward_subs_resolution          true
% 2.40/0.99  --res_orphan_elimination                true
% 2.40/0.99  --res_time_limit                        2.
% 2.40/0.99  --res_out_proof                         true
% 2.40/0.99  
% 2.40/0.99  ------ Superposition Options
% 2.40/0.99  
% 2.40/0.99  --superposition_flag                    true
% 2.40/0.99  --sup_passive_queue_type                priority_queues
% 2.40/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.40/0.99  --sup_passive_queues_freq               [8;1;4]
% 2.40/0.99  --demod_completeness_check              fast
% 2.40/0.99  --demod_use_ground                      true
% 2.40/0.99  --sup_to_prop_solver                    passive
% 2.40/0.99  --sup_prop_simpl_new                    true
% 2.40/0.99  --sup_prop_simpl_given                  true
% 2.40/0.99  --sup_fun_splitting                     false
% 2.40/0.99  --sup_smt_interval                      50000
% 2.40/0.99  
% 2.40/0.99  ------ Superposition Simplification Setup
% 2.40/0.99  
% 2.40/0.99  --sup_indices_passive                   []
% 2.40/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.40/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.40/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.40/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 2.40/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.40/0.99  --sup_full_bw                           [BwDemod]
% 2.40/0.99  --sup_immed_triv                        [TrivRules]
% 2.40/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.40/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.40/0.99  --sup_immed_bw_main                     []
% 2.40/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.40/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 2.40/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.40/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.40/0.99  
% 2.40/0.99  ------ Combination Options
% 2.40/0.99  
% 2.40/0.99  --comb_res_mult                         3
% 2.40/0.99  --comb_sup_mult                         2
% 2.40/0.99  --comb_inst_mult                        10
% 2.40/0.99  
% 2.40/0.99  ------ Debug Options
% 2.40/0.99  
% 2.40/0.99  --dbg_backtrace                         false
% 2.40/0.99  --dbg_dump_prop_clauses                 false
% 2.40/0.99  --dbg_dump_prop_clauses_file            -
% 2.40/0.99  --dbg_out_stat                          false
% 2.40/0.99  ------ Parsing...
% 2.40/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.40/0.99  
% 2.40/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 2.40/0.99  
% 2.40/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.40/0.99  
% 2.40/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.40/0.99  ------ Proving...
% 2.40/0.99  ------ Problem Properties 
% 2.40/0.99  
% 2.40/0.99  
% 2.40/0.99  clauses                                 28
% 2.40/0.99  conjectures                             2
% 2.40/0.99  EPR                                     7
% 2.40/0.99  Horn                                    22
% 2.40/0.99  unary                                   6
% 2.40/0.99  binary                                  11
% 2.40/0.99  lits                                    66
% 2.40/0.99  lits eq                                 17
% 2.40/0.99  fd_pure                                 0
% 2.40/0.99  fd_pseudo                               0
% 2.40/0.99  fd_cond                                 0
% 2.40/0.99  fd_pseudo_cond                          8
% 2.40/0.99  AC symbols                              0
% 2.40/0.99  
% 2.40/0.99  ------ Schedule dynamic 5 is on 
% 2.40/0.99  
% 2.40/0.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.40/0.99  
% 2.40/0.99  
% 2.40/0.99  ------ 
% 2.40/0.99  Current options:
% 2.40/0.99  ------ 
% 2.40/0.99  
% 2.40/0.99  ------ Input Options
% 2.40/0.99  
% 2.40/0.99  --out_options                           all
% 2.40/0.99  --tptp_safe_out                         true
% 2.40/0.99  --problem_path                          ""
% 2.40/0.99  --include_path                          ""
% 2.40/0.99  --clausifier                            res/vclausify_rel
% 2.40/0.99  --clausifier_options                    --mode clausify
% 2.40/0.99  --stdin                                 false
% 2.40/0.99  --stats_out                             all
% 2.40/0.99  
% 2.40/0.99  ------ General Options
% 2.40/0.99  
% 2.40/0.99  --fof                                   false
% 2.40/0.99  --time_out_real                         305.
% 2.40/0.99  --time_out_virtual                      -1.
% 2.40/0.99  --symbol_type_check                     false
% 2.40/0.99  --clausify_out                          false
% 2.40/0.99  --sig_cnt_out                           false
% 2.40/0.99  --trig_cnt_out                          false
% 2.40/0.99  --trig_cnt_out_tolerance                1.
% 2.40/0.99  --trig_cnt_out_sk_spl                   false
% 2.40/0.99  --abstr_cl_out                          false
% 2.40/0.99  
% 2.40/0.99  ------ Global Options
% 2.40/0.99  
% 2.40/0.99  --schedule                              default
% 2.40/0.99  --add_important_lit                     false
% 2.40/0.99  --prop_solver_per_cl                    1000
% 2.40/0.99  --min_unsat_core                        false
% 2.40/0.99  --soft_assumptions                      false
% 2.40/0.99  --soft_lemma_size                       3
% 2.40/0.99  --prop_impl_unit_size                   0
% 2.40/0.99  --prop_impl_unit                        []
% 2.40/0.99  --share_sel_clauses                     true
% 2.40/0.99  --reset_solvers                         false
% 2.40/0.99  --bc_imp_inh                            [conj_cone]
% 2.40/0.99  --conj_cone_tolerance                   3.
% 2.40/0.99  --extra_neg_conj                        none
% 2.40/0.99  --large_theory_mode                     true
% 2.40/0.99  --prolific_symb_bound                   200
% 2.40/0.99  --lt_threshold                          2000
% 2.40/0.99  --clause_weak_htbl                      true
% 2.40/0.99  --gc_record_bc_elim                     false
% 2.40/0.99  
% 2.40/0.99  ------ Preprocessing Options
% 2.40/0.99  
% 2.40/0.99  --preprocessing_flag                    true
% 2.40/0.99  --time_out_prep_mult                    0.1
% 2.40/0.99  --splitting_mode                        input
% 2.40/0.99  --splitting_grd                         true
% 2.40/0.99  --splitting_cvd                         false
% 2.40/0.99  --splitting_cvd_svl                     false
% 2.40/0.99  --splitting_nvd                         32
% 2.40/0.99  --sub_typing                            true
% 2.40/0.99  --prep_gs_sim                           true
% 2.40/0.99  --prep_unflatten                        true
% 2.40/0.99  --prep_res_sim                          true
% 2.40/0.99  --prep_upred                            true
% 2.40/0.99  --prep_sem_filter                       exhaustive
% 2.40/0.99  --prep_sem_filter_out                   false
% 2.40/0.99  --pred_elim                             true
% 2.40/0.99  --res_sim_input                         true
% 2.40/0.99  --eq_ax_congr_red                       true
% 2.40/0.99  --pure_diseq_elim                       true
% 2.40/0.99  --brand_transform                       false
% 2.40/0.99  --non_eq_to_eq                          false
% 2.40/0.99  --prep_def_merge                        true
% 2.40/0.99  --prep_def_merge_prop_impl              false
% 2.40/0.99  --prep_def_merge_mbd                    true
% 2.40/0.99  --prep_def_merge_tr_red                 false
% 2.40/0.99  --prep_def_merge_tr_cl                  false
% 2.40/0.99  --smt_preprocessing                     true
% 2.40/0.99  --smt_ac_axioms                         fast
% 2.40/0.99  --preprocessed_out                      false
% 2.40/0.99  --preprocessed_stats                    false
% 2.40/0.99  
% 2.40/0.99  ------ Abstraction refinement Options
% 2.40/0.99  
% 2.40/0.99  --abstr_ref                             []
% 2.40/0.99  --abstr_ref_prep                        false
% 2.40/0.99  --abstr_ref_until_sat                   false
% 2.40/0.99  --abstr_ref_sig_restrict                funpre
% 2.40/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 2.40/0.99  --abstr_ref_under                       []
% 2.40/0.99  
% 2.40/0.99  ------ SAT Options
% 2.40/0.99  
% 2.40/0.99  --sat_mode                              false
% 2.40/0.99  --sat_fm_restart_options                ""
% 2.40/0.99  --sat_gr_def                            false
% 2.40/0.99  --sat_epr_types                         true
% 2.40/0.99  --sat_non_cyclic_types                  false
% 2.40/0.99  --sat_finite_models                     false
% 2.40/0.99  --sat_fm_lemmas                         false
% 2.40/0.99  --sat_fm_prep                           false
% 2.40/0.99  --sat_fm_uc_incr                        true
% 2.40/0.99  --sat_out_model                         small
% 2.40/0.99  --sat_out_clauses                       false
% 2.40/0.99  
% 2.40/0.99  ------ QBF Options
% 2.40/0.99  
% 2.40/0.99  --qbf_mode                              false
% 2.40/0.99  --qbf_elim_univ                         false
% 2.40/0.99  --qbf_dom_inst                          none
% 2.40/0.99  --qbf_dom_pre_inst                      false
% 2.40/0.99  --qbf_sk_in                             false
% 2.40/0.99  --qbf_pred_elim                         true
% 2.40/0.99  --qbf_split                             512
% 2.40/0.99  
% 2.40/0.99  ------ BMC1 Options
% 2.40/0.99  
% 2.40/0.99  --bmc1_incremental                      false
% 2.40/0.99  --bmc1_axioms                           reachable_all
% 2.40/0.99  --bmc1_min_bound                        0
% 2.40/0.99  --bmc1_max_bound                        -1
% 2.40/0.99  --bmc1_max_bound_default                -1
% 2.40/0.99  --bmc1_symbol_reachability              true
% 2.40/0.99  --bmc1_property_lemmas                  false
% 2.40/0.99  --bmc1_k_induction                      false
% 2.40/0.99  --bmc1_non_equiv_states                 false
% 2.40/0.99  --bmc1_deadlock                         false
% 2.40/0.99  --bmc1_ucm                              false
% 2.40/0.99  --bmc1_add_unsat_core                   none
% 2.40/0.99  --bmc1_unsat_core_children              false
% 2.40/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 2.40/0.99  --bmc1_out_stat                         full
% 2.40/0.99  --bmc1_ground_init                      false
% 2.40/0.99  --bmc1_pre_inst_next_state              false
% 2.40/0.99  --bmc1_pre_inst_state                   false
% 2.40/0.99  --bmc1_pre_inst_reach_state             false
% 2.40/0.99  --bmc1_out_unsat_core                   false
% 2.40/0.99  --bmc1_aig_witness_out                  false
% 2.40/0.99  --bmc1_verbose                          false
% 2.40/0.99  --bmc1_dump_clauses_tptp                false
% 2.40/0.99  --bmc1_dump_unsat_core_tptp             false
% 2.40/0.99  --bmc1_dump_file                        -
% 2.40/0.99  --bmc1_ucm_expand_uc_limit              128
% 2.40/0.99  --bmc1_ucm_n_expand_iterations          6
% 2.40/0.99  --bmc1_ucm_extend_mode                  1
% 2.40/0.99  --bmc1_ucm_init_mode                    2
% 2.40/0.99  --bmc1_ucm_cone_mode                    none
% 2.40/0.99  --bmc1_ucm_reduced_relation_type        0
% 2.40/0.99  --bmc1_ucm_relax_model                  4
% 2.40/0.99  --bmc1_ucm_full_tr_after_sat            true
% 2.40/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 2.40/0.99  --bmc1_ucm_layered_model                none
% 2.40/0.99  --bmc1_ucm_max_lemma_size               10
% 2.40/0.99  
% 2.40/0.99  ------ AIG Options
% 2.40/0.99  
% 2.40/0.99  --aig_mode                              false
% 2.40/0.99  
% 2.40/0.99  ------ Instantiation Options
% 2.40/0.99  
% 2.40/0.99  --instantiation_flag                    true
% 2.40/0.99  --inst_sos_flag                         false
% 2.40/0.99  --inst_sos_phase                        true
% 2.40/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.40/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.40/0.99  --inst_lit_sel_side                     none
% 2.40/0.99  --inst_solver_per_active                1400
% 2.40/0.99  --inst_solver_calls_frac                1.
% 2.40/0.99  --inst_passive_queue_type               priority_queues
% 2.40/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.40/0.99  --inst_passive_queues_freq              [25;2]
% 2.40/0.99  --inst_dismatching                      true
% 2.40/0.99  --inst_eager_unprocessed_to_passive     true
% 2.40/0.99  --inst_prop_sim_given                   true
% 2.40/0.99  --inst_prop_sim_new                     false
% 2.40/0.99  --inst_subs_new                         false
% 2.40/0.99  --inst_eq_res_simp                      false
% 2.40/0.99  --inst_subs_given                       false
% 2.40/0.99  --inst_orphan_elimination               true
% 2.40/0.99  --inst_learning_loop_flag               true
% 2.40/0.99  --inst_learning_start                   3000
% 2.40/0.99  --inst_learning_factor                  2
% 2.40/0.99  --inst_start_prop_sim_after_learn       3
% 2.40/0.99  --inst_sel_renew                        solver
% 2.40/0.99  --inst_lit_activity_flag                true
% 2.40/0.99  --inst_restr_to_given                   false
% 2.40/0.99  --inst_activity_threshold               500
% 2.40/0.99  --inst_out_proof                        true
% 2.40/0.99  
% 2.40/0.99  ------ Resolution Options
% 2.40/0.99  
% 2.40/0.99  --resolution_flag                       false
% 2.40/0.99  --res_lit_sel                           adaptive
% 2.40/0.99  --res_lit_sel_side                      none
% 2.40/0.99  --res_ordering                          kbo
% 2.40/0.99  --res_to_prop_solver                    active
% 2.40/0.99  --res_prop_simpl_new                    false
% 2.40/0.99  --res_prop_simpl_given                  true
% 2.40/0.99  --res_passive_queue_type                priority_queues
% 2.40/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.40/0.99  --res_passive_queues_freq               [15;5]
% 2.40/0.99  --res_forward_subs                      full
% 2.40/0.99  --res_backward_subs                     full
% 2.40/0.99  --res_forward_subs_resolution           true
% 2.40/0.99  --res_backward_subs_resolution          true
% 2.40/0.99  --res_orphan_elimination                true
% 2.40/0.99  --res_time_limit                        2.
% 2.40/0.99  --res_out_proof                         true
% 2.40/0.99  
% 2.40/0.99  ------ Superposition Options
% 2.40/0.99  
% 2.40/0.99  --superposition_flag                    true
% 2.40/0.99  --sup_passive_queue_type                priority_queues
% 2.40/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.40/0.99  --sup_passive_queues_freq               [8;1;4]
% 2.40/0.99  --demod_completeness_check              fast
% 2.40/0.99  --demod_use_ground                      true
% 2.40/0.99  --sup_to_prop_solver                    passive
% 2.40/0.99  --sup_prop_simpl_new                    true
% 2.40/0.99  --sup_prop_simpl_given                  true
% 2.40/0.99  --sup_fun_splitting                     false
% 2.40/0.99  --sup_smt_interval                      50000
% 2.40/0.99  
% 2.40/0.99  ------ Superposition Simplification Setup
% 2.40/0.99  
% 2.40/0.99  --sup_indices_passive                   []
% 2.40/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.40/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.40/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.40/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 2.40/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.40/0.99  --sup_full_bw                           [BwDemod]
% 2.40/0.99  --sup_immed_triv                        [TrivRules]
% 2.40/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.40/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.40/0.99  --sup_immed_bw_main                     []
% 2.40/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.40/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 2.40/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.40/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.40/0.99  
% 2.40/0.99  ------ Combination Options
% 2.40/0.99  
% 2.40/0.99  --comb_res_mult                         3
% 2.40/0.99  --comb_sup_mult                         2
% 2.40/0.99  --comb_inst_mult                        10
% 2.40/0.99  
% 2.40/0.99  ------ Debug Options
% 2.40/0.99  
% 2.40/0.99  --dbg_backtrace                         false
% 2.40/0.99  --dbg_dump_prop_clauses                 false
% 2.40/0.99  --dbg_dump_prop_clauses_file            -
% 2.40/0.99  --dbg_out_stat                          false
% 2.40/0.99  
% 2.40/0.99  
% 2.40/0.99  
% 2.40/0.99  
% 2.40/0.99  ------ Proving...
% 2.40/0.99  
% 2.40/0.99  
% 2.40/0.99  % SZS status Theorem for theBenchmark.p
% 2.40/0.99  
% 2.40/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 2.40/0.99  
% 2.40/0.99  fof(f3,axiom,(
% 2.40/0.99    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 2.40/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.40/0.99  
% 2.40/0.99  fof(f32,plain,(
% 2.40/0.99    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.40/0.99    inference(nnf_transformation,[],[f3])).
% 2.40/0.99  
% 2.40/0.99  fof(f33,plain,(
% 2.40/0.99    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.40/0.99    inference(flattening,[],[f32])).
% 2.40/0.99  
% 2.40/0.99  fof(f55,plain,(
% 2.40/0.99    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 2.40/0.99    inference(cnf_transformation,[],[f33])).
% 2.40/0.99  
% 2.40/0.99  fof(f12,axiom,(
% 2.40/0.99    ! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => (r2_hidden(X1,X0) | r1_ordinal1(X0,X1))))),
% 2.40/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.40/0.99  
% 2.40/0.99  fof(f22,plain,(
% 2.40/0.99    ! [X0] : (! [X1] : ((r2_hidden(X1,X0) | r1_ordinal1(X0,X1)) | ~v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 2.40/0.99    inference(ennf_transformation,[],[f12])).
% 2.40/0.99  
% 2.40/0.99  fof(f23,plain,(
% 2.40/0.99    ! [X0] : (! [X1] : (r2_hidden(X1,X0) | r1_ordinal1(X0,X1) | ~v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 2.40/0.99    inference(flattening,[],[f22])).
% 2.40/0.99  
% 2.40/0.99  fof(f73,plain,(
% 2.40/0.99    ( ! [X0,X1] : (r2_hidden(X1,X0) | r1_ordinal1(X0,X1) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0)) )),
% 2.40/0.99    inference(cnf_transformation,[],[f23])).
% 2.40/0.99  
% 2.40/0.99  fof(f15,conjecture,(
% 2.40/0.99    ! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => (r2_hidden(X0,X1) <=> r1_ordinal1(k1_ordinal1(X0),X1))))),
% 2.40/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.40/0.99  
% 2.40/0.99  fof(f16,negated_conjecture,(
% 2.40/0.99    ~! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => (r2_hidden(X0,X1) <=> r1_ordinal1(k1_ordinal1(X0),X1))))),
% 2.40/0.99    inference(negated_conjecture,[],[f15])).
% 2.40/0.99  
% 2.40/0.99  fof(f26,plain,(
% 2.40/0.99    ? [X0] : (? [X1] : ((r2_hidden(X0,X1) <~> r1_ordinal1(k1_ordinal1(X0),X1)) & v3_ordinal1(X1)) & v3_ordinal1(X0))),
% 2.40/0.99    inference(ennf_transformation,[],[f16])).
% 2.40/0.99  
% 2.40/0.99  fof(f41,plain,(
% 2.40/0.99    ? [X0] : (? [X1] : (((~r1_ordinal1(k1_ordinal1(X0),X1) | ~r2_hidden(X0,X1)) & (r1_ordinal1(k1_ordinal1(X0),X1) | r2_hidden(X0,X1))) & v3_ordinal1(X1)) & v3_ordinal1(X0))),
% 2.40/0.99    inference(nnf_transformation,[],[f26])).
% 2.40/0.99  
% 2.40/0.99  fof(f42,plain,(
% 2.40/0.99    ? [X0] : (? [X1] : ((~r1_ordinal1(k1_ordinal1(X0),X1) | ~r2_hidden(X0,X1)) & (r1_ordinal1(k1_ordinal1(X0),X1) | r2_hidden(X0,X1)) & v3_ordinal1(X1)) & v3_ordinal1(X0))),
% 2.40/0.99    inference(flattening,[],[f41])).
% 2.40/0.99  
% 2.40/0.99  fof(f44,plain,(
% 2.40/0.99    ( ! [X0] : (? [X1] : ((~r1_ordinal1(k1_ordinal1(X0),X1) | ~r2_hidden(X0,X1)) & (r1_ordinal1(k1_ordinal1(X0),X1) | r2_hidden(X0,X1)) & v3_ordinal1(X1)) => ((~r1_ordinal1(k1_ordinal1(X0),sK3) | ~r2_hidden(X0,sK3)) & (r1_ordinal1(k1_ordinal1(X0),sK3) | r2_hidden(X0,sK3)) & v3_ordinal1(sK3))) )),
% 2.40/0.99    introduced(choice_axiom,[])).
% 2.40/0.99  
% 2.40/0.99  fof(f43,plain,(
% 2.40/0.99    ? [X0] : (? [X1] : ((~r1_ordinal1(k1_ordinal1(X0),X1) | ~r2_hidden(X0,X1)) & (r1_ordinal1(k1_ordinal1(X0),X1) | r2_hidden(X0,X1)) & v3_ordinal1(X1)) & v3_ordinal1(X0)) => (? [X1] : ((~r1_ordinal1(k1_ordinal1(sK2),X1) | ~r2_hidden(sK2,X1)) & (r1_ordinal1(k1_ordinal1(sK2),X1) | r2_hidden(sK2,X1)) & v3_ordinal1(X1)) & v3_ordinal1(sK2))),
% 2.40/0.99    introduced(choice_axiom,[])).
% 2.40/0.99  
% 2.40/0.99  fof(f45,plain,(
% 2.40/0.99    ((~r1_ordinal1(k1_ordinal1(sK2),sK3) | ~r2_hidden(sK2,sK3)) & (r1_ordinal1(k1_ordinal1(sK2),sK3) | r2_hidden(sK2,sK3)) & v3_ordinal1(sK3)) & v3_ordinal1(sK2)),
% 2.40/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f42,f44,f43])).
% 2.40/0.99  
% 2.40/0.99  fof(f79,plain,(
% 2.40/0.99    ~r1_ordinal1(k1_ordinal1(sK2),sK3) | ~r2_hidden(sK2,sK3)),
% 2.40/0.99    inference(cnf_transformation,[],[f45])).
% 2.40/0.99  
% 2.40/0.99  fof(f10,axiom,(
% 2.40/0.99    ! [X0] : k2_xboole_0(X0,k1_tarski(X0)) = k1_ordinal1(X0)),
% 2.40/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.40/0.99  
% 2.40/0.99  fof(f70,plain,(
% 2.40/0.99    ( ! [X0] : (k2_xboole_0(X0,k1_tarski(X0)) = k1_ordinal1(X0)) )),
% 2.40/0.99    inference(cnf_transformation,[],[f10])).
% 2.40/0.99  
% 2.40/0.99  fof(f9,axiom,(
% 2.40/0.99    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 2.40/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.40/0.99  
% 2.40/0.99  fof(f69,plain,(
% 2.40/0.99    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 2.40/0.99    inference(cnf_transformation,[],[f9])).
% 2.40/0.99  
% 2.40/0.99  fof(f80,plain,(
% 2.40/0.99    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k1_enumset1(X0,X0,X1))) )),
% 2.40/0.99    inference(definition_unfolding,[],[f69,f66])).
% 2.40/0.99  
% 2.40/0.99  fof(f6,axiom,(
% 2.40/0.99    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 2.40/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.40/0.99  
% 2.40/0.99  fof(f65,plain,(
% 2.40/0.99    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 2.40/0.99    inference(cnf_transformation,[],[f6])).
% 2.40/0.99  
% 2.40/0.99  fof(f7,axiom,(
% 2.40/0.99    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 2.40/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.40/0.99  
% 2.40/0.99  fof(f66,plain,(
% 2.40/0.99    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 2.40/0.99    inference(cnf_transformation,[],[f7])).
% 2.40/0.99  
% 2.40/0.99  fof(f81,plain,(
% 2.40/0.99    ( ! [X0] : (k1_enumset1(X0,X0,X0) = k1_tarski(X0)) )),
% 2.40/0.99    inference(definition_unfolding,[],[f65,f66])).
% 2.40/0.99  
% 2.40/0.99  fof(f82,plain,(
% 2.40/0.99    ( ! [X0] : (k3_tarski(k1_enumset1(X0,X0,k1_enumset1(X0,X0,X0))) = k1_ordinal1(X0)) )),
% 2.40/0.99    inference(definition_unfolding,[],[f70,f80,f81])).
% 2.40/0.99  
% 2.40/0.99  fof(f93,plain,(
% 2.40/0.99    ~r1_ordinal1(k3_tarski(k1_enumset1(sK2,sK2,k1_enumset1(sK2,sK2,sK2))),sK3) | ~r2_hidden(sK2,sK3)),
% 2.40/0.99    inference(definition_unfolding,[],[f79,f82])).
% 2.40/0.99  
% 2.40/0.99  fof(f76,plain,(
% 2.40/0.99    v3_ordinal1(sK2)),
% 2.40/0.99    inference(cnf_transformation,[],[f45])).
% 2.40/0.99  
% 2.40/0.99  fof(f77,plain,(
% 2.40/0.99    v3_ordinal1(sK3)),
% 2.40/0.99    inference(cnf_transformation,[],[f45])).
% 2.40/0.99  
% 2.40/0.99  fof(f13,axiom,(
% 2.40/0.99    ! [X0] : (v3_ordinal1(X0) => v3_ordinal1(k1_ordinal1(X0)))),
% 2.40/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.40/0.99  
% 2.40/0.99  fof(f24,plain,(
% 2.40/0.99    ! [X0] : (v3_ordinal1(k1_ordinal1(X0)) | ~v3_ordinal1(X0))),
% 2.40/0.99    inference(ennf_transformation,[],[f13])).
% 2.40/0.99  
% 2.40/0.99  fof(f74,plain,(
% 2.40/0.99    ( ! [X0] : (v3_ordinal1(k1_ordinal1(X0)) | ~v3_ordinal1(X0)) )),
% 2.40/0.99    inference(cnf_transformation,[],[f24])).
% 2.40/0.99  
% 2.40/0.99  fof(f92,plain,(
% 2.40/0.99    ( ! [X0] : (v3_ordinal1(k3_tarski(k1_enumset1(X0,X0,k1_enumset1(X0,X0,X0)))) | ~v3_ordinal1(X0)) )),
% 2.40/0.99    inference(definition_unfolding,[],[f74,f82])).
% 2.40/0.99  
% 2.40/0.99  fof(f1,axiom,(
% 2.40/0.99    ! [X0,X1] : (r2_hidden(X0,X1) => ~r2_hidden(X1,X0))),
% 2.40/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.40/0.99  
% 2.40/0.99  fof(f17,plain,(
% 2.40/0.99    ! [X0,X1] : (~r2_hidden(X1,X0) | ~r2_hidden(X0,X1))),
% 2.40/0.99    inference(ennf_transformation,[],[f1])).
% 2.40/0.99  
% 2.40/0.99  fof(f46,plain,(
% 2.40/0.99    ( ! [X0,X1] : (~r2_hidden(X1,X0) | ~r2_hidden(X0,X1)) )),
% 2.40/0.99    inference(cnf_transformation,[],[f17])).
% 2.40/0.99  
% 2.40/0.99  fof(f8,axiom,(
% 2.40/0.99    ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) <=> r2_hidden(X0,X1))),
% 2.40/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.40/0.99  
% 2.40/0.99  fof(f39,plain,(
% 2.40/0.99    ! [X0,X1] : ((r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) & (r2_hidden(X0,X1) | ~r1_tarski(k1_tarski(X0),X1)))),
% 2.40/0.99    inference(nnf_transformation,[],[f8])).
% 2.40/0.99  
% 2.40/0.99  fof(f68,plain,(
% 2.40/0.99    ( ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) )),
% 2.40/0.99    inference(cnf_transformation,[],[f39])).
% 2.40/0.99  
% 2.40/0.99  fof(f90,plain,(
% 2.40/0.99    ( ! [X0,X1] : (r1_tarski(k1_enumset1(X0,X0,X0),X1) | ~r2_hidden(X0,X1)) )),
% 2.40/0.99    inference(definition_unfolding,[],[f68,f81])).
% 2.40/0.99  
% 2.40/0.99  fof(f2,axiom,(
% 2.40/0.99    ! [X0,X1,X2] : (k2_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) | r2_hidden(X3,X0))))),
% 2.40/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.40/0.99  
% 2.40/0.99  fof(f27,plain,(
% 2.40/0.99    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) | r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) & ~r2_hidden(X3,X0))) & ((r2_hidden(X3,X1) | r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k2_xboole_0(X0,X1) != X2))),
% 2.40/0.99    inference(nnf_transformation,[],[f2])).
% 2.40/0.99  
% 2.40/0.99  fof(f28,plain,(
% 2.40/0.99    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) & ~r2_hidden(X3,X0))) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | ~r2_hidden(X3,X2))) | k2_xboole_0(X0,X1) != X2))),
% 2.40/0.99    inference(flattening,[],[f27])).
% 2.40/0.99  
% 2.40/0.99  fof(f29,plain,(
% 2.40/0.99    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (~r2_hidden(X4,X1) & ~r2_hidden(X4,X0))) & (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,X2))) | k2_xboole_0(X0,X1) != X2))),
% 2.40/0.99    inference(rectify,[],[f28])).
% 2.40/0.99  
% 2.40/0.99  fof(f30,plain,(
% 2.40/0.99    ! [X2,X1,X0] : (? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2))) => (((~r2_hidden(sK0(X0,X1,X2),X1) & ~r2_hidden(sK0(X0,X1,X2),X0)) | ~r2_hidden(sK0(X0,X1,X2),X2)) & (r2_hidden(sK0(X0,X1,X2),X1) | r2_hidden(sK0(X0,X1,X2),X0) | r2_hidden(sK0(X0,X1,X2),X2))))),
% 2.40/0.99    introduced(choice_axiom,[])).
% 2.40/0.99  
% 2.40/0.99  fof(f31,plain,(
% 2.40/0.99    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | (((~r2_hidden(sK0(X0,X1,X2),X1) & ~r2_hidden(sK0(X0,X1,X2),X0)) | ~r2_hidden(sK0(X0,X1,X2),X2)) & (r2_hidden(sK0(X0,X1,X2),X1) | r2_hidden(sK0(X0,X1,X2),X0) | r2_hidden(sK0(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (~r2_hidden(X4,X1) & ~r2_hidden(X4,X0))) & (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,X2))) | k2_xboole_0(X0,X1) != X2))),
% 2.40/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f29,f30])).
% 2.40/0.99  
% 2.40/0.99  fof(f47,plain,(
% 2.40/0.99    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,X2) | k2_xboole_0(X0,X1) != X2) )),
% 2.40/0.99    inference(cnf_transformation,[],[f31])).
% 2.40/0.99  
% 2.40/0.99  fof(f88,plain,(
% 2.40/0.99    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,X2) | k3_tarski(k1_enumset1(X0,X0,X1)) != X2) )),
% 2.40/0.99    inference(definition_unfolding,[],[f47,f80])).
% 2.40/0.99  
% 2.40/0.99  fof(f97,plain,(
% 2.40/0.99    ( ! [X4,X0,X1] : (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,k3_tarski(k1_enumset1(X0,X0,X1)))) )),
% 2.40/0.99    inference(equality_resolution,[],[f88])).
% 2.40/0.99  
% 2.40/0.99  fof(f14,axiom,(
% 2.40/0.99    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 2.40/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.40/0.99  
% 2.40/0.99  fof(f25,plain,(
% 2.40/0.99    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 2.40/0.99    inference(ennf_transformation,[],[f14])).
% 2.40/0.99  
% 2.40/0.99  fof(f75,plain,(
% 2.40/0.99    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1)) )),
% 2.40/0.99    inference(cnf_transformation,[],[f25])).
% 2.40/0.99  
% 2.40/0.99  fof(f49,plain,(
% 2.40/0.99    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | k2_xboole_0(X0,X1) != X2) )),
% 2.40/0.99    inference(cnf_transformation,[],[f31])).
% 2.40/0.99  
% 2.40/0.99  fof(f86,plain,(
% 2.40/0.99    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | k3_tarski(k1_enumset1(X0,X0,X1)) != X2) )),
% 2.40/0.99    inference(definition_unfolding,[],[f49,f80])).
% 2.40/0.99  
% 2.40/0.99  fof(f95,plain,(
% 2.40/0.99    ( ! [X4,X0,X1] : (r2_hidden(X4,k3_tarski(k1_enumset1(X0,X0,X1))) | ~r2_hidden(X4,X1)) )),
% 2.40/0.99    inference(equality_resolution,[],[f86])).
% 2.40/0.99  
% 2.40/0.99  fof(f11,axiom,(
% 2.40/0.99    ! [X0,X1] : ((v3_ordinal1(X1) & v3_ordinal1(X0)) => (r1_ordinal1(X0,X1) <=> r1_tarski(X0,X1)))),
% 2.40/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.40/0.99  
% 2.40/0.99  fof(f20,plain,(
% 2.40/0.99    ! [X0,X1] : ((r1_ordinal1(X0,X1) <=> r1_tarski(X0,X1)) | (~v3_ordinal1(X1) | ~v3_ordinal1(X0)))),
% 2.40/0.99    inference(ennf_transformation,[],[f11])).
% 2.40/0.99  
% 2.40/0.99  fof(f21,plain,(
% 2.40/0.99    ! [X0,X1] : ((r1_ordinal1(X0,X1) <=> r1_tarski(X0,X1)) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0))),
% 2.40/0.99    inference(flattening,[],[f20])).
% 2.40/0.99  
% 2.40/0.99  fof(f40,plain,(
% 2.40/0.99    ! [X0,X1] : (((r1_ordinal1(X0,X1) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~r1_ordinal1(X0,X1))) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0))),
% 2.40/0.99    inference(nnf_transformation,[],[f21])).
% 2.40/0.99  
% 2.40/0.99  fof(f71,plain,(
% 2.40/0.99    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r1_ordinal1(X0,X1) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0)) )),
% 2.40/0.99    inference(cnf_transformation,[],[f40])).
% 2.40/0.99  
% 2.40/0.99  fof(f78,plain,(
% 2.40/0.99    r1_ordinal1(k1_ordinal1(sK2),sK3) | r2_hidden(sK2,sK3)),
% 2.40/0.99    inference(cnf_transformation,[],[f45])).
% 2.40/0.99  
% 2.40/0.99  fof(f94,plain,(
% 2.40/0.99    r1_ordinal1(k3_tarski(k1_enumset1(sK2,sK2,k1_enumset1(sK2,sK2,sK2))),sK3) | r2_hidden(sK2,sK3)),
% 2.40/0.99    inference(definition_unfolding,[],[f78,f82])).
% 2.40/0.99  
% 2.40/0.99  fof(f4,axiom,(
% 2.40/0.99    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X1),X2) => r1_tarski(X0,X2))),
% 2.40/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.40/0.99  
% 2.40/0.99  fof(f18,plain,(
% 2.40/0.99    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(k2_xboole_0(X0,X1),X2))),
% 2.40/0.99    inference(ennf_transformation,[],[f4])).
% 2.40/0.99  
% 2.40/0.99  fof(f56,plain,(
% 2.40/0.99    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(k2_xboole_0(X0,X1),X2)) )),
% 2.40/0.99    inference(cnf_transformation,[],[f18])).
% 2.40/0.99  
% 2.40/0.99  fof(f89,plain,(
% 2.40/0.99    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(k3_tarski(k1_enumset1(X0,X0,X1)),X2)) )),
% 2.40/0.99    inference(definition_unfolding,[],[f56,f80])).
% 2.40/0.99  
% 2.40/0.99  fof(f53,plain,(
% 2.40/0.99    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 2.40/0.99    inference(cnf_transformation,[],[f33])).
% 2.40/0.99  
% 2.40/0.99  fof(f99,plain,(
% 2.40/0.99    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 2.40/0.99    inference(equality_resolution,[],[f53])).
% 2.40/0.99  
% 2.40/0.99  fof(f5,axiom,(
% 2.40/0.99    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> ~(X2 != X4 & X1 != X4 & X0 != X4)))),
% 2.40/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.40/0.99  
% 2.40/0.99  fof(f19,plain,(
% 2.40/0.99    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> (X2 = X4 | X1 = X4 | X0 = X4)))),
% 2.40/0.99    inference(ennf_transformation,[],[f5])).
% 2.40/0.99  
% 2.40/0.99  fof(f34,plain,(
% 2.40/0.99    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & ((X2 = X4 | X1 = X4 | X0 = X4) | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & ((X2 = X4 | X1 = X4 | X0 = X4) | ~r2_hidden(X4,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 2.40/0.99    inference(nnf_transformation,[],[f19])).
% 2.40/0.99  
% 2.40/0.99  fof(f35,plain,(
% 2.40/0.99    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & (X2 = X4 | X1 = X4 | X0 = X4 | ~r2_hidden(X4,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 2.40/0.99    inference(flattening,[],[f34])).
% 2.40/0.99  
% 2.40/0.99  fof(f36,plain,(
% 2.40/0.99    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X2 != X5 & X1 != X5 & X0 != X5)) & (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 2.40/0.99    inference(rectify,[],[f35])).
% 2.40/0.99  
% 2.40/0.99  fof(f37,plain,(
% 2.40/0.99    ! [X3,X2,X1,X0] : (? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3))) => (((sK1(X0,X1,X2,X3) != X2 & sK1(X0,X1,X2,X3) != X1 & sK1(X0,X1,X2,X3) != X0) | ~r2_hidden(sK1(X0,X1,X2,X3),X3)) & (sK1(X0,X1,X2,X3) = X2 | sK1(X0,X1,X2,X3) = X1 | sK1(X0,X1,X2,X3) = X0 | r2_hidden(sK1(X0,X1,X2,X3),X3))))),
% 2.40/0.99    introduced(choice_axiom,[])).
% 2.40/0.99  
% 2.40/0.99  fof(f38,plain,(
% 2.40/0.99    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | (((sK1(X0,X1,X2,X3) != X2 & sK1(X0,X1,X2,X3) != X1 & sK1(X0,X1,X2,X3) != X0) | ~r2_hidden(sK1(X0,X1,X2,X3),X3)) & (sK1(X0,X1,X2,X3) = X2 | sK1(X0,X1,X2,X3) = X1 | sK1(X0,X1,X2,X3) = X0 | r2_hidden(sK1(X0,X1,X2,X3),X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X2 != X5 & X1 != X5 & X0 != X5)) & (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 2.40/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f36,f37])).
% 2.40/0.99  
% 2.40/0.99  fof(f58,plain,(
% 2.40/0.99    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X0 != X5 | k1_enumset1(X0,X1,X2) != X3) )),
% 2.40/0.99    inference(cnf_transformation,[],[f38])).
% 2.40/0.99  
% 2.40/0.99  fof(f104,plain,(
% 2.40/0.99    ( ! [X2,X5,X3,X1] : (r2_hidden(X5,X3) | k1_enumset1(X5,X1,X2) != X3) )),
% 2.40/0.99    inference(equality_resolution,[],[f58])).
% 2.40/0.99  
% 2.40/0.99  fof(f105,plain,(
% 2.40/0.99    ( ! [X2,X5,X1] : (r2_hidden(X5,k1_enumset1(X5,X1,X2))) )),
% 2.40/0.99    inference(equality_resolution,[],[f104])).
% 2.40/0.99  
% 2.40/0.99  fof(f57,plain,(
% 2.40/0.99    ( ! [X2,X0,X5,X3,X1] : (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3) | k1_enumset1(X0,X1,X2) != X3) )),
% 2.40/0.99    inference(cnf_transformation,[],[f38])).
% 2.40/0.99  
% 2.40/0.99  fof(f106,plain,(
% 2.40/0.99    ( ! [X2,X0,X5,X1] : (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,k1_enumset1(X0,X1,X2))) )),
% 2.40/0.99    inference(equality_resolution,[],[f57])).
% 2.40/0.99  
% 2.40/0.99  cnf(c_7,plain,
% 2.40/0.99      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X1 = X0 ),
% 2.40/0.99      inference(cnf_transformation,[],[f55]) ).
% 2.40/0.99  
% 2.40/0.99  cnf(c_6792,plain,
% 2.40/0.99      ( ~ r1_tarski(X0,sK3) | ~ r1_tarski(sK3,X0) | sK3 = X0 ),
% 2.40/0.99      inference(instantiation,[status(thm)],[c_7]) ).
% 2.40/0.99  
% 2.40/0.99  cnf(c_6794,plain,
% 2.40/0.99      ( ~ r1_tarski(sK3,sK2) | ~ r1_tarski(sK2,sK3) | sK3 = sK2 ),
% 2.40/0.99      inference(instantiation,[status(thm)],[c_6792]) ).
% 2.40/0.99  
% 2.40/0.99  cnf(c_709,plain,
% 2.40/0.99      ( ~ r2_hidden(X0,X1) | r2_hidden(X2,X3) | X2 != X0 | X3 != X1 ),
% 2.40/0.99      theory(equality) ).
% 2.40/0.99  
% 2.40/0.99  cnf(c_1664,plain,
% 2.40/0.99      ( r2_hidden(X0,X1)
% 2.40/0.99      | ~ r2_hidden(X2,k1_enumset1(X3,X4,X2))
% 2.40/0.99      | X0 != X2
% 2.40/0.99      | X1 != k1_enumset1(X3,X4,X2) ),
% 2.40/0.99      inference(instantiation,[status(thm)],[c_709]) ).
% 2.40/0.99  
% 2.40/0.99  cnf(c_2050,plain,
% 2.40/0.99      ( ~ r2_hidden(X0,k1_enumset1(X1,X2,X0))
% 2.40/0.99      | r2_hidden(X3,k1_enumset1(X1,X2,X0))
% 2.40/0.99      | X3 != X0
% 2.40/0.99      | k1_enumset1(X1,X2,X0) != k1_enumset1(X1,X2,X0) ),
% 2.40/0.99      inference(instantiation,[status(thm)],[c_1664]) ).
% 2.40/0.99  
% 2.40/0.99  cnf(c_5561,plain,
% 2.40/0.99      ( r2_hidden(sK3,k1_enumset1(sK2,sK2,sK2))
% 2.40/0.99      | ~ r2_hidden(sK2,k1_enumset1(sK2,sK2,sK2))
% 2.40/0.99      | k1_enumset1(sK2,sK2,sK2) != k1_enumset1(sK2,sK2,sK2)
% 2.40/0.99      | sK3 != sK2 ),
% 2.40/0.99      inference(instantiation,[status(thm)],[c_2050]) ).
% 2.40/0.99  
% 2.40/0.99  cnf(c_23,plain,
% 2.40/0.99      ( r1_ordinal1(X0,X1)
% 2.40/0.99      | r2_hidden(X1,X0)
% 2.40/0.99      | ~ v3_ordinal1(X1)
% 2.40/0.99      | ~ v3_ordinal1(X0) ),
% 2.40/0.99      inference(cnf_transformation,[],[f73]) ).
% 2.40/0.99  
% 2.40/0.99  cnf(c_26,negated_conjecture,
% 2.40/0.99      ( ~ r1_ordinal1(k3_tarski(k1_enumset1(sK2,sK2,k1_enumset1(sK2,sK2,sK2))),sK3)
% 2.40/0.99      | ~ r2_hidden(sK2,sK3) ),
% 2.40/0.99      inference(cnf_transformation,[],[f93]) ).
% 2.40/0.99  
% 2.40/0.99  cnf(c_231,plain,
% 2.40/0.99      ( ~ r2_hidden(sK2,sK3)
% 2.40/0.99      | ~ r1_ordinal1(k3_tarski(k1_enumset1(sK2,sK2,k1_enumset1(sK2,sK2,sK2))),sK3) ),
% 2.40/0.99      inference(prop_impl,[status(thm)],[c_26]) ).
% 2.40/0.99  
% 2.40/0.99  cnf(c_232,plain,
% 2.40/0.99      ( ~ r1_ordinal1(k3_tarski(k1_enumset1(sK2,sK2,k1_enumset1(sK2,sK2,sK2))),sK3)
% 2.40/0.99      | ~ r2_hidden(sK2,sK3) ),
% 2.40/0.99      inference(renaming,[status(thm)],[c_231]) ).
% 2.40/0.99  
% 2.40/0.99  cnf(c_402,plain,
% 2.40/0.99      ( r2_hidden(X0,X1)
% 2.40/0.99      | ~ r2_hidden(sK2,sK3)
% 2.40/0.99      | ~ v3_ordinal1(X1)
% 2.40/0.99      | ~ v3_ordinal1(X0)
% 2.40/0.99      | k3_tarski(k1_enumset1(sK2,sK2,k1_enumset1(sK2,sK2,sK2))) != X1
% 2.40/0.99      | sK3 != X0 ),
% 2.40/0.99      inference(resolution_lifted,[status(thm)],[c_23,c_232]) ).
% 2.40/0.99  
% 2.40/0.99  cnf(c_403,plain,
% 2.40/0.99      ( r2_hidden(sK3,k3_tarski(k1_enumset1(sK2,sK2,k1_enumset1(sK2,sK2,sK2))))
% 2.40/0.99      | ~ r2_hidden(sK2,sK3)
% 2.40/0.99      | ~ v3_ordinal1(k3_tarski(k1_enumset1(sK2,sK2,k1_enumset1(sK2,sK2,sK2))))
% 2.40/0.99      | ~ v3_ordinal1(sK3) ),
% 2.40/0.99      inference(unflattening,[status(thm)],[c_402]) ).
% 2.40/0.99  
% 2.40/0.99  cnf(c_29,negated_conjecture,
% 2.40/0.99      ( v3_ordinal1(sK2) ),
% 2.40/0.99      inference(cnf_transformation,[],[f76]) ).
% 2.40/0.99  
% 2.40/0.99  cnf(c_28,negated_conjecture,
% 2.40/0.99      ( v3_ordinal1(sK3) ),
% 2.40/0.99      inference(cnf_transformation,[],[f77]) ).
% 2.40/0.99  
% 2.40/0.99  cnf(c_24,plain,
% 2.40/0.99      ( ~ v3_ordinal1(X0)
% 2.40/0.99      | v3_ordinal1(k3_tarski(k1_enumset1(X0,X0,k1_enumset1(X0,X0,X0)))) ),
% 2.40/0.99      inference(cnf_transformation,[],[f92]) ).
% 2.40/0.99  
% 2.40/0.99  cnf(c_38,plain,
% 2.40/0.99      ( v3_ordinal1(k3_tarski(k1_enumset1(sK2,sK2,k1_enumset1(sK2,sK2,sK2))))
% 2.40/0.99      | ~ v3_ordinal1(sK2) ),
% 2.40/0.99      inference(instantiation,[status(thm)],[c_24]) ).
% 2.40/0.99  
% 2.40/0.99  cnf(c_405,plain,
% 2.40/0.99      ( r2_hidden(sK3,k3_tarski(k1_enumset1(sK2,sK2,k1_enumset1(sK2,sK2,sK2))))
% 2.40/0.99      | ~ r2_hidden(sK2,sK3) ),
% 2.40/0.99      inference(global_propositional_subsumption,
% 2.40/0.99                [status(thm)],
% 2.40/0.99                [c_403,c_29,c_28,c_38]) ).
% 2.40/0.99  
% 2.40/0.99  cnf(c_1327,plain,
% 2.40/0.99      ( r2_hidden(sK3,k3_tarski(k1_enumset1(sK2,sK2,k1_enumset1(sK2,sK2,sK2)))) = iProver_top
% 2.40/0.99      | r2_hidden(sK2,sK3) != iProver_top ),
% 2.40/0.99      inference(predicate_to_equality,[status(thm)],[c_405]) ).
% 2.40/0.99  
% 2.40/0.99  cnf(c_30,plain,
% 2.40/0.99      ( v3_ordinal1(sK2) = iProver_top ),
% 2.40/0.99      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 2.40/0.99  
% 2.40/0.99  cnf(c_31,plain,
% 2.40/0.99      ( v3_ordinal1(sK3) = iProver_top ),
% 2.40/0.99      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 2.40/0.99  
% 2.40/0.99  cnf(c_37,plain,
% 2.40/0.99      ( v3_ordinal1(X0) != iProver_top
% 2.40/0.99      | v3_ordinal1(k3_tarski(k1_enumset1(X0,X0,k1_enumset1(X0,X0,X0)))) = iProver_top ),
% 2.40/0.99      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 2.40/0.99  
% 2.40/0.99  cnf(c_39,plain,
% 2.40/0.99      ( v3_ordinal1(k3_tarski(k1_enumset1(sK2,sK2,k1_enumset1(sK2,sK2,sK2)))) = iProver_top
% 2.40/0.99      | v3_ordinal1(sK2) != iProver_top ),
% 2.40/0.99      inference(instantiation,[status(thm)],[c_37]) ).
% 2.40/0.99  
% 2.40/0.99  cnf(c_404,plain,
% 2.40/0.99      ( r2_hidden(sK3,k3_tarski(k1_enumset1(sK2,sK2,k1_enumset1(sK2,sK2,sK2)))) = iProver_top
% 2.40/0.99      | r2_hidden(sK2,sK3) != iProver_top
% 2.40/0.99      | v3_ordinal1(k3_tarski(k1_enumset1(sK2,sK2,k1_enumset1(sK2,sK2,sK2)))) != iProver_top
% 2.40/0.99      | v3_ordinal1(sK3) != iProver_top ),
% 2.40/0.99      inference(predicate_to_equality,[status(thm)],[c_403]) ).
% 2.40/0.99  
% 2.40/0.99  cnf(c_0,plain,
% 2.40/0.99      ( ~ r2_hidden(X0,X1) | ~ r2_hidden(X1,X0) ),
% 2.40/0.99      inference(cnf_transformation,[],[f46]) ).
% 2.40/0.99  
% 2.40/0.99  cnf(c_1544,plain,
% 2.40/0.99      ( ~ r2_hidden(sK3,sK2) | ~ r2_hidden(sK2,sK3) ),
% 2.40/0.99      inference(instantiation,[status(thm)],[c_0]) ).
% 2.40/0.99  
% 2.40/0.99  cnf(c_1545,plain,
% 2.40/0.99      ( r2_hidden(sK3,sK2) != iProver_top
% 2.40/0.99      | r2_hidden(sK2,sK3) != iProver_top ),
% 2.40/0.99      inference(predicate_to_equality,[status(thm)],[c_1544]) ).
% 2.40/0.99  
% 2.40/0.99  cnf(c_19,plain,
% 2.40/0.99      ( r1_tarski(k1_enumset1(X0,X0,X0),X1) | ~ r2_hidden(X0,X1) ),
% 2.40/0.99      inference(cnf_transformation,[],[f90]) ).
% 2.40/0.99  
% 2.40/0.99  cnf(c_1640,plain,
% 2.40/0.99      ( r1_tarski(k1_enumset1(sK2,sK2,sK2),sK3) | ~ r2_hidden(sK2,sK3) ),
% 2.40/0.99      inference(instantiation,[status(thm)],[c_19]) ).
% 2.40/0.99  
% 2.40/0.99  cnf(c_1641,plain,
% 2.40/0.99      ( r1_tarski(k1_enumset1(sK2,sK2,sK2),sK3) = iProver_top
% 2.40/0.99      | r2_hidden(sK2,sK3) != iProver_top ),
% 2.40/0.99      inference(predicate_to_equality,[status(thm)],[c_1640]) ).
% 2.40/0.99  
% 2.40/0.99  cnf(c_6,plain,
% 2.40/0.99      ( r2_hidden(X0,X1)
% 2.40/0.99      | r2_hidden(X0,X2)
% 2.40/0.99      | ~ r2_hidden(X0,k3_tarski(k1_enumset1(X2,X2,X1))) ),
% 2.40/0.99      inference(cnf_transformation,[],[f97]) ).
% 2.40/0.99  
% 2.40/0.99  cnf(c_1657,plain,
% 2.40/0.99      ( r2_hidden(sK3,k1_enumset1(sK2,sK2,sK2))
% 2.40/0.99      | ~ r2_hidden(sK3,k3_tarski(k1_enumset1(sK2,sK2,k1_enumset1(sK2,sK2,sK2))))
% 2.40/0.99      | r2_hidden(sK3,sK2) ),
% 2.40/0.99      inference(instantiation,[status(thm)],[c_6]) ).
% 2.40/0.99  
% 2.40/0.99  cnf(c_1658,plain,
% 2.40/0.99      ( r2_hidden(sK3,k1_enumset1(sK2,sK2,sK2)) = iProver_top
% 2.40/0.99      | r2_hidden(sK3,k3_tarski(k1_enumset1(sK2,sK2,k1_enumset1(sK2,sK2,sK2)))) != iProver_top
% 2.40/0.99      | r2_hidden(sK3,sK2) = iProver_top ),
% 2.40/0.99      inference(predicate_to_equality,[status(thm)],[c_1657]) ).
% 2.40/0.99  
% 2.40/0.99  cnf(c_25,plain,
% 2.40/0.99      ( ~ r1_tarski(X0,X1) | ~ r2_hidden(X1,X0) ),
% 2.40/0.99      inference(cnf_transformation,[],[f75]) ).
% 2.40/0.99  
% 2.40/0.99  cnf(c_1996,plain,
% 2.40/0.99      ( ~ r1_tarski(k1_enumset1(X0,X0,X0),X1)
% 2.40/0.99      | ~ r2_hidden(X1,k1_enumset1(X0,X0,X0)) ),
% 2.40/0.99      inference(instantiation,[status(thm)],[c_25]) ).
% 2.40/0.99  
% 2.40/0.99  cnf(c_3177,plain,
% 2.40/0.99      ( ~ r1_tarski(k1_enumset1(sK2,sK2,sK2),sK3)
% 2.40/0.99      | ~ r2_hidden(sK3,k1_enumset1(sK2,sK2,sK2)) ),
% 2.40/0.99      inference(instantiation,[status(thm)],[c_1996]) ).
% 2.40/0.99  
% 2.40/0.99  cnf(c_3181,plain,
% 2.40/0.99      ( r1_tarski(k1_enumset1(sK2,sK2,sK2),sK3) != iProver_top
% 2.40/0.99      | r2_hidden(sK3,k1_enumset1(sK2,sK2,sK2)) != iProver_top ),
% 2.40/0.99      inference(predicate_to_equality,[status(thm)],[c_3177]) ).
% 2.40/0.99  
% 2.40/0.99  cnf(c_4396,plain,
% 2.40/0.99      ( r2_hidden(sK2,sK3) != iProver_top ),
% 2.40/0.99      inference(global_propositional_subsumption,
% 2.40/0.99                [status(thm)],
% 2.40/0.99                [c_1327,c_30,c_31,c_39,c_404,c_1545,c_1641,c_1658,c_3181]) ).
% 2.40/0.99  
% 2.40/0.99  cnf(c_3469,plain,
% 2.40/0.99      ( ~ r1_tarski(X0,sK3) | ~ r1_tarski(sK3,X0) | X0 = sK3 ),
% 2.40/0.99      inference(instantiation,[status(thm)],[c_7]) ).
% 2.40/0.99  
% 2.40/0.99  cnf(c_3470,plain,
% 2.40/0.99      ( X0 = sK3
% 2.40/0.99      | r1_tarski(X0,sK3) != iProver_top
% 2.40/0.99      | r1_tarski(sK3,X0) != iProver_top ),
% 2.40/0.99      inference(predicate_to_equality,[status(thm)],[c_3469]) ).
% 2.40/0.99  
% 2.40/0.99  cnf(c_3472,plain,
% 2.40/0.99      ( sK2 = sK3
% 2.40/0.99      | r1_tarski(sK3,sK2) != iProver_top
% 2.40/0.99      | r1_tarski(sK2,sK3) != iProver_top ),
% 2.40/0.99      inference(instantiation,[status(thm)],[c_3470]) ).
% 2.40/0.99  
% 2.40/0.99  cnf(c_4,plain,
% 2.40/0.99      ( ~ r2_hidden(X0,X1)
% 2.40/0.99      | r2_hidden(X0,k3_tarski(k1_enumset1(X2,X2,X1))) ),
% 2.40/0.99      inference(cnf_transformation,[],[f95]) ).
% 2.40/0.99  
% 2.40/0.99  cnf(c_1984,plain,
% 2.40/0.99      ( ~ r2_hidden(X0,k1_enumset1(X1,X1,X1))
% 2.40/0.99      | r2_hidden(X0,k3_tarski(k1_enumset1(X2,X2,k1_enumset1(X1,X1,X1)))) ),
% 2.40/0.99      inference(instantiation,[status(thm)],[c_4]) ).
% 2.40/0.99  
% 2.40/0.99  cnf(c_2273,plain,
% 2.40/0.99      ( ~ r2_hidden(sK3,k1_enumset1(sK2,sK2,sK2))
% 2.40/0.99      | r2_hidden(sK3,k3_tarski(k1_enumset1(sK2,sK2,k1_enumset1(sK2,sK2,sK2)))) ),
% 2.40/0.99      inference(instantiation,[status(thm)],[c_1984]) ).
% 2.40/0.99  
% 2.40/0.99  cnf(c_22,plain,
% 2.40/0.99      ( ~ r1_ordinal1(X0,X1)
% 2.40/0.99      | r1_tarski(X0,X1)
% 2.40/0.99      | ~ v3_ordinal1(X1)
% 2.40/0.99      | ~ v3_ordinal1(X0) ),
% 2.40/0.99      inference(cnf_transformation,[],[f71]) ).
% 2.40/0.99  
% 2.40/0.99  cnf(c_27,negated_conjecture,
% 2.40/0.99      ( r1_ordinal1(k3_tarski(k1_enumset1(sK2,sK2,k1_enumset1(sK2,sK2,sK2))),sK3)
% 2.40/0.99      | r2_hidden(sK2,sK3) ),
% 2.40/0.99      inference(cnf_transformation,[],[f94]) ).
% 2.40/0.99  
% 2.40/0.99  cnf(c_233,plain,
% 2.40/0.99      ( r2_hidden(sK2,sK3)
% 2.40/0.99      | r1_ordinal1(k3_tarski(k1_enumset1(sK2,sK2,k1_enumset1(sK2,sK2,sK2))),sK3) ),
% 2.40/0.99      inference(prop_impl,[status(thm)],[c_27]) ).
% 2.40/0.99  
% 2.40/0.99  cnf(c_234,plain,
% 2.40/0.99      ( r1_ordinal1(k3_tarski(k1_enumset1(sK2,sK2,k1_enumset1(sK2,sK2,sK2))),sK3)
% 2.40/0.99      | r2_hidden(sK2,sK3) ),
% 2.40/0.99      inference(renaming,[status(thm)],[c_233]) ).
% 2.40/0.99  
% 2.40/0.99  cnf(c_430,plain,
% 2.40/0.99      ( r1_tarski(X0,X1)
% 2.40/0.99      | r2_hidden(sK2,sK3)
% 2.40/0.99      | ~ v3_ordinal1(X0)
% 2.40/0.99      | ~ v3_ordinal1(X1)
% 2.40/0.99      | k3_tarski(k1_enumset1(sK2,sK2,k1_enumset1(sK2,sK2,sK2))) != X0
% 2.40/0.99      | sK3 != X1 ),
% 2.40/0.99      inference(resolution_lifted,[status(thm)],[c_22,c_234]) ).
% 2.40/0.99  
% 2.40/0.99  cnf(c_431,plain,
% 2.40/0.99      ( r1_tarski(k3_tarski(k1_enumset1(sK2,sK2,k1_enumset1(sK2,sK2,sK2))),sK3)
% 2.40/0.99      | r2_hidden(sK2,sK3)
% 2.40/0.99      | ~ v3_ordinal1(k3_tarski(k1_enumset1(sK2,sK2,k1_enumset1(sK2,sK2,sK2))))
% 2.40/0.99      | ~ v3_ordinal1(sK3) ),
% 2.40/0.99      inference(unflattening,[status(thm)],[c_430]) ).
% 2.40/0.99  
% 2.40/0.99  cnf(c_559,plain,
% 2.40/0.99      ( r2_hidden(sK2,sK3)
% 2.40/0.99      | r1_tarski(k3_tarski(k1_enumset1(sK2,sK2,k1_enumset1(sK2,sK2,sK2))),sK3) ),
% 2.40/0.99      inference(prop_impl,[status(thm)],[c_29,c_28,c_38,c_431]) ).
% 2.40/0.99  
% 2.40/0.99  cnf(c_560,plain,
% 2.40/0.99      ( r1_tarski(k3_tarski(k1_enumset1(sK2,sK2,k1_enumset1(sK2,sK2,sK2))),sK3)
% 2.40/0.99      | r2_hidden(sK2,sK3) ),
% 2.40/0.99      inference(renaming,[status(thm)],[c_559]) ).
% 2.40/0.99  
% 2.40/0.99  cnf(c_1325,plain,
% 2.40/0.99      ( r1_tarski(k3_tarski(k1_enumset1(sK2,sK2,k1_enumset1(sK2,sK2,sK2))),sK3) = iProver_top
% 2.40/0.99      | r2_hidden(sK2,sK3) = iProver_top ),
% 2.40/0.99      inference(predicate_to_equality,[status(thm)],[c_560]) ).
% 2.40/0.99  
% 2.40/0.99  cnf(c_10,plain,
% 2.40/0.99      ( r1_tarski(X0,X1)
% 2.40/0.99      | ~ r1_tarski(k3_tarski(k1_enumset1(X0,X0,X2)),X1) ),
% 2.40/0.99      inference(cnf_transformation,[],[f89]) ).
% 2.40/0.99  
% 2.40/0.99  cnf(c_1343,plain,
% 2.40/0.99      ( r1_tarski(X0,X1) = iProver_top
% 2.40/0.99      | r1_tarski(k3_tarski(k1_enumset1(X0,X0,X2)),X1) != iProver_top ),
% 2.40/0.99      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 2.40/0.99  
% 2.40/0.99  cnf(c_2136,plain,
% 2.40/0.99      ( r1_tarski(sK2,sK3) = iProver_top
% 2.40/0.99      | r2_hidden(sK2,sK3) = iProver_top ),
% 2.40/0.99      inference(superposition,[status(thm)],[c_1325,c_1343]) ).
% 2.40/0.99  
% 2.40/0.99  cnf(c_2146,plain,
% 2.40/0.99      ( r1_tarski(sK2,sK3) | r2_hidden(sK2,sK3) ),
% 2.40/0.99      inference(predicate_to_equality_rev,[status(thm)],[c_2136]) ).
% 2.40/0.99  
% 2.40/0.99  cnf(c_1331,plain,
% 2.40/0.99      ( r1_tarski(X0,X1) != iProver_top
% 2.40/0.99      | r2_hidden(X1,X0) != iProver_top ),
% 2.40/0.99      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 2.40/0.99  
% 2.40/0.99  cnf(c_1759,plain,
% 2.40/0.99      ( r2_hidden(sK3,k3_tarski(k1_enumset1(sK2,sK2,k1_enumset1(sK2,sK2,sK2)))) != iProver_top
% 2.40/0.99      | r2_hidden(sK2,sK3) = iProver_top ),
% 2.40/0.99      inference(superposition,[status(thm)],[c_1325,c_1331]) ).
% 2.40/0.99  
% 2.40/0.99  cnf(c_1760,plain,
% 2.40/0.99      ( ~ r2_hidden(sK3,k3_tarski(k1_enumset1(sK2,sK2,k1_enumset1(sK2,sK2,sK2))))
% 2.40/0.99      | r2_hidden(sK2,sK3) ),
% 2.40/0.99      inference(predicate_to_equality_rev,[status(thm)],[c_1759]) ).
% 2.40/0.99  
% 2.40/0.99  cnf(c_385,plain,
% 2.40/0.99      ( r1_tarski(X0,X1)
% 2.40/0.99      | r2_hidden(X1,X0)
% 2.40/0.99      | ~ v3_ordinal1(X0)
% 2.40/0.99      | ~ v3_ordinal1(X1) ),
% 2.40/0.99      inference(resolution,[status(thm)],[c_23,c_22]) ).
% 2.40/0.99  
% 2.40/0.99  cnf(c_1730,plain,
% 2.40/0.99      ( r1_tarski(sK3,sK2)
% 2.40/0.99      | r2_hidden(sK2,sK3)
% 2.40/0.99      | ~ v3_ordinal1(sK3)
% 2.40/0.99      | ~ v3_ordinal1(sK2) ),
% 2.40/0.99      inference(instantiation,[status(thm)],[c_385]) ).
% 2.40/0.99  
% 2.40/0.99  cnf(c_1736,plain,
% 2.40/0.99      ( r1_tarski(sK3,sK2) = iProver_top
% 2.40/0.99      | r2_hidden(sK2,sK3) = iProver_top
% 2.40/0.99      | v3_ordinal1(sK3) != iProver_top
% 2.40/0.99      | v3_ordinal1(sK2) != iProver_top ),
% 2.40/0.99      inference(predicate_to_equality,[status(thm)],[c_1730]) ).
% 2.40/0.99  
% 2.40/0.99  cnf(c_1675,plain,
% 2.40/0.99      ( r2_hidden(X0,X1) | ~ r2_hidden(sK2,sK3) | X1 != sK3 | X0 != sK2 ),
% 2.40/0.99      inference(instantiation,[status(thm)],[c_709]) ).
% 2.40/0.99  
% 2.40/0.99  cnf(c_1677,plain,
% 2.40/0.99      ( ~ r2_hidden(sK2,sK3)
% 2.40/0.99      | r2_hidden(sK2,sK2)
% 2.40/0.99      | sK2 != sK3
% 2.40/0.99      | sK2 != sK2 ),
% 2.40/0.99      inference(instantiation,[status(thm)],[c_1675]) ).
% 2.40/0.99  
% 2.40/0.99  cnf(c_710,plain,
% 2.40/0.99      ( X0 != X1
% 2.40/0.99      | X2 != X3
% 2.40/0.99      | X4 != X5
% 2.40/0.99      | k1_enumset1(X0,X2,X4) = k1_enumset1(X1,X3,X5) ),
% 2.40/0.99      theory(equality) ).
% 2.40/0.99  
% 2.40/0.99  cnf(c_715,plain,
% 2.40/0.99      ( k1_enumset1(sK2,sK2,sK2) = k1_enumset1(sK2,sK2,sK2)
% 2.40/0.99      | sK2 != sK2 ),
% 2.40/0.99      inference(instantiation,[status(thm)],[c_710]) ).
% 2.40/0.99  
% 2.40/0.99  cnf(c_9,plain,
% 2.40/0.99      ( r1_tarski(X0,X0) ),
% 2.40/0.99      inference(cnf_transformation,[],[f99]) ).
% 2.40/0.99  
% 2.40/0.99  cnf(c_75,plain,
% 2.40/0.99      ( r1_tarski(sK2,sK2) ),
% 2.40/0.99      inference(instantiation,[status(thm)],[c_9]) ).
% 2.40/0.99  
% 2.40/0.99  cnf(c_17,plain,
% 2.40/0.99      ( r2_hidden(X0,k1_enumset1(X0,X1,X2)) ),
% 2.40/0.99      inference(cnf_transformation,[],[f105]) ).
% 2.40/0.99  
% 2.40/0.99  cnf(c_59,plain,
% 2.40/0.99      ( r2_hidden(sK2,k1_enumset1(sK2,sK2,sK2)) ),
% 2.40/0.99      inference(instantiation,[status(thm)],[c_17]) ).
% 2.40/0.99  
% 2.40/0.99  cnf(c_18,plain,
% 2.40/0.99      ( ~ r2_hidden(X0,k1_enumset1(X1,X2,X3))
% 2.40/0.99      | X0 = X1
% 2.40/0.99      | X0 = X2
% 2.40/0.99      | X0 = X3 ),
% 2.40/0.99      inference(cnf_transformation,[],[f106]) ).
% 2.40/0.99  
% 2.40/0.99  cnf(c_56,plain,
% 2.40/0.99      ( ~ r2_hidden(sK2,k1_enumset1(sK2,sK2,sK2)) | sK2 = sK2 ),
% 2.40/0.99      inference(instantiation,[status(thm)],[c_18]) ).
% 2.40/0.99  
% 2.40/0.99  cnf(c_35,plain,
% 2.40/0.99      ( ~ r1_tarski(sK2,sK2) | ~ r2_hidden(sK2,sK2) ),
% 2.40/0.99      inference(instantiation,[status(thm)],[c_25]) ).
% 2.40/0.99  
% 2.40/0.99  cnf(contradiction,plain,
% 2.40/0.99      ( $false ),
% 2.40/0.99      inference(minisat,
% 2.40/0.99                [status(thm)],
% 2.40/0.99                [c_6794,c_5561,c_4396,c_3472,c_2273,c_2146,c_2136,c_1760,
% 2.40/0.99                 c_1736,c_1730,c_1677,c_715,c_75,c_59,c_56,c_35,c_31,
% 2.40/0.99                 c_28,c_30,c_29]) ).
% 2.40/0.99  
% 2.40/0.99  
% 2.40/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 2.40/0.99  
% 2.40/0.99  ------                               Statistics
% 2.40/0.99  
% 2.40/0.99  ------ General
% 2.40/0.99  
% 2.40/0.99  abstr_ref_over_cycles:                  0
% 2.40/0.99  abstr_ref_under_cycles:                 0
% 2.40/0.99  gc_basic_clause_elim:                   0
% 2.40/0.99  forced_gc_time:                         0
% 2.40/0.99  parsing_time:                           0.01
% 2.40/0.99  unif_index_cands_time:                  0.
% 2.40/0.99  unif_index_add_time:                    0.
% 2.40/0.99  orderings_time:                         0.
% 2.40/0.99  out_proof_time:                         0.013
% 2.40/0.99  total_time:                             0.209
% 2.40/0.99  num_of_symbols:                         38
% 2.40/0.99  num_of_terms:                           8581
% 2.40/0.99  
% 2.40/0.99  ------ Preprocessing
% 2.40/0.99  
% 2.40/0.99  num_of_splits:                          0
% 2.40/0.99  num_of_split_atoms:                     0
% 2.40/0.99  num_of_reused_defs:                     0
% 2.40/0.99  num_eq_ax_congr_red:                    22
% 2.40/0.99  num_of_sem_filtered_clauses:            1
% 2.40/0.99  num_of_subtypes:                        0
% 2.40/0.99  monotx_restored_types:                  0
% 2.40/0.99  sat_num_of_epr_types:                   0
% 2.40/0.99  sat_num_of_non_cyclic_types:            0
% 2.40/0.99  sat_guarded_non_collapsed_types:        0
% 2.40/0.99  num_pure_diseq_elim:                    0
% 2.40/0.99  simp_replaced_by:                       0
% 2.40/0.99  res_preprocessed:                       128
% 2.40/0.99  prep_upred:                             0
% 2.40/0.99  prep_unflattend:                        6
% 2.40/0.99  smt_new_axioms:                         0
% 2.40/0.99  pred_elim_cands:                        3
% 2.40/0.99  pred_elim:                              1
% 2.40/0.99  pred_elim_cl:                           1
% 2.40/0.99  pred_elim_cycles:                       3
% 2.40/0.99  merged_defs:                            16
% 2.40/0.99  merged_defs_ncl:                        0
% 2.40/0.99  bin_hyper_res:                          16
% 2.40/0.99  prep_cycles:                            4
% 2.40/0.99  pred_elim_time:                         0.002
% 2.40/0.99  splitting_time:                         0.
% 2.40/0.99  sem_filter_time:                        0.
% 2.40/0.99  monotx_time:                            0.
% 2.40/0.99  subtype_inf_time:                       0.
% 2.40/0.99  
% 2.40/0.99  ------ Problem properties
% 2.40/0.99  
% 2.40/0.99  clauses:                                28
% 2.40/0.99  conjectures:                            2
% 2.40/0.99  epr:                                    7
% 2.40/0.99  horn:                                   22
% 2.40/0.99  ground:                                 5
% 2.40/0.99  unary:                                  6
% 2.40/0.99  binary:                                 11
% 2.40/0.99  lits:                                   66
% 2.40/0.99  lits_eq:                                17
% 2.40/0.99  fd_pure:                                0
% 2.40/0.99  fd_pseudo:                              0
% 2.40/0.99  fd_cond:                                0
% 2.40/0.99  fd_pseudo_cond:                         8
% 2.40/0.99  ac_symbols:                             0
% 2.40/0.99  
% 2.40/0.99  ------ Propositional Solver
% 2.40/0.99  
% 2.40/0.99  prop_solver_calls:                      26
% 2.40/0.99  prop_fast_solver_calls:                 737
% 2.40/0.99  smt_solver_calls:                       0
% 2.40/0.99  smt_fast_solver_calls:                  0
% 2.40/0.99  prop_num_of_clauses:                    2514
% 2.40/0.99  prop_preprocess_simplified:             9496
% 2.40/0.99  prop_fo_subsumed:                       7
% 2.40/0.99  prop_solver_time:                       0.
% 2.40/0.99  smt_solver_time:                        0.
% 2.40/0.99  smt_fast_solver_time:                   0.
% 2.40/0.99  prop_fast_solver_time:                  0.
% 2.40/0.99  prop_unsat_core_time:                   0.
% 2.40/0.99  
% 2.40/0.99  ------ QBF
% 2.40/0.99  
% 2.40/0.99  qbf_q_res:                              0
% 2.40/0.99  qbf_num_tautologies:                    0
% 2.40/0.99  qbf_prep_cycles:                        0
% 2.40/0.99  
% 2.40/0.99  ------ BMC1
% 2.40/0.99  
% 2.40/0.99  bmc1_current_bound:                     -1
% 2.40/0.99  bmc1_last_solved_bound:                 -1
% 2.40/0.99  bmc1_unsat_core_size:                   -1
% 2.40/0.99  bmc1_unsat_core_parents_size:           -1
% 2.40/0.99  bmc1_merge_next_fun:                    0
% 2.40/0.99  bmc1_unsat_core_clauses_time:           0.
% 2.40/0.99  
% 2.40/0.99  ------ Instantiation
% 2.40/0.99  
% 2.40/0.99  inst_num_of_clauses:                    759
% 2.40/0.99  inst_num_in_passive:                    396
% 2.40/0.99  inst_num_in_active:                     215
% 2.40/0.99  inst_num_in_unprocessed:                147
% 2.40/0.99  inst_num_of_loops:                      255
% 2.40/0.99  inst_num_of_learning_restarts:          0
% 2.40/0.99  inst_num_moves_active_passive:          39
% 2.40/0.99  inst_lit_activity:                      0
% 2.40/0.99  inst_lit_activity_moves:                0
% 2.40/0.99  inst_num_tautologies:                   0
% 2.40/0.99  inst_num_prop_implied:                  0
% 2.40/0.99  inst_num_existing_simplified:           0
% 2.40/0.99  inst_num_eq_res_simplified:             0
% 2.40/0.99  inst_num_child_elim:                    0
% 2.40/0.99  inst_num_of_dismatching_blockings:      95
% 2.40/0.99  inst_num_of_non_proper_insts:           487
% 2.40/0.99  inst_num_of_duplicates:                 0
% 2.40/0.99  inst_inst_num_from_inst_to_res:         0
% 2.40/0.99  inst_dismatching_checking_time:         0.
% 2.40/0.99  
% 2.40/0.99  ------ Resolution
% 2.40/0.99  
% 2.40/0.99  res_num_of_clauses:                     0
% 2.40/0.99  res_num_in_passive:                     0
% 2.40/0.99  res_num_in_active:                      0
% 2.40/0.99  res_num_of_loops:                       132
% 2.40/0.99  res_forward_subset_subsumed:            26
% 2.40/0.99  res_backward_subset_subsumed:           0
% 2.40/0.99  res_forward_subsumed:                   0
% 2.40/0.99  res_backward_subsumed:                  0
% 2.40/0.99  res_forward_subsumption_resolution:     0
% 2.40/0.99  res_backward_subsumption_resolution:    0
% 2.40/0.99  res_clause_to_clause_subsumption:       1097
% 2.40/0.99  res_orphan_elimination:                 0
% 2.40/0.99  res_tautology_del:                      37
% 2.40/0.99  res_num_eq_res_simplified:              0
% 2.40/0.99  res_num_sel_changes:                    0
% 2.40/0.99  res_moves_from_active_to_pass:          0
% 2.40/0.99  
% 2.40/0.99  ------ Superposition
% 2.40/0.99  
% 2.40/0.99  sup_time_total:                         0.
% 2.40/0.99  sup_time_generating:                    0.
% 2.40/0.99  sup_time_sim_full:                      0.
% 2.40/0.99  sup_time_sim_immed:                     0.
% 2.40/0.99  
% 2.40/0.99  sup_num_of_clauses:                     108
% 2.40/0.99  sup_num_in_active:                      50
% 2.40/0.99  sup_num_in_passive:                     58
% 2.40/0.99  sup_num_of_loops:                       50
% 2.40/0.99  sup_fw_superposition:                   60
% 2.40/0.99  sup_bw_superposition:                   47
% 2.40/0.99  sup_immediate_simplified:               3
% 2.40/0.99  sup_given_eliminated:                   0
% 2.40/0.99  comparisons_done:                       0
% 2.40/0.99  comparisons_avoided:                    0
% 2.40/0.99  
% 2.40/0.99  ------ Simplifications
% 2.40/0.99  
% 2.40/0.99  
% 2.40/0.99  sim_fw_subset_subsumed:                 4
% 2.40/0.99  sim_bw_subset_subsumed:                 1
% 2.40/0.99  sim_fw_subsumed:                        2
% 2.40/0.99  sim_bw_subsumed:                        0
% 2.40/0.99  sim_fw_subsumption_res:                 0
% 2.40/0.99  sim_bw_subsumption_res:                 0
% 2.40/0.99  sim_tautology_del:                      10
% 2.40/0.99  sim_eq_tautology_del:                   1
% 2.40/0.99  sim_eq_res_simp:                        6
% 2.40/0.99  sim_fw_demodulated:                     0
% 2.40/0.99  sim_bw_demodulated:                     0
% 2.40/0.99  sim_light_normalised:                   0
% 2.40/0.99  sim_joinable_taut:                      0
% 2.40/0.99  sim_joinable_simp:                      0
% 2.40/0.99  sim_ac_normalised:                      0
% 2.40/0.99  sim_smt_subsumption:                    0
% 2.40/0.99  
%------------------------------------------------------------------------------
