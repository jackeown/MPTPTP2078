%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:53:49 EST 2020

% Result     : Theorem 2.46s
% Output     : CNFRefutation 2.46s
% Verified   : 
% Statistics : Number of formulae       :  149 ( 826 expanded)
%              Number of clauses        :   80 ( 171 expanded)
%              Number of leaves         :   17 ( 213 expanded)
%              Depth                    :   19
%              Number of atoms          :  477 (2987 expanded)
%              Number of equality atoms :  145 ( 502 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal clause size      :   14 (   3 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f10,axiom,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ! [X1] :
          ( v3_ordinal1(X1)
         => ( r2_hidden(X1,X0)
            | r1_ordinal1(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(X1,X0)
          | r1_ordinal1(X0,X1)
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(X1,X0)
          | r1_ordinal1(X0,X1)
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(flattening,[],[f16])).

fof(f53,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,X0)
      | r1_ordinal1(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( ( v3_ordinal1(X1)
        & v3_ordinal1(X0) )
     => ( r1_ordinal1(X0,X1)
      <=> r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1] :
      ( ( r1_ordinal1(X0,X1)
      <=> r1_tarski(X0,X1) )
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ( r1_ordinal1(X0,X1)
      <=> r1_tarski(X0,X1) )
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(flattening,[],[f14])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( ( r1_ordinal1(X0,X1)
          | ~ r1_tarski(X0,X1) )
        & ( r1_tarski(X0,X1)
          | ~ r1_ordinal1(X0,X1) ) )
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f48,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r1_ordinal1(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f11,conjecture,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ! [X1] :
          ( v3_ordinal1(X1)
         => ( r2_hidden(X0,k1_ordinal1(X1))
          <=> r1_ordinal1(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f12,negated_conjecture,(
    ~ ! [X0] :
        ( v3_ordinal1(X0)
       => ! [X1] :
            ( v3_ordinal1(X1)
           => ( r2_hidden(X0,k1_ordinal1(X1))
            <=> r1_ordinal1(X0,X1) ) ) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f18,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( r2_hidden(X0,k1_ordinal1(X1))
          <~> r1_ordinal1(X0,X1) )
          & v3_ordinal1(X1) )
      & v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f29,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ r1_ordinal1(X0,X1)
            | ~ r2_hidden(X0,k1_ordinal1(X1)) )
          & ( r1_ordinal1(X0,X1)
            | r2_hidden(X0,k1_ordinal1(X1)) )
          & v3_ordinal1(X1) )
      & v3_ordinal1(X0) ) ),
    inference(nnf_transformation,[],[f18])).

fof(f30,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ r1_ordinal1(X0,X1)
            | ~ r2_hidden(X0,k1_ordinal1(X1)) )
          & ( r1_ordinal1(X0,X1)
            | r2_hidden(X0,k1_ordinal1(X1)) )
          & v3_ordinal1(X1) )
      & v3_ordinal1(X0) ) ),
    inference(flattening,[],[f29])).

fof(f32,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ( ~ r1_ordinal1(X0,X1)
            | ~ r2_hidden(X0,k1_ordinal1(X1)) )
          & ( r1_ordinal1(X0,X1)
            | r2_hidden(X0,k1_ordinal1(X1)) )
          & v3_ordinal1(X1) )
     => ( ( ~ r1_ordinal1(X0,sK2)
          | ~ r2_hidden(X0,k1_ordinal1(sK2)) )
        & ( r1_ordinal1(X0,sK2)
          | r2_hidden(X0,k1_ordinal1(sK2)) )
        & v3_ordinal1(sK2) ) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( ~ r1_ordinal1(X0,X1)
              | ~ r2_hidden(X0,k1_ordinal1(X1)) )
            & ( r1_ordinal1(X0,X1)
              | r2_hidden(X0,k1_ordinal1(X1)) )
            & v3_ordinal1(X1) )
        & v3_ordinal1(X0) )
   => ( ? [X1] :
          ( ( ~ r1_ordinal1(sK1,X1)
            | ~ r2_hidden(sK1,k1_ordinal1(X1)) )
          & ( r1_ordinal1(sK1,X1)
            | r2_hidden(sK1,k1_ordinal1(X1)) )
          & v3_ordinal1(X1) )
      & v3_ordinal1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,
    ( ( ~ r1_ordinal1(sK1,sK2)
      | ~ r2_hidden(sK1,k1_ordinal1(sK2)) )
    & ( r1_ordinal1(sK1,sK2)
      | r2_hidden(sK1,k1_ordinal1(sK2)) )
    & v3_ordinal1(sK2)
    & v3_ordinal1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f30,f32,f31])).

fof(f56,plain,
    ( r1_ordinal1(sK1,sK2)
    | r2_hidden(sK1,k1_ordinal1(sK2)) ),
    inference(cnf_transformation,[],[f33])).

fof(f7,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_tarski(X0)) = k1_ordinal1(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f47,plain,(
    ! [X0] : k2_xboole_0(X0,k1_tarski(X0)) = k1_ordinal1(X0) ),
    inference(cnf_transformation,[],[f7])).

fof(f6,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f58,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k1_enumset1(X0,X0,X1)) ),
    inference(definition_unfolding,[],[f46,f45])).

fof(f4,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f5,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f5])).

fof(f59,plain,(
    ! [X0] : k1_tarski(X0) = k1_enumset1(X0,X0,X0) ),
    inference(definition_unfolding,[],[f44,f45])).

fof(f60,plain,(
    ! [X0] : k3_tarski(k1_enumset1(X0,X0,k1_enumset1(X0,X0,X0))) = k1_ordinal1(X0) ),
    inference(definition_unfolding,[],[f47,f58,f59])).

fof(f71,plain,
    ( r1_ordinal1(sK1,sK2)
    | r2_hidden(sK1,k3_tarski(k1_enumset1(sK2,sK2,k1_enumset1(sK2,sK2,sK2)))) ),
    inference(definition_unfolding,[],[f56,f60])).

fof(f54,plain,(
    v3_ordinal1(sK1) ),
    inference(cnf_transformation,[],[f33])).

fof(f55,plain,(
    v3_ordinal1(sK2) ),
    inference(cnf_transformation,[],[f33])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,k1_ordinal1(X1))
    <=> ( X0 = X1
        | r2_hidden(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( r2_hidden(X0,k1_ordinal1(X1))
        | ( X0 != X1
          & ~ r2_hidden(X0,X1) ) )
      & ( X0 = X1
        | r2_hidden(X0,X1)
        | ~ r2_hidden(X0,k1_ordinal1(X1)) ) ) ),
    inference(nnf_transformation,[],[f9])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( r2_hidden(X0,k1_ordinal1(X1))
        | ( X0 != X1
          & ~ r2_hidden(X0,X1) ) )
      & ( X0 = X1
        | r2_hidden(X0,X1)
        | ~ r2_hidden(X0,k1_ordinal1(X1)) ) ) ),
    inference(flattening,[],[f27])).

fof(f50,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | r2_hidden(X0,X1)
      | ~ r2_hidden(X0,k1_ordinal1(X1)) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f69,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | r2_hidden(X0,X1)
      | ~ r2_hidden(X0,k3_tarski(k1_enumset1(X1,X1,k1_enumset1(X1,X1,X1)))) ) ),
    inference(definition_unfolding,[],[f50,f60])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f24])).

fof(f41,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f76,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f41])).

fof(f43,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            | r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
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

fof(f20,plain,(
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
    inference(flattening,[],[f19])).

fof(f21,plain,(
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
    inference(rectify,[],[f20])).

fof(f22,plain,(
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

fof(f23,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f21,f22])).

fof(f36,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X0)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f23])).

fof(f65,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X0)
      | k3_tarski(k1_enumset1(X0,X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f36,f58])).

fof(f73,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k3_tarski(k1_enumset1(X0,X0,X1)))
      | ~ r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f65])).

fof(f49,plain,(
    ! [X0,X1] :
      ( r1_ordinal1(X0,X1)
      | ~ r1_tarski(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f57,plain,
    ( ~ r1_ordinal1(sK1,sK2)
    | ~ r2_hidden(sK1,k1_ordinal1(sK2)) ),
    inference(cnf_transformation,[],[f33])).

fof(f70,plain,
    ( ~ r1_ordinal1(sK1,sK2)
    | ~ r2_hidden(sK1,k3_tarski(k1_enumset1(sK2,sK2,k1_enumset1(sK2,sK2,sK2)))) ),
    inference(definition_unfolding,[],[f57,f60])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f51,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,k1_ordinal1(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f68,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,k3_tarski(k1_enumset1(X1,X1,k1_enumset1(X1,X1,X1))))
      | ~ r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f51,f60])).

fof(f52,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,k1_ordinal1(X1))
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f28])).

fof(f67,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,k3_tarski(k1_enumset1(X1,X1,k1_enumset1(X1,X1,X1))))
      | X0 != X1 ) ),
    inference(definition_unfolding,[],[f52,f60])).

fof(f77,plain,(
    ! [X1] : r2_hidden(X1,k3_tarski(k1_enumset1(X1,X1,k1_enumset1(X1,X1,X1)))) ),
    inference(equality_resolution,[],[f67])).

fof(f35,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X1)
      | r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f23])).

fof(f66,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X1)
      | r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k3_tarski(k1_enumset1(X0,X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f35,f58])).

fof(f74,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X1)
      | r2_hidden(X4,X0)
      | ~ r2_hidden(X4,k3_tarski(k1_enumset1(X0,X0,X1))) ) ),
    inference(equality_resolution,[],[f66])).

fof(f37,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X1)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f23])).

fof(f64,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X1)
      | k3_tarski(k1_enumset1(X0,X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f37,f58])).

fof(f72,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k3_tarski(k1_enumset1(X0,X0,X1)))
      | ~ r2_hidden(X4,X1) ) ),
    inference(equality_resolution,[],[f64])).

cnf(c_15,plain,
    ( r1_ordinal1(X0,X1)
    | r2_hidden(X1,X0)
    | ~ v3_ordinal1(X1)
    | ~ v3_ordinal1(X0) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_11,plain,
    ( ~ r1_ordinal1(X0,X1)
    | r1_tarski(X0,X1)
    | ~ v3_ordinal1(X1)
    | ~ v3_ordinal1(X0) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_256,plain,
    ( r1_tarski(X0,X1)
    | r2_hidden(X1,X0)
    | ~ v3_ordinal1(X0)
    | ~ v3_ordinal1(X1) ),
    inference(resolution,[status(thm)],[c_15,c_11])).

cnf(c_922,plain,
    ( r1_tarski(X0,X1) = iProver_top
    | r2_hidden(X1,X0) = iProver_top
    | v3_ordinal1(X1) != iProver_top
    | v3_ordinal1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_256])).

cnf(c_17,negated_conjecture,
    ( r1_ordinal1(sK1,sK2)
    | r2_hidden(sK1,k3_tarski(k1_enumset1(sK2,sK2,k1_enumset1(sK2,sK2,sK2)))) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_153,plain,
    ( r1_ordinal1(sK1,sK2)
    | r2_hidden(sK1,k3_tarski(k1_enumset1(sK2,sK2,k1_enumset1(sK2,sK2,sK2)))) ),
    inference(prop_impl,[status(thm)],[c_17])).

cnf(c_301,plain,
    ( r1_tarski(X0,X1)
    | r2_hidden(sK1,k3_tarski(k1_enumset1(sK2,sK2,k1_enumset1(sK2,sK2,sK2))))
    | ~ v3_ordinal1(X0)
    | ~ v3_ordinal1(X1)
    | sK2 != X1
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_153])).

cnf(c_302,plain,
    ( r1_tarski(sK1,sK2)
    | r2_hidden(sK1,k3_tarski(k1_enumset1(sK2,sK2,k1_enumset1(sK2,sK2,sK2))))
    | ~ v3_ordinal1(sK2)
    | ~ v3_ordinal1(sK1) ),
    inference(unflattening,[status(thm)],[c_301])).

cnf(c_19,negated_conjecture,
    ( v3_ordinal1(sK1) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_18,negated_conjecture,
    ( v3_ordinal1(sK2) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_304,plain,
    ( r1_tarski(sK1,sK2)
    | r2_hidden(sK1,k3_tarski(k1_enumset1(sK2,sK2,k1_enumset1(sK2,sK2,sK2)))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_302,c_19,c_18])).

cnf(c_392,plain,
    ( r1_tarski(sK1,sK2)
    | r2_hidden(sK1,k3_tarski(k1_enumset1(sK2,sK2,k1_enumset1(sK2,sK2,sK2)))) ),
    inference(prop_impl,[status(thm)],[c_19,c_18,c_302])).

cnf(c_920,plain,
    ( r1_tarski(sK1,sK2) = iProver_top
    | r2_hidden(sK1,k3_tarski(k1_enumset1(sK2,sK2,k1_enumset1(sK2,sK2,sK2)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_392])).

cnf(c_14,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k3_tarski(k1_enumset1(X1,X1,k1_enumset1(X1,X1,X1))))
    | X0 = X1 ),
    inference(cnf_transformation,[],[f69])).

cnf(c_925,plain,
    ( X0 = X1
    | r2_hidden(X0,X1) = iProver_top
    | r2_hidden(X0,k3_tarski(k1_enumset1(X1,X1,k1_enumset1(X1,X1,X1)))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_4152,plain,
    ( sK2 = sK1
    | r1_tarski(sK1,sK2) = iProver_top
    | r2_hidden(sK1,sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_920,c_925])).

cnf(c_9,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_43,plain,
    ( r1_tarski(sK2,sK2) ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_42,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_44,plain,
    ( r1_tarski(sK2,sK2) = iProver_top ),
    inference(instantiation,[status(thm)],[c_42])).

cnf(c_7,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f43])).

cnf(c_47,plain,
    ( ~ r1_tarski(sK2,sK2)
    | sK2 = sK2 ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_306,plain,
    ( r1_tarski(sK1,sK2) = iProver_top
    | r2_hidden(sK1,k3_tarski(k1_enumset1(sK2,sK2,k1_enumset1(sK2,sK2,sK2)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_304])).

cnf(c_498,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_1137,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(sK1,sK2)
    | sK2 != X1
    | sK1 != X0 ),
    inference(instantiation,[status(thm)],[c_498])).

cnf(c_1138,plain,
    ( sK2 != X0
    | sK1 != X1
    | r1_tarski(X1,X0) != iProver_top
    | r1_tarski(sK1,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1137])).

cnf(c_1140,plain,
    ( sK2 != sK2
    | sK1 != sK2
    | r1_tarski(sK2,sK2) != iProver_top
    | r1_tarski(sK1,sK2) = iProver_top ),
    inference(instantiation,[status(thm)],[c_1138])).

cnf(c_5,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,k3_tarski(k1_enumset1(X1,X1,X2))) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_931,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,k3_tarski(k1_enumset1(X1,X1,X2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_10,plain,
    ( r1_ordinal1(X0,X1)
    | ~ r1_tarski(X0,X1)
    | ~ v3_ordinal1(X1)
    | ~ v3_ordinal1(X0) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_16,negated_conjecture,
    ( ~ r1_ordinal1(sK1,sK2)
    | ~ r2_hidden(sK1,k3_tarski(k1_enumset1(sK2,sK2,k1_enumset1(sK2,sK2,sK2)))) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_151,plain,
    ( ~ r1_ordinal1(sK1,sK2)
    | ~ r2_hidden(sK1,k3_tarski(k1_enumset1(sK2,sK2,k1_enumset1(sK2,sK2,sK2)))) ),
    inference(prop_impl,[status(thm)],[c_16])).

cnf(c_287,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r2_hidden(sK1,k3_tarski(k1_enumset1(sK2,sK2,k1_enumset1(sK2,sK2,sK2))))
    | ~ v3_ordinal1(X0)
    | ~ v3_ordinal1(X1)
    | sK2 != X1
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_151])).

cnf(c_288,plain,
    ( ~ r1_tarski(sK1,sK2)
    | ~ r2_hidden(sK1,k3_tarski(k1_enumset1(sK2,sK2,k1_enumset1(sK2,sK2,sK2))))
    | ~ v3_ordinal1(sK2)
    | ~ v3_ordinal1(sK1) ),
    inference(unflattening,[status(thm)],[c_287])).

cnf(c_290,plain,
    ( ~ r1_tarski(sK1,sK2)
    | ~ r2_hidden(sK1,k3_tarski(k1_enumset1(sK2,sK2,k1_enumset1(sK2,sK2,sK2)))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_288,c_19,c_18])).

cnf(c_390,plain,
    ( ~ r1_tarski(sK1,sK2)
    | ~ r2_hidden(sK1,k3_tarski(k1_enumset1(sK2,sK2,k1_enumset1(sK2,sK2,sK2)))) ),
    inference(prop_impl,[status(thm)],[c_19,c_18,c_288])).

cnf(c_921,plain,
    ( r1_tarski(sK1,sK2) != iProver_top
    | r2_hidden(sK1,k3_tarski(k1_enumset1(sK2,sK2,k1_enumset1(sK2,sK2,sK2)))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_390])).

cnf(c_1848,plain,
    ( r1_tarski(sK1,sK2) != iProver_top
    | r2_hidden(sK1,sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_931,c_921])).

cnf(c_273,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(sK1,k3_tarski(k1_enumset1(sK2,sK2,k1_enumset1(sK2,sK2,sK2))))
    | ~ v3_ordinal1(X1)
    | ~ v3_ordinal1(X0)
    | sK2 != X0
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_151])).

cnf(c_274,plain,
    ( r2_hidden(sK2,sK1)
    | ~ r2_hidden(sK1,k3_tarski(k1_enumset1(sK2,sK2,k1_enumset1(sK2,sK2,sK2))))
    | ~ v3_ordinal1(sK2)
    | ~ v3_ordinal1(sK1) ),
    inference(unflattening,[status(thm)],[c_273])).

cnf(c_276,plain,
    ( r2_hidden(sK2,sK1)
    | ~ r2_hidden(sK1,k3_tarski(k1_enumset1(sK2,sK2,k1_enumset1(sK2,sK2,sK2)))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_274,c_19,c_18])).

cnf(c_278,plain,
    ( r2_hidden(sK2,sK1) = iProver_top
    | r2_hidden(sK1,k3_tarski(k1_enumset1(sK2,sK2,k1_enumset1(sK2,sK2,sK2)))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_276])).

cnf(c_0,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X1,X0) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_1056,plain,
    ( ~ r2_hidden(sK2,sK1)
    | ~ r2_hidden(sK1,sK2) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_1057,plain,
    ( r2_hidden(sK2,sK1) != iProver_top
    | r2_hidden(sK1,sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1056])).

cnf(c_13,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,k3_tarski(k1_enumset1(X1,X1,k1_enumset1(X1,X1,X1)))) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_1142,plain,
    ( r2_hidden(sK1,k3_tarski(k1_enumset1(sK2,sK2,k1_enumset1(sK2,sK2,sK2))))
    | ~ r2_hidden(sK1,sK2) ),
    inference(instantiation,[status(thm)],[c_13])).

cnf(c_1143,plain,
    ( r2_hidden(sK1,k3_tarski(k1_enumset1(sK2,sK2,k1_enumset1(sK2,sK2,sK2)))) = iProver_top
    | r2_hidden(sK1,sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1142])).

cnf(c_2112,plain,
    ( r2_hidden(sK1,sK2) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1848,c_278,c_1057,c_1143])).

cnf(c_3871,plain,
    ( ~ r2_hidden(sK1,k3_tarski(k1_enumset1(sK2,sK2,k1_enumset1(sK2,sK2,sK2))))
    | r2_hidden(sK1,sK2)
    | sK1 = sK2 ),
    inference(instantiation,[status(thm)],[c_14])).

cnf(c_3872,plain,
    ( sK1 = sK2
    | r2_hidden(sK1,k3_tarski(k1_enumset1(sK2,sK2,k1_enumset1(sK2,sK2,sK2)))) != iProver_top
    | r2_hidden(sK1,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3871])).

cnf(c_6229,plain,
    ( r1_tarski(sK1,sK2) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4152,c_43,c_44,c_47,c_278,c_306,c_1057,c_1140,c_1143,c_3872])).

cnf(c_929,plain,
    ( X0 = X1
    | r1_tarski(X1,X0) != iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_6234,plain,
    ( sK2 = sK1
    | r1_tarski(sK2,sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_6229,c_929])).

cnf(c_12,plain,
    ( r2_hidden(X0,k3_tarski(k1_enumset1(X0,X0,k1_enumset1(X0,X0,X0)))) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_33,plain,
    ( r2_hidden(X0,k3_tarski(k1_enumset1(X0,X0,k1_enumset1(X0,X0,X0)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_35,plain,
    ( r2_hidden(sK2,k3_tarski(k1_enumset1(sK2,sK2,k1_enumset1(sK2,sK2,sK2)))) = iProver_top ),
    inference(instantiation,[status(thm)],[c_33])).

cnf(c_63,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_65,plain,
    ( r2_hidden(sK2,sK2) != iProver_top ),
    inference(instantiation,[status(thm)],[c_63])).

cnf(c_496,plain,
    ( X0 != X1
    | X2 != X3
    | X4 != X5
    | k1_enumset1(X0,X2,X4) = k1_enumset1(X1,X3,X5) ),
    theory(equality)).

cnf(c_501,plain,
    ( k1_enumset1(sK2,sK2,sK2) = k1_enumset1(sK2,sK2,sK2)
    | sK2 != sK2 ),
    inference(instantiation,[status(thm)],[c_496])).

cnf(c_6,plain,
    ( r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | ~ r2_hidden(X0,k3_tarski(k1_enumset1(X2,X2,X1))) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_1099,plain,
    ( r2_hidden(X0,X0)
    | r2_hidden(X0,k1_enumset1(X0,X0,X0))
    | ~ r2_hidden(X0,k3_tarski(k1_enumset1(X0,X0,k1_enumset1(X0,X0,X0)))) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_1100,plain,
    ( r2_hidden(X0,X0) = iProver_top
    | r2_hidden(X0,k1_enumset1(X0,X0,X0)) = iProver_top
    | r2_hidden(X0,k3_tarski(k1_enumset1(X0,X0,k1_enumset1(X0,X0,X0)))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1099])).

cnf(c_1102,plain,
    ( r2_hidden(sK2,k1_enumset1(sK2,sK2,sK2)) = iProver_top
    | r2_hidden(sK2,k3_tarski(k1_enumset1(sK2,sK2,k1_enumset1(sK2,sK2,sK2)))) != iProver_top
    | r2_hidden(sK2,sK2) = iProver_top ),
    inference(instantiation,[status(thm)],[c_1100])).

cnf(c_4,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,k3_tarski(k1_enumset1(X2,X2,X1))) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_932,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,k3_tarski(k1_enumset1(X2,X2,X1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_1847,plain,
    ( r1_tarski(sK1,sK2) != iProver_top
    | r2_hidden(sK1,k1_enumset1(sK2,sK2,sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_932,c_921])).

cnf(c_495,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_1167,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(X2,k1_enumset1(X2,X2,X2))
    | X0 != X2
    | X1 != k1_enumset1(X2,X2,X2) ),
    inference(instantiation,[status(thm)],[c_495])).

cnf(c_1337,plain,
    ( ~ r2_hidden(X0,k1_enumset1(X0,X0,X0))
    | r2_hidden(X1,k1_enumset1(X0,X0,X0))
    | X1 != X0
    | k1_enumset1(X0,X0,X0) != k1_enumset1(X0,X0,X0) ),
    inference(instantiation,[status(thm)],[c_1167])).

cnf(c_2274,plain,
    ( ~ r2_hidden(sK2,k1_enumset1(sK2,sK2,sK2))
    | r2_hidden(sK1,k1_enumset1(sK2,sK2,sK2))
    | k1_enumset1(sK2,sK2,sK2) != k1_enumset1(sK2,sK2,sK2)
    | sK1 != sK2 ),
    inference(instantiation,[status(thm)],[c_1337])).

cnf(c_2275,plain,
    ( k1_enumset1(sK2,sK2,sK2) != k1_enumset1(sK2,sK2,sK2)
    | sK1 != sK2
    | r2_hidden(sK2,k1_enumset1(sK2,sK2,sK2)) != iProver_top
    | r2_hidden(sK1,k1_enumset1(sK2,sK2,sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2274])).

cnf(c_3868,plain,
    ( ~ r1_tarski(sK2,sK1)
    | ~ r1_tarski(sK1,sK2)
    | sK1 = sK2 ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_3869,plain,
    ( sK1 = sK2
    | r1_tarski(sK2,sK1) != iProver_top
    | r1_tarski(sK1,sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3868])).

cnf(c_6826,plain,
    ( r1_tarski(sK2,sK1) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6234,c_35,c_43,c_44,c_47,c_65,c_278,c_306,c_501,c_1057,c_1102,c_1140,c_1143,c_1847,c_2275,c_3869,c_3872])).

cnf(c_6831,plain,
    ( r2_hidden(sK1,sK2) = iProver_top
    | v3_ordinal1(sK2) != iProver_top
    | v3_ordinal1(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_922,c_6826])).

cnf(c_21,plain,
    ( v3_ordinal1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_20,plain,
    ( v3_ordinal1(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_6831,c_2112,c_21,c_20])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.14/0.34  % Computer   : n018.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 12:03:41 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running in FOF mode
% 2.46/0.98  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.46/0.98  
% 2.46/0.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.46/0.98  
% 2.46/0.98  ------  iProver source info
% 2.46/0.98  
% 2.46/0.98  git: date: 2020-06-30 10:37:57 +0100
% 2.46/0.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.46/0.98  git: non_committed_changes: false
% 2.46/0.98  git: last_make_outside_of_git: false
% 2.46/0.98  
% 2.46/0.98  ------ 
% 2.46/0.98  
% 2.46/0.98  ------ Input Options
% 2.46/0.98  
% 2.46/0.98  --out_options                           all
% 2.46/0.98  --tptp_safe_out                         true
% 2.46/0.98  --problem_path                          ""
% 2.46/0.98  --include_path                          ""
% 2.46/0.98  --clausifier                            res/vclausify_rel
% 2.46/0.98  --clausifier_options                    --mode clausify
% 2.46/0.98  --stdin                                 false
% 2.46/0.98  --stats_out                             all
% 2.46/0.98  
% 2.46/0.98  ------ General Options
% 2.46/0.98  
% 2.46/0.98  --fof                                   false
% 2.46/0.98  --time_out_real                         305.
% 2.46/0.98  --time_out_virtual                      -1.
% 2.46/0.98  --symbol_type_check                     false
% 2.46/0.98  --clausify_out                          false
% 2.46/0.98  --sig_cnt_out                           false
% 2.46/0.98  --trig_cnt_out                          false
% 2.46/0.98  --trig_cnt_out_tolerance                1.
% 2.46/0.98  --trig_cnt_out_sk_spl                   false
% 2.46/0.98  --abstr_cl_out                          false
% 2.46/0.98  
% 2.46/0.98  ------ Global Options
% 2.46/0.98  
% 2.46/0.98  --schedule                              default
% 2.46/0.98  --add_important_lit                     false
% 2.46/0.98  --prop_solver_per_cl                    1000
% 2.46/0.98  --min_unsat_core                        false
% 2.46/0.98  --soft_assumptions                      false
% 2.46/0.98  --soft_lemma_size                       3
% 2.46/0.98  --prop_impl_unit_size                   0
% 2.46/0.98  --prop_impl_unit                        []
% 2.46/0.98  --share_sel_clauses                     true
% 2.46/0.98  --reset_solvers                         false
% 2.46/0.98  --bc_imp_inh                            [conj_cone]
% 2.46/0.98  --conj_cone_tolerance                   3.
% 2.46/0.98  --extra_neg_conj                        none
% 2.46/0.98  --large_theory_mode                     true
% 2.46/0.98  --prolific_symb_bound                   200
% 2.46/0.98  --lt_threshold                          2000
% 2.46/0.98  --clause_weak_htbl                      true
% 2.46/0.98  --gc_record_bc_elim                     false
% 2.46/0.98  
% 2.46/0.98  ------ Preprocessing Options
% 2.46/0.98  
% 2.46/0.98  --preprocessing_flag                    true
% 2.46/0.98  --time_out_prep_mult                    0.1
% 2.46/0.98  --splitting_mode                        input
% 2.46/0.98  --splitting_grd                         true
% 2.46/0.98  --splitting_cvd                         false
% 2.46/0.98  --splitting_cvd_svl                     false
% 2.46/0.98  --splitting_nvd                         32
% 2.46/0.98  --sub_typing                            true
% 2.46/0.98  --prep_gs_sim                           true
% 2.46/0.98  --prep_unflatten                        true
% 2.46/0.98  --prep_res_sim                          true
% 2.46/0.98  --prep_upred                            true
% 2.46/0.98  --prep_sem_filter                       exhaustive
% 2.46/0.98  --prep_sem_filter_out                   false
% 2.46/0.98  --pred_elim                             true
% 2.46/0.98  --res_sim_input                         true
% 2.46/0.98  --eq_ax_congr_red                       true
% 2.46/0.98  --pure_diseq_elim                       true
% 2.46/0.98  --brand_transform                       false
% 2.46/0.98  --non_eq_to_eq                          false
% 2.46/0.98  --prep_def_merge                        true
% 2.46/0.98  --prep_def_merge_prop_impl              false
% 2.46/0.98  --prep_def_merge_mbd                    true
% 2.46/0.98  --prep_def_merge_tr_red                 false
% 2.46/0.98  --prep_def_merge_tr_cl                  false
% 2.46/0.98  --smt_preprocessing                     true
% 2.46/0.98  --smt_ac_axioms                         fast
% 2.46/0.98  --preprocessed_out                      false
% 2.46/0.98  --preprocessed_stats                    false
% 2.46/0.98  
% 2.46/0.98  ------ Abstraction refinement Options
% 2.46/0.98  
% 2.46/0.98  --abstr_ref                             []
% 2.46/0.98  --abstr_ref_prep                        false
% 2.46/0.98  --abstr_ref_until_sat                   false
% 2.46/0.98  --abstr_ref_sig_restrict                funpre
% 2.46/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 2.46/0.98  --abstr_ref_under                       []
% 2.46/0.98  
% 2.46/0.98  ------ SAT Options
% 2.46/0.98  
% 2.46/0.98  --sat_mode                              false
% 2.46/0.98  --sat_fm_restart_options                ""
% 2.46/0.98  --sat_gr_def                            false
% 2.46/0.98  --sat_epr_types                         true
% 2.46/0.98  --sat_non_cyclic_types                  false
% 2.46/0.98  --sat_finite_models                     false
% 2.46/0.98  --sat_fm_lemmas                         false
% 2.46/0.98  --sat_fm_prep                           false
% 2.46/0.98  --sat_fm_uc_incr                        true
% 2.46/0.98  --sat_out_model                         small
% 2.46/0.98  --sat_out_clauses                       false
% 2.46/0.98  
% 2.46/0.98  ------ QBF Options
% 2.46/0.98  
% 2.46/0.98  --qbf_mode                              false
% 2.46/0.98  --qbf_elim_univ                         false
% 2.46/0.98  --qbf_dom_inst                          none
% 2.46/0.98  --qbf_dom_pre_inst                      false
% 2.46/0.98  --qbf_sk_in                             false
% 2.46/0.98  --qbf_pred_elim                         true
% 2.46/0.98  --qbf_split                             512
% 2.46/0.98  
% 2.46/0.98  ------ BMC1 Options
% 2.46/0.98  
% 2.46/0.98  --bmc1_incremental                      false
% 2.46/0.98  --bmc1_axioms                           reachable_all
% 2.46/0.98  --bmc1_min_bound                        0
% 2.46/0.98  --bmc1_max_bound                        -1
% 2.46/0.98  --bmc1_max_bound_default                -1
% 2.46/0.98  --bmc1_symbol_reachability              true
% 2.46/0.98  --bmc1_property_lemmas                  false
% 2.46/0.98  --bmc1_k_induction                      false
% 2.46/0.98  --bmc1_non_equiv_states                 false
% 2.46/0.98  --bmc1_deadlock                         false
% 2.46/0.98  --bmc1_ucm                              false
% 2.46/0.98  --bmc1_add_unsat_core                   none
% 2.46/0.98  --bmc1_unsat_core_children              false
% 2.46/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 2.46/0.98  --bmc1_out_stat                         full
% 2.46/0.98  --bmc1_ground_init                      false
% 2.46/0.98  --bmc1_pre_inst_next_state              false
% 2.46/0.98  --bmc1_pre_inst_state                   false
% 2.46/0.98  --bmc1_pre_inst_reach_state             false
% 2.46/0.98  --bmc1_out_unsat_core                   false
% 2.46/0.98  --bmc1_aig_witness_out                  false
% 2.46/0.98  --bmc1_verbose                          false
% 2.46/0.98  --bmc1_dump_clauses_tptp                false
% 2.46/0.98  --bmc1_dump_unsat_core_tptp             false
% 2.46/0.98  --bmc1_dump_file                        -
% 2.46/0.98  --bmc1_ucm_expand_uc_limit              128
% 2.46/0.98  --bmc1_ucm_n_expand_iterations          6
% 2.46/0.98  --bmc1_ucm_extend_mode                  1
% 2.46/0.98  --bmc1_ucm_init_mode                    2
% 2.46/0.98  --bmc1_ucm_cone_mode                    none
% 2.46/0.98  --bmc1_ucm_reduced_relation_type        0
% 2.46/0.98  --bmc1_ucm_relax_model                  4
% 2.46/0.98  --bmc1_ucm_full_tr_after_sat            true
% 2.46/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 2.46/0.98  --bmc1_ucm_layered_model                none
% 2.46/0.98  --bmc1_ucm_max_lemma_size               10
% 2.46/0.98  
% 2.46/0.98  ------ AIG Options
% 2.46/0.98  
% 2.46/0.98  --aig_mode                              false
% 2.46/0.98  
% 2.46/0.98  ------ Instantiation Options
% 2.46/0.98  
% 2.46/0.98  --instantiation_flag                    true
% 2.46/0.98  --inst_sos_flag                         false
% 2.46/0.98  --inst_sos_phase                        true
% 2.46/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.46/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.46/0.98  --inst_lit_sel_side                     num_symb
% 2.46/0.98  --inst_solver_per_active                1400
% 2.46/0.98  --inst_solver_calls_frac                1.
% 2.46/0.98  --inst_passive_queue_type               priority_queues
% 2.46/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.46/0.98  --inst_passive_queues_freq              [25;2]
% 2.46/0.98  --inst_dismatching                      true
% 2.46/0.98  --inst_eager_unprocessed_to_passive     true
% 2.46/0.98  --inst_prop_sim_given                   true
% 2.46/0.98  --inst_prop_sim_new                     false
% 2.46/0.98  --inst_subs_new                         false
% 2.46/0.98  --inst_eq_res_simp                      false
% 2.46/0.98  --inst_subs_given                       false
% 2.46/0.98  --inst_orphan_elimination               true
% 2.46/0.98  --inst_learning_loop_flag               true
% 2.46/0.98  --inst_learning_start                   3000
% 2.46/0.98  --inst_learning_factor                  2
% 2.46/0.98  --inst_start_prop_sim_after_learn       3
% 2.46/0.98  --inst_sel_renew                        solver
% 2.46/0.98  --inst_lit_activity_flag                true
% 2.46/0.98  --inst_restr_to_given                   false
% 2.46/0.98  --inst_activity_threshold               500
% 2.46/0.98  --inst_out_proof                        true
% 2.46/0.98  
% 2.46/0.98  ------ Resolution Options
% 2.46/0.98  
% 2.46/0.98  --resolution_flag                       true
% 2.46/0.98  --res_lit_sel                           adaptive
% 2.46/0.98  --res_lit_sel_side                      none
% 2.46/0.98  --res_ordering                          kbo
% 2.46/0.98  --res_to_prop_solver                    active
% 2.46/0.98  --res_prop_simpl_new                    false
% 2.46/0.98  --res_prop_simpl_given                  true
% 2.46/0.98  --res_passive_queue_type                priority_queues
% 2.46/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.46/0.98  --res_passive_queues_freq               [15;5]
% 2.46/0.98  --res_forward_subs                      full
% 2.46/0.98  --res_backward_subs                     full
% 2.46/0.98  --res_forward_subs_resolution           true
% 2.46/0.98  --res_backward_subs_resolution          true
% 2.46/0.98  --res_orphan_elimination                true
% 2.46/0.98  --res_time_limit                        2.
% 2.46/0.98  --res_out_proof                         true
% 2.46/0.98  
% 2.46/0.98  ------ Superposition Options
% 2.46/0.98  
% 2.46/0.98  --superposition_flag                    true
% 2.46/0.98  --sup_passive_queue_type                priority_queues
% 2.46/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.46/0.98  --sup_passive_queues_freq               [8;1;4]
% 2.46/0.98  --demod_completeness_check              fast
% 2.46/0.98  --demod_use_ground                      true
% 2.46/0.98  --sup_to_prop_solver                    passive
% 2.46/0.98  --sup_prop_simpl_new                    true
% 2.46/0.98  --sup_prop_simpl_given                  true
% 2.46/0.98  --sup_fun_splitting                     false
% 2.46/0.98  --sup_smt_interval                      50000
% 2.46/0.98  
% 2.46/0.98  ------ Superposition Simplification Setup
% 2.46/0.98  
% 2.46/0.98  --sup_indices_passive                   []
% 2.46/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.46/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.46/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.46/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 2.46/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.46/0.98  --sup_full_bw                           [BwDemod]
% 2.46/0.98  --sup_immed_triv                        [TrivRules]
% 2.46/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.46/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.46/0.98  --sup_immed_bw_main                     []
% 2.46/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.46/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 2.46/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.46/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.46/0.98  
% 2.46/0.98  ------ Combination Options
% 2.46/0.98  
% 2.46/0.98  --comb_res_mult                         3
% 2.46/0.98  --comb_sup_mult                         2
% 2.46/0.98  --comb_inst_mult                        10
% 2.46/0.98  
% 2.46/0.98  ------ Debug Options
% 2.46/0.98  
% 2.46/0.98  --dbg_backtrace                         false
% 2.46/0.98  --dbg_dump_prop_clauses                 false
% 2.46/0.98  --dbg_dump_prop_clauses_file            -
% 2.46/0.98  --dbg_out_stat                          false
% 2.46/0.98  ------ Parsing...
% 2.46/0.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.46/0.98  
% 2.46/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 2.46/0.98  
% 2.46/0.98  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.46/0.98  
% 2.46/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.46/0.98  ------ Proving...
% 2.46/0.98  ------ Problem Properties 
% 2.46/0.98  
% 2.46/0.98  
% 2.46/0.98  clauses                                 18
% 2.46/0.98  conjectures                             2
% 2.46/0.98  EPR                                     7
% 2.46/0.98  Horn                                    12
% 2.46/0.98  unary                                   4
% 2.46/0.98  binary                                  7
% 2.46/0.98  lits                                    41
% 2.46/0.98  lits eq                                 5
% 2.46/0.98  fd_pure                                 0
% 2.46/0.98  fd_pseudo                               0
% 2.46/0.98  fd_cond                                 0
% 2.46/0.98  fd_pseudo_cond                          5
% 2.46/0.98  AC symbols                              0
% 2.46/0.98  
% 2.46/0.98  ------ Schedule dynamic 5 is on 
% 2.46/0.98  
% 2.46/0.98  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.46/0.98  
% 2.46/0.98  
% 2.46/0.98  ------ 
% 2.46/0.98  Current options:
% 2.46/0.98  ------ 
% 2.46/0.98  
% 2.46/0.98  ------ Input Options
% 2.46/0.98  
% 2.46/0.98  --out_options                           all
% 2.46/0.98  --tptp_safe_out                         true
% 2.46/0.98  --problem_path                          ""
% 2.46/0.98  --include_path                          ""
% 2.46/0.98  --clausifier                            res/vclausify_rel
% 2.46/0.98  --clausifier_options                    --mode clausify
% 2.46/0.98  --stdin                                 false
% 2.46/0.98  --stats_out                             all
% 2.46/0.98  
% 2.46/0.98  ------ General Options
% 2.46/0.98  
% 2.46/0.98  --fof                                   false
% 2.46/0.98  --time_out_real                         305.
% 2.46/0.98  --time_out_virtual                      -1.
% 2.46/0.98  --symbol_type_check                     false
% 2.46/0.98  --clausify_out                          false
% 2.46/0.98  --sig_cnt_out                           false
% 2.46/0.98  --trig_cnt_out                          false
% 2.46/0.98  --trig_cnt_out_tolerance                1.
% 2.46/0.98  --trig_cnt_out_sk_spl                   false
% 2.46/0.98  --abstr_cl_out                          false
% 2.46/0.98  
% 2.46/0.98  ------ Global Options
% 2.46/0.98  
% 2.46/0.98  --schedule                              default
% 2.46/0.98  --add_important_lit                     false
% 2.46/0.98  --prop_solver_per_cl                    1000
% 2.46/0.98  --min_unsat_core                        false
% 2.46/0.98  --soft_assumptions                      false
% 2.46/0.98  --soft_lemma_size                       3
% 2.46/0.98  --prop_impl_unit_size                   0
% 2.46/0.98  --prop_impl_unit                        []
% 2.46/0.98  --share_sel_clauses                     true
% 2.46/0.98  --reset_solvers                         false
% 2.46/0.98  --bc_imp_inh                            [conj_cone]
% 2.46/0.98  --conj_cone_tolerance                   3.
% 2.46/0.98  --extra_neg_conj                        none
% 2.46/0.98  --large_theory_mode                     true
% 2.46/0.98  --prolific_symb_bound                   200
% 2.46/0.98  --lt_threshold                          2000
% 2.46/0.98  --clause_weak_htbl                      true
% 2.46/0.98  --gc_record_bc_elim                     false
% 2.46/0.98  
% 2.46/0.98  ------ Preprocessing Options
% 2.46/0.98  
% 2.46/0.98  --preprocessing_flag                    true
% 2.46/0.98  --time_out_prep_mult                    0.1
% 2.46/0.98  --splitting_mode                        input
% 2.46/0.98  --splitting_grd                         true
% 2.46/0.98  --splitting_cvd                         false
% 2.46/0.98  --splitting_cvd_svl                     false
% 2.46/0.98  --splitting_nvd                         32
% 2.46/0.98  --sub_typing                            true
% 2.46/0.98  --prep_gs_sim                           true
% 2.46/0.98  --prep_unflatten                        true
% 2.46/0.98  --prep_res_sim                          true
% 2.46/0.98  --prep_upred                            true
% 2.46/0.98  --prep_sem_filter                       exhaustive
% 2.46/0.98  --prep_sem_filter_out                   false
% 2.46/0.98  --pred_elim                             true
% 2.46/0.98  --res_sim_input                         true
% 2.46/0.98  --eq_ax_congr_red                       true
% 2.46/0.98  --pure_diseq_elim                       true
% 2.46/0.98  --brand_transform                       false
% 2.46/0.98  --non_eq_to_eq                          false
% 2.46/0.98  --prep_def_merge                        true
% 2.46/0.98  --prep_def_merge_prop_impl              false
% 2.46/0.98  --prep_def_merge_mbd                    true
% 2.46/0.98  --prep_def_merge_tr_red                 false
% 2.46/0.98  --prep_def_merge_tr_cl                  false
% 2.46/0.98  --smt_preprocessing                     true
% 2.46/0.98  --smt_ac_axioms                         fast
% 2.46/0.98  --preprocessed_out                      false
% 2.46/0.98  --preprocessed_stats                    false
% 2.46/0.98  
% 2.46/0.98  ------ Abstraction refinement Options
% 2.46/0.98  
% 2.46/0.98  --abstr_ref                             []
% 2.46/0.98  --abstr_ref_prep                        false
% 2.46/0.98  --abstr_ref_until_sat                   false
% 2.46/0.98  --abstr_ref_sig_restrict                funpre
% 2.46/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 2.46/0.98  --abstr_ref_under                       []
% 2.46/0.98  
% 2.46/0.98  ------ SAT Options
% 2.46/0.98  
% 2.46/0.98  --sat_mode                              false
% 2.46/0.98  --sat_fm_restart_options                ""
% 2.46/0.98  --sat_gr_def                            false
% 2.46/0.98  --sat_epr_types                         true
% 2.46/0.98  --sat_non_cyclic_types                  false
% 2.46/0.98  --sat_finite_models                     false
% 2.46/0.98  --sat_fm_lemmas                         false
% 2.46/0.98  --sat_fm_prep                           false
% 2.46/0.98  --sat_fm_uc_incr                        true
% 2.46/0.98  --sat_out_model                         small
% 2.46/0.98  --sat_out_clauses                       false
% 2.46/0.98  
% 2.46/0.98  ------ QBF Options
% 2.46/0.98  
% 2.46/0.98  --qbf_mode                              false
% 2.46/0.98  --qbf_elim_univ                         false
% 2.46/0.98  --qbf_dom_inst                          none
% 2.46/0.98  --qbf_dom_pre_inst                      false
% 2.46/0.98  --qbf_sk_in                             false
% 2.46/0.98  --qbf_pred_elim                         true
% 2.46/0.98  --qbf_split                             512
% 2.46/0.98  
% 2.46/0.98  ------ BMC1 Options
% 2.46/0.98  
% 2.46/0.98  --bmc1_incremental                      false
% 2.46/0.98  --bmc1_axioms                           reachable_all
% 2.46/0.98  --bmc1_min_bound                        0
% 2.46/0.98  --bmc1_max_bound                        -1
% 2.46/0.98  --bmc1_max_bound_default                -1
% 2.46/0.98  --bmc1_symbol_reachability              true
% 2.46/0.98  --bmc1_property_lemmas                  false
% 2.46/0.98  --bmc1_k_induction                      false
% 2.46/0.98  --bmc1_non_equiv_states                 false
% 2.46/0.98  --bmc1_deadlock                         false
% 2.46/0.98  --bmc1_ucm                              false
% 2.46/0.98  --bmc1_add_unsat_core                   none
% 2.46/0.98  --bmc1_unsat_core_children              false
% 2.46/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 2.46/0.98  --bmc1_out_stat                         full
% 2.46/0.98  --bmc1_ground_init                      false
% 2.46/0.98  --bmc1_pre_inst_next_state              false
% 2.46/0.98  --bmc1_pre_inst_state                   false
% 2.46/0.98  --bmc1_pre_inst_reach_state             false
% 2.46/0.98  --bmc1_out_unsat_core                   false
% 2.46/0.98  --bmc1_aig_witness_out                  false
% 2.46/0.98  --bmc1_verbose                          false
% 2.46/0.98  --bmc1_dump_clauses_tptp                false
% 2.46/0.98  --bmc1_dump_unsat_core_tptp             false
% 2.46/0.98  --bmc1_dump_file                        -
% 2.46/0.98  --bmc1_ucm_expand_uc_limit              128
% 2.46/0.98  --bmc1_ucm_n_expand_iterations          6
% 2.46/0.98  --bmc1_ucm_extend_mode                  1
% 2.46/0.98  --bmc1_ucm_init_mode                    2
% 2.46/0.98  --bmc1_ucm_cone_mode                    none
% 2.46/0.98  --bmc1_ucm_reduced_relation_type        0
% 2.46/0.98  --bmc1_ucm_relax_model                  4
% 2.46/0.98  --bmc1_ucm_full_tr_after_sat            true
% 2.46/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 2.46/0.98  --bmc1_ucm_layered_model                none
% 2.46/0.98  --bmc1_ucm_max_lemma_size               10
% 2.46/0.98  
% 2.46/0.98  ------ AIG Options
% 2.46/0.98  
% 2.46/0.98  --aig_mode                              false
% 2.46/0.98  
% 2.46/0.98  ------ Instantiation Options
% 2.46/0.98  
% 2.46/0.98  --instantiation_flag                    true
% 2.46/0.98  --inst_sos_flag                         false
% 2.46/0.98  --inst_sos_phase                        true
% 2.46/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.46/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.46/0.98  --inst_lit_sel_side                     none
% 2.46/0.98  --inst_solver_per_active                1400
% 2.46/0.98  --inst_solver_calls_frac                1.
% 2.46/0.98  --inst_passive_queue_type               priority_queues
% 2.46/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.46/0.98  --inst_passive_queues_freq              [25;2]
% 2.46/0.98  --inst_dismatching                      true
% 2.46/0.98  --inst_eager_unprocessed_to_passive     true
% 2.46/0.98  --inst_prop_sim_given                   true
% 2.46/0.98  --inst_prop_sim_new                     false
% 2.46/0.98  --inst_subs_new                         false
% 2.46/0.98  --inst_eq_res_simp                      false
% 2.46/0.98  --inst_subs_given                       false
% 2.46/0.98  --inst_orphan_elimination               true
% 2.46/0.98  --inst_learning_loop_flag               true
% 2.46/0.98  --inst_learning_start                   3000
% 2.46/0.98  --inst_learning_factor                  2
% 2.46/0.98  --inst_start_prop_sim_after_learn       3
% 2.46/0.98  --inst_sel_renew                        solver
% 2.46/0.98  --inst_lit_activity_flag                true
% 2.46/0.98  --inst_restr_to_given                   false
% 2.46/0.98  --inst_activity_threshold               500
% 2.46/0.98  --inst_out_proof                        true
% 2.46/0.98  
% 2.46/0.98  ------ Resolution Options
% 2.46/0.98  
% 2.46/0.98  --resolution_flag                       false
% 2.46/0.98  --res_lit_sel                           adaptive
% 2.46/0.98  --res_lit_sel_side                      none
% 2.46/0.98  --res_ordering                          kbo
% 2.46/0.98  --res_to_prop_solver                    active
% 2.46/0.98  --res_prop_simpl_new                    false
% 2.46/0.98  --res_prop_simpl_given                  true
% 2.46/0.98  --res_passive_queue_type                priority_queues
% 2.46/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.46/0.98  --res_passive_queues_freq               [15;5]
% 2.46/0.98  --res_forward_subs                      full
% 2.46/0.98  --res_backward_subs                     full
% 2.46/0.98  --res_forward_subs_resolution           true
% 2.46/0.98  --res_backward_subs_resolution          true
% 2.46/0.98  --res_orphan_elimination                true
% 2.46/0.98  --res_time_limit                        2.
% 2.46/0.98  --res_out_proof                         true
% 2.46/0.98  
% 2.46/0.98  ------ Superposition Options
% 2.46/0.98  
% 2.46/0.98  --superposition_flag                    true
% 2.46/0.98  --sup_passive_queue_type                priority_queues
% 2.46/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.46/0.98  --sup_passive_queues_freq               [8;1;4]
% 2.46/0.98  --demod_completeness_check              fast
% 2.46/0.98  --demod_use_ground                      true
% 2.46/0.98  --sup_to_prop_solver                    passive
% 2.46/0.98  --sup_prop_simpl_new                    true
% 2.46/0.98  --sup_prop_simpl_given                  true
% 2.46/0.98  --sup_fun_splitting                     false
% 2.46/0.98  --sup_smt_interval                      50000
% 2.46/0.98  
% 2.46/0.98  ------ Superposition Simplification Setup
% 2.46/0.98  
% 2.46/0.98  --sup_indices_passive                   []
% 2.46/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.46/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.46/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.46/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 2.46/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.46/0.98  --sup_full_bw                           [BwDemod]
% 2.46/0.98  --sup_immed_triv                        [TrivRules]
% 2.46/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.46/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.46/0.98  --sup_immed_bw_main                     []
% 2.46/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.46/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 2.46/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.46/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.46/0.98  
% 2.46/0.98  ------ Combination Options
% 2.46/0.98  
% 2.46/0.98  --comb_res_mult                         3
% 2.46/0.98  --comb_sup_mult                         2
% 2.46/0.98  --comb_inst_mult                        10
% 2.46/0.98  
% 2.46/0.98  ------ Debug Options
% 2.46/0.98  
% 2.46/0.98  --dbg_backtrace                         false
% 2.46/0.98  --dbg_dump_prop_clauses                 false
% 2.46/0.98  --dbg_dump_prop_clauses_file            -
% 2.46/0.98  --dbg_out_stat                          false
% 2.46/0.98  
% 2.46/0.98  
% 2.46/0.98  
% 2.46/0.98  
% 2.46/0.98  ------ Proving...
% 2.46/0.98  
% 2.46/0.98  
% 2.46/0.98  % SZS status Theorem for theBenchmark.p
% 2.46/0.98  
% 2.46/0.98  % SZS output start CNFRefutation for theBenchmark.p
% 2.46/0.98  
% 2.46/0.98  fof(f10,axiom,(
% 2.46/0.98    ! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => (r2_hidden(X1,X0) | r1_ordinal1(X0,X1))))),
% 2.46/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.46/0.98  
% 2.46/0.98  fof(f16,plain,(
% 2.46/0.98    ! [X0] : (! [X1] : ((r2_hidden(X1,X0) | r1_ordinal1(X0,X1)) | ~v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 2.46/0.98    inference(ennf_transformation,[],[f10])).
% 2.46/0.98  
% 2.46/0.98  fof(f17,plain,(
% 2.46/0.98    ! [X0] : (! [X1] : (r2_hidden(X1,X0) | r1_ordinal1(X0,X1) | ~v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 2.46/0.98    inference(flattening,[],[f16])).
% 2.46/0.98  
% 2.46/0.98  fof(f53,plain,(
% 2.46/0.98    ( ! [X0,X1] : (r2_hidden(X1,X0) | r1_ordinal1(X0,X1) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0)) )),
% 2.46/0.98    inference(cnf_transformation,[],[f17])).
% 2.46/0.98  
% 2.46/0.98  fof(f8,axiom,(
% 2.46/0.98    ! [X0,X1] : ((v3_ordinal1(X1) & v3_ordinal1(X0)) => (r1_ordinal1(X0,X1) <=> r1_tarski(X0,X1)))),
% 2.46/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.46/0.98  
% 2.46/0.98  fof(f14,plain,(
% 2.46/0.98    ! [X0,X1] : ((r1_ordinal1(X0,X1) <=> r1_tarski(X0,X1)) | (~v3_ordinal1(X1) | ~v3_ordinal1(X0)))),
% 2.46/0.98    inference(ennf_transformation,[],[f8])).
% 2.46/0.98  
% 2.46/0.98  fof(f15,plain,(
% 2.46/0.98    ! [X0,X1] : ((r1_ordinal1(X0,X1) <=> r1_tarski(X0,X1)) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0))),
% 2.46/0.98    inference(flattening,[],[f14])).
% 2.46/0.98  
% 2.46/0.98  fof(f26,plain,(
% 2.46/0.98    ! [X0,X1] : (((r1_ordinal1(X0,X1) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~r1_ordinal1(X0,X1))) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0))),
% 2.46/0.98    inference(nnf_transformation,[],[f15])).
% 2.46/0.98  
% 2.46/0.98  fof(f48,plain,(
% 2.46/0.98    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r1_ordinal1(X0,X1) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0)) )),
% 2.46/0.98    inference(cnf_transformation,[],[f26])).
% 2.46/0.98  
% 2.46/0.98  fof(f11,conjecture,(
% 2.46/0.98    ! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => (r2_hidden(X0,k1_ordinal1(X1)) <=> r1_ordinal1(X0,X1))))),
% 2.46/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.46/0.98  
% 2.46/0.98  fof(f12,negated_conjecture,(
% 2.46/0.98    ~! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => (r2_hidden(X0,k1_ordinal1(X1)) <=> r1_ordinal1(X0,X1))))),
% 2.46/0.98    inference(negated_conjecture,[],[f11])).
% 2.46/0.98  
% 2.46/0.98  fof(f18,plain,(
% 2.46/0.98    ? [X0] : (? [X1] : ((r2_hidden(X0,k1_ordinal1(X1)) <~> r1_ordinal1(X0,X1)) & v3_ordinal1(X1)) & v3_ordinal1(X0))),
% 2.46/0.98    inference(ennf_transformation,[],[f12])).
% 2.46/0.98  
% 2.46/0.98  fof(f29,plain,(
% 2.46/0.98    ? [X0] : (? [X1] : (((~r1_ordinal1(X0,X1) | ~r2_hidden(X0,k1_ordinal1(X1))) & (r1_ordinal1(X0,X1) | r2_hidden(X0,k1_ordinal1(X1)))) & v3_ordinal1(X1)) & v3_ordinal1(X0))),
% 2.46/0.98    inference(nnf_transformation,[],[f18])).
% 2.46/0.98  
% 2.46/0.98  fof(f30,plain,(
% 2.46/0.98    ? [X0] : (? [X1] : ((~r1_ordinal1(X0,X1) | ~r2_hidden(X0,k1_ordinal1(X1))) & (r1_ordinal1(X0,X1) | r2_hidden(X0,k1_ordinal1(X1))) & v3_ordinal1(X1)) & v3_ordinal1(X0))),
% 2.46/0.98    inference(flattening,[],[f29])).
% 2.46/0.98  
% 2.46/0.98  fof(f32,plain,(
% 2.46/0.98    ( ! [X0] : (? [X1] : ((~r1_ordinal1(X0,X1) | ~r2_hidden(X0,k1_ordinal1(X1))) & (r1_ordinal1(X0,X1) | r2_hidden(X0,k1_ordinal1(X1))) & v3_ordinal1(X1)) => ((~r1_ordinal1(X0,sK2) | ~r2_hidden(X0,k1_ordinal1(sK2))) & (r1_ordinal1(X0,sK2) | r2_hidden(X0,k1_ordinal1(sK2))) & v3_ordinal1(sK2))) )),
% 2.46/0.98    introduced(choice_axiom,[])).
% 2.46/0.98  
% 2.46/0.98  fof(f31,plain,(
% 2.46/0.98    ? [X0] : (? [X1] : ((~r1_ordinal1(X0,X1) | ~r2_hidden(X0,k1_ordinal1(X1))) & (r1_ordinal1(X0,X1) | r2_hidden(X0,k1_ordinal1(X1))) & v3_ordinal1(X1)) & v3_ordinal1(X0)) => (? [X1] : ((~r1_ordinal1(sK1,X1) | ~r2_hidden(sK1,k1_ordinal1(X1))) & (r1_ordinal1(sK1,X1) | r2_hidden(sK1,k1_ordinal1(X1))) & v3_ordinal1(X1)) & v3_ordinal1(sK1))),
% 2.46/0.98    introduced(choice_axiom,[])).
% 2.46/0.98  
% 2.46/0.98  fof(f33,plain,(
% 2.46/0.98    ((~r1_ordinal1(sK1,sK2) | ~r2_hidden(sK1,k1_ordinal1(sK2))) & (r1_ordinal1(sK1,sK2) | r2_hidden(sK1,k1_ordinal1(sK2))) & v3_ordinal1(sK2)) & v3_ordinal1(sK1)),
% 2.46/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f30,f32,f31])).
% 2.46/0.98  
% 2.46/0.98  fof(f56,plain,(
% 2.46/0.98    r1_ordinal1(sK1,sK2) | r2_hidden(sK1,k1_ordinal1(sK2))),
% 2.46/0.98    inference(cnf_transformation,[],[f33])).
% 2.46/0.98  
% 2.46/0.98  fof(f7,axiom,(
% 2.46/0.98    ! [X0] : k2_xboole_0(X0,k1_tarski(X0)) = k1_ordinal1(X0)),
% 2.46/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.46/0.98  
% 2.46/0.98  fof(f47,plain,(
% 2.46/0.98    ( ! [X0] : (k2_xboole_0(X0,k1_tarski(X0)) = k1_ordinal1(X0)) )),
% 2.46/0.98    inference(cnf_transformation,[],[f7])).
% 2.46/0.98  
% 2.46/0.98  fof(f6,axiom,(
% 2.46/0.98    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 2.46/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.46/0.98  
% 2.46/0.98  fof(f46,plain,(
% 2.46/0.98    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 2.46/0.98    inference(cnf_transformation,[],[f6])).
% 2.46/0.98  
% 2.46/0.98  fof(f58,plain,(
% 2.46/0.98    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k1_enumset1(X0,X0,X1))) )),
% 2.46/0.98    inference(definition_unfolding,[],[f46,f45])).
% 2.46/0.98  
% 2.46/0.98  fof(f4,axiom,(
% 2.46/0.98    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 2.46/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.46/0.98  
% 2.46/0.98  fof(f44,plain,(
% 2.46/0.98    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 2.46/0.98    inference(cnf_transformation,[],[f4])).
% 2.46/0.98  
% 2.46/0.98  fof(f5,axiom,(
% 2.46/0.98    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 2.46/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.46/0.98  
% 2.46/0.98  fof(f45,plain,(
% 2.46/0.98    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 2.46/0.98    inference(cnf_transformation,[],[f5])).
% 2.46/0.98  
% 2.46/0.98  fof(f59,plain,(
% 2.46/0.98    ( ! [X0] : (k1_tarski(X0) = k1_enumset1(X0,X0,X0)) )),
% 2.46/0.98    inference(definition_unfolding,[],[f44,f45])).
% 2.46/0.98  
% 2.46/0.98  fof(f60,plain,(
% 2.46/0.98    ( ! [X0] : (k3_tarski(k1_enumset1(X0,X0,k1_enumset1(X0,X0,X0))) = k1_ordinal1(X0)) )),
% 2.46/0.98    inference(definition_unfolding,[],[f47,f58,f59])).
% 2.46/0.98  
% 2.46/0.98  fof(f71,plain,(
% 2.46/0.98    r1_ordinal1(sK1,sK2) | r2_hidden(sK1,k3_tarski(k1_enumset1(sK2,sK2,k1_enumset1(sK2,sK2,sK2))))),
% 2.46/0.98    inference(definition_unfolding,[],[f56,f60])).
% 2.46/0.98  
% 2.46/0.98  fof(f54,plain,(
% 2.46/0.98    v3_ordinal1(sK1)),
% 2.46/0.98    inference(cnf_transformation,[],[f33])).
% 2.46/0.98  
% 2.46/0.98  fof(f55,plain,(
% 2.46/0.98    v3_ordinal1(sK2)),
% 2.46/0.98    inference(cnf_transformation,[],[f33])).
% 2.46/0.98  
% 2.46/0.98  fof(f9,axiom,(
% 2.46/0.98    ! [X0,X1] : (r2_hidden(X0,k1_ordinal1(X1)) <=> (X0 = X1 | r2_hidden(X0,X1)))),
% 2.46/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.46/0.98  
% 2.46/0.98  fof(f27,plain,(
% 2.46/0.98    ! [X0,X1] : ((r2_hidden(X0,k1_ordinal1(X1)) | (X0 != X1 & ~r2_hidden(X0,X1))) & ((X0 = X1 | r2_hidden(X0,X1)) | ~r2_hidden(X0,k1_ordinal1(X1))))),
% 2.46/0.98    inference(nnf_transformation,[],[f9])).
% 2.46/0.98  
% 2.46/0.98  fof(f28,plain,(
% 2.46/0.98    ! [X0,X1] : ((r2_hidden(X0,k1_ordinal1(X1)) | (X0 != X1 & ~r2_hidden(X0,X1))) & (X0 = X1 | r2_hidden(X0,X1) | ~r2_hidden(X0,k1_ordinal1(X1))))),
% 2.46/0.98    inference(flattening,[],[f27])).
% 2.46/0.98  
% 2.46/0.98  fof(f50,plain,(
% 2.46/0.98    ( ! [X0,X1] : (X0 = X1 | r2_hidden(X0,X1) | ~r2_hidden(X0,k1_ordinal1(X1))) )),
% 2.46/0.98    inference(cnf_transformation,[],[f28])).
% 2.46/0.98  
% 2.46/0.98  fof(f69,plain,(
% 2.46/0.98    ( ! [X0,X1] : (X0 = X1 | r2_hidden(X0,X1) | ~r2_hidden(X0,k3_tarski(k1_enumset1(X1,X1,k1_enumset1(X1,X1,X1))))) )),
% 2.46/0.98    inference(definition_unfolding,[],[f50,f60])).
% 2.46/0.98  
% 2.46/0.98  fof(f3,axiom,(
% 2.46/0.98    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 2.46/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.46/0.98  
% 2.46/0.98  fof(f24,plain,(
% 2.46/0.98    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.46/0.98    inference(nnf_transformation,[],[f3])).
% 2.46/0.98  
% 2.46/0.98  fof(f25,plain,(
% 2.46/0.98    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.46/0.98    inference(flattening,[],[f24])).
% 2.46/0.98  
% 2.46/0.98  fof(f41,plain,(
% 2.46/0.98    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 2.46/0.98    inference(cnf_transformation,[],[f25])).
% 2.46/0.98  
% 2.46/0.98  fof(f76,plain,(
% 2.46/0.98    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 2.46/0.98    inference(equality_resolution,[],[f41])).
% 2.46/0.98  
% 2.46/0.98  fof(f43,plain,(
% 2.46/0.98    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 2.46/0.98    inference(cnf_transformation,[],[f25])).
% 2.46/0.98  
% 2.46/0.98  fof(f2,axiom,(
% 2.46/0.98    ! [X0,X1,X2] : (k2_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) | r2_hidden(X3,X0))))),
% 2.46/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.46/0.98  
% 2.46/0.98  fof(f19,plain,(
% 2.46/0.98    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) | r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) & ~r2_hidden(X3,X0))) & ((r2_hidden(X3,X1) | r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k2_xboole_0(X0,X1) != X2))),
% 2.46/0.98    inference(nnf_transformation,[],[f2])).
% 2.46/0.98  
% 2.46/0.98  fof(f20,plain,(
% 2.46/0.98    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) & ~r2_hidden(X3,X0))) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | ~r2_hidden(X3,X2))) | k2_xboole_0(X0,X1) != X2))),
% 2.46/0.98    inference(flattening,[],[f19])).
% 2.46/0.98  
% 2.46/0.98  fof(f21,plain,(
% 2.46/0.98    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (~r2_hidden(X4,X1) & ~r2_hidden(X4,X0))) & (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,X2))) | k2_xboole_0(X0,X1) != X2))),
% 2.46/0.98    inference(rectify,[],[f20])).
% 2.46/0.98  
% 2.46/0.98  fof(f22,plain,(
% 2.46/0.98    ! [X2,X1,X0] : (? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2))) => (((~r2_hidden(sK0(X0,X1,X2),X1) & ~r2_hidden(sK0(X0,X1,X2),X0)) | ~r2_hidden(sK0(X0,X1,X2),X2)) & (r2_hidden(sK0(X0,X1,X2),X1) | r2_hidden(sK0(X0,X1,X2),X0) | r2_hidden(sK0(X0,X1,X2),X2))))),
% 2.46/0.98    introduced(choice_axiom,[])).
% 2.46/0.98  
% 2.46/0.98  fof(f23,plain,(
% 2.46/0.98    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | (((~r2_hidden(sK0(X0,X1,X2),X1) & ~r2_hidden(sK0(X0,X1,X2),X0)) | ~r2_hidden(sK0(X0,X1,X2),X2)) & (r2_hidden(sK0(X0,X1,X2),X1) | r2_hidden(sK0(X0,X1,X2),X0) | r2_hidden(sK0(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (~r2_hidden(X4,X1) & ~r2_hidden(X4,X0))) & (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,X2))) | k2_xboole_0(X0,X1) != X2))),
% 2.46/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f21,f22])).
% 2.46/0.98  
% 2.46/0.98  fof(f36,plain,(
% 2.46/0.98    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | ~r2_hidden(X4,X0) | k2_xboole_0(X0,X1) != X2) )),
% 2.46/0.98    inference(cnf_transformation,[],[f23])).
% 2.46/0.98  
% 2.46/0.98  fof(f65,plain,(
% 2.46/0.98    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | ~r2_hidden(X4,X0) | k3_tarski(k1_enumset1(X0,X0,X1)) != X2) )),
% 2.46/0.98    inference(definition_unfolding,[],[f36,f58])).
% 2.46/0.98  
% 2.46/0.98  fof(f73,plain,(
% 2.46/0.98    ( ! [X4,X0,X1] : (r2_hidden(X4,k3_tarski(k1_enumset1(X0,X0,X1))) | ~r2_hidden(X4,X0)) )),
% 2.46/0.98    inference(equality_resolution,[],[f65])).
% 2.46/0.98  
% 2.46/0.98  fof(f49,plain,(
% 2.46/0.98    ( ! [X0,X1] : (r1_ordinal1(X0,X1) | ~r1_tarski(X0,X1) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0)) )),
% 2.46/0.98    inference(cnf_transformation,[],[f26])).
% 2.46/0.98  
% 2.46/0.98  fof(f57,plain,(
% 2.46/0.98    ~r1_ordinal1(sK1,sK2) | ~r2_hidden(sK1,k1_ordinal1(sK2))),
% 2.46/0.98    inference(cnf_transformation,[],[f33])).
% 2.46/0.98  
% 2.46/0.98  fof(f70,plain,(
% 2.46/0.98    ~r1_ordinal1(sK1,sK2) | ~r2_hidden(sK1,k3_tarski(k1_enumset1(sK2,sK2,k1_enumset1(sK2,sK2,sK2))))),
% 2.46/0.98    inference(definition_unfolding,[],[f57,f60])).
% 2.46/0.98  
% 2.46/0.98  fof(f1,axiom,(
% 2.46/0.98    ! [X0,X1] : (r2_hidden(X0,X1) => ~r2_hidden(X1,X0))),
% 2.46/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.46/0.98  
% 2.46/0.98  fof(f13,plain,(
% 2.46/0.98    ! [X0,X1] : (~r2_hidden(X1,X0) | ~r2_hidden(X0,X1))),
% 2.46/0.98    inference(ennf_transformation,[],[f1])).
% 2.46/0.98  
% 2.46/0.98  fof(f34,plain,(
% 2.46/0.98    ( ! [X0,X1] : (~r2_hidden(X1,X0) | ~r2_hidden(X0,X1)) )),
% 2.46/0.98    inference(cnf_transformation,[],[f13])).
% 2.46/0.98  
% 2.46/0.98  fof(f51,plain,(
% 2.46/0.98    ( ! [X0,X1] : (r2_hidden(X0,k1_ordinal1(X1)) | ~r2_hidden(X0,X1)) )),
% 2.46/0.98    inference(cnf_transformation,[],[f28])).
% 2.46/0.98  
% 2.46/0.98  fof(f68,plain,(
% 2.46/0.98    ( ! [X0,X1] : (r2_hidden(X0,k3_tarski(k1_enumset1(X1,X1,k1_enumset1(X1,X1,X1)))) | ~r2_hidden(X0,X1)) )),
% 2.46/0.98    inference(definition_unfolding,[],[f51,f60])).
% 2.46/0.98  
% 2.46/0.98  fof(f52,plain,(
% 2.46/0.98    ( ! [X0,X1] : (r2_hidden(X0,k1_ordinal1(X1)) | X0 != X1) )),
% 2.46/0.98    inference(cnf_transformation,[],[f28])).
% 2.46/0.98  
% 2.46/0.98  fof(f67,plain,(
% 2.46/0.98    ( ! [X0,X1] : (r2_hidden(X0,k3_tarski(k1_enumset1(X1,X1,k1_enumset1(X1,X1,X1)))) | X0 != X1) )),
% 2.46/0.98    inference(definition_unfolding,[],[f52,f60])).
% 2.46/0.98  
% 2.46/0.98  fof(f77,plain,(
% 2.46/0.98    ( ! [X1] : (r2_hidden(X1,k3_tarski(k1_enumset1(X1,X1,k1_enumset1(X1,X1,X1))))) )),
% 2.46/0.98    inference(equality_resolution,[],[f67])).
% 2.46/0.98  
% 2.46/0.98  fof(f35,plain,(
% 2.46/0.98    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,X2) | k2_xboole_0(X0,X1) != X2) )),
% 2.46/0.98    inference(cnf_transformation,[],[f23])).
% 2.46/0.98  
% 2.46/0.98  fof(f66,plain,(
% 2.46/0.98    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,X2) | k3_tarski(k1_enumset1(X0,X0,X1)) != X2) )),
% 2.46/0.98    inference(definition_unfolding,[],[f35,f58])).
% 2.46/0.98  
% 2.46/0.98  fof(f74,plain,(
% 2.46/0.98    ( ! [X4,X0,X1] : (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,k3_tarski(k1_enumset1(X0,X0,X1)))) )),
% 2.46/0.98    inference(equality_resolution,[],[f66])).
% 2.46/0.98  
% 2.46/0.98  fof(f37,plain,(
% 2.46/0.98    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | k2_xboole_0(X0,X1) != X2) )),
% 2.46/0.98    inference(cnf_transformation,[],[f23])).
% 2.46/0.98  
% 2.46/0.98  fof(f64,plain,(
% 2.46/0.98    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | k3_tarski(k1_enumset1(X0,X0,X1)) != X2) )),
% 2.46/0.98    inference(definition_unfolding,[],[f37,f58])).
% 2.46/0.98  
% 2.46/0.98  fof(f72,plain,(
% 2.46/0.98    ( ! [X4,X0,X1] : (r2_hidden(X4,k3_tarski(k1_enumset1(X0,X0,X1))) | ~r2_hidden(X4,X1)) )),
% 2.46/0.98    inference(equality_resolution,[],[f64])).
% 2.46/0.98  
% 2.46/0.98  cnf(c_15,plain,
% 2.46/0.98      ( r1_ordinal1(X0,X1)
% 2.46/0.98      | r2_hidden(X1,X0)
% 2.46/0.98      | ~ v3_ordinal1(X1)
% 2.46/0.98      | ~ v3_ordinal1(X0) ),
% 2.46/0.98      inference(cnf_transformation,[],[f53]) ).
% 2.46/0.98  
% 2.46/0.98  cnf(c_11,plain,
% 2.46/0.98      ( ~ r1_ordinal1(X0,X1)
% 2.46/0.98      | r1_tarski(X0,X1)
% 2.46/0.98      | ~ v3_ordinal1(X1)
% 2.46/0.98      | ~ v3_ordinal1(X0) ),
% 2.46/0.98      inference(cnf_transformation,[],[f48]) ).
% 2.46/0.98  
% 2.46/0.98  cnf(c_256,plain,
% 2.46/0.98      ( r1_tarski(X0,X1)
% 2.46/0.98      | r2_hidden(X1,X0)
% 2.46/0.98      | ~ v3_ordinal1(X0)
% 2.46/0.98      | ~ v3_ordinal1(X1) ),
% 2.46/0.98      inference(resolution,[status(thm)],[c_15,c_11]) ).
% 2.46/0.98  
% 2.46/0.98  cnf(c_922,plain,
% 2.46/0.98      ( r1_tarski(X0,X1) = iProver_top
% 2.46/0.98      | r2_hidden(X1,X0) = iProver_top
% 2.46/0.98      | v3_ordinal1(X1) != iProver_top
% 2.46/0.98      | v3_ordinal1(X0) != iProver_top ),
% 2.46/0.98      inference(predicate_to_equality,[status(thm)],[c_256]) ).
% 2.46/0.98  
% 2.46/0.98  cnf(c_17,negated_conjecture,
% 2.46/0.98      ( r1_ordinal1(sK1,sK2)
% 2.46/0.98      | r2_hidden(sK1,k3_tarski(k1_enumset1(sK2,sK2,k1_enumset1(sK2,sK2,sK2)))) ),
% 2.46/0.98      inference(cnf_transformation,[],[f71]) ).
% 2.46/0.98  
% 2.46/0.98  cnf(c_153,plain,
% 2.46/0.98      ( r1_ordinal1(sK1,sK2)
% 2.46/0.98      | r2_hidden(sK1,k3_tarski(k1_enumset1(sK2,sK2,k1_enumset1(sK2,sK2,sK2)))) ),
% 2.46/0.98      inference(prop_impl,[status(thm)],[c_17]) ).
% 2.46/0.98  
% 2.46/0.98  cnf(c_301,plain,
% 2.46/0.98      ( r1_tarski(X0,X1)
% 2.46/0.98      | r2_hidden(sK1,k3_tarski(k1_enumset1(sK2,sK2,k1_enumset1(sK2,sK2,sK2))))
% 2.46/0.98      | ~ v3_ordinal1(X0)
% 2.46/0.98      | ~ v3_ordinal1(X1)
% 2.46/0.98      | sK2 != X1
% 2.46/0.98      | sK1 != X0 ),
% 2.46/0.98      inference(resolution_lifted,[status(thm)],[c_11,c_153]) ).
% 2.46/0.98  
% 2.46/0.98  cnf(c_302,plain,
% 2.46/0.98      ( r1_tarski(sK1,sK2)
% 2.46/0.98      | r2_hidden(sK1,k3_tarski(k1_enumset1(sK2,sK2,k1_enumset1(sK2,sK2,sK2))))
% 2.46/0.98      | ~ v3_ordinal1(sK2)
% 2.46/0.98      | ~ v3_ordinal1(sK1) ),
% 2.46/0.98      inference(unflattening,[status(thm)],[c_301]) ).
% 2.46/0.98  
% 2.46/0.98  cnf(c_19,negated_conjecture,
% 2.46/0.98      ( v3_ordinal1(sK1) ),
% 2.46/0.98      inference(cnf_transformation,[],[f54]) ).
% 2.46/0.98  
% 2.46/0.98  cnf(c_18,negated_conjecture,
% 2.46/0.98      ( v3_ordinal1(sK2) ),
% 2.46/0.98      inference(cnf_transformation,[],[f55]) ).
% 2.46/0.98  
% 2.46/0.98  cnf(c_304,plain,
% 2.46/0.98      ( r1_tarski(sK1,sK2)
% 2.46/0.98      | r2_hidden(sK1,k3_tarski(k1_enumset1(sK2,sK2,k1_enumset1(sK2,sK2,sK2)))) ),
% 2.46/0.98      inference(global_propositional_subsumption,
% 2.46/0.98                [status(thm)],
% 2.46/0.98                [c_302,c_19,c_18]) ).
% 2.46/0.98  
% 2.46/0.98  cnf(c_392,plain,
% 2.46/0.98      ( r1_tarski(sK1,sK2)
% 2.46/0.98      | r2_hidden(sK1,k3_tarski(k1_enumset1(sK2,sK2,k1_enumset1(sK2,sK2,sK2)))) ),
% 2.46/0.98      inference(prop_impl,[status(thm)],[c_19,c_18,c_302]) ).
% 2.46/0.98  
% 2.46/0.98  cnf(c_920,plain,
% 2.46/0.98      ( r1_tarski(sK1,sK2) = iProver_top
% 2.46/0.98      | r2_hidden(sK1,k3_tarski(k1_enumset1(sK2,sK2,k1_enumset1(sK2,sK2,sK2)))) = iProver_top ),
% 2.46/0.98      inference(predicate_to_equality,[status(thm)],[c_392]) ).
% 2.46/0.98  
% 2.46/0.98  cnf(c_14,plain,
% 2.46/0.98      ( r2_hidden(X0,X1)
% 2.46/0.98      | ~ r2_hidden(X0,k3_tarski(k1_enumset1(X1,X1,k1_enumset1(X1,X1,X1))))
% 2.46/0.98      | X0 = X1 ),
% 2.46/0.98      inference(cnf_transformation,[],[f69]) ).
% 2.46/0.98  
% 2.46/0.98  cnf(c_925,plain,
% 2.46/0.98      ( X0 = X1
% 2.46/0.98      | r2_hidden(X0,X1) = iProver_top
% 2.46/0.98      | r2_hidden(X0,k3_tarski(k1_enumset1(X1,X1,k1_enumset1(X1,X1,X1)))) != iProver_top ),
% 2.46/0.98      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 2.46/0.98  
% 2.46/0.98  cnf(c_4152,plain,
% 2.46/0.98      ( sK2 = sK1
% 2.46/0.98      | r1_tarski(sK1,sK2) = iProver_top
% 2.46/0.98      | r2_hidden(sK1,sK2) = iProver_top ),
% 2.46/0.98      inference(superposition,[status(thm)],[c_920,c_925]) ).
% 2.46/0.98  
% 2.46/0.98  cnf(c_9,plain,
% 2.46/0.98      ( r1_tarski(X0,X0) ),
% 2.46/0.98      inference(cnf_transformation,[],[f76]) ).
% 2.46/0.98  
% 2.46/0.98  cnf(c_43,plain,
% 2.46/0.98      ( r1_tarski(sK2,sK2) ),
% 2.46/0.98      inference(instantiation,[status(thm)],[c_9]) ).
% 2.46/0.98  
% 2.46/0.98  cnf(c_42,plain,
% 2.46/0.98      ( r1_tarski(X0,X0) = iProver_top ),
% 2.46/0.98      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 2.46/0.98  
% 2.46/0.98  cnf(c_44,plain,
% 2.46/0.98      ( r1_tarski(sK2,sK2) = iProver_top ),
% 2.46/0.98      inference(instantiation,[status(thm)],[c_42]) ).
% 2.46/0.98  
% 2.46/0.98  cnf(c_7,plain,
% 2.46/0.98      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X1 = X0 ),
% 2.46/0.98      inference(cnf_transformation,[],[f43]) ).
% 2.46/0.98  
% 2.46/0.98  cnf(c_47,plain,
% 2.46/0.98      ( ~ r1_tarski(sK2,sK2) | sK2 = sK2 ),
% 2.46/0.98      inference(instantiation,[status(thm)],[c_7]) ).
% 2.46/0.98  
% 2.46/0.98  cnf(c_306,plain,
% 2.46/0.98      ( r1_tarski(sK1,sK2) = iProver_top
% 2.46/0.98      | r2_hidden(sK1,k3_tarski(k1_enumset1(sK2,sK2,k1_enumset1(sK2,sK2,sK2)))) = iProver_top ),
% 2.46/0.98      inference(predicate_to_equality,[status(thm)],[c_304]) ).
% 2.46/0.98  
% 2.46/0.98  cnf(c_498,plain,
% 2.46/0.98      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,X3) | X2 != X0 | X3 != X1 ),
% 2.46/0.98      theory(equality) ).
% 2.46/0.98  
% 2.46/0.98  cnf(c_1137,plain,
% 2.46/0.98      ( ~ r1_tarski(X0,X1) | r1_tarski(sK1,sK2) | sK2 != X1 | sK1 != X0 ),
% 2.46/0.98      inference(instantiation,[status(thm)],[c_498]) ).
% 2.46/0.98  
% 2.46/0.98  cnf(c_1138,plain,
% 2.46/0.98      ( sK2 != X0
% 2.46/0.98      | sK1 != X1
% 2.46/0.98      | r1_tarski(X1,X0) != iProver_top
% 2.46/0.98      | r1_tarski(sK1,sK2) = iProver_top ),
% 2.46/0.98      inference(predicate_to_equality,[status(thm)],[c_1137]) ).
% 2.46/0.98  
% 2.46/0.98  cnf(c_1140,plain,
% 2.46/0.98      ( sK2 != sK2
% 2.46/0.98      | sK1 != sK2
% 2.46/0.98      | r1_tarski(sK2,sK2) != iProver_top
% 2.46/0.98      | r1_tarski(sK1,sK2) = iProver_top ),
% 2.46/0.98      inference(instantiation,[status(thm)],[c_1138]) ).
% 2.46/0.98  
% 2.46/0.98  cnf(c_5,plain,
% 2.46/0.98      ( ~ r2_hidden(X0,X1)
% 2.46/0.98      | r2_hidden(X0,k3_tarski(k1_enumset1(X1,X1,X2))) ),
% 2.46/0.98      inference(cnf_transformation,[],[f73]) ).
% 2.46/0.98  
% 2.46/0.98  cnf(c_931,plain,
% 2.46/0.98      ( r2_hidden(X0,X1) != iProver_top
% 2.46/0.98      | r2_hidden(X0,k3_tarski(k1_enumset1(X1,X1,X2))) = iProver_top ),
% 2.46/0.98      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 2.46/0.98  
% 2.46/0.98  cnf(c_10,plain,
% 2.46/0.98      ( r1_ordinal1(X0,X1)
% 2.46/0.98      | ~ r1_tarski(X0,X1)
% 2.46/0.98      | ~ v3_ordinal1(X1)
% 2.46/0.98      | ~ v3_ordinal1(X0) ),
% 2.46/0.98      inference(cnf_transformation,[],[f49]) ).
% 2.46/0.98  
% 2.46/0.98  cnf(c_16,negated_conjecture,
% 2.46/0.98      ( ~ r1_ordinal1(sK1,sK2)
% 2.46/0.98      | ~ r2_hidden(sK1,k3_tarski(k1_enumset1(sK2,sK2,k1_enumset1(sK2,sK2,sK2)))) ),
% 2.46/0.98      inference(cnf_transformation,[],[f70]) ).
% 2.46/0.98  
% 2.46/0.98  cnf(c_151,plain,
% 2.46/0.98      ( ~ r1_ordinal1(sK1,sK2)
% 2.46/0.98      | ~ r2_hidden(sK1,k3_tarski(k1_enumset1(sK2,sK2,k1_enumset1(sK2,sK2,sK2)))) ),
% 2.46/0.98      inference(prop_impl,[status(thm)],[c_16]) ).
% 2.46/0.98  
% 2.46/0.98  cnf(c_287,plain,
% 2.46/0.98      ( ~ r1_tarski(X0,X1)
% 2.46/0.98      | ~ r2_hidden(sK1,k3_tarski(k1_enumset1(sK2,sK2,k1_enumset1(sK2,sK2,sK2))))
% 2.46/0.98      | ~ v3_ordinal1(X0)
% 2.46/0.98      | ~ v3_ordinal1(X1)
% 2.46/0.98      | sK2 != X1
% 2.46/0.98      | sK1 != X0 ),
% 2.46/0.98      inference(resolution_lifted,[status(thm)],[c_10,c_151]) ).
% 2.46/0.98  
% 2.46/0.98  cnf(c_288,plain,
% 2.46/0.98      ( ~ r1_tarski(sK1,sK2)
% 2.46/0.98      | ~ r2_hidden(sK1,k3_tarski(k1_enumset1(sK2,sK2,k1_enumset1(sK2,sK2,sK2))))
% 2.46/0.98      | ~ v3_ordinal1(sK2)
% 2.46/0.98      | ~ v3_ordinal1(sK1) ),
% 2.46/0.98      inference(unflattening,[status(thm)],[c_287]) ).
% 2.46/0.98  
% 2.46/0.98  cnf(c_290,plain,
% 2.46/0.98      ( ~ r1_tarski(sK1,sK2)
% 2.46/0.98      | ~ r2_hidden(sK1,k3_tarski(k1_enumset1(sK2,sK2,k1_enumset1(sK2,sK2,sK2)))) ),
% 2.46/0.98      inference(global_propositional_subsumption,
% 2.46/0.98                [status(thm)],
% 2.46/0.98                [c_288,c_19,c_18]) ).
% 2.46/0.98  
% 2.46/0.98  cnf(c_390,plain,
% 2.46/0.98      ( ~ r1_tarski(sK1,sK2)
% 2.46/0.98      | ~ r2_hidden(sK1,k3_tarski(k1_enumset1(sK2,sK2,k1_enumset1(sK2,sK2,sK2)))) ),
% 2.46/0.98      inference(prop_impl,[status(thm)],[c_19,c_18,c_288]) ).
% 2.46/0.98  
% 2.46/0.98  cnf(c_921,plain,
% 2.46/0.98      ( r1_tarski(sK1,sK2) != iProver_top
% 2.46/0.98      | r2_hidden(sK1,k3_tarski(k1_enumset1(sK2,sK2,k1_enumset1(sK2,sK2,sK2)))) != iProver_top ),
% 2.46/0.98      inference(predicate_to_equality,[status(thm)],[c_390]) ).
% 2.46/0.98  
% 2.46/0.98  cnf(c_1848,plain,
% 2.46/0.98      ( r1_tarski(sK1,sK2) != iProver_top
% 2.46/0.98      | r2_hidden(sK1,sK2) != iProver_top ),
% 2.46/0.98      inference(superposition,[status(thm)],[c_931,c_921]) ).
% 2.46/0.98  
% 2.46/0.98  cnf(c_273,plain,
% 2.46/0.98      ( r2_hidden(X0,X1)
% 2.46/0.98      | ~ r2_hidden(sK1,k3_tarski(k1_enumset1(sK2,sK2,k1_enumset1(sK2,sK2,sK2))))
% 2.46/0.98      | ~ v3_ordinal1(X1)
% 2.46/0.98      | ~ v3_ordinal1(X0)
% 2.46/0.98      | sK2 != X0
% 2.46/0.98      | sK1 != X1 ),
% 2.46/0.98      inference(resolution_lifted,[status(thm)],[c_15,c_151]) ).
% 2.46/0.98  
% 2.46/0.98  cnf(c_274,plain,
% 2.46/0.98      ( r2_hidden(sK2,sK1)
% 2.46/0.98      | ~ r2_hidden(sK1,k3_tarski(k1_enumset1(sK2,sK2,k1_enumset1(sK2,sK2,sK2))))
% 2.46/0.98      | ~ v3_ordinal1(sK2)
% 2.46/0.98      | ~ v3_ordinal1(sK1) ),
% 2.46/0.98      inference(unflattening,[status(thm)],[c_273]) ).
% 2.46/0.98  
% 2.46/0.98  cnf(c_276,plain,
% 2.46/0.98      ( r2_hidden(sK2,sK1)
% 2.46/0.98      | ~ r2_hidden(sK1,k3_tarski(k1_enumset1(sK2,sK2,k1_enumset1(sK2,sK2,sK2)))) ),
% 2.46/0.98      inference(global_propositional_subsumption,
% 2.46/0.98                [status(thm)],
% 2.46/0.98                [c_274,c_19,c_18]) ).
% 2.46/0.98  
% 2.46/0.98  cnf(c_278,plain,
% 2.46/0.98      ( r2_hidden(sK2,sK1) = iProver_top
% 2.46/0.98      | r2_hidden(sK1,k3_tarski(k1_enumset1(sK2,sK2,k1_enumset1(sK2,sK2,sK2)))) != iProver_top ),
% 2.46/0.98      inference(predicate_to_equality,[status(thm)],[c_276]) ).
% 2.46/0.98  
% 2.46/0.98  cnf(c_0,plain,
% 2.46/0.98      ( ~ r2_hidden(X0,X1) | ~ r2_hidden(X1,X0) ),
% 2.46/0.98      inference(cnf_transformation,[],[f34]) ).
% 2.46/0.98  
% 2.46/0.98  cnf(c_1056,plain,
% 2.46/0.98      ( ~ r2_hidden(sK2,sK1) | ~ r2_hidden(sK1,sK2) ),
% 2.46/0.98      inference(instantiation,[status(thm)],[c_0]) ).
% 2.46/0.98  
% 2.46/0.98  cnf(c_1057,plain,
% 2.46/0.98      ( r2_hidden(sK2,sK1) != iProver_top
% 2.46/0.98      | r2_hidden(sK1,sK2) != iProver_top ),
% 2.46/0.98      inference(predicate_to_equality,[status(thm)],[c_1056]) ).
% 2.46/0.98  
% 2.46/0.98  cnf(c_13,plain,
% 2.46/0.98      ( ~ r2_hidden(X0,X1)
% 2.46/0.98      | r2_hidden(X0,k3_tarski(k1_enumset1(X1,X1,k1_enumset1(X1,X1,X1)))) ),
% 2.46/0.98      inference(cnf_transformation,[],[f68]) ).
% 2.46/0.98  
% 2.46/0.98  cnf(c_1142,plain,
% 2.46/0.98      ( r2_hidden(sK1,k3_tarski(k1_enumset1(sK2,sK2,k1_enumset1(sK2,sK2,sK2))))
% 2.46/0.98      | ~ r2_hidden(sK1,sK2) ),
% 2.46/0.98      inference(instantiation,[status(thm)],[c_13]) ).
% 2.46/0.98  
% 2.46/0.98  cnf(c_1143,plain,
% 2.46/0.98      ( r2_hidden(sK1,k3_tarski(k1_enumset1(sK2,sK2,k1_enumset1(sK2,sK2,sK2)))) = iProver_top
% 2.46/0.98      | r2_hidden(sK1,sK2) != iProver_top ),
% 2.46/0.98      inference(predicate_to_equality,[status(thm)],[c_1142]) ).
% 2.46/0.98  
% 2.46/0.98  cnf(c_2112,plain,
% 2.46/0.98      ( r2_hidden(sK1,sK2) != iProver_top ),
% 2.46/0.98      inference(global_propositional_subsumption,
% 2.46/0.98                [status(thm)],
% 2.46/0.98                [c_1848,c_278,c_1057,c_1143]) ).
% 2.46/0.98  
% 2.46/0.98  cnf(c_3871,plain,
% 2.46/0.98      ( ~ r2_hidden(sK1,k3_tarski(k1_enumset1(sK2,sK2,k1_enumset1(sK2,sK2,sK2))))
% 2.46/0.98      | r2_hidden(sK1,sK2)
% 2.46/0.98      | sK1 = sK2 ),
% 2.46/0.98      inference(instantiation,[status(thm)],[c_14]) ).
% 2.46/0.98  
% 2.46/0.98  cnf(c_3872,plain,
% 2.46/0.98      ( sK1 = sK2
% 2.46/0.99      | r2_hidden(sK1,k3_tarski(k1_enumset1(sK2,sK2,k1_enumset1(sK2,sK2,sK2)))) != iProver_top
% 2.46/0.99      | r2_hidden(sK1,sK2) = iProver_top ),
% 2.46/0.99      inference(predicate_to_equality,[status(thm)],[c_3871]) ).
% 2.46/0.99  
% 2.46/0.99  cnf(c_6229,plain,
% 2.46/0.99      ( r1_tarski(sK1,sK2) = iProver_top ),
% 2.46/0.99      inference(global_propositional_subsumption,
% 2.46/0.99                [status(thm)],
% 2.46/0.99                [c_4152,c_43,c_44,c_47,c_278,c_306,c_1057,c_1140,c_1143,
% 2.46/0.99                 c_3872]) ).
% 2.46/0.99  
% 2.46/0.99  cnf(c_929,plain,
% 2.46/0.99      ( X0 = X1
% 2.46/0.99      | r1_tarski(X1,X0) != iProver_top
% 2.46/0.99      | r1_tarski(X0,X1) != iProver_top ),
% 2.46/0.99      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 2.46/0.99  
% 2.46/0.99  cnf(c_6234,plain,
% 2.46/0.99      ( sK2 = sK1 | r1_tarski(sK2,sK1) != iProver_top ),
% 2.46/0.99      inference(superposition,[status(thm)],[c_6229,c_929]) ).
% 2.46/0.99  
% 2.46/0.99  cnf(c_12,plain,
% 2.46/0.99      ( r2_hidden(X0,k3_tarski(k1_enumset1(X0,X0,k1_enumset1(X0,X0,X0)))) ),
% 2.46/0.99      inference(cnf_transformation,[],[f77]) ).
% 2.46/0.99  
% 2.46/0.99  cnf(c_33,plain,
% 2.46/0.99      ( r2_hidden(X0,k3_tarski(k1_enumset1(X0,X0,k1_enumset1(X0,X0,X0)))) = iProver_top ),
% 2.46/0.99      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 2.46/0.99  
% 2.46/0.99  cnf(c_35,plain,
% 2.46/0.99      ( r2_hidden(sK2,k3_tarski(k1_enumset1(sK2,sK2,k1_enumset1(sK2,sK2,sK2)))) = iProver_top ),
% 2.46/0.99      inference(instantiation,[status(thm)],[c_33]) ).
% 2.46/0.99  
% 2.46/0.99  cnf(c_63,plain,
% 2.46/0.99      ( r2_hidden(X0,X1) != iProver_top
% 2.46/0.99      | r2_hidden(X1,X0) != iProver_top ),
% 2.46/0.99      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 2.46/0.99  
% 2.46/0.99  cnf(c_65,plain,
% 2.46/0.99      ( r2_hidden(sK2,sK2) != iProver_top ),
% 2.46/0.99      inference(instantiation,[status(thm)],[c_63]) ).
% 2.46/0.99  
% 2.46/0.99  cnf(c_496,plain,
% 2.46/0.99      ( X0 != X1
% 2.46/0.99      | X2 != X3
% 2.46/0.99      | X4 != X5
% 2.46/0.99      | k1_enumset1(X0,X2,X4) = k1_enumset1(X1,X3,X5) ),
% 2.46/0.99      theory(equality) ).
% 2.46/0.99  
% 2.46/0.99  cnf(c_501,plain,
% 2.46/0.99      ( k1_enumset1(sK2,sK2,sK2) = k1_enumset1(sK2,sK2,sK2)
% 2.46/0.99      | sK2 != sK2 ),
% 2.46/0.99      inference(instantiation,[status(thm)],[c_496]) ).
% 2.46/0.99  
% 2.46/0.99  cnf(c_6,plain,
% 2.46/0.99      ( r2_hidden(X0,X1)
% 2.46/0.99      | r2_hidden(X0,X2)
% 2.46/0.99      | ~ r2_hidden(X0,k3_tarski(k1_enumset1(X2,X2,X1))) ),
% 2.46/0.99      inference(cnf_transformation,[],[f74]) ).
% 2.46/0.99  
% 2.46/0.99  cnf(c_1099,plain,
% 2.46/0.99      ( r2_hidden(X0,X0)
% 2.46/0.99      | r2_hidden(X0,k1_enumset1(X0,X0,X0))
% 2.46/0.99      | ~ r2_hidden(X0,k3_tarski(k1_enumset1(X0,X0,k1_enumset1(X0,X0,X0)))) ),
% 2.46/0.99      inference(instantiation,[status(thm)],[c_6]) ).
% 2.46/0.99  
% 2.46/0.99  cnf(c_1100,plain,
% 2.46/0.99      ( r2_hidden(X0,X0) = iProver_top
% 2.46/0.99      | r2_hidden(X0,k1_enumset1(X0,X0,X0)) = iProver_top
% 2.46/0.99      | r2_hidden(X0,k3_tarski(k1_enumset1(X0,X0,k1_enumset1(X0,X0,X0)))) != iProver_top ),
% 2.46/0.99      inference(predicate_to_equality,[status(thm)],[c_1099]) ).
% 2.46/0.99  
% 2.46/0.99  cnf(c_1102,plain,
% 2.46/0.99      ( r2_hidden(sK2,k1_enumset1(sK2,sK2,sK2)) = iProver_top
% 2.46/0.99      | r2_hidden(sK2,k3_tarski(k1_enumset1(sK2,sK2,k1_enumset1(sK2,sK2,sK2)))) != iProver_top
% 2.46/0.99      | r2_hidden(sK2,sK2) = iProver_top ),
% 2.46/0.99      inference(instantiation,[status(thm)],[c_1100]) ).
% 2.46/0.99  
% 2.46/0.99  cnf(c_4,plain,
% 2.46/0.99      ( ~ r2_hidden(X0,X1)
% 2.46/0.99      | r2_hidden(X0,k3_tarski(k1_enumset1(X2,X2,X1))) ),
% 2.46/0.99      inference(cnf_transformation,[],[f72]) ).
% 2.46/0.99  
% 2.46/0.99  cnf(c_932,plain,
% 2.46/0.99      ( r2_hidden(X0,X1) != iProver_top
% 2.46/0.99      | r2_hidden(X0,k3_tarski(k1_enumset1(X2,X2,X1))) = iProver_top ),
% 2.46/0.99      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 2.46/0.99  
% 2.46/0.99  cnf(c_1847,plain,
% 2.46/0.99      ( r1_tarski(sK1,sK2) != iProver_top
% 2.46/0.99      | r2_hidden(sK1,k1_enumset1(sK2,sK2,sK2)) != iProver_top ),
% 2.46/0.99      inference(superposition,[status(thm)],[c_932,c_921]) ).
% 2.46/0.99  
% 2.46/0.99  cnf(c_495,plain,
% 2.46/0.99      ( ~ r2_hidden(X0,X1) | r2_hidden(X2,X3) | X2 != X0 | X3 != X1 ),
% 2.46/0.99      theory(equality) ).
% 2.46/0.99  
% 2.46/0.99  cnf(c_1167,plain,
% 2.46/0.99      ( r2_hidden(X0,X1)
% 2.46/0.99      | ~ r2_hidden(X2,k1_enumset1(X2,X2,X2))
% 2.46/0.99      | X0 != X2
% 2.46/0.99      | X1 != k1_enumset1(X2,X2,X2) ),
% 2.46/0.99      inference(instantiation,[status(thm)],[c_495]) ).
% 2.46/0.99  
% 2.46/0.99  cnf(c_1337,plain,
% 2.46/0.99      ( ~ r2_hidden(X0,k1_enumset1(X0,X0,X0))
% 2.46/0.99      | r2_hidden(X1,k1_enumset1(X0,X0,X0))
% 2.46/0.99      | X1 != X0
% 2.46/0.99      | k1_enumset1(X0,X0,X0) != k1_enumset1(X0,X0,X0) ),
% 2.46/0.99      inference(instantiation,[status(thm)],[c_1167]) ).
% 2.46/0.99  
% 2.46/0.99  cnf(c_2274,plain,
% 2.46/0.99      ( ~ r2_hidden(sK2,k1_enumset1(sK2,sK2,sK2))
% 2.46/0.99      | r2_hidden(sK1,k1_enumset1(sK2,sK2,sK2))
% 2.46/0.99      | k1_enumset1(sK2,sK2,sK2) != k1_enumset1(sK2,sK2,sK2)
% 2.46/0.99      | sK1 != sK2 ),
% 2.46/0.99      inference(instantiation,[status(thm)],[c_1337]) ).
% 2.46/0.99  
% 2.46/0.99  cnf(c_2275,plain,
% 2.46/0.99      ( k1_enumset1(sK2,sK2,sK2) != k1_enumset1(sK2,sK2,sK2)
% 2.46/0.99      | sK1 != sK2
% 2.46/0.99      | r2_hidden(sK2,k1_enumset1(sK2,sK2,sK2)) != iProver_top
% 2.46/0.99      | r2_hidden(sK1,k1_enumset1(sK2,sK2,sK2)) = iProver_top ),
% 2.46/0.99      inference(predicate_to_equality,[status(thm)],[c_2274]) ).
% 2.46/0.99  
% 2.46/0.99  cnf(c_3868,plain,
% 2.46/0.99      ( ~ r1_tarski(sK2,sK1) | ~ r1_tarski(sK1,sK2) | sK1 = sK2 ),
% 2.46/0.99      inference(instantiation,[status(thm)],[c_7]) ).
% 2.46/0.99  
% 2.46/0.99  cnf(c_3869,plain,
% 2.46/0.99      ( sK1 = sK2
% 2.46/0.99      | r1_tarski(sK2,sK1) != iProver_top
% 2.46/0.99      | r1_tarski(sK1,sK2) != iProver_top ),
% 2.46/0.99      inference(predicate_to_equality,[status(thm)],[c_3868]) ).
% 2.46/0.99  
% 2.46/0.99  cnf(c_6826,plain,
% 2.46/0.99      ( r1_tarski(sK2,sK1) != iProver_top ),
% 2.46/0.99      inference(global_propositional_subsumption,
% 2.46/0.99                [status(thm)],
% 2.46/0.99                [c_6234,c_35,c_43,c_44,c_47,c_65,c_278,c_306,c_501,
% 2.46/0.99                 c_1057,c_1102,c_1140,c_1143,c_1847,c_2275,c_3869,c_3872]) ).
% 2.46/0.99  
% 2.46/0.99  cnf(c_6831,plain,
% 2.46/0.99      ( r2_hidden(sK1,sK2) = iProver_top
% 2.46/0.99      | v3_ordinal1(sK2) != iProver_top
% 2.46/0.99      | v3_ordinal1(sK1) != iProver_top ),
% 2.46/0.99      inference(superposition,[status(thm)],[c_922,c_6826]) ).
% 2.46/0.99  
% 2.46/0.99  cnf(c_21,plain,
% 2.46/0.99      ( v3_ordinal1(sK2) = iProver_top ),
% 2.46/0.99      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 2.46/0.99  
% 2.46/0.99  cnf(c_20,plain,
% 2.46/0.99      ( v3_ordinal1(sK1) = iProver_top ),
% 2.46/0.99      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 2.46/0.99  
% 2.46/0.99  cnf(contradiction,plain,
% 2.46/0.99      ( $false ),
% 2.46/0.99      inference(minisat,[status(thm)],[c_6831,c_2112,c_21,c_20]) ).
% 2.46/0.99  
% 2.46/0.99  
% 2.46/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 2.46/0.99  
% 2.46/0.99  ------                               Statistics
% 2.46/0.99  
% 2.46/0.99  ------ General
% 2.46/0.99  
% 2.46/0.99  abstr_ref_over_cycles:                  0
% 2.46/0.99  abstr_ref_under_cycles:                 0
% 2.46/0.99  gc_basic_clause_elim:                   0
% 2.46/0.99  forced_gc_time:                         0
% 2.46/0.99  parsing_time:                           0.009
% 2.46/0.99  unif_index_cands_time:                  0.
% 2.46/0.99  unif_index_add_time:                    0.
% 2.46/0.99  orderings_time:                         0.
% 2.46/0.99  out_proof_time:                         0.01
% 2.46/0.99  total_time:                             0.242
% 2.46/0.99  num_of_symbols:                         37
% 2.46/0.99  num_of_terms:                           10298
% 2.46/0.99  
% 2.46/0.99  ------ Preprocessing
% 2.46/0.99  
% 2.46/0.99  num_of_splits:                          0
% 2.46/0.99  num_of_split_atoms:                     0
% 2.46/0.99  num_of_reused_defs:                     0
% 2.46/0.99  num_eq_ax_congr_red:                    11
% 2.46/0.99  num_of_sem_filtered_clauses:            1
% 2.46/0.99  num_of_subtypes:                        0
% 2.46/0.99  monotx_restored_types:                  0
% 2.46/0.99  sat_num_of_epr_types:                   0
% 2.46/0.99  sat_num_of_non_cyclic_types:            0
% 2.46/0.99  sat_guarded_non_collapsed_types:        0
% 2.46/0.99  num_pure_diseq_elim:                    0
% 2.46/0.99  simp_replaced_by:                       0
% 2.46/0.99  res_preprocessed:                       88
% 2.46/0.99  prep_upred:                             0
% 2.46/0.99  prep_unflattend:                        6
% 2.46/0.99  smt_new_axioms:                         0
% 2.46/0.99  pred_elim_cands:                        3
% 2.46/0.99  pred_elim:                              1
% 2.46/0.99  pred_elim_cl:                           1
% 2.46/0.99  pred_elim_cycles:                       3
% 2.46/0.99  merged_defs:                            8
% 2.46/0.99  merged_defs_ncl:                        0
% 2.46/0.99  bin_hyper_res:                          9
% 2.46/0.99  prep_cycles:                            4
% 2.46/0.99  pred_elim_time:                         0.001
% 2.46/0.99  splitting_time:                         0.
% 2.46/0.99  sem_filter_time:                        0.
% 2.46/0.99  monotx_time:                            0.001
% 2.46/0.99  subtype_inf_time:                       0.
% 2.46/0.99  
% 2.46/0.99  ------ Problem properties
% 2.46/0.99  
% 2.46/0.99  clauses:                                18
% 2.46/0.99  conjectures:                            2
% 2.46/0.99  epr:                                    7
% 2.46/0.99  horn:                                   12
% 2.46/0.99  ground:                                 5
% 2.46/0.99  unary:                                  4
% 2.46/0.99  binary:                                 7
% 2.46/0.99  lits:                                   41
% 2.46/0.99  lits_eq:                                5
% 2.46/0.99  fd_pure:                                0
% 2.46/0.99  fd_pseudo:                              0
% 2.46/0.99  fd_cond:                                0
% 2.46/0.99  fd_pseudo_cond:                         5
% 2.46/0.99  ac_symbols:                             0
% 2.46/0.99  
% 2.46/0.99  ------ Propositional Solver
% 2.46/0.99  
% 2.46/0.99  prop_solver_calls:                      27
% 2.46/0.99  prop_fast_solver_calls:                 532
% 2.46/0.99  smt_solver_calls:                       0
% 2.46/0.99  smt_fast_solver_calls:                  0
% 2.46/0.99  prop_num_of_clauses:                    2783
% 2.46/0.99  prop_preprocess_simplified:             8679
% 2.46/0.99  prop_fo_subsumed:                       10
% 2.46/0.99  prop_solver_time:                       0.
% 2.46/0.99  smt_solver_time:                        0.
% 2.46/0.99  smt_fast_solver_time:                   0.
% 2.46/0.99  prop_fast_solver_time:                  0.
% 2.46/0.99  prop_unsat_core_time:                   0.
% 2.46/0.99  
% 2.46/0.99  ------ QBF
% 2.46/0.99  
% 2.46/0.99  qbf_q_res:                              0
% 2.46/0.99  qbf_num_tautologies:                    0
% 2.46/0.99  qbf_prep_cycles:                        0
% 2.46/0.99  
% 2.46/0.99  ------ BMC1
% 2.46/0.99  
% 2.46/0.99  bmc1_current_bound:                     -1
% 2.46/0.99  bmc1_last_solved_bound:                 -1
% 2.46/0.99  bmc1_unsat_core_size:                   -1
% 2.46/0.99  bmc1_unsat_core_parents_size:           -1
% 2.46/0.99  bmc1_merge_next_fun:                    0
% 2.46/0.99  bmc1_unsat_core_clauses_time:           0.
% 2.46/0.99  
% 2.46/0.99  ------ Instantiation
% 2.46/0.99  
% 2.46/0.99  inst_num_of_clauses:                    944
% 2.46/0.99  inst_num_in_passive:                    286
% 2.46/0.99  inst_num_in_active:                     186
% 2.46/0.99  inst_num_in_unprocessed:                472
% 2.46/0.99  inst_num_of_loops:                      190
% 2.46/0.99  inst_num_of_learning_restarts:          0
% 2.46/0.99  inst_num_moves_active_passive:          3
% 2.46/0.99  inst_lit_activity:                      0
% 2.46/0.99  inst_lit_activity_moves:                0
% 2.46/0.99  inst_num_tautologies:                   0
% 2.46/0.99  inst_num_prop_implied:                  0
% 2.46/0.99  inst_num_existing_simplified:           0
% 2.46/0.99  inst_num_eq_res_simplified:             0
% 2.46/0.99  inst_num_child_elim:                    0
% 2.46/0.99  inst_num_of_dismatching_blockings:      202
% 2.46/0.99  inst_num_of_non_proper_insts:           477
% 2.46/0.99  inst_num_of_duplicates:                 0
% 2.46/0.99  inst_inst_num_from_inst_to_res:         0
% 2.46/0.99  inst_dismatching_checking_time:         0.
% 2.46/0.99  
% 2.46/0.99  ------ Resolution
% 2.46/0.99  
% 2.46/0.99  res_num_of_clauses:                     0
% 2.46/0.99  res_num_in_passive:                     0
% 2.46/0.99  res_num_in_active:                      0
% 2.46/0.99  res_num_of_loops:                       92
% 2.46/0.99  res_forward_subset_subsumed:            34
% 2.46/0.99  res_backward_subset_subsumed:           0
% 2.46/0.99  res_forward_subsumed:                   0
% 2.46/0.99  res_backward_subsumed:                  0
% 2.46/0.99  res_forward_subsumption_resolution:     0
% 2.46/0.99  res_backward_subsumption_resolution:    0
% 2.46/0.99  res_clause_to_clause_subsumption:       837
% 2.46/0.99  res_orphan_elimination:                 0
% 2.46/0.99  res_tautology_del:                      51
% 2.46/0.99  res_num_eq_res_simplified:              0
% 2.46/0.99  res_num_sel_changes:                    0
% 2.46/0.99  res_moves_from_active_to_pass:          0
% 2.46/0.99  
% 2.46/0.99  ------ Superposition
% 2.46/0.99  
% 2.46/0.99  sup_time_total:                         0.
% 2.46/0.99  sup_time_generating:                    0.
% 2.46/0.99  sup_time_sim_full:                      0.
% 2.46/0.99  sup_time_sim_immed:                     0.
% 2.46/0.99  
% 2.46/0.99  sup_num_of_clauses:                     92
% 2.46/0.99  sup_num_in_active:                      34
% 2.46/0.99  sup_num_in_passive:                     58
% 2.46/0.99  sup_num_of_loops:                       36
% 2.46/0.99  sup_fw_superposition:                   57
% 2.46/0.99  sup_bw_superposition:                   35
% 2.46/0.99  sup_immediate_simplified:               0
% 2.46/0.99  sup_given_eliminated:                   0
% 2.46/0.99  comparisons_done:                       0
% 2.46/0.99  comparisons_avoided:                    0
% 2.46/0.99  
% 2.46/0.99  ------ Simplifications
% 2.46/0.99  
% 2.46/0.99  
% 2.46/0.99  sim_fw_subset_subsumed:                 3
% 2.46/0.99  sim_bw_subset_subsumed:                 5
% 2.46/0.99  sim_fw_subsumed:                        2
% 2.46/0.99  sim_bw_subsumed:                        0
% 2.46/0.99  sim_fw_subsumption_res:                 0
% 2.46/0.99  sim_bw_subsumption_res:                 0
% 2.46/0.99  sim_tautology_del:                      9
% 2.46/0.99  sim_eq_tautology_del:                   2
% 2.46/0.99  sim_eq_res_simp:                        6
% 2.46/0.99  sim_fw_demodulated:                     0
% 2.46/0.99  sim_bw_demodulated:                     0
% 2.46/0.99  sim_light_normalised:                   0
% 2.46/0.99  sim_joinable_taut:                      0
% 2.46/0.99  sim_joinable_simp:                      0
% 2.46/0.99  sim_ac_normalised:                      0
% 2.46/0.99  sim_smt_subsumption:                    0
% 2.46/0.99  
%------------------------------------------------------------------------------
