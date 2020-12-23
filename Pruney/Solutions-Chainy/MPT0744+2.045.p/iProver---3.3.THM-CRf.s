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
% DateTime   : Thu Dec  3 11:53:55 EST 2020

% Result     : Theorem 3.48s
% Output     : CNFRefutation 3.48s
% Verified   : 
% Statistics : Number of formulae       :  174 ( 736 expanded)
%              Number of clauses        :   76 ( 113 expanded)
%              Number of leaves         :   30 ( 203 expanded)
%              Depth                    :   21
%              Number of atoms          :  537 (2249 expanded)
%              Number of equality atoms :  129 ( 495 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal clause size      :   14 (   3 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            | r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
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

fof(f40,plain,(
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
    inference(flattening,[],[f39])).

fof(f41,plain,(
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
    inference(rectify,[],[f40])).

fof(f42,plain,(
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

fof(f43,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f41,f42])).

fof(f56,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X1)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f43])).

fof(f12,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f70,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f12])).

fof(f5,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f63,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f5])).

fof(f6,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f64,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f6])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f65,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f7])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f66,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f8])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f67,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f9])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f68,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f10])).

fof(f86,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f67,f68])).

fof(f87,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f66,f86])).

fof(f88,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f65,f87])).

fof(f89,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f64,f88])).

fof(f90,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f63,f89])).

fof(f91,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f70,f90])).

fof(f97,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X1)
      | k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f56,f91])).

fof(f104,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))
      | ~ r2_hidden(X4,X1) ) ),
    inference(equality_resolution,[],[f97])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( ( v3_ordinal1(X1)
        & v3_ordinal1(X0) )
     => ( r1_ordinal1(X0,X1)
      <=> r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( r1_ordinal1(X0,X1)
      <=> r1_tarski(X0,X1) )
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( r1_ordinal1(X0,X1)
      <=> r1_tarski(X0,X1) )
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(flattening,[],[f31])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ( ( r1_ordinal1(X0,X1)
          | ~ r1_tarski(X0,X1) )
        & ( r1_tarski(X0,X1)
          | ~ r1_ordinal1(X0,X1) ) )
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(nnf_transformation,[],[f32])).

fof(f77,plain,(
    ! [X0,X1] :
      ( r1_ordinal1(X0,X1)
      | ~ r1_tarski(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f21,conjecture,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ! [X1] :
          ( v3_ordinal1(X1)
         => ( r2_hidden(X0,k1_ordinal1(X1))
          <=> r1_ordinal1(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,negated_conjecture,(
    ~ ! [X0] :
        ( v3_ordinal1(X0)
       => ! [X1] :
            ( v3_ordinal1(X1)
           => ( r2_hidden(X0,k1_ordinal1(X1))
            <=> r1_ordinal1(X0,X1) ) ) ) ),
    inference(negated_conjecture,[],[f21])).

fof(f38,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( r2_hidden(X0,k1_ordinal1(X1))
          <~> r1_ordinal1(X0,X1) )
          & v3_ordinal1(X1) )
      & v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f49,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ r1_ordinal1(X0,X1)
            | ~ r2_hidden(X0,k1_ordinal1(X1)) )
          & ( r1_ordinal1(X0,X1)
            | r2_hidden(X0,k1_ordinal1(X1)) )
          & v3_ordinal1(X1) )
      & v3_ordinal1(X0) ) ),
    inference(nnf_transformation,[],[f38])).

fof(f50,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ r1_ordinal1(X0,X1)
            | ~ r2_hidden(X0,k1_ordinal1(X1)) )
          & ( r1_ordinal1(X0,X1)
            | r2_hidden(X0,k1_ordinal1(X1)) )
          & v3_ordinal1(X1) )
      & v3_ordinal1(X0) ) ),
    inference(flattening,[],[f49])).

fof(f52,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ( ~ r1_ordinal1(X0,X1)
            | ~ r2_hidden(X0,k1_ordinal1(X1)) )
          & ( r1_ordinal1(X0,X1)
            | r2_hidden(X0,k1_ordinal1(X1)) )
          & v3_ordinal1(X1) )
     => ( ( ~ r1_ordinal1(X0,sK3)
          | ~ r2_hidden(X0,k1_ordinal1(sK3)) )
        & ( r1_ordinal1(X0,sK3)
          | r2_hidden(X0,k1_ordinal1(sK3)) )
        & v3_ordinal1(sK3) ) ) ),
    introduced(choice_axiom,[])).

fof(f51,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( ~ r1_ordinal1(X0,X1)
              | ~ r2_hidden(X0,k1_ordinal1(X1)) )
            & ( r1_ordinal1(X0,X1)
              | r2_hidden(X0,k1_ordinal1(X1)) )
            & v3_ordinal1(X1) )
        & v3_ordinal1(X0) )
   => ( ? [X1] :
          ( ( ~ r1_ordinal1(sK2,X1)
            | ~ r2_hidden(sK2,k1_ordinal1(X1)) )
          & ( r1_ordinal1(sK2,X1)
            | r2_hidden(sK2,k1_ordinal1(X1)) )
          & v3_ordinal1(X1) )
      & v3_ordinal1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f53,plain,
    ( ( ~ r1_ordinal1(sK2,sK3)
      | ~ r2_hidden(sK2,k1_ordinal1(sK3)) )
    & ( r1_ordinal1(sK2,sK3)
      | r2_hidden(sK2,k1_ordinal1(sK3)) )
    & v3_ordinal1(sK3)
    & v3_ordinal1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f50,f52,f51])).

fof(f85,plain,
    ( ~ r1_ordinal1(sK2,sK3)
    | ~ r2_hidden(sK2,k1_ordinal1(sK3)) ),
    inference(cnf_transformation,[],[f53])).

fof(f14,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_tarski(X0)) = k1_ordinal1(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f72,plain,(
    ! [X0] : k2_xboole_0(X0,k1_tarski(X0)) = k1_ordinal1(X0) ),
    inference(cnf_transformation,[],[f14])).

fof(f4,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f62,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f92,plain,(
    ! [X0] : k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f62,f90])).

fof(f93,plain,(
    ! [X0] : k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))) = k1_ordinal1(X0) ),
    inference(definition_unfolding,[],[f72,f91,f92])).

fof(f102,plain,
    ( ~ r1_ordinal1(sK2,sK3)
    | ~ r2_hidden(sK2,k3_tarski(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3)))) ),
    inference(definition_unfolding,[],[f85,f93])).

fof(f82,plain,(
    v3_ordinal1(sK2) ),
    inference(cnf_transformation,[],[f53])).

fof(f83,plain,(
    v3_ordinal1(sK3) ),
    inference(cnf_transformation,[],[f53])).

fof(f3,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f3])).

fof(f61,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f23])).

fof(f100,plain,(
    ! [X0] : k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) = X0 ),
    inference(definition_unfolding,[],[f61,f91])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => r1_tarski(X0,k3_tarski(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k3_tarski(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f69,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k3_tarski(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f13,axiom,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ( v2_ordinal1(X0)
        & v1_ordinal1(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => v1_ordinal1(X0) ) ),
    inference(pure_predicate_removal,[],[f13])).

fof(f29,plain,(
    ! [X0] :
      ( v1_ordinal1(X0)
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f71,plain,(
    ! [X0] :
      ( v1_ordinal1(X0)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f54,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X1)
      | r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f43])).

fof(f99,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X1)
      | r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f54,f91])).

fof(f106,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X1)
      | r2_hidden(X4,X0)
      | ~ r2_hidden(X4,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) ) ),
    inference(equality_resolution,[],[f99])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r2_xboole_0(X0,X1)
    <=> ( X0 != X1
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( X0 != X1
        & r1_tarski(X0,X1) )
     => r2_xboole_0(X0,X1) ) ),
    inference(unused_predicate_definition_removal,[],[f2])).

fof(f26,plain,(
    ! [X0,X1] :
      ( r2_xboole_0(X0,X1)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f27,plain,(
    ! [X0,X1] :
      ( r2_xboole_0(X0,X1)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f26])).

fof(f60,plain,(
    ! [X0,X1] :
      ( r2_xboole_0(X0,X1)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f18,axiom,(
    ! [X0] :
      ( v1_ordinal1(X0)
     => ! [X1] :
          ( v3_ordinal1(X1)
         => ( r2_xboole_0(X0,X1)
           => r2_hidden(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(X0,X1)
          | ~ r2_xboole_0(X0,X1)
          | ~ v3_ordinal1(X1) )
      | ~ v1_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(X0,X1)
          | ~ r2_xboole_0(X0,X1)
          | ~ v3_ordinal1(X1) )
      | ~ v1_ordinal1(X0) ) ),
    inference(flattening,[],[f33])).

fof(f79,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | ~ r2_xboole_0(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v1_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f76,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r1_ordinal1(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f84,plain,
    ( r1_ordinal1(sK2,sK3)
    | r2_hidden(sK2,k1_ordinal1(sK3)) ),
    inference(cnf_transformation,[],[f53])).

fof(f103,plain,
    ( r1_ordinal1(sK2,sK3)
    | r2_hidden(sK2,k3_tarski(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3)))) ),
    inference(definition_unfolding,[],[f84,f93])).

fof(f15,axiom,(
    ! [X0] :
      ( v1_ordinal1(X0)
    <=> ! [X1] :
          ( r2_hidden(X1,X0)
         => r1_tarski(X1,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0] :
      ( v1_ordinal1(X0)
    <=> ! [X1] :
          ( r1_tarski(X1,X0)
          | ~ r2_hidden(X1,X0) ) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f44,plain,(
    ! [X0] :
      ( ( v1_ordinal1(X0)
        | ? [X1] :
            ( ~ r1_tarski(X1,X0)
            & r2_hidden(X1,X0) ) )
      & ( ! [X1] :
            ( r1_tarski(X1,X0)
            | ~ r2_hidden(X1,X0) )
        | ~ v1_ordinal1(X0) ) ) ),
    inference(nnf_transformation,[],[f30])).

fof(f45,plain,(
    ! [X0] :
      ( ( v1_ordinal1(X0)
        | ? [X1] :
            ( ~ r1_tarski(X1,X0)
            & r2_hidden(X1,X0) ) )
      & ( ! [X2] :
            ( r1_tarski(X2,X0)
            | ~ r2_hidden(X2,X0) )
        | ~ v1_ordinal1(X0) ) ) ),
    inference(rectify,[],[f44])).

fof(f46,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ r1_tarski(X1,X0)
          & r2_hidden(X1,X0) )
     => ( ~ r1_tarski(sK1(X0),X0)
        & r2_hidden(sK1(X0),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f47,plain,(
    ! [X0] :
      ( ( v1_ordinal1(X0)
        | ( ~ r1_tarski(sK1(X0),X0)
          & r2_hidden(sK1(X0),X0) ) )
      & ( ! [X2] :
            ( r1_tarski(X2,X0)
            | ~ r2_hidden(X2,X0) )
        | ~ v1_ordinal1(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f45,f46])).

fof(f73,plain,(
    ! [X2,X0] :
      ( r1_tarski(X2,X0)
      | ~ r2_hidden(X2,X0)
      | ~ v1_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f55,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X0)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f43])).

fof(f98,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X0)
      | k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f55,f91])).

fof(f105,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))
      | ~ r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f98])).

fof(f20,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f81,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f19,axiom,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ! [X1] :
          ( v3_ordinal1(X1)
         => ( r2_hidden(X1,X0)
            | r1_ordinal1(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(X1,X0)
          | r1_ordinal1(X0,X1)
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f36,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(X1,X0)
          | r1_ordinal1(X0,X1)
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(flattening,[],[f35])).

fof(f80,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,X0)
      | r1_ordinal1(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f17,axiom,(
    ! [X0] : r2_hidden(X0,k1_ordinal1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f78,plain,(
    ! [X0] : r2_hidden(X0,k1_ordinal1(X0)) ),
    inference(cnf_transformation,[],[f17])).

fof(f101,plain,(
    ! [X0] : r2_hidden(X0,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)))) ),
    inference(definition_unfolding,[],[f78,f93])).

cnf(c_1222,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_1976,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(X2,k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2))
    | X0 != X2
    | X1 != k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2) ),
    inference(instantiation,[status(thm)],[c_1222])).

cnf(c_2174,plain,
    ( ~ r2_hidden(X0,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))
    | r2_hidden(X1,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))
    | X1 != X0
    | k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) != k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
    inference(instantiation,[status(thm)],[c_1976])).

cnf(c_5314,plain,
    ( ~ r2_hidden(sK3,k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3))
    | r2_hidden(sK2,k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3))
    | k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3) != k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3)
    | sK2 != sK3 ),
    inference(instantiation,[status(thm)],[c_2174])).

cnf(c_3,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,k3_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X1))) ),
    inference(cnf_transformation,[],[f104])).

cnf(c_1708,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,k3_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_13,plain,
    ( r1_ordinal1(X0,X1)
    | ~ r1_tarski(X0,X1)
    | ~ v3_ordinal1(X0)
    | ~ v3_ordinal1(X1) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_19,negated_conjecture,
    ( ~ r1_ordinal1(sK2,sK3)
    | ~ r2_hidden(sK2,k3_tarski(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3)))) ),
    inference(cnf_transformation,[],[f102])).

cnf(c_171,plain,
    ( ~ r1_ordinal1(sK2,sK3)
    | ~ r2_hidden(sK2,k3_tarski(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3)))) ),
    inference(prop_impl,[status(thm)],[c_19])).

cnf(c_478,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r2_hidden(sK2,k3_tarski(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3))))
    | ~ v3_ordinal1(X0)
    | ~ v3_ordinal1(X1)
    | sK3 != X1
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_171])).

cnf(c_479,plain,
    ( ~ r1_tarski(sK2,sK3)
    | ~ r2_hidden(sK2,k3_tarski(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3))))
    | ~ v3_ordinal1(sK3)
    | ~ v3_ordinal1(sK2) ),
    inference(unflattening,[status(thm)],[c_478])).

cnf(c_22,negated_conjecture,
    ( v3_ordinal1(sK2) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_21,negated_conjecture,
    ( v3_ordinal1(sK3) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_481,plain,
    ( ~ r1_tarski(sK2,sK3)
    | ~ r2_hidden(sK2,k3_tarski(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3)))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_479,c_22,c_21])).

cnf(c_779,plain,
    ( ~ r1_tarski(sK2,sK3)
    | ~ r2_hidden(sK2,k3_tarski(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3)))) ),
    inference(prop_impl,[status(thm)],[c_22,c_21,c_479])).

cnf(c_1694,plain,
    ( r1_tarski(sK2,sK3) != iProver_top
    | r2_hidden(sK2,k3_tarski(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3)))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_779])).

cnf(c_3255,plain,
    ( r1_tarski(sK2,sK3) != iProver_top
    | r2_hidden(sK2,k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1708,c_1694])).

cnf(c_7,plain,
    ( k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) = X0 ),
    inference(cnf_transformation,[],[f100])).

cnf(c_8,plain,
    ( r1_tarski(X0,k3_tarski(X1))
    | ~ r2_hidden(X0,X1) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_1705,plain,
    ( r1_tarski(X0,k3_tarski(X1)) = iProver_top
    | r2_hidden(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_2236,plain,
    ( r1_tarski(X0,X1) = iProver_top
    | r2_hidden(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_7,c_1705])).

cnf(c_3811,plain,
    ( r2_hidden(sK2,k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3)) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_3255,c_2236])).

cnf(c_3266,plain,
    ( ~ r1_tarski(sK2,sK3)
    | ~ r2_hidden(sK2,k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3)) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_3255])).

cnf(c_1219,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_2082,plain,
    ( X0 != X1
    | sK2 != X1
    | sK2 = X0 ),
    inference(instantiation,[status(thm)],[c_1219])).

cnf(c_2498,plain,
    ( X0 != sK2
    | sK2 = X0
    | sK2 != sK2 ),
    inference(instantiation,[status(thm)],[c_2082])).

cnf(c_2499,plain,
    ( sK3 != sK2
    | sK2 = sK3
    | sK2 != sK2 ),
    inference(instantiation,[status(thm)],[c_2498])).

cnf(c_1218,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_2077,plain,
    ( sK2 = sK2 ),
    inference(instantiation,[status(thm)],[c_1218])).

cnf(c_1223,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_1949,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(sK2,sK3)
    | sK3 != X1
    | sK2 != X0 ),
    inference(instantiation,[status(thm)],[c_1223])).

cnf(c_1951,plain,
    ( ~ r1_tarski(sK3,sK3)
    | r1_tarski(sK2,sK3)
    | sK3 != sK3
    | sK2 != sK3 ),
    inference(instantiation,[status(thm)],[c_1949])).

cnf(c_1697,plain,
    ( v3_ordinal1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_9,plain,
    ( ~ v3_ordinal1(X0)
    | v1_ordinal1(X0) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_1704,plain,
    ( v3_ordinal1(X0) != iProver_top
    | v1_ordinal1(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_1940,plain,
    ( v1_ordinal1(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_1697,c_1704])).

cnf(c_5,plain,
    ( r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | ~ r2_hidden(X0,k3_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X1))) ),
    inference(cnf_transformation,[],[f106])).

cnf(c_1926,plain,
    ( r2_hidden(X0,X0)
    | r2_hidden(X0,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))
    | ~ r2_hidden(X0,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)))) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_1928,plain,
    ( r2_hidden(sK3,k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3))
    | ~ r2_hidden(sK3,k3_tarski(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3))))
    | r2_hidden(sK3,sK3) ),
    inference(instantiation,[status(thm)],[c_1926])).

cnf(c_1903,plain,
    ( r2_hidden(sK2,k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3))
    | ~ r2_hidden(sK2,k3_tarski(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3))))
    | r2_hidden(sK2,sK3) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_1904,plain,
    ( r2_hidden(sK2,k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3)) = iProver_top
    | r2_hidden(sK2,k3_tarski(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3)))) != iProver_top
    | r2_hidden(sK2,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1903])).

cnf(c_1220,plain,
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

cnf(c_1225,plain,
    ( k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3) = k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3)
    | sK3 != sK3 ),
    inference(instantiation,[status(thm)],[c_1220])).

cnf(c_6,plain,
    ( ~ r1_tarski(X0,X1)
    | r2_xboole_0(X0,X1)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f60])).

cnf(c_16,plain,
    ( ~ r2_xboole_0(X0,X1)
    | r2_hidden(X0,X1)
    | ~ v3_ordinal1(X1)
    | ~ v1_ordinal1(X0) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_290,plain,
    ( ~ r1_tarski(X0,X1)
    | r2_hidden(X0,X1)
    | ~ v3_ordinal1(X1)
    | ~ v1_ordinal1(X0)
    | X1 = X0 ),
    inference(resolution,[status(thm)],[c_6,c_16])).

cnf(c_14,plain,
    ( ~ r1_ordinal1(X0,X1)
    | r1_tarski(X0,X1)
    | ~ v3_ordinal1(X0)
    | ~ v3_ordinal1(X1) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_20,negated_conjecture,
    ( r1_ordinal1(sK2,sK3)
    | r2_hidden(sK2,k3_tarski(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3)))) ),
    inference(cnf_transformation,[],[f103])).

cnf(c_173,plain,
    ( r1_ordinal1(sK2,sK3)
    | r2_hidden(sK2,k3_tarski(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3)))) ),
    inference(prop_impl,[status(thm)],[c_20])).

cnf(c_492,plain,
    ( r1_tarski(X0,X1)
    | r2_hidden(sK2,k3_tarski(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3))))
    | ~ v3_ordinal1(X0)
    | ~ v3_ordinal1(X1)
    | sK3 != X1
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_173])).

cnf(c_493,plain,
    ( r1_tarski(sK2,sK3)
    | r2_hidden(sK2,k3_tarski(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3))))
    | ~ v3_ordinal1(sK3)
    | ~ v3_ordinal1(sK2) ),
    inference(unflattening,[status(thm)],[c_492])).

cnf(c_495,plain,
    ( r1_tarski(sK2,sK3)
    | r2_hidden(sK2,k3_tarski(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3)))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_493,c_22,c_21])).

cnf(c_619,plain,
    ( r2_hidden(X0,X1)
    | r2_hidden(sK2,k3_tarski(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3))))
    | ~ v3_ordinal1(X1)
    | ~ v1_ordinal1(X0)
    | X1 = X0
    | sK3 != X1
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_290,c_495])).

cnf(c_620,plain,
    ( r2_hidden(sK2,k3_tarski(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3))))
    | r2_hidden(sK2,sK3)
    | ~ v3_ordinal1(sK3)
    | ~ v1_ordinal1(sK2)
    | sK3 = sK2 ),
    inference(unflattening,[status(thm)],[c_619])).

cnf(c_621,plain,
    ( sK3 = sK2
    | r2_hidden(sK2,k3_tarski(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3)))) = iProver_top
    | r2_hidden(sK2,sK3) = iProver_top
    | v3_ordinal1(sK3) != iProver_top
    | v1_ordinal1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_620])).

cnf(c_12,plain,
    ( r1_tarski(X0,X1)
    | ~ r2_hidden(X0,X1)
    | ~ v1_ordinal1(X1) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_605,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(sK2,k3_tarski(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3))))
    | ~ v1_ordinal1(X1)
    | sK3 != X1
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_481])).

cnf(c_606,plain,
    ( ~ r2_hidden(sK2,k3_tarski(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3))))
    | ~ r2_hidden(sK2,sK3)
    | ~ v1_ordinal1(sK3) ),
    inference(unflattening,[status(thm)],[c_605])).

cnf(c_55,plain,
    ( ~ v3_ordinal1(sK3)
    | v1_ordinal1(sK3) ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_608,plain,
    ( ~ r2_hidden(sK2,sK3)
    | ~ r2_hidden(sK2,k3_tarski(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3)))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_606,c_21,c_55])).

cnf(c_609,plain,
    ( ~ r2_hidden(sK2,k3_tarski(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3))))
    | ~ r2_hidden(sK2,sK3) ),
    inference(renaming,[status(thm)],[c_608])).

cnf(c_4,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))) ),
    inference(cnf_transformation,[],[f105])).

cnf(c_616,plain,
    ( ~ r2_hidden(sK2,sK3) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_609,c_4])).

cnf(c_618,plain,
    ( r2_hidden(sK2,sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_616])).

cnf(c_18,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r2_hidden(X1,X0) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_548,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X1,X0)
    | ~ v1_ordinal1(X1) ),
    inference(resolution,[status(thm)],[c_12,c_18])).

cnf(c_550,plain,
    ( ~ r2_hidden(sK3,sK3)
    | ~ v1_ordinal1(sK3) ),
    inference(instantiation,[status(thm)],[c_548])).

cnf(c_17,plain,
    ( r1_ordinal1(X0,X1)
    | r2_hidden(X1,X0)
    | ~ v3_ordinal1(X0)
    | ~ v3_ordinal1(X1) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_445,plain,
    ( r1_tarski(X0,X1)
    | r2_hidden(X1,X0)
    | ~ v3_ordinal1(X0)
    | ~ v3_ordinal1(X1) ),
    inference(resolution,[status(thm)],[c_17,c_14])).

cnf(c_520,plain,
    ( r2_hidden(X0,X1)
    | r2_hidden(X1,X0)
    | ~ v3_ordinal1(X0)
    | ~ v3_ordinal1(X1)
    | ~ v1_ordinal1(X1)
    | X1 = X0 ),
    inference(resolution,[status(thm)],[c_445,c_290])).

cnf(c_522,plain,
    ( r2_hidden(sK3,sK3)
    | ~ v3_ordinal1(sK3)
    | ~ v1_ordinal1(sK3)
    | sK3 = sK3 ),
    inference(instantiation,[status(thm)],[c_520])).

cnf(c_447,plain,
    ( r1_tarski(sK3,sK3)
    | r2_hidden(sK3,sK3)
    | ~ v3_ordinal1(sK3) ),
    inference(instantiation,[status(thm)],[c_445])).

cnf(c_15,plain,
    ( r2_hidden(X0,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)))) ),
    inference(cnf_transformation,[],[f101])).

cnf(c_37,plain,
    ( r2_hidden(sK3,k3_tarski(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3)))) ),
    inference(instantiation,[status(thm)],[c_15])).

cnf(c_24,plain,
    ( v3_ordinal1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_5314,c_3811,c_3266,c_2499,c_2077,c_1951,c_1940,c_1928,c_1904,c_1225,c_621,c_618,c_550,c_522,c_447,c_55,c_37,c_24,c_21])).

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
% 0.13/0.34  % DateTime   : Tue Dec  1 18:21:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 3.48/1.02  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.48/1.02  
% 3.48/1.02  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.48/1.02  
% 3.48/1.02  ------  iProver source info
% 3.48/1.02  
% 3.48/1.02  git: date: 2020-06-30 10:37:57 +0100
% 3.48/1.02  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.48/1.02  git: non_committed_changes: false
% 3.48/1.02  git: last_make_outside_of_git: false
% 3.48/1.02  
% 3.48/1.02  ------ 
% 3.48/1.02  
% 3.48/1.02  ------ Input Options
% 3.48/1.02  
% 3.48/1.02  --out_options                           all
% 3.48/1.02  --tptp_safe_out                         true
% 3.48/1.02  --problem_path                          ""
% 3.48/1.02  --include_path                          ""
% 3.48/1.02  --clausifier                            res/vclausify_rel
% 3.48/1.02  --clausifier_options                    --mode clausify
% 3.48/1.02  --stdin                                 false
% 3.48/1.02  --stats_out                             all
% 3.48/1.02  
% 3.48/1.02  ------ General Options
% 3.48/1.02  
% 3.48/1.02  --fof                                   false
% 3.48/1.02  --time_out_real                         305.
% 3.48/1.02  --time_out_virtual                      -1.
% 3.48/1.02  --symbol_type_check                     false
% 3.48/1.02  --clausify_out                          false
% 3.48/1.02  --sig_cnt_out                           false
% 3.48/1.02  --trig_cnt_out                          false
% 3.48/1.02  --trig_cnt_out_tolerance                1.
% 3.48/1.02  --trig_cnt_out_sk_spl                   false
% 3.48/1.02  --abstr_cl_out                          false
% 3.48/1.02  
% 3.48/1.02  ------ Global Options
% 3.48/1.02  
% 3.48/1.02  --schedule                              default
% 3.48/1.02  --add_important_lit                     false
% 3.48/1.02  --prop_solver_per_cl                    1000
% 3.48/1.02  --min_unsat_core                        false
% 3.48/1.02  --soft_assumptions                      false
% 3.48/1.02  --soft_lemma_size                       3
% 3.48/1.02  --prop_impl_unit_size                   0
% 3.48/1.02  --prop_impl_unit                        []
% 3.48/1.02  --share_sel_clauses                     true
% 3.48/1.02  --reset_solvers                         false
% 3.48/1.02  --bc_imp_inh                            [conj_cone]
% 3.48/1.02  --conj_cone_tolerance                   3.
% 3.48/1.02  --extra_neg_conj                        none
% 3.48/1.02  --large_theory_mode                     true
% 3.48/1.02  --prolific_symb_bound                   200
% 3.48/1.02  --lt_threshold                          2000
% 3.48/1.02  --clause_weak_htbl                      true
% 3.48/1.02  --gc_record_bc_elim                     false
% 3.48/1.02  
% 3.48/1.02  ------ Preprocessing Options
% 3.48/1.02  
% 3.48/1.02  --preprocessing_flag                    true
% 3.48/1.02  --time_out_prep_mult                    0.1
% 3.48/1.02  --splitting_mode                        input
% 3.48/1.02  --splitting_grd                         true
% 3.48/1.02  --splitting_cvd                         false
% 3.48/1.02  --splitting_cvd_svl                     false
% 3.48/1.02  --splitting_nvd                         32
% 3.48/1.02  --sub_typing                            true
% 3.48/1.02  --prep_gs_sim                           true
% 3.48/1.02  --prep_unflatten                        true
% 3.48/1.02  --prep_res_sim                          true
% 3.48/1.02  --prep_upred                            true
% 3.48/1.02  --prep_sem_filter                       exhaustive
% 3.48/1.02  --prep_sem_filter_out                   false
% 3.48/1.02  --pred_elim                             true
% 3.48/1.02  --res_sim_input                         true
% 3.48/1.02  --eq_ax_congr_red                       true
% 3.48/1.02  --pure_diseq_elim                       true
% 3.48/1.02  --brand_transform                       false
% 3.48/1.02  --non_eq_to_eq                          false
% 3.48/1.02  --prep_def_merge                        true
% 3.48/1.02  --prep_def_merge_prop_impl              false
% 3.48/1.02  --prep_def_merge_mbd                    true
% 3.48/1.02  --prep_def_merge_tr_red                 false
% 3.48/1.02  --prep_def_merge_tr_cl                  false
% 3.48/1.02  --smt_preprocessing                     true
% 3.48/1.02  --smt_ac_axioms                         fast
% 3.48/1.02  --preprocessed_out                      false
% 3.48/1.02  --preprocessed_stats                    false
% 3.48/1.02  
% 3.48/1.02  ------ Abstraction refinement Options
% 3.48/1.02  
% 3.48/1.02  --abstr_ref                             []
% 3.48/1.02  --abstr_ref_prep                        false
% 3.48/1.02  --abstr_ref_until_sat                   false
% 3.48/1.02  --abstr_ref_sig_restrict                funpre
% 3.48/1.02  --abstr_ref_af_restrict_to_split_sk     false
% 3.48/1.02  --abstr_ref_under                       []
% 3.48/1.02  
% 3.48/1.02  ------ SAT Options
% 3.48/1.02  
% 3.48/1.02  --sat_mode                              false
% 3.48/1.02  --sat_fm_restart_options                ""
% 3.48/1.02  --sat_gr_def                            false
% 3.48/1.02  --sat_epr_types                         true
% 3.48/1.02  --sat_non_cyclic_types                  false
% 3.48/1.02  --sat_finite_models                     false
% 3.48/1.02  --sat_fm_lemmas                         false
% 3.48/1.02  --sat_fm_prep                           false
% 3.48/1.02  --sat_fm_uc_incr                        true
% 3.48/1.02  --sat_out_model                         small
% 3.48/1.02  --sat_out_clauses                       false
% 3.48/1.02  
% 3.48/1.02  ------ QBF Options
% 3.48/1.02  
% 3.48/1.02  --qbf_mode                              false
% 3.48/1.02  --qbf_elim_univ                         false
% 3.48/1.02  --qbf_dom_inst                          none
% 3.48/1.02  --qbf_dom_pre_inst                      false
% 3.48/1.02  --qbf_sk_in                             false
% 3.48/1.02  --qbf_pred_elim                         true
% 3.48/1.02  --qbf_split                             512
% 3.48/1.02  
% 3.48/1.02  ------ BMC1 Options
% 3.48/1.02  
% 3.48/1.02  --bmc1_incremental                      false
% 3.48/1.02  --bmc1_axioms                           reachable_all
% 3.48/1.02  --bmc1_min_bound                        0
% 3.48/1.02  --bmc1_max_bound                        -1
% 3.48/1.02  --bmc1_max_bound_default                -1
% 3.48/1.02  --bmc1_symbol_reachability              true
% 3.48/1.02  --bmc1_property_lemmas                  false
% 3.48/1.02  --bmc1_k_induction                      false
% 3.48/1.02  --bmc1_non_equiv_states                 false
% 3.48/1.02  --bmc1_deadlock                         false
% 3.48/1.02  --bmc1_ucm                              false
% 3.48/1.02  --bmc1_add_unsat_core                   none
% 3.48/1.02  --bmc1_unsat_core_children              false
% 3.48/1.02  --bmc1_unsat_core_extrapolate_axioms    false
% 3.48/1.02  --bmc1_out_stat                         full
% 3.48/1.02  --bmc1_ground_init                      false
% 3.48/1.02  --bmc1_pre_inst_next_state              false
% 3.48/1.02  --bmc1_pre_inst_state                   false
% 3.48/1.02  --bmc1_pre_inst_reach_state             false
% 3.48/1.02  --bmc1_out_unsat_core                   false
% 3.48/1.02  --bmc1_aig_witness_out                  false
% 3.48/1.02  --bmc1_verbose                          false
% 3.48/1.02  --bmc1_dump_clauses_tptp                false
% 3.48/1.02  --bmc1_dump_unsat_core_tptp             false
% 3.48/1.02  --bmc1_dump_file                        -
% 3.48/1.02  --bmc1_ucm_expand_uc_limit              128
% 3.48/1.02  --bmc1_ucm_n_expand_iterations          6
% 3.48/1.02  --bmc1_ucm_extend_mode                  1
% 3.48/1.02  --bmc1_ucm_init_mode                    2
% 3.48/1.02  --bmc1_ucm_cone_mode                    none
% 3.48/1.02  --bmc1_ucm_reduced_relation_type        0
% 3.48/1.02  --bmc1_ucm_relax_model                  4
% 3.48/1.02  --bmc1_ucm_full_tr_after_sat            true
% 3.48/1.02  --bmc1_ucm_expand_neg_assumptions       false
% 3.48/1.02  --bmc1_ucm_layered_model                none
% 3.48/1.02  --bmc1_ucm_max_lemma_size               10
% 3.48/1.02  
% 3.48/1.02  ------ AIG Options
% 3.48/1.02  
% 3.48/1.02  --aig_mode                              false
% 3.48/1.02  
% 3.48/1.02  ------ Instantiation Options
% 3.48/1.02  
% 3.48/1.02  --instantiation_flag                    true
% 3.48/1.02  --inst_sos_flag                         false
% 3.48/1.02  --inst_sos_phase                        true
% 3.48/1.02  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.48/1.02  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.48/1.02  --inst_lit_sel_side                     num_symb
% 3.48/1.02  --inst_solver_per_active                1400
% 3.48/1.02  --inst_solver_calls_frac                1.
% 3.48/1.02  --inst_passive_queue_type               priority_queues
% 3.48/1.02  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.48/1.02  --inst_passive_queues_freq              [25;2]
% 3.48/1.02  --inst_dismatching                      true
% 3.48/1.02  --inst_eager_unprocessed_to_passive     true
% 3.48/1.02  --inst_prop_sim_given                   true
% 3.48/1.02  --inst_prop_sim_new                     false
% 3.48/1.02  --inst_subs_new                         false
% 3.48/1.02  --inst_eq_res_simp                      false
% 3.48/1.02  --inst_subs_given                       false
% 3.48/1.02  --inst_orphan_elimination               true
% 3.48/1.02  --inst_learning_loop_flag               true
% 3.48/1.02  --inst_learning_start                   3000
% 3.48/1.02  --inst_learning_factor                  2
% 3.48/1.02  --inst_start_prop_sim_after_learn       3
% 3.48/1.02  --inst_sel_renew                        solver
% 3.48/1.02  --inst_lit_activity_flag                true
% 3.48/1.02  --inst_restr_to_given                   false
% 3.48/1.02  --inst_activity_threshold               500
% 3.48/1.02  --inst_out_proof                        true
% 3.48/1.02  
% 3.48/1.02  ------ Resolution Options
% 3.48/1.02  
% 3.48/1.02  --resolution_flag                       true
% 3.48/1.02  --res_lit_sel                           adaptive
% 3.48/1.02  --res_lit_sel_side                      none
% 3.48/1.02  --res_ordering                          kbo
% 3.48/1.02  --res_to_prop_solver                    active
% 3.48/1.02  --res_prop_simpl_new                    false
% 3.48/1.02  --res_prop_simpl_given                  true
% 3.48/1.02  --res_passive_queue_type                priority_queues
% 3.48/1.02  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.48/1.02  --res_passive_queues_freq               [15;5]
% 3.48/1.02  --res_forward_subs                      full
% 3.48/1.02  --res_backward_subs                     full
% 3.48/1.02  --res_forward_subs_resolution           true
% 3.48/1.02  --res_backward_subs_resolution          true
% 3.48/1.02  --res_orphan_elimination                true
% 3.48/1.02  --res_time_limit                        2.
% 3.48/1.02  --res_out_proof                         true
% 3.48/1.02  
% 3.48/1.02  ------ Superposition Options
% 3.48/1.02  
% 3.48/1.02  --superposition_flag                    true
% 3.48/1.02  --sup_passive_queue_type                priority_queues
% 3.48/1.02  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.48/1.02  --sup_passive_queues_freq               [8;1;4]
% 3.48/1.02  --demod_completeness_check              fast
% 3.48/1.02  --demod_use_ground                      true
% 3.48/1.02  --sup_to_prop_solver                    passive
% 3.48/1.02  --sup_prop_simpl_new                    true
% 3.48/1.02  --sup_prop_simpl_given                  true
% 3.48/1.02  --sup_fun_splitting                     false
% 3.48/1.02  --sup_smt_interval                      50000
% 3.48/1.02  
% 3.48/1.02  ------ Superposition Simplification Setup
% 3.48/1.02  
% 3.48/1.02  --sup_indices_passive                   []
% 3.48/1.02  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.48/1.02  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.48/1.02  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.48/1.02  --sup_full_triv                         [TrivRules;PropSubs]
% 3.48/1.02  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.48/1.02  --sup_full_bw                           [BwDemod]
% 3.48/1.02  --sup_immed_triv                        [TrivRules]
% 3.48/1.02  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.48/1.02  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.48/1.02  --sup_immed_bw_main                     []
% 3.48/1.02  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.48/1.02  --sup_input_triv                        [Unflattening;TrivRules]
% 3.48/1.02  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.48/1.02  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.48/1.02  
% 3.48/1.02  ------ Combination Options
% 3.48/1.02  
% 3.48/1.02  --comb_res_mult                         3
% 3.48/1.02  --comb_sup_mult                         2
% 3.48/1.02  --comb_inst_mult                        10
% 3.48/1.02  
% 3.48/1.02  ------ Debug Options
% 3.48/1.02  
% 3.48/1.02  --dbg_backtrace                         false
% 3.48/1.02  --dbg_dump_prop_clauses                 false
% 3.48/1.02  --dbg_dump_prop_clauses_file            -
% 3.48/1.02  --dbg_out_stat                          false
% 3.48/1.02  ------ Parsing...
% 3.48/1.02  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.48/1.02  
% 3.48/1.02  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 3.48/1.02  
% 3.48/1.02  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.48/1.02  
% 3.48/1.02  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.48/1.02  ------ Proving...
% 3.48/1.02  ------ Problem Properties 
% 3.48/1.02  
% 3.48/1.02  
% 3.48/1.02  clauses                                 21
% 3.48/1.02  conjectures                             2
% 3.48/1.02  EPR                                     8
% 3.48/1.02  Horn                                    14
% 3.48/1.02  unary                                   4
% 3.48/1.02  binary                                  10
% 3.48/1.02  lits                                    49
% 3.48/1.02  lits eq                                 5
% 3.48/1.02  fd_pure                                 0
% 3.48/1.02  fd_pseudo                               0
% 3.48/1.02  fd_cond                                 0
% 3.48/1.02  fd_pseudo_cond                          4
% 3.48/1.02  AC symbols                              0
% 3.48/1.02  
% 3.48/1.02  ------ Schedule dynamic 5 is on 
% 3.48/1.02  
% 3.48/1.02  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.48/1.02  
% 3.48/1.02  
% 3.48/1.02  ------ 
% 3.48/1.02  Current options:
% 3.48/1.02  ------ 
% 3.48/1.02  
% 3.48/1.02  ------ Input Options
% 3.48/1.02  
% 3.48/1.02  --out_options                           all
% 3.48/1.02  --tptp_safe_out                         true
% 3.48/1.02  --problem_path                          ""
% 3.48/1.02  --include_path                          ""
% 3.48/1.02  --clausifier                            res/vclausify_rel
% 3.48/1.02  --clausifier_options                    --mode clausify
% 3.48/1.02  --stdin                                 false
% 3.48/1.02  --stats_out                             all
% 3.48/1.02  
% 3.48/1.02  ------ General Options
% 3.48/1.02  
% 3.48/1.02  --fof                                   false
% 3.48/1.02  --time_out_real                         305.
% 3.48/1.02  --time_out_virtual                      -1.
% 3.48/1.02  --symbol_type_check                     false
% 3.48/1.02  --clausify_out                          false
% 3.48/1.02  --sig_cnt_out                           false
% 3.48/1.02  --trig_cnt_out                          false
% 3.48/1.02  --trig_cnt_out_tolerance                1.
% 3.48/1.02  --trig_cnt_out_sk_spl                   false
% 3.48/1.02  --abstr_cl_out                          false
% 3.48/1.02  
% 3.48/1.02  ------ Global Options
% 3.48/1.02  
% 3.48/1.02  --schedule                              default
% 3.48/1.02  --add_important_lit                     false
% 3.48/1.02  --prop_solver_per_cl                    1000
% 3.48/1.02  --min_unsat_core                        false
% 3.48/1.02  --soft_assumptions                      false
% 3.48/1.02  --soft_lemma_size                       3
% 3.48/1.02  --prop_impl_unit_size                   0
% 3.48/1.02  --prop_impl_unit                        []
% 3.48/1.02  --share_sel_clauses                     true
% 3.48/1.02  --reset_solvers                         false
% 3.48/1.02  --bc_imp_inh                            [conj_cone]
% 3.48/1.02  --conj_cone_tolerance                   3.
% 3.48/1.02  --extra_neg_conj                        none
% 3.48/1.02  --large_theory_mode                     true
% 3.48/1.02  --prolific_symb_bound                   200
% 3.48/1.02  --lt_threshold                          2000
% 3.48/1.02  --clause_weak_htbl                      true
% 3.48/1.02  --gc_record_bc_elim                     false
% 3.48/1.02  
% 3.48/1.02  ------ Preprocessing Options
% 3.48/1.02  
% 3.48/1.02  --preprocessing_flag                    true
% 3.48/1.02  --time_out_prep_mult                    0.1
% 3.48/1.02  --splitting_mode                        input
% 3.48/1.02  --splitting_grd                         true
% 3.48/1.02  --splitting_cvd                         false
% 3.48/1.02  --splitting_cvd_svl                     false
% 3.48/1.02  --splitting_nvd                         32
% 3.48/1.02  --sub_typing                            true
% 3.48/1.02  --prep_gs_sim                           true
% 3.48/1.02  --prep_unflatten                        true
% 3.48/1.02  --prep_res_sim                          true
% 3.48/1.02  --prep_upred                            true
% 3.48/1.02  --prep_sem_filter                       exhaustive
% 3.48/1.02  --prep_sem_filter_out                   false
% 3.48/1.02  --pred_elim                             true
% 3.48/1.02  --res_sim_input                         true
% 3.48/1.02  --eq_ax_congr_red                       true
% 3.48/1.02  --pure_diseq_elim                       true
% 3.48/1.02  --brand_transform                       false
% 3.48/1.02  --non_eq_to_eq                          false
% 3.48/1.02  --prep_def_merge                        true
% 3.48/1.02  --prep_def_merge_prop_impl              false
% 3.48/1.02  --prep_def_merge_mbd                    true
% 3.48/1.02  --prep_def_merge_tr_red                 false
% 3.48/1.02  --prep_def_merge_tr_cl                  false
% 3.48/1.02  --smt_preprocessing                     true
% 3.48/1.02  --smt_ac_axioms                         fast
% 3.48/1.02  --preprocessed_out                      false
% 3.48/1.02  --preprocessed_stats                    false
% 3.48/1.02  
% 3.48/1.02  ------ Abstraction refinement Options
% 3.48/1.02  
% 3.48/1.02  --abstr_ref                             []
% 3.48/1.02  --abstr_ref_prep                        false
% 3.48/1.02  --abstr_ref_until_sat                   false
% 3.48/1.02  --abstr_ref_sig_restrict                funpre
% 3.48/1.02  --abstr_ref_af_restrict_to_split_sk     false
% 3.48/1.02  --abstr_ref_under                       []
% 3.48/1.02  
% 3.48/1.02  ------ SAT Options
% 3.48/1.02  
% 3.48/1.02  --sat_mode                              false
% 3.48/1.02  --sat_fm_restart_options                ""
% 3.48/1.02  --sat_gr_def                            false
% 3.48/1.02  --sat_epr_types                         true
% 3.48/1.02  --sat_non_cyclic_types                  false
% 3.48/1.02  --sat_finite_models                     false
% 3.48/1.02  --sat_fm_lemmas                         false
% 3.48/1.02  --sat_fm_prep                           false
% 3.48/1.02  --sat_fm_uc_incr                        true
% 3.48/1.02  --sat_out_model                         small
% 3.48/1.02  --sat_out_clauses                       false
% 3.48/1.02  
% 3.48/1.02  ------ QBF Options
% 3.48/1.02  
% 3.48/1.02  --qbf_mode                              false
% 3.48/1.02  --qbf_elim_univ                         false
% 3.48/1.02  --qbf_dom_inst                          none
% 3.48/1.02  --qbf_dom_pre_inst                      false
% 3.48/1.02  --qbf_sk_in                             false
% 3.48/1.02  --qbf_pred_elim                         true
% 3.48/1.02  --qbf_split                             512
% 3.48/1.02  
% 3.48/1.02  ------ BMC1 Options
% 3.48/1.02  
% 3.48/1.02  --bmc1_incremental                      false
% 3.48/1.02  --bmc1_axioms                           reachable_all
% 3.48/1.02  --bmc1_min_bound                        0
% 3.48/1.02  --bmc1_max_bound                        -1
% 3.48/1.02  --bmc1_max_bound_default                -1
% 3.48/1.02  --bmc1_symbol_reachability              true
% 3.48/1.02  --bmc1_property_lemmas                  false
% 3.48/1.02  --bmc1_k_induction                      false
% 3.48/1.02  --bmc1_non_equiv_states                 false
% 3.48/1.02  --bmc1_deadlock                         false
% 3.48/1.02  --bmc1_ucm                              false
% 3.48/1.02  --bmc1_add_unsat_core                   none
% 3.48/1.02  --bmc1_unsat_core_children              false
% 3.48/1.02  --bmc1_unsat_core_extrapolate_axioms    false
% 3.48/1.02  --bmc1_out_stat                         full
% 3.48/1.02  --bmc1_ground_init                      false
% 3.48/1.02  --bmc1_pre_inst_next_state              false
% 3.48/1.02  --bmc1_pre_inst_state                   false
% 3.48/1.02  --bmc1_pre_inst_reach_state             false
% 3.48/1.02  --bmc1_out_unsat_core                   false
% 3.48/1.02  --bmc1_aig_witness_out                  false
% 3.48/1.02  --bmc1_verbose                          false
% 3.48/1.02  --bmc1_dump_clauses_tptp                false
% 3.48/1.02  --bmc1_dump_unsat_core_tptp             false
% 3.48/1.02  --bmc1_dump_file                        -
% 3.48/1.02  --bmc1_ucm_expand_uc_limit              128
% 3.48/1.02  --bmc1_ucm_n_expand_iterations          6
% 3.48/1.02  --bmc1_ucm_extend_mode                  1
% 3.48/1.02  --bmc1_ucm_init_mode                    2
% 3.48/1.02  --bmc1_ucm_cone_mode                    none
% 3.48/1.02  --bmc1_ucm_reduced_relation_type        0
% 3.48/1.02  --bmc1_ucm_relax_model                  4
% 3.48/1.02  --bmc1_ucm_full_tr_after_sat            true
% 3.48/1.02  --bmc1_ucm_expand_neg_assumptions       false
% 3.48/1.02  --bmc1_ucm_layered_model                none
% 3.48/1.02  --bmc1_ucm_max_lemma_size               10
% 3.48/1.02  
% 3.48/1.02  ------ AIG Options
% 3.48/1.02  
% 3.48/1.02  --aig_mode                              false
% 3.48/1.02  
% 3.48/1.02  ------ Instantiation Options
% 3.48/1.02  
% 3.48/1.02  --instantiation_flag                    true
% 3.48/1.02  --inst_sos_flag                         false
% 3.48/1.02  --inst_sos_phase                        true
% 3.48/1.02  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.48/1.02  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.48/1.02  --inst_lit_sel_side                     none
% 3.48/1.02  --inst_solver_per_active                1400
% 3.48/1.02  --inst_solver_calls_frac                1.
% 3.48/1.02  --inst_passive_queue_type               priority_queues
% 3.48/1.02  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.48/1.02  --inst_passive_queues_freq              [25;2]
% 3.48/1.02  --inst_dismatching                      true
% 3.48/1.02  --inst_eager_unprocessed_to_passive     true
% 3.48/1.02  --inst_prop_sim_given                   true
% 3.48/1.02  --inst_prop_sim_new                     false
% 3.48/1.02  --inst_subs_new                         false
% 3.48/1.02  --inst_eq_res_simp                      false
% 3.48/1.02  --inst_subs_given                       false
% 3.48/1.02  --inst_orphan_elimination               true
% 3.48/1.02  --inst_learning_loop_flag               true
% 3.48/1.02  --inst_learning_start                   3000
% 3.48/1.02  --inst_learning_factor                  2
% 3.48/1.02  --inst_start_prop_sim_after_learn       3
% 3.48/1.02  --inst_sel_renew                        solver
% 3.48/1.02  --inst_lit_activity_flag                true
% 3.48/1.02  --inst_restr_to_given                   false
% 3.48/1.02  --inst_activity_threshold               500
% 3.48/1.02  --inst_out_proof                        true
% 3.48/1.02  
% 3.48/1.02  ------ Resolution Options
% 3.48/1.02  
% 3.48/1.02  --resolution_flag                       false
% 3.48/1.02  --res_lit_sel                           adaptive
% 3.48/1.02  --res_lit_sel_side                      none
% 3.48/1.02  --res_ordering                          kbo
% 3.48/1.02  --res_to_prop_solver                    active
% 3.48/1.02  --res_prop_simpl_new                    false
% 3.48/1.02  --res_prop_simpl_given                  true
% 3.48/1.02  --res_passive_queue_type                priority_queues
% 3.48/1.02  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.48/1.02  --res_passive_queues_freq               [15;5]
% 3.48/1.02  --res_forward_subs                      full
% 3.48/1.02  --res_backward_subs                     full
% 3.48/1.02  --res_forward_subs_resolution           true
% 3.48/1.02  --res_backward_subs_resolution          true
% 3.48/1.02  --res_orphan_elimination                true
% 3.48/1.02  --res_time_limit                        2.
% 3.48/1.02  --res_out_proof                         true
% 3.48/1.02  
% 3.48/1.02  ------ Superposition Options
% 3.48/1.02  
% 3.48/1.02  --superposition_flag                    true
% 3.48/1.02  --sup_passive_queue_type                priority_queues
% 3.48/1.02  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.48/1.02  --sup_passive_queues_freq               [8;1;4]
% 3.48/1.02  --demod_completeness_check              fast
% 3.48/1.02  --demod_use_ground                      true
% 3.48/1.02  --sup_to_prop_solver                    passive
% 3.48/1.02  --sup_prop_simpl_new                    true
% 3.48/1.02  --sup_prop_simpl_given                  true
% 3.48/1.02  --sup_fun_splitting                     false
% 3.48/1.02  --sup_smt_interval                      50000
% 3.48/1.02  
% 3.48/1.02  ------ Superposition Simplification Setup
% 3.48/1.02  
% 3.48/1.02  --sup_indices_passive                   []
% 3.48/1.02  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.48/1.02  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.48/1.02  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.48/1.02  --sup_full_triv                         [TrivRules;PropSubs]
% 3.48/1.02  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.48/1.02  --sup_full_bw                           [BwDemod]
% 3.48/1.02  --sup_immed_triv                        [TrivRules]
% 3.48/1.02  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.48/1.02  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.48/1.02  --sup_immed_bw_main                     []
% 3.48/1.02  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.48/1.02  --sup_input_triv                        [Unflattening;TrivRules]
% 3.48/1.02  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.48/1.02  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.48/1.02  
% 3.48/1.02  ------ Combination Options
% 3.48/1.02  
% 3.48/1.02  --comb_res_mult                         3
% 3.48/1.02  --comb_sup_mult                         2
% 3.48/1.02  --comb_inst_mult                        10
% 3.48/1.02  
% 3.48/1.02  ------ Debug Options
% 3.48/1.02  
% 3.48/1.02  --dbg_backtrace                         false
% 3.48/1.02  --dbg_dump_prop_clauses                 false
% 3.48/1.02  --dbg_dump_prop_clauses_file            -
% 3.48/1.02  --dbg_out_stat                          false
% 3.48/1.02  
% 3.48/1.02  
% 3.48/1.02  
% 3.48/1.02  
% 3.48/1.02  ------ Proving...
% 3.48/1.02  
% 3.48/1.02  
% 3.48/1.02  % SZS status Theorem for theBenchmark.p
% 3.48/1.02  
% 3.48/1.02  % SZS output start CNFRefutation for theBenchmark.p
% 3.48/1.02  
% 3.48/1.02  fof(f1,axiom,(
% 3.48/1.02    ! [X0,X1,X2] : (k2_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) | r2_hidden(X3,X0))))),
% 3.48/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.48/1.02  
% 3.48/1.02  fof(f39,plain,(
% 3.48/1.02    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) | r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) & ~r2_hidden(X3,X0))) & ((r2_hidden(X3,X1) | r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k2_xboole_0(X0,X1) != X2))),
% 3.48/1.02    inference(nnf_transformation,[],[f1])).
% 3.48/1.02  
% 3.48/1.02  fof(f40,plain,(
% 3.48/1.02    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) & ~r2_hidden(X3,X0))) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | ~r2_hidden(X3,X2))) | k2_xboole_0(X0,X1) != X2))),
% 3.48/1.02    inference(flattening,[],[f39])).
% 3.48/1.02  
% 3.48/1.02  fof(f41,plain,(
% 3.48/1.02    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (~r2_hidden(X4,X1) & ~r2_hidden(X4,X0))) & (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,X2))) | k2_xboole_0(X0,X1) != X2))),
% 3.48/1.02    inference(rectify,[],[f40])).
% 3.48/1.02  
% 3.48/1.02  fof(f42,plain,(
% 3.48/1.02    ! [X2,X1,X0] : (? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2))) => (((~r2_hidden(sK0(X0,X1,X2),X1) & ~r2_hidden(sK0(X0,X1,X2),X0)) | ~r2_hidden(sK0(X0,X1,X2),X2)) & (r2_hidden(sK0(X0,X1,X2),X1) | r2_hidden(sK0(X0,X1,X2),X0) | r2_hidden(sK0(X0,X1,X2),X2))))),
% 3.48/1.02    introduced(choice_axiom,[])).
% 3.48/1.02  
% 3.48/1.02  fof(f43,plain,(
% 3.48/1.02    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | (((~r2_hidden(sK0(X0,X1,X2),X1) & ~r2_hidden(sK0(X0,X1,X2),X0)) | ~r2_hidden(sK0(X0,X1,X2),X2)) & (r2_hidden(sK0(X0,X1,X2),X1) | r2_hidden(sK0(X0,X1,X2),X0) | r2_hidden(sK0(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (~r2_hidden(X4,X1) & ~r2_hidden(X4,X0))) & (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,X2))) | k2_xboole_0(X0,X1) != X2))),
% 3.48/1.02    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f41,f42])).
% 3.48/1.02  
% 3.48/1.02  fof(f56,plain,(
% 3.48/1.02    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | k2_xboole_0(X0,X1) != X2) )),
% 3.48/1.02    inference(cnf_transformation,[],[f43])).
% 3.48/1.02  
% 3.48/1.02  fof(f12,axiom,(
% 3.48/1.02    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 3.48/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.48/1.02  
% 3.48/1.02  fof(f70,plain,(
% 3.48/1.02    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 3.48/1.02    inference(cnf_transformation,[],[f12])).
% 3.48/1.02  
% 3.48/1.02  fof(f5,axiom,(
% 3.48/1.02    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 3.48/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.48/1.02  
% 3.48/1.02  fof(f63,plain,(
% 3.48/1.02    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 3.48/1.02    inference(cnf_transformation,[],[f5])).
% 3.48/1.02  
% 3.48/1.02  fof(f6,axiom,(
% 3.48/1.02    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 3.48/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.48/1.02  
% 3.48/1.02  fof(f64,plain,(
% 3.48/1.02    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 3.48/1.02    inference(cnf_transformation,[],[f6])).
% 3.48/1.02  
% 3.48/1.02  fof(f7,axiom,(
% 3.48/1.02    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 3.48/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.48/1.02  
% 3.48/1.02  fof(f65,plain,(
% 3.48/1.02    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 3.48/1.02    inference(cnf_transformation,[],[f7])).
% 3.48/1.02  
% 3.48/1.02  fof(f8,axiom,(
% 3.48/1.02    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)),
% 3.48/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.48/1.02  
% 3.48/1.02  fof(f66,plain,(
% 3.48/1.02    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)) )),
% 3.48/1.02    inference(cnf_transformation,[],[f8])).
% 3.48/1.02  
% 3.48/1.02  fof(f9,axiom,(
% 3.48/1.02    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)),
% 3.48/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.48/1.02  
% 3.48/1.02  fof(f67,plain,(
% 3.48/1.02    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)) )),
% 3.48/1.02    inference(cnf_transformation,[],[f9])).
% 3.48/1.02  
% 3.48/1.02  fof(f10,axiom,(
% 3.48/1.02    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)),
% 3.48/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.48/1.02  
% 3.48/1.02  fof(f68,plain,(
% 3.48/1.02    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)) )),
% 3.48/1.02    inference(cnf_transformation,[],[f10])).
% 3.48/1.02  
% 3.48/1.02  fof(f86,plain,(
% 3.48/1.02    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 3.48/1.02    inference(definition_unfolding,[],[f67,f68])).
% 3.48/1.02  
% 3.48/1.02  fof(f87,plain,(
% 3.48/1.02    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 3.48/1.02    inference(definition_unfolding,[],[f66,f86])).
% 3.48/1.02  
% 3.48/1.02  fof(f88,plain,(
% 3.48/1.02    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 3.48/1.02    inference(definition_unfolding,[],[f65,f87])).
% 3.48/1.02  
% 3.48/1.02  fof(f89,plain,(
% 3.48/1.02    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 3.48/1.02    inference(definition_unfolding,[],[f64,f88])).
% 3.48/1.02  
% 3.48/1.02  fof(f90,plain,(
% 3.48/1.02    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 3.48/1.02    inference(definition_unfolding,[],[f63,f89])).
% 3.48/1.02  
% 3.48/1.02  fof(f91,plain,(
% 3.48/1.02    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) )),
% 3.48/1.02    inference(definition_unfolding,[],[f70,f90])).
% 3.48/1.02  
% 3.48/1.02  fof(f97,plain,(
% 3.48/1.02    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) != X2) )),
% 3.48/1.02    inference(definition_unfolding,[],[f56,f91])).
% 3.48/1.02  
% 3.48/1.02  fof(f104,plain,(
% 3.48/1.02    ( ! [X4,X0,X1] : (r2_hidden(X4,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) | ~r2_hidden(X4,X1)) )),
% 3.48/1.02    inference(equality_resolution,[],[f97])).
% 3.48/1.02  
% 3.48/1.02  fof(f16,axiom,(
% 3.48/1.02    ! [X0,X1] : ((v3_ordinal1(X1) & v3_ordinal1(X0)) => (r1_ordinal1(X0,X1) <=> r1_tarski(X0,X1)))),
% 3.48/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.48/1.02  
% 3.48/1.02  fof(f31,plain,(
% 3.48/1.02    ! [X0,X1] : ((r1_ordinal1(X0,X1) <=> r1_tarski(X0,X1)) | (~v3_ordinal1(X1) | ~v3_ordinal1(X0)))),
% 3.48/1.02    inference(ennf_transformation,[],[f16])).
% 3.48/1.02  
% 3.48/1.02  fof(f32,plain,(
% 3.48/1.02    ! [X0,X1] : ((r1_ordinal1(X0,X1) <=> r1_tarski(X0,X1)) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0))),
% 3.48/1.02    inference(flattening,[],[f31])).
% 3.48/1.02  
% 3.48/1.02  fof(f48,plain,(
% 3.48/1.02    ! [X0,X1] : (((r1_ordinal1(X0,X1) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~r1_ordinal1(X0,X1))) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0))),
% 3.48/1.02    inference(nnf_transformation,[],[f32])).
% 3.48/1.02  
% 3.48/1.02  fof(f77,plain,(
% 3.48/1.02    ( ! [X0,X1] : (r1_ordinal1(X0,X1) | ~r1_tarski(X0,X1) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0)) )),
% 3.48/1.02    inference(cnf_transformation,[],[f48])).
% 3.48/1.02  
% 3.48/1.02  fof(f21,conjecture,(
% 3.48/1.02    ! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => (r2_hidden(X0,k1_ordinal1(X1)) <=> r1_ordinal1(X0,X1))))),
% 3.48/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.48/1.02  
% 3.48/1.02  fof(f22,negated_conjecture,(
% 3.48/1.02    ~! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => (r2_hidden(X0,k1_ordinal1(X1)) <=> r1_ordinal1(X0,X1))))),
% 3.48/1.02    inference(negated_conjecture,[],[f21])).
% 3.48/1.02  
% 3.48/1.02  fof(f38,plain,(
% 3.48/1.02    ? [X0] : (? [X1] : ((r2_hidden(X0,k1_ordinal1(X1)) <~> r1_ordinal1(X0,X1)) & v3_ordinal1(X1)) & v3_ordinal1(X0))),
% 3.48/1.02    inference(ennf_transformation,[],[f22])).
% 3.48/1.02  
% 3.48/1.02  fof(f49,plain,(
% 3.48/1.02    ? [X0] : (? [X1] : (((~r1_ordinal1(X0,X1) | ~r2_hidden(X0,k1_ordinal1(X1))) & (r1_ordinal1(X0,X1) | r2_hidden(X0,k1_ordinal1(X1)))) & v3_ordinal1(X1)) & v3_ordinal1(X0))),
% 3.48/1.02    inference(nnf_transformation,[],[f38])).
% 3.48/1.02  
% 3.48/1.02  fof(f50,plain,(
% 3.48/1.02    ? [X0] : (? [X1] : ((~r1_ordinal1(X0,X1) | ~r2_hidden(X0,k1_ordinal1(X1))) & (r1_ordinal1(X0,X1) | r2_hidden(X0,k1_ordinal1(X1))) & v3_ordinal1(X1)) & v3_ordinal1(X0))),
% 3.48/1.02    inference(flattening,[],[f49])).
% 3.48/1.02  
% 3.48/1.02  fof(f52,plain,(
% 3.48/1.02    ( ! [X0] : (? [X1] : ((~r1_ordinal1(X0,X1) | ~r2_hidden(X0,k1_ordinal1(X1))) & (r1_ordinal1(X0,X1) | r2_hidden(X0,k1_ordinal1(X1))) & v3_ordinal1(X1)) => ((~r1_ordinal1(X0,sK3) | ~r2_hidden(X0,k1_ordinal1(sK3))) & (r1_ordinal1(X0,sK3) | r2_hidden(X0,k1_ordinal1(sK3))) & v3_ordinal1(sK3))) )),
% 3.48/1.02    introduced(choice_axiom,[])).
% 3.48/1.02  
% 3.48/1.02  fof(f51,plain,(
% 3.48/1.02    ? [X0] : (? [X1] : ((~r1_ordinal1(X0,X1) | ~r2_hidden(X0,k1_ordinal1(X1))) & (r1_ordinal1(X0,X1) | r2_hidden(X0,k1_ordinal1(X1))) & v3_ordinal1(X1)) & v3_ordinal1(X0)) => (? [X1] : ((~r1_ordinal1(sK2,X1) | ~r2_hidden(sK2,k1_ordinal1(X1))) & (r1_ordinal1(sK2,X1) | r2_hidden(sK2,k1_ordinal1(X1))) & v3_ordinal1(X1)) & v3_ordinal1(sK2))),
% 3.48/1.02    introduced(choice_axiom,[])).
% 3.48/1.02  
% 3.48/1.02  fof(f53,plain,(
% 3.48/1.02    ((~r1_ordinal1(sK2,sK3) | ~r2_hidden(sK2,k1_ordinal1(sK3))) & (r1_ordinal1(sK2,sK3) | r2_hidden(sK2,k1_ordinal1(sK3))) & v3_ordinal1(sK3)) & v3_ordinal1(sK2)),
% 3.48/1.02    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f50,f52,f51])).
% 3.48/1.02  
% 3.48/1.02  fof(f85,plain,(
% 3.48/1.02    ~r1_ordinal1(sK2,sK3) | ~r2_hidden(sK2,k1_ordinal1(sK3))),
% 3.48/1.02    inference(cnf_transformation,[],[f53])).
% 3.48/1.02  
% 3.48/1.02  fof(f14,axiom,(
% 3.48/1.02    ! [X0] : k2_xboole_0(X0,k1_tarski(X0)) = k1_ordinal1(X0)),
% 3.48/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.48/1.02  
% 3.48/1.02  fof(f72,plain,(
% 3.48/1.02    ( ! [X0] : (k2_xboole_0(X0,k1_tarski(X0)) = k1_ordinal1(X0)) )),
% 3.48/1.02    inference(cnf_transformation,[],[f14])).
% 3.48/1.02  
% 3.48/1.02  fof(f4,axiom,(
% 3.48/1.02    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 3.48/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.48/1.02  
% 3.48/1.02  fof(f62,plain,(
% 3.48/1.02    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 3.48/1.02    inference(cnf_transformation,[],[f4])).
% 3.48/1.02  
% 3.48/1.02  fof(f92,plain,(
% 3.48/1.02    ( ! [X0] : (k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) )),
% 3.48/1.02    inference(definition_unfolding,[],[f62,f90])).
% 3.48/1.02  
% 3.48/1.02  fof(f93,plain,(
% 3.48/1.02    ( ! [X0] : (k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))) = k1_ordinal1(X0)) )),
% 3.48/1.02    inference(definition_unfolding,[],[f72,f91,f92])).
% 3.48/1.02  
% 3.48/1.02  fof(f102,plain,(
% 3.48/1.02    ~r1_ordinal1(sK2,sK3) | ~r2_hidden(sK2,k3_tarski(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3))))),
% 3.48/1.02    inference(definition_unfolding,[],[f85,f93])).
% 3.48/1.02  
% 3.48/1.02  fof(f82,plain,(
% 3.48/1.02    v3_ordinal1(sK2)),
% 3.48/1.02    inference(cnf_transformation,[],[f53])).
% 3.48/1.02  
% 3.48/1.02  fof(f83,plain,(
% 3.48/1.02    v3_ordinal1(sK3)),
% 3.48/1.02    inference(cnf_transformation,[],[f53])).
% 3.48/1.02  
% 3.48/1.02  fof(f3,axiom,(
% 3.48/1.02    ! [X0,X1] : k2_xboole_0(X0,X0) = X0),
% 3.48/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.48/1.02  
% 3.48/1.02  fof(f23,plain,(
% 3.48/1.02    ! [X0] : k2_xboole_0(X0,X0) = X0),
% 3.48/1.02    inference(rectify,[],[f3])).
% 3.48/1.02  
% 3.48/1.02  fof(f61,plain,(
% 3.48/1.02    ( ! [X0] : (k2_xboole_0(X0,X0) = X0) )),
% 3.48/1.02    inference(cnf_transformation,[],[f23])).
% 3.48/1.02  
% 3.48/1.02  fof(f100,plain,(
% 3.48/1.02    ( ! [X0] : (k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) = X0) )),
% 3.48/1.02    inference(definition_unfolding,[],[f61,f91])).
% 3.48/1.02  
% 3.48/1.02  fof(f11,axiom,(
% 3.48/1.02    ! [X0,X1] : (r2_hidden(X0,X1) => r1_tarski(X0,k3_tarski(X1)))),
% 3.48/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.48/1.02  
% 3.48/1.02  fof(f28,plain,(
% 3.48/1.02    ! [X0,X1] : (r1_tarski(X0,k3_tarski(X1)) | ~r2_hidden(X0,X1))),
% 3.48/1.02    inference(ennf_transformation,[],[f11])).
% 3.48/1.02  
% 3.48/1.02  fof(f69,plain,(
% 3.48/1.02    ( ! [X0,X1] : (r1_tarski(X0,k3_tarski(X1)) | ~r2_hidden(X0,X1)) )),
% 3.48/1.02    inference(cnf_transformation,[],[f28])).
% 3.48/1.02  
% 3.48/1.02  fof(f13,axiom,(
% 3.48/1.02    ! [X0] : (v3_ordinal1(X0) => (v2_ordinal1(X0) & v1_ordinal1(X0)))),
% 3.48/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.48/1.02  
% 3.48/1.02  fof(f25,plain,(
% 3.48/1.02    ! [X0] : (v3_ordinal1(X0) => v1_ordinal1(X0))),
% 3.48/1.02    inference(pure_predicate_removal,[],[f13])).
% 3.48/1.02  
% 3.48/1.02  fof(f29,plain,(
% 3.48/1.02    ! [X0] : (v1_ordinal1(X0) | ~v3_ordinal1(X0))),
% 3.48/1.02    inference(ennf_transformation,[],[f25])).
% 3.48/1.02  
% 3.48/1.02  fof(f71,plain,(
% 3.48/1.02    ( ! [X0] : (v1_ordinal1(X0) | ~v3_ordinal1(X0)) )),
% 3.48/1.02    inference(cnf_transformation,[],[f29])).
% 3.48/1.02  
% 3.48/1.02  fof(f54,plain,(
% 3.48/1.02    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,X2) | k2_xboole_0(X0,X1) != X2) )),
% 3.48/1.02    inference(cnf_transformation,[],[f43])).
% 3.48/1.02  
% 3.48/1.02  fof(f99,plain,(
% 3.48/1.02    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,X2) | k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) != X2) )),
% 3.48/1.02    inference(definition_unfolding,[],[f54,f91])).
% 3.48/1.02  
% 3.48/1.02  fof(f106,plain,(
% 3.48/1.02    ( ! [X4,X0,X1] : (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) )),
% 3.48/1.02    inference(equality_resolution,[],[f99])).
% 3.48/1.02  
% 3.48/1.02  fof(f2,axiom,(
% 3.48/1.02    ! [X0,X1] : (r2_xboole_0(X0,X1) <=> (X0 != X1 & r1_tarski(X0,X1)))),
% 3.48/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.48/1.02  
% 3.48/1.02  fof(f24,plain,(
% 3.48/1.02    ! [X0,X1] : ((X0 != X1 & r1_tarski(X0,X1)) => r2_xboole_0(X0,X1))),
% 3.48/1.02    inference(unused_predicate_definition_removal,[],[f2])).
% 3.48/1.03  
% 3.48/1.03  fof(f26,plain,(
% 3.48/1.03    ! [X0,X1] : (r2_xboole_0(X0,X1) | (X0 = X1 | ~r1_tarski(X0,X1)))),
% 3.48/1.03    inference(ennf_transformation,[],[f24])).
% 3.48/1.03  
% 3.48/1.03  fof(f27,plain,(
% 3.48/1.03    ! [X0,X1] : (r2_xboole_0(X0,X1) | X0 = X1 | ~r1_tarski(X0,X1))),
% 3.48/1.03    inference(flattening,[],[f26])).
% 3.48/1.03  
% 3.48/1.03  fof(f60,plain,(
% 3.48/1.03    ( ! [X0,X1] : (r2_xboole_0(X0,X1) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 3.48/1.03    inference(cnf_transformation,[],[f27])).
% 3.48/1.03  
% 3.48/1.03  fof(f18,axiom,(
% 3.48/1.03    ! [X0] : (v1_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => (r2_xboole_0(X0,X1) => r2_hidden(X0,X1))))),
% 3.48/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.48/1.03  
% 3.48/1.03  fof(f33,plain,(
% 3.48/1.03    ! [X0] : (! [X1] : ((r2_hidden(X0,X1) | ~r2_xboole_0(X0,X1)) | ~v3_ordinal1(X1)) | ~v1_ordinal1(X0))),
% 3.48/1.03    inference(ennf_transformation,[],[f18])).
% 3.48/1.03  
% 3.48/1.03  fof(f34,plain,(
% 3.48/1.03    ! [X0] : (! [X1] : (r2_hidden(X0,X1) | ~r2_xboole_0(X0,X1) | ~v3_ordinal1(X1)) | ~v1_ordinal1(X0))),
% 3.48/1.03    inference(flattening,[],[f33])).
% 3.48/1.03  
% 3.48/1.03  fof(f79,plain,(
% 3.48/1.03    ( ! [X0,X1] : (r2_hidden(X0,X1) | ~r2_xboole_0(X0,X1) | ~v3_ordinal1(X1) | ~v1_ordinal1(X0)) )),
% 3.48/1.03    inference(cnf_transformation,[],[f34])).
% 3.48/1.03  
% 3.48/1.03  fof(f76,plain,(
% 3.48/1.03    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r1_ordinal1(X0,X1) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0)) )),
% 3.48/1.03    inference(cnf_transformation,[],[f48])).
% 3.48/1.03  
% 3.48/1.03  fof(f84,plain,(
% 3.48/1.03    r1_ordinal1(sK2,sK3) | r2_hidden(sK2,k1_ordinal1(sK3))),
% 3.48/1.03    inference(cnf_transformation,[],[f53])).
% 3.48/1.03  
% 3.48/1.03  fof(f103,plain,(
% 3.48/1.03    r1_ordinal1(sK2,sK3) | r2_hidden(sK2,k3_tarski(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3))))),
% 3.48/1.03    inference(definition_unfolding,[],[f84,f93])).
% 3.48/1.03  
% 3.48/1.03  fof(f15,axiom,(
% 3.48/1.03    ! [X0] : (v1_ordinal1(X0) <=> ! [X1] : (r2_hidden(X1,X0) => r1_tarski(X1,X0)))),
% 3.48/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.48/1.03  
% 3.48/1.03  fof(f30,plain,(
% 3.48/1.03    ! [X0] : (v1_ordinal1(X0) <=> ! [X1] : (r1_tarski(X1,X0) | ~r2_hidden(X1,X0)))),
% 3.48/1.03    inference(ennf_transformation,[],[f15])).
% 3.48/1.03  
% 3.48/1.03  fof(f44,plain,(
% 3.48/1.03    ! [X0] : ((v1_ordinal1(X0) | ? [X1] : (~r1_tarski(X1,X0) & r2_hidden(X1,X0))) & (! [X1] : (r1_tarski(X1,X0) | ~r2_hidden(X1,X0)) | ~v1_ordinal1(X0)))),
% 3.48/1.03    inference(nnf_transformation,[],[f30])).
% 3.48/1.03  
% 3.48/1.03  fof(f45,plain,(
% 3.48/1.03    ! [X0] : ((v1_ordinal1(X0) | ? [X1] : (~r1_tarski(X1,X0) & r2_hidden(X1,X0))) & (! [X2] : (r1_tarski(X2,X0) | ~r2_hidden(X2,X0)) | ~v1_ordinal1(X0)))),
% 3.48/1.03    inference(rectify,[],[f44])).
% 3.48/1.03  
% 3.48/1.03  fof(f46,plain,(
% 3.48/1.03    ! [X0] : (? [X1] : (~r1_tarski(X1,X0) & r2_hidden(X1,X0)) => (~r1_tarski(sK1(X0),X0) & r2_hidden(sK1(X0),X0)))),
% 3.48/1.03    introduced(choice_axiom,[])).
% 3.48/1.03  
% 3.48/1.03  fof(f47,plain,(
% 3.48/1.03    ! [X0] : ((v1_ordinal1(X0) | (~r1_tarski(sK1(X0),X0) & r2_hidden(sK1(X0),X0))) & (! [X2] : (r1_tarski(X2,X0) | ~r2_hidden(X2,X0)) | ~v1_ordinal1(X0)))),
% 3.48/1.03    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f45,f46])).
% 3.48/1.03  
% 3.48/1.03  fof(f73,plain,(
% 3.48/1.03    ( ! [X2,X0] : (r1_tarski(X2,X0) | ~r2_hidden(X2,X0) | ~v1_ordinal1(X0)) )),
% 3.48/1.03    inference(cnf_transformation,[],[f47])).
% 3.48/1.03  
% 3.48/1.03  fof(f55,plain,(
% 3.48/1.03    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | ~r2_hidden(X4,X0) | k2_xboole_0(X0,X1) != X2) )),
% 3.48/1.03    inference(cnf_transformation,[],[f43])).
% 3.48/1.03  
% 3.48/1.03  fof(f98,plain,(
% 3.48/1.03    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | ~r2_hidden(X4,X0) | k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) != X2) )),
% 3.48/1.03    inference(definition_unfolding,[],[f55,f91])).
% 3.48/1.03  
% 3.48/1.03  fof(f105,plain,(
% 3.48/1.03    ( ! [X4,X0,X1] : (r2_hidden(X4,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) | ~r2_hidden(X4,X0)) )),
% 3.48/1.03    inference(equality_resolution,[],[f98])).
% 3.48/1.03  
% 3.48/1.03  fof(f20,axiom,(
% 3.48/1.03    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 3.48/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.48/1.03  
% 3.48/1.03  fof(f37,plain,(
% 3.48/1.03    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 3.48/1.03    inference(ennf_transformation,[],[f20])).
% 3.48/1.03  
% 3.48/1.03  fof(f81,plain,(
% 3.48/1.03    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1)) )),
% 3.48/1.03    inference(cnf_transformation,[],[f37])).
% 3.48/1.03  
% 3.48/1.03  fof(f19,axiom,(
% 3.48/1.03    ! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => (r2_hidden(X1,X0) | r1_ordinal1(X0,X1))))),
% 3.48/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.48/1.03  
% 3.48/1.03  fof(f35,plain,(
% 3.48/1.03    ! [X0] : (! [X1] : ((r2_hidden(X1,X0) | r1_ordinal1(X0,X1)) | ~v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 3.48/1.03    inference(ennf_transformation,[],[f19])).
% 3.48/1.03  
% 3.48/1.03  fof(f36,plain,(
% 3.48/1.03    ! [X0] : (! [X1] : (r2_hidden(X1,X0) | r1_ordinal1(X0,X1) | ~v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 3.48/1.03    inference(flattening,[],[f35])).
% 3.48/1.03  
% 3.48/1.03  fof(f80,plain,(
% 3.48/1.03    ( ! [X0,X1] : (r2_hidden(X1,X0) | r1_ordinal1(X0,X1) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0)) )),
% 3.48/1.03    inference(cnf_transformation,[],[f36])).
% 3.48/1.03  
% 3.48/1.03  fof(f17,axiom,(
% 3.48/1.03    ! [X0] : r2_hidden(X0,k1_ordinal1(X0))),
% 3.48/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.48/1.03  
% 3.48/1.03  fof(f78,plain,(
% 3.48/1.03    ( ! [X0] : (r2_hidden(X0,k1_ordinal1(X0))) )),
% 3.48/1.03    inference(cnf_transformation,[],[f17])).
% 3.48/1.03  
% 3.48/1.03  fof(f101,plain,(
% 3.48/1.03    ( ! [X0] : (r2_hidden(X0,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))))) )),
% 3.48/1.03    inference(definition_unfolding,[],[f78,f93])).
% 3.48/1.03  
% 3.48/1.03  cnf(c_1222,plain,
% 3.48/1.03      ( ~ r2_hidden(X0,X1) | r2_hidden(X2,X3) | X2 != X0 | X3 != X1 ),
% 3.48/1.03      theory(equality) ).
% 3.48/1.03  
% 3.48/1.03  cnf(c_1976,plain,
% 3.48/1.03      ( r2_hidden(X0,X1)
% 3.48/1.03      | ~ r2_hidden(X2,k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2))
% 3.48/1.03      | X0 != X2
% 3.48/1.03      | X1 != k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2) ),
% 3.48/1.03      inference(instantiation,[status(thm)],[c_1222]) ).
% 3.48/1.03  
% 3.48/1.03  cnf(c_2174,plain,
% 3.48/1.03      ( ~ r2_hidden(X0,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))
% 3.48/1.03      | r2_hidden(X1,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))
% 3.48/1.03      | X1 != X0
% 3.48/1.03      | k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) != k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
% 3.48/1.03      inference(instantiation,[status(thm)],[c_1976]) ).
% 3.48/1.03  
% 3.48/1.03  cnf(c_5314,plain,
% 3.48/1.03      ( ~ r2_hidden(sK3,k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3))
% 3.48/1.03      | r2_hidden(sK2,k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3))
% 3.48/1.03      | k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3) != k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3)
% 3.48/1.03      | sK2 != sK3 ),
% 3.48/1.03      inference(instantiation,[status(thm)],[c_2174]) ).
% 3.48/1.03  
% 3.48/1.03  cnf(c_3,plain,
% 3.48/1.03      ( ~ r2_hidden(X0,X1)
% 3.48/1.03      | r2_hidden(X0,k3_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X1))) ),
% 3.48/1.03      inference(cnf_transformation,[],[f104]) ).
% 3.48/1.03  
% 3.48/1.03  cnf(c_1708,plain,
% 3.48/1.03      ( r2_hidden(X0,X1) != iProver_top
% 3.48/1.03      | r2_hidden(X0,k3_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X1))) = iProver_top ),
% 3.48/1.03      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 3.48/1.03  
% 3.48/1.03  cnf(c_13,plain,
% 3.48/1.03      ( r1_ordinal1(X0,X1)
% 3.48/1.03      | ~ r1_tarski(X0,X1)
% 3.48/1.03      | ~ v3_ordinal1(X0)
% 3.48/1.03      | ~ v3_ordinal1(X1) ),
% 3.48/1.03      inference(cnf_transformation,[],[f77]) ).
% 3.48/1.03  
% 3.48/1.03  cnf(c_19,negated_conjecture,
% 3.48/1.03      ( ~ r1_ordinal1(sK2,sK3)
% 3.48/1.03      | ~ r2_hidden(sK2,k3_tarski(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3)))) ),
% 3.48/1.03      inference(cnf_transformation,[],[f102]) ).
% 3.48/1.03  
% 3.48/1.03  cnf(c_171,plain,
% 3.48/1.03      ( ~ r1_ordinal1(sK2,sK3)
% 3.48/1.03      | ~ r2_hidden(sK2,k3_tarski(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3)))) ),
% 3.48/1.03      inference(prop_impl,[status(thm)],[c_19]) ).
% 3.48/1.03  
% 3.48/1.03  cnf(c_478,plain,
% 3.48/1.03      ( ~ r1_tarski(X0,X1)
% 3.48/1.03      | ~ r2_hidden(sK2,k3_tarski(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3))))
% 3.48/1.03      | ~ v3_ordinal1(X0)
% 3.48/1.03      | ~ v3_ordinal1(X1)
% 3.48/1.03      | sK3 != X1
% 3.48/1.03      | sK2 != X0 ),
% 3.48/1.03      inference(resolution_lifted,[status(thm)],[c_13,c_171]) ).
% 3.48/1.03  
% 3.48/1.03  cnf(c_479,plain,
% 3.48/1.03      ( ~ r1_tarski(sK2,sK3)
% 3.48/1.03      | ~ r2_hidden(sK2,k3_tarski(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3))))
% 3.48/1.03      | ~ v3_ordinal1(sK3)
% 3.48/1.03      | ~ v3_ordinal1(sK2) ),
% 3.48/1.03      inference(unflattening,[status(thm)],[c_478]) ).
% 3.48/1.03  
% 3.48/1.03  cnf(c_22,negated_conjecture,
% 3.48/1.03      ( v3_ordinal1(sK2) ),
% 3.48/1.03      inference(cnf_transformation,[],[f82]) ).
% 3.48/1.03  
% 3.48/1.03  cnf(c_21,negated_conjecture,
% 3.48/1.03      ( v3_ordinal1(sK3) ),
% 3.48/1.03      inference(cnf_transformation,[],[f83]) ).
% 3.48/1.03  
% 3.48/1.03  cnf(c_481,plain,
% 3.48/1.03      ( ~ r1_tarski(sK2,sK3)
% 3.48/1.03      | ~ r2_hidden(sK2,k3_tarski(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3)))) ),
% 3.48/1.03      inference(global_propositional_subsumption,
% 3.48/1.03                [status(thm)],
% 3.48/1.03                [c_479,c_22,c_21]) ).
% 3.48/1.03  
% 3.48/1.03  cnf(c_779,plain,
% 3.48/1.03      ( ~ r1_tarski(sK2,sK3)
% 3.48/1.03      | ~ r2_hidden(sK2,k3_tarski(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3)))) ),
% 3.48/1.03      inference(prop_impl,[status(thm)],[c_22,c_21,c_479]) ).
% 3.48/1.03  
% 3.48/1.03  cnf(c_1694,plain,
% 3.48/1.03      ( r1_tarski(sK2,sK3) != iProver_top
% 3.48/1.03      | r2_hidden(sK2,k3_tarski(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3)))) != iProver_top ),
% 3.48/1.03      inference(predicate_to_equality,[status(thm)],[c_779]) ).
% 3.48/1.03  
% 3.48/1.03  cnf(c_3255,plain,
% 3.48/1.03      ( r1_tarski(sK2,sK3) != iProver_top
% 3.48/1.03      | r2_hidden(sK2,k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3)) != iProver_top ),
% 3.48/1.03      inference(superposition,[status(thm)],[c_1708,c_1694]) ).
% 3.48/1.03  
% 3.48/1.03  cnf(c_7,plain,
% 3.48/1.03      ( k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) = X0 ),
% 3.48/1.03      inference(cnf_transformation,[],[f100]) ).
% 3.48/1.03  
% 3.48/1.03  cnf(c_8,plain,
% 3.48/1.03      ( r1_tarski(X0,k3_tarski(X1)) | ~ r2_hidden(X0,X1) ),
% 3.48/1.03      inference(cnf_transformation,[],[f69]) ).
% 3.48/1.03  
% 3.48/1.03  cnf(c_1705,plain,
% 3.48/1.03      ( r1_tarski(X0,k3_tarski(X1)) = iProver_top
% 3.48/1.03      | r2_hidden(X0,X1) != iProver_top ),
% 3.48/1.03      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 3.48/1.03  
% 3.48/1.03  cnf(c_2236,plain,
% 3.48/1.03      ( r1_tarski(X0,X1) = iProver_top
% 3.48/1.03      | r2_hidden(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)) != iProver_top ),
% 3.48/1.03      inference(superposition,[status(thm)],[c_7,c_1705]) ).
% 3.48/1.03  
% 3.48/1.03  cnf(c_3811,plain,
% 3.48/1.03      ( r2_hidden(sK2,k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3)) != iProver_top ),
% 3.48/1.03      inference(forward_subsumption_resolution,
% 3.48/1.03                [status(thm)],
% 3.48/1.03                [c_3255,c_2236]) ).
% 3.48/1.03  
% 3.48/1.03  cnf(c_3266,plain,
% 3.48/1.03      ( ~ r1_tarski(sK2,sK3)
% 3.48/1.03      | ~ r2_hidden(sK2,k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3)) ),
% 3.48/1.03      inference(predicate_to_equality_rev,[status(thm)],[c_3255]) ).
% 3.48/1.03  
% 3.48/1.03  cnf(c_1219,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 3.48/1.03  
% 3.48/1.03  cnf(c_2082,plain,
% 3.48/1.03      ( X0 != X1 | sK2 != X1 | sK2 = X0 ),
% 3.48/1.03      inference(instantiation,[status(thm)],[c_1219]) ).
% 3.48/1.03  
% 3.48/1.03  cnf(c_2498,plain,
% 3.48/1.03      ( X0 != sK2 | sK2 = X0 | sK2 != sK2 ),
% 3.48/1.03      inference(instantiation,[status(thm)],[c_2082]) ).
% 3.48/1.03  
% 3.48/1.03  cnf(c_2499,plain,
% 3.48/1.03      ( sK3 != sK2 | sK2 = sK3 | sK2 != sK2 ),
% 3.48/1.03      inference(instantiation,[status(thm)],[c_2498]) ).
% 3.48/1.03  
% 3.48/1.03  cnf(c_1218,plain,( X0 = X0 ),theory(equality) ).
% 3.48/1.03  
% 3.48/1.03  cnf(c_2077,plain,
% 3.48/1.03      ( sK2 = sK2 ),
% 3.48/1.03      inference(instantiation,[status(thm)],[c_1218]) ).
% 3.48/1.03  
% 3.48/1.03  cnf(c_1223,plain,
% 3.48/1.03      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,X3) | X2 != X0 | X3 != X1 ),
% 3.48/1.03      theory(equality) ).
% 3.48/1.03  
% 3.48/1.03  cnf(c_1949,plain,
% 3.48/1.03      ( ~ r1_tarski(X0,X1) | r1_tarski(sK2,sK3) | sK3 != X1 | sK2 != X0 ),
% 3.48/1.03      inference(instantiation,[status(thm)],[c_1223]) ).
% 3.48/1.03  
% 3.48/1.03  cnf(c_1951,plain,
% 3.48/1.03      ( ~ r1_tarski(sK3,sK3)
% 3.48/1.03      | r1_tarski(sK2,sK3)
% 3.48/1.03      | sK3 != sK3
% 3.48/1.03      | sK2 != sK3 ),
% 3.48/1.03      inference(instantiation,[status(thm)],[c_1949]) ).
% 3.48/1.03  
% 3.48/1.03  cnf(c_1697,plain,
% 3.48/1.03      ( v3_ordinal1(sK2) = iProver_top ),
% 3.48/1.03      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 3.48/1.03  
% 3.48/1.03  cnf(c_9,plain,
% 3.48/1.03      ( ~ v3_ordinal1(X0) | v1_ordinal1(X0) ),
% 3.48/1.03      inference(cnf_transformation,[],[f71]) ).
% 3.48/1.03  
% 3.48/1.03  cnf(c_1704,plain,
% 3.48/1.03      ( v3_ordinal1(X0) != iProver_top | v1_ordinal1(X0) = iProver_top ),
% 3.48/1.03      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 3.48/1.03  
% 3.48/1.03  cnf(c_1940,plain,
% 3.48/1.03      ( v1_ordinal1(sK2) = iProver_top ),
% 3.48/1.03      inference(superposition,[status(thm)],[c_1697,c_1704]) ).
% 3.48/1.03  
% 3.48/1.03  cnf(c_5,plain,
% 3.48/1.03      ( r2_hidden(X0,X1)
% 3.48/1.03      | r2_hidden(X0,X2)
% 3.48/1.03      | ~ r2_hidden(X0,k3_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X1))) ),
% 3.48/1.03      inference(cnf_transformation,[],[f106]) ).
% 3.48/1.03  
% 3.48/1.03  cnf(c_1926,plain,
% 3.48/1.03      ( r2_hidden(X0,X0)
% 3.48/1.03      | r2_hidden(X0,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))
% 3.48/1.03      | ~ r2_hidden(X0,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)))) ),
% 3.48/1.03      inference(instantiation,[status(thm)],[c_5]) ).
% 3.48/1.03  
% 3.48/1.03  cnf(c_1928,plain,
% 3.48/1.03      ( r2_hidden(sK3,k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3))
% 3.48/1.03      | ~ r2_hidden(sK3,k3_tarski(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3))))
% 3.48/1.03      | r2_hidden(sK3,sK3) ),
% 3.48/1.03      inference(instantiation,[status(thm)],[c_1926]) ).
% 3.48/1.03  
% 3.48/1.03  cnf(c_1903,plain,
% 3.48/1.03      ( r2_hidden(sK2,k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3))
% 3.48/1.03      | ~ r2_hidden(sK2,k3_tarski(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3))))
% 3.48/1.03      | r2_hidden(sK2,sK3) ),
% 3.48/1.03      inference(instantiation,[status(thm)],[c_5]) ).
% 3.48/1.03  
% 3.48/1.03  cnf(c_1904,plain,
% 3.48/1.03      ( r2_hidden(sK2,k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3)) = iProver_top
% 3.48/1.03      | r2_hidden(sK2,k3_tarski(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3)))) != iProver_top
% 3.48/1.03      | r2_hidden(sK2,sK3) = iProver_top ),
% 3.48/1.03      inference(predicate_to_equality,[status(thm)],[c_1903]) ).
% 3.48/1.03  
% 3.48/1.03  cnf(c_1220,plain,
% 3.48/1.03      ( X0 != X1
% 3.48/1.03      | X2 != X3
% 3.48/1.03      | X4 != X5
% 3.48/1.03      | X6 != X7
% 3.48/1.03      | X8 != X9
% 3.48/1.03      | X10 != X11
% 3.48/1.03      | X12 != X13
% 3.48/1.03      | X14 != X15
% 3.48/1.03      | k6_enumset1(X0,X2,X4,X6,X8,X10,X12,X14) = k6_enumset1(X1,X3,X5,X7,X9,X11,X13,X15) ),
% 3.48/1.03      theory(equality) ).
% 3.48/1.03  
% 3.48/1.03  cnf(c_1225,plain,
% 3.48/1.03      ( k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3) = k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3)
% 3.48/1.03      | sK3 != sK3 ),
% 3.48/1.03      inference(instantiation,[status(thm)],[c_1220]) ).
% 3.48/1.03  
% 3.48/1.03  cnf(c_6,plain,
% 3.48/1.03      ( ~ r1_tarski(X0,X1) | r2_xboole_0(X0,X1) | X1 = X0 ),
% 3.48/1.03      inference(cnf_transformation,[],[f60]) ).
% 3.48/1.03  
% 3.48/1.03  cnf(c_16,plain,
% 3.48/1.03      ( ~ r2_xboole_0(X0,X1)
% 3.48/1.03      | r2_hidden(X0,X1)
% 3.48/1.03      | ~ v3_ordinal1(X1)
% 3.48/1.03      | ~ v1_ordinal1(X0) ),
% 3.48/1.03      inference(cnf_transformation,[],[f79]) ).
% 3.48/1.03  
% 3.48/1.03  cnf(c_290,plain,
% 3.48/1.03      ( ~ r1_tarski(X0,X1)
% 3.48/1.03      | r2_hidden(X0,X1)
% 3.48/1.03      | ~ v3_ordinal1(X1)
% 3.48/1.03      | ~ v1_ordinal1(X0)
% 3.48/1.03      | X1 = X0 ),
% 3.48/1.03      inference(resolution,[status(thm)],[c_6,c_16]) ).
% 3.48/1.03  
% 3.48/1.03  cnf(c_14,plain,
% 3.48/1.03      ( ~ r1_ordinal1(X0,X1)
% 3.48/1.03      | r1_tarski(X0,X1)
% 3.48/1.03      | ~ v3_ordinal1(X0)
% 3.48/1.03      | ~ v3_ordinal1(X1) ),
% 3.48/1.03      inference(cnf_transformation,[],[f76]) ).
% 3.48/1.03  
% 3.48/1.03  cnf(c_20,negated_conjecture,
% 3.48/1.03      ( r1_ordinal1(sK2,sK3)
% 3.48/1.03      | r2_hidden(sK2,k3_tarski(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3)))) ),
% 3.48/1.03      inference(cnf_transformation,[],[f103]) ).
% 3.48/1.03  
% 3.48/1.03  cnf(c_173,plain,
% 3.48/1.03      ( r1_ordinal1(sK2,sK3)
% 3.48/1.03      | r2_hidden(sK2,k3_tarski(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3)))) ),
% 3.48/1.03      inference(prop_impl,[status(thm)],[c_20]) ).
% 3.48/1.03  
% 3.48/1.03  cnf(c_492,plain,
% 3.48/1.03      ( r1_tarski(X0,X1)
% 3.48/1.03      | r2_hidden(sK2,k3_tarski(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3))))
% 3.48/1.03      | ~ v3_ordinal1(X0)
% 3.48/1.03      | ~ v3_ordinal1(X1)
% 3.48/1.03      | sK3 != X1
% 3.48/1.03      | sK2 != X0 ),
% 3.48/1.03      inference(resolution_lifted,[status(thm)],[c_14,c_173]) ).
% 3.48/1.03  
% 3.48/1.03  cnf(c_493,plain,
% 3.48/1.03      ( r1_tarski(sK2,sK3)
% 3.48/1.03      | r2_hidden(sK2,k3_tarski(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3))))
% 3.48/1.03      | ~ v3_ordinal1(sK3)
% 3.48/1.03      | ~ v3_ordinal1(sK2) ),
% 3.48/1.03      inference(unflattening,[status(thm)],[c_492]) ).
% 3.48/1.03  
% 3.48/1.03  cnf(c_495,plain,
% 3.48/1.03      ( r1_tarski(sK2,sK3)
% 3.48/1.03      | r2_hidden(sK2,k3_tarski(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3)))) ),
% 3.48/1.03      inference(global_propositional_subsumption,
% 3.48/1.03                [status(thm)],
% 3.48/1.03                [c_493,c_22,c_21]) ).
% 3.48/1.03  
% 3.48/1.03  cnf(c_619,plain,
% 3.48/1.03      ( r2_hidden(X0,X1)
% 3.48/1.03      | r2_hidden(sK2,k3_tarski(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3))))
% 3.48/1.03      | ~ v3_ordinal1(X1)
% 3.48/1.03      | ~ v1_ordinal1(X0)
% 3.48/1.03      | X1 = X0
% 3.48/1.03      | sK3 != X1
% 3.48/1.03      | sK2 != X0 ),
% 3.48/1.03      inference(resolution_lifted,[status(thm)],[c_290,c_495]) ).
% 3.48/1.03  
% 3.48/1.03  cnf(c_620,plain,
% 3.48/1.03      ( r2_hidden(sK2,k3_tarski(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3))))
% 3.48/1.03      | r2_hidden(sK2,sK3)
% 3.48/1.03      | ~ v3_ordinal1(sK3)
% 3.48/1.03      | ~ v1_ordinal1(sK2)
% 3.48/1.03      | sK3 = sK2 ),
% 3.48/1.03      inference(unflattening,[status(thm)],[c_619]) ).
% 3.48/1.03  
% 3.48/1.03  cnf(c_621,plain,
% 3.48/1.03      ( sK3 = sK2
% 3.48/1.03      | r2_hidden(sK2,k3_tarski(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3)))) = iProver_top
% 3.48/1.03      | r2_hidden(sK2,sK3) = iProver_top
% 3.48/1.03      | v3_ordinal1(sK3) != iProver_top
% 3.48/1.03      | v1_ordinal1(sK2) != iProver_top ),
% 3.48/1.03      inference(predicate_to_equality,[status(thm)],[c_620]) ).
% 3.48/1.03  
% 3.48/1.03  cnf(c_12,plain,
% 3.48/1.03      ( r1_tarski(X0,X1) | ~ r2_hidden(X0,X1) | ~ v1_ordinal1(X1) ),
% 3.48/1.03      inference(cnf_transformation,[],[f73]) ).
% 3.48/1.03  
% 3.48/1.03  cnf(c_605,plain,
% 3.48/1.03      ( ~ r2_hidden(X0,X1)
% 3.48/1.03      | ~ r2_hidden(sK2,k3_tarski(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3))))
% 3.48/1.03      | ~ v1_ordinal1(X1)
% 3.48/1.03      | sK3 != X1
% 3.48/1.03      | sK2 != X0 ),
% 3.48/1.03      inference(resolution_lifted,[status(thm)],[c_12,c_481]) ).
% 3.48/1.03  
% 3.48/1.03  cnf(c_606,plain,
% 3.48/1.03      ( ~ r2_hidden(sK2,k3_tarski(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3))))
% 3.48/1.03      | ~ r2_hidden(sK2,sK3)
% 3.48/1.03      | ~ v1_ordinal1(sK3) ),
% 3.48/1.03      inference(unflattening,[status(thm)],[c_605]) ).
% 3.48/1.03  
% 3.48/1.03  cnf(c_55,plain,
% 3.48/1.03      ( ~ v3_ordinal1(sK3) | v1_ordinal1(sK3) ),
% 3.48/1.03      inference(instantiation,[status(thm)],[c_9]) ).
% 3.48/1.03  
% 3.48/1.03  cnf(c_608,plain,
% 3.48/1.03      ( ~ r2_hidden(sK2,sK3)
% 3.48/1.03      | ~ r2_hidden(sK2,k3_tarski(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3)))) ),
% 3.48/1.03      inference(global_propositional_subsumption,
% 3.48/1.03                [status(thm)],
% 3.48/1.03                [c_606,c_21,c_55]) ).
% 3.48/1.03  
% 3.48/1.03  cnf(c_609,plain,
% 3.48/1.03      ( ~ r2_hidden(sK2,k3_tarski(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3))))
% 3.48/1.03      | ~ r2_hidden(sK2,sK3) ),
% 3.48/1.03      inference(renaming,[status(thm)],[c_608]) ).
% 3.48/1.03  
% 3.48/1.03  cnf(c_4,plain,
% 3.48/1.03      ( ~ r2_hidden(X0,X1)
% 3.48/1.03      | r2_hidden(X0,k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))) ),
% 3.48/1.03      inference(cnf_transformation,[],[f105]) ).
% 3.48/1.03  
% 3.48/1.03  cnf(c_616,plain,
% 3.48/1.03      ( ~ r2_hidden(sK2,sK3) ),
% 3.48/1.03      inference(forward_subsumption_resolution,[status(thm)],[c_609,c_4]) ).
% 3.48/1.03  
% 3.48/1.03  cnf(c_618,plain,
% 3.48/1.03      ( r2_hidden(sK2,sK3) != iProver_top ),
% 3.48/1.03      inference(predicate_to_equality,[status(thm)],[c_616]) ).
% 3.48/1.03  
% 3.48/1.03  cnf(c_18,plain,
% 3.48/1.03      ( ~ r1_tarski(X0,X1) | ~ r2_hidden(X1,X0) ),
% 3.48/1.03      inference(cnf_transformation,[],[f81]) ).
% 3.48/1.03  
% 3.48/1.03  cnf(c_548,plain,
% 3.48/1.03      ( ~ r2_hidden(X0,X1) | ~ r2_hidden(X1,X0) | ~ v1_ordinal1(X1) ),
% 3.48/1.03      inference(resolution,[status(thm)],[c_12,c_18]) ).
% 3.48/1.03  
% 3.48/1.03  cnf(c_550,plain,
% 3.48/1.03      ( ~ r2_hidden(sK3,sK3) | ~ v1_ordinal1(sK3) ),
% 3.48/1.03      inference(instantiation,[status(thm)],[c_548]) ).
% 3.48/1.03  
% 3.48/1.03  cnf(c_17,plain,
% 3.48/1.03      ( r1_ordinal1(X0,X1)
% 3.48/1.03      | r2_hidden(X1,X0)
% 3.48/1.03      | ~ v3_ordinal1(X0)
% 3.48/1.03      | ~ v3_ordinal1(X1) ),
% 3.48/1.03      inference(cnf_transformation,[],[f80]) ).
% 3.48/1.03  
% 3.48/1.03  cnf(c_445,plain,
% 3.48/1.03      ( r1_tarski(X0,X1)
% 3.48/1.03      | r2_hidden(X1,X0)
% 3.48/1.03      | ~ v3_ordinal1(X0)
% 3.48/1.03      | ~ v3_ordinal1(X1) ),
% 3.48/1.03      inference(resolution,[status(thm)],[c_17,c_14]) ).
% 3.48/1.03  
% 3.48/1.03  cnf(c_520,plain,
% 3.48/1.03      ( r2_hidden(X0,X1)
% 3.48/1.03      | r2_hidden(X1,X0)
% 3.48/1.03      | ~ v3_ordinal1(X0)
% 3.48/1.03      | ~ v3_ordinal1(X1)
% 3.48/1.03      | ~ v1_ordinal1(X1)
% 3.48/1.03      | X1 = X0 ),
% 3.48/1.03      inference(resolution,[status(thm)],[c_445,c_290]) ).
% 3.48/1.03  
% 3.48/1.03  cnf(c_522,plain,
% 3.48/1.03      ( r2_hidden(sK3,sK3)
% 3.48/1.03      | ~ v3_ordinal1(sK3)
% 3.48/1.03      | ~ v1_ordinal1(sK3)
% 3.48/1.03      | sK3 = sK3 ),
% 3.48/1.03      inference(instantiation,[status(thm)],[c_520]) ).
% 3.48/1.03  
% 3.48/1.03  cnf(c_447,plain,
% 3.48/1.03      ( r1_tarski(sK3,sK3) | r2_hidden(sK3,sK3) | ~ v3_ordinal1(sK3) ),
% 3.48/1.03      inference(instantiation,[status(thm)],[c_445]) ).
% 3.48/1.03  
% 3.48/1.03  cnf(c_15,plain,
% 3.48/1.03      ( r2_hidden(X0,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)))) ),
% 3.48/1.03      inference(cnf_transformation,[],[f101]) ).
% 3.48/1.03  
% 3.48/1.03  cnf(c_37,plain,
% 3.48/1.03      ( r2_hidden(sK3,k3_tarski(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3)))) ),
% 3.48/1.03      inference(instantiation,[status(thm)],[c_15]) ).
% 3.48/1.03  
% 3.48/1.03  cnf(c_24,plain,
% 3.48/1.03      ( v3_ordinal1(sK3) = iProver_top ),
% 3.48/1.03      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 3.48/1.03  
% 3.48/1.03  cnf(contradiction,plain,
% 3.48/1.03      ( $false ),
% 3.48/1.03      inference(minisat,
% 3.48/1.03                [status(thm)],
% 3.48/1.03                [c_5314,c_3811,c_3266,c_2499,c_2077,c_1951,c_1940,c_1928,
% 3.48/1.03                 c_1904,c_1225,c_621,c_618,c_550,c_522,c_447,c_55,c_37,
% 3.48/1.03                 c_24,c_21]) ).
% 3.48/1.03  
% 3.48/1.03  
% 3.48/1.03  % SZS output end CNFRefutation for theBenchmark.p
% 3.48/1.03  
% 3.48/1.03  ------                               Statistics
% 3.48/1.03  
% 3.48/1.03  ------ General
% 3.48/1.03  
% 3.48/1.03  abstr_ref_over_cycles:                  0
% 3.48/1.03  abstr_ref_under_cycles:                 0
% 3.48/1.03  gc_basic_clause_elim:                   0
% 3.48/1.03  forced_gc_time:                         0
% 3.48/1.03  parsing_time:                           0.019
% 3.48/1.03  unif_index_cands_time:                  0.
% 3.48/1.03  unif_index_add_time:                    0.
% 3.48/1.03  orderings_time:                         0.
% 3.48/1.03  out_proof_time:                         0.01
% 3.48/1.03  total_time:                             0.293
% 3.48/1.03  num_of_symbols:                         40
% 3.48/1.03  num_of_terms:                           6205
% 3.48/1.03  
% 3.48/1.03  ------ Preprocessing
% 3.48/1.03  
% 3.48/1.03  num_of_splits:                          0
% 3.48/1.03  num_of_split_atoms:                     0
% 3.48/1.03  num_of_reused_defs:                     0
% 3.48/1.03  num_eq_ax_congr_red:                    17
% 3.48/1.03  num_of_sem_filtered_clauses:            1
% 3.48/1.03  num_of_subtypes:                        0
% 3.48/1.03  monotx_restored_types:                  0
% 3.48/1.03  sat_num_of_epr_types:                   0
% 3.48/1.03  sat_num_of_non_cyclic_types:            0
% 3.48/1.03  sat_guarded_non_collapsed_types:        0
% 3.48/1.03  num_pure_diseq_elim:                    0
% 3.48/1.03  simp_replaced_by:                       0
% 3.48/1.03  res_preprocessed:                       101
% 3.48/1.03  prep_upred:                             0
% 3.48/1.03  prep_unflattend:                        57
% 3.48/1.03  smt_new_axioms:                         0
% 3.48/1.03  pred_elim_cands:                        4
% 3.48/1.03  pred_elim:                              2
% 3.48/1.03  pred_elim_cl:                           2
% 3.48/1.03  pred_elim_cycles:                       6
% 3.48/1.03  merged_defs:                            8
% 3.48/1.03  merged_defs_ncl:                        0
% 3.48/1.03  bin_hyper_res:                          9
% 3.48/1.03  prep_cycles:                            4
% 3.48/1.03  pred_elim_time:                         0.016
% 3.48/1.03  splitting_time:                         0.
% 3.48/1.03  sem_filter_time:                        0.
% 3.48/1.03  monotx_time:                            0.001
% 3.48/1.03  subtype_inf_time:                       0.
% 3.48/1.03  
% 3.48/1.03  ------ Problem properties
% 3.48/1.03  
% 3.48/1.03  clauses:                                21
% 3.48/1.03  conjectures:                            2
% 3.48/1.03  epr:                                    8
% 3.48/1.03  horn:                                   14
% 3.48/1.03  ground:                                 5
% 3.48/1.03  unary:                                  4
% 3.48/1.03  binary:                                 10
% 3.48/1.03  lits:                                   49
% 3.48/1.03  lits_eq:                                5
% 3.48/1.03  fd_pure:                                0
% 3.48/1.03  fd_pseudo:                              0
% 3.48/1.03  fd_cond:                                0
% 3.48/1.03  fd_pseudo_cond:                         4
% 3.48/1.03  ac_symbols:                             0
% 3.48/1.03  
% 3.48/1.03  ------ Propositional Solver
% 3.48/1.03  
% 3.48/1.03  prop_solver_calls:                      27
% 3.48/1.03  prop_fast_solver_calls:                 770
% 3.48/1.03  smt_solver_calls:                       0
% 3.48/1.03  smt_fast_solver_calls:                  0
% 3.48/1.03  prop_num_of_clauses:                    1840
% 3.48/1.03  prop_preprocess_simplified:             7254
% 3.48/1.03  prop_fo_subsumed:                       26
% 3.48/1.03  prop_solver_time:                       0.
% 3.48/1.03  smt_solver_time:                        0.
% 3.48/1.03  smt_fast_solver_time:                   0.
% 3.48/1.03  prop_fast_solver_time:                  0.
% 3.48/1.03  prop_unsat_core_time:                   0.
% 3.48/1.03  
% 3.48/1.03  ------ QBF
% 3.48/1.03  
% 3.48/1.03  qbf_q_res:                              0
% 3.48/1.03  qbf_num_tautologies:                    0
% 3.48/1.03  qbf_prep_cycles:                        0
% 3.48/1.03  
% 3.48/1.03  ------ BMC1
% 3.48/1.03  
% 3.48/1.03  bmc1_current_bound:                     -1
% 3.48/1.03  bmc1_last_solved_bound:                 -1
% 3.48/1.03  bmc1_unsat_core_size:                   -1
% 3.48/1.03  bmc1_unsat_core_parents_size:           -1
% 3.48/1.03  bmc1_merge_next_fun:                    0
% 3.48/1.03  bmc1_unsat_core_clauses_time:           0.
% 3.48/1.03  
% 3.48/1.03  ------ Instantiation
% 3.48/1.03  
% 3.48/1.03  inst_num_of_clauses:                    555
% 3.48/1.03  inst_num_in_passive:                    395
% 3.48/1.03  inst_num_in_active:                     157
% 3.48/1.03  inst_num_in_unprocessed:                2
% 3.48/1.03  inst_num_of_loops:                      180
% 3.48/1.03  inst_num_of_learning_restarts:          0
% 3.48/1.03  inst_num_moves_active_passive:          21
% 3.48/1.03  inst_lit_activity:                      0
% 3.48/1.03  inst_lit_activity_moves:                0
% 3.48/1.03  inst_num_tautologies:                   0
% 3.48/1.03  inst_num_prop_implied:                  0
% 3.48/1.03  inst_num_existing_simplified:           0
% 3.48/1.03  inst_num_eq_res_simplified:             0
% 3.48/1.03  inst_num_child_elim:                    0
% 3.48/1.03  inst_num_of_dismatching_blockings:      135
% 3.48/1.03  inst_num_of_non_proper_insts:           261
% 3.48/1.03  inst_num_of_duplicates:                 0
% 3.48/1.03  inst_inst_num_from_inst_to_res:         0
% 3.48/1.03  inst_dismatching_checking_time:         0.
% 3.48/1.03  
% 3.48/1.03  ------ Resolution
% 3.48/1.03  
% 3.48/1.03  res_num_of_clauses:                     0
% 3.48/1.03  res_num_in_passive:                     0
% 3.48/1.03  res_num_in_active:                      0
% 3.48/1.03  res_num_of_loops:                       105
% 3.48/1.03  res_forward_subset_subsumed:            13
% 3.48/1.03  res_backward_subset_subsumed:           0
% 3.48/1.03  res_forward_subsumed:                   2
% 3.48/1.03  res_backward_subsumed:                  0
% 3.48/1.03  res_forward_subsumption_resolution:     1
% 3.48/1.03  res_backward_subsumption_resolution:    0
% 3.48/1.03  res_clause_to_clause_subsumption:       305
% 3.48/1.03  res_orphan_elimination:                 0
% 3.48/1.03  res_tautology_del:                      49
% 3.48/1.03  res_num_eq_res_simplified:              0
% 3.48/1.03  res_num_sel_changes:                    0
% 3.48/1.03  res_moves_from_active_to_pass:          0
% 3.48/1.03  
% 3.48/1.03  ------ Superposition
% 3.48/1.03  
% 3.48/1.03  sup_time_total:                         0.
% 3.48/1.03  sup_time_generating:                    0.
% 3.48/1.03  sup_time_sim_full:                      0.
% 3.48/1.03  sup_time_sim_immed:                     0.
% 3.48/1.03  
% 3.48/1.03  sup_num_of_clauses:                     63
% 3.48/1.03  sup_num_in_active:                      34
% 3.48/1.03  sup_num_in_passive:                     29
% 3.48/1.03  sup_num_of_loops:                       34
% 3.48/1.03  sup_fw_superposition:                   41
% 3.48/1.03  sup_bw_superposition:                   14
% 3.48/1.03  sup_immediate_simplified:               3
% 3.48/1.03  sup_given_eliminated:                   0
% 3.48/1.03  comparisons_done:                       0
% 3.48/1.03  comparisons_avoided:                    0
% 3.48/1.03  
% 3.48/1.03  ------ Simplifications
% 3.48/1.03  
% 3.48/1.03  
% 3.48/1.03  sim_fw_subset_subsumed:                 0
% 3.48/1.03  sim_bw_subset_subsumed:                 0
% 3.48/1.03  sim_fw_subsumed:                        1
% 3.48/1.03  sim_bw_subsumed:                        0
% 3.48/1.03  sim_fw_subsumption_res:                 1
% 3.48/1.03  sim_bw_subsumption_res:                 0
% 3.48/1.03  sim_tautology_del:                      7
% 3.48/1.03  sim_eq_tautology_del:                   0
% 3.48/1.03  sim_eq_res_simp:                        0
% 3.48/1.03  sim_fw_demodulated:                     0
% 3.48/1.03  sim_bw_demodulated:                     0
% 3.48/1.03  sim_light_normalised:                   2
% 3.48/1.03  sim_joinable_taut:                      0
% 3.48/1.03  sim_joinable_simp:                      0
% 3.48/1.03  sim_ac_normalised:                      0
% 3.48/1.03  sim_smt_subsumption:                    0
% 3.48/1.03  
%------------------------------------------------------------------------------
