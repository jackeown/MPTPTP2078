%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:32:28 EST 2020

% Result     : Theorem 2.47s
% Output     : CNFRefutation 2.47s
% Verified   : 
% Statistics : Number of formulae       :  165 (1730 expanded)
%              Number of clauses        :   82 ( 187 expanded)
%              Number of leaves         :   25 ( 532 expanded)
%              Depth                    :   21
%              Number of atoms          :  384 (2956 expanded)
%              Number of equality atoms :  238 (2584 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal clause size      :   14 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f17,axiom,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
     => r1_xboole_0(k1_tarski(X0),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f62,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f9,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f53,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f9])).

fof(f10,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f54,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f10])).

fof(f11,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f55,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f11])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f56,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f12])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f57,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f13])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f58,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f14])).

fof(f15,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f59,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f15])).

fof(f71,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f58,f59])).

fof(f72,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f57,f71])).

fof(f73,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f56,f72])).

fof(f74,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f55,f73])).

fof(f75,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f54,f74])).

fof(f77,plain,(
    ! [X0] : k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f53,f75])).

fof(f85,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f62,f77])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f45,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f20,conjecture,(
    ! [X0,X1,X2] :
      ~ ( ~ ( k1_xboole_0 = X2
            & k1_tarski(X0) = X1 )
        & ~ ( k1_tarski(X0) = X2
            & k1_xboole_0 = X1 )
        & ~ ( k1_tarski(X0) = X2
            & k1_tarski(X0) = X1 )
        & k2_xboole_0(X1,X2) = k1_tarski(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ~ ( ~ ( k1_xboole_0 = X2
              & k1_tarski(X0) = X1 )
          & ~ ( k1_tarski(X0) = X2
              & k1_xboole_0 = X1 )
          & ~ ( k1_tarski(X0) = X2
              & k1_tarski(X0) = X1 )
          & k2_xboole_0(X1,X2) = k1_tarski(X0) ) ),
    inference(negated_conjecture,[],[f20])).

fof(f30,plain,(
    ? [X0,X1,X2] :
      ( ( k1_xboole_0 != X2
        | k1_tarski(X0) != X1 )
      & ( k1_tarski(X0) != X2
        | k1_xboole_0 != X1 )
      & ( k1_tarski(X0) != X2
        | k1_tarski(X0) != X1 )
      & k2_xboole_0(X1,X2) = k1_tarski(X0) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f38,plain,
    ( ? [X0,X1,X2] :
        ( ( k1_xboole_0 != X2
          | k1_tarski(X0) != X1 )
        & ( k1_tarski(X0) != X2
          | k1_xboole_0 != X1 )
        & ( k1_tarski(X0) != X2
          | k1_tarski(X0) != X1 )
        & k2_xboole_0(X1,X2) = k1_tarski(X0) )
   => ( ( k1_xboole_0 != sK3
        | k1_tarski(sK1) != sK2 )
      & ( k1_tarski(sK1) != sK3
        | k1_xboole_0 != sK2 )
      & ( k1_tarski(sK1) != sK3
        | k1_tarski(sK1) != sK2 )
      & k2_xboole_0(sK2,sK3) = k1_tarski(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,
    ( ( k1_xboole_0 != sK3
      | k1_tarski(sK1) != sK2 )
    & ( k1_tarski(sK1) != sK3
      | k1_xboole_0 != sK2 )
    & ( k1_tarski(sK1) != sK3
      | k1_tarski(sK1) != sK2 )
    & k2_xboole_0(sK2,sK3) = k1_tarski(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f30,f38])).

fof(f67,plain,(
    k2_xboole_0(sK2,sK3) = k1_tarski(sK1) ),
    inference(cnf_transformation,[],[f39])).

fof(f19,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f66,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f19])).

fof(f76,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f66,f75])).

fof(f92,plain,(
    k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) = k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3)) ),
    inference(definition_unfolding,[],[f67,f76,f77])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( ~ ( r1_xboole_0(X0,k2_xboole_0(X1,X2))
          & ~ ( r1_xboole_0(X0,X2)
              & r1_xboole_0(X0,X1) ) )
      & ~ ( r1_xboole_0(X0,X2)
          & r1_xboole_0(X0,X1)
          & ~ r1_xboole_0(X0,k2_xboole_0(X1,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( ( ~ r1_xboole_0(X0,k2_xboole_0(X1,X2))
        | ( r1_xboole_0(X0,X2)
          & r1_xboole_0(X0,X1) ) )
      & ( ~ r1_xboole_0(X0,X2)
        | ~ r1_xboole_0(X0,X1)
        | r1_xboole_0(X0,k2_xboole_0(X1,X2)) ) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,k2_xboole_0(X1,X2))
      | r1_xboole_0(X0,X2) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f79,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)))
      | r1_xboole_0(X0,X2) ) ),
    inference(definition_unfolding,[],[f51,f76])).

fof(f6,axiom,(
    ! [X0] :
      ( ~ ( r1_xboole_0(X0,X0)
          & k1_xboole_0 != X0 )
      & ~ ( k1_xboole_0 = X0
          & ~ r1_xboole_0(X0,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0] :
      ( ( ~ r1_xboole_0(X0,X0)
        | k1_xboole_0 = X0 )
      & ( k1_xboole_0 != X0
        | r1_xboole_0(X0,X0) ) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f48,plain,(
    ! [X0] :
      ( ~ r1_xboole_0(X0,X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f27])).

fof(f8,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f52,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f82,plain,(
    ! [X0,X1] : r1_tarski(X0,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) ),
    inference(definition_unfolding,[],[f52,f76])).

fof(f18,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,k1_tarski(X1))
    <=> ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,k1_tarski(X1))
        | ( k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k1_tarski(X1)) ) ) ),
    inference(nnf_transformation,[],[f18])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,k1_tarski(X1))
        | ( k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k1_tarski(X1)) ) ) ),
    inference(flattening,[],[f36])).

fof(f63,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = X0
      | k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_tarski(X1)) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f88,plain,(
    ! [X0,X1] :
      ( k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) = X0
      | k1_xboole_0 = X0
      | ~ r1_tarski(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)) ) ),
    inference(definition_unfolding,[],[f63,f77,f77])).

fof(f70,plain,
    ( k1_xboole_0 != sK3
    | k1_tarski(sK1) != sK2 ),
    inference(cnf_transformation,[],[f39])).

fof(f89,plain,
    ( k1_xboole_0 != sK3
    | k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) != sK2 ),
    inference(definition_unfolding,[],[f70,f77])).

fof(f47,plain,(
    ! [X0] :
      ( k1_xboole_0 != X0
      | r1_xboole_0(X0,X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f93,plain,(
    r1_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(equality_resolution,[],[f47])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => ! [X1] : ~ r2_hidden(X1,X0) ) ),
    inference(unused_predicate_definition_removal,[],[f1])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] : ~ r2_hidden(X1,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f3,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f3])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X0,X1)
      | r1_xboole_0(X0,k2_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f81,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X0,X1)
      | r1_xboole_0(X0,k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))) ) ),
    inference(definition_unfolding,[],[f49,f76])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
    <=> r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(k1_tarski(X0),X1)
        | ~ r2_hidden(X0,X1) )
      & ( r2_hidden(X0,X1)
        | ~ r1_tarski(k1_tarski(X0),X1) ) ) ),
    inference(nnf_transformation,[],[f16])).

fof(f61,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f83,plain,(
    ! [X0,X1] :
      ( r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f61,f77])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f46,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f78,plain,(
    ! [X0,X1] :
      ( k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f46,f76])).

fof(f68,plain,
    ( k1_tarski(sK1) != sK3
    | k1_tarski(sK1) != sK2 ),
    inference(cnf_transformation,[],[f39])).

fof(f91,plain,
    ( k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) != sK3
    | k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) != sK2 ),
    inference(definition_unfolding,[],[f68,f77,f77])).

fof(f69,plain,
    ( k1_tarski(sK1) != sK3
    | k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f39])).

fof(f90,plain,
    ( k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) != sK3
    | k1_xboole_0 != sK2 ),
    inference(definition_unfolding,[],[f69,f77])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f24])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f31])).

fof(f33,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK0(X0,X1),X1)
          & r2_hidden(sK0(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f32,f33])).

fof(f42,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK0(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_15,plain,
    ( r1_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1)
    | r2_hidden(X0,X1) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_1386,plain,
    ( r1_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1) = iProver_top
    | r2_hidden(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_5,plain,
    ( ~ r1_xboole_0(X0,X1)
    | r1_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_1396,plain,
    ( r1_xboole_0(X0,X1) != iProver_top
    | r1_xboole_0(X1,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_2235,plain,
    ( r1_xboole_0(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)) = iProver_top
    | r2_hidden(X1,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1386,c_1396])).

cnf(c_22,negated_conjecture,
    ( k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) = k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3)) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_9,plain,
    ( r1_xboole_0(X0,X1)
    | ~ r1_xboole_0(X0,k3_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X1))) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_1392,plain,
    ( r1_xboole_0(X0,X1) = iProver_top
    | r1_xboole_0(X0,k3_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_3037,plain,
    ( r1_xboole_0(X0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)) != iProver_top
    | r1_xboole_0(X0,sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_22,c_1392])).

cnf(c_5710,plain,
    ( r1_xboole_0(X0,sK3) = iProver_top
    | r2_hidden(sK1,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_2235,c_3037])).

cnf(c_7,plain,
    ( ~ r1_xboole_0(X0,X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f48])).

cnf(c_1394,plain,
    ( k1_xboole_0 = X0
    | r1_xboole_0(X0,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_5738,plain,
    ( sK3 = k1_xboole_0
    | r2_hidden(sK1,sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_5710,c_1394])).

cnf(c_12,plain,
    ( r1_tarski(X0,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_1389,plain,
    ( r1_tarski(X0,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_1816,plain,
    ( r1_tarski(sK2,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_22,c_1389])).

cnf(c_18,plain,
    ( ~ r1_tarski(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))
    | k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) = X0
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f88])).

cnf(c_1383,plain,
    ( k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) = X1
    | k1_xboole_0 = X1
    | r1_tarski(X1,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_3330,plain,
    ( k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) = sK2
    | sK2 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1816,c_1383])).

cnf(c_19,negated_conjecture,
    ( k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) != sK2
    | k1_xboole_0 != sK3 ),
    inference(cnf_transformation,[],[f89])).

cnf(c_3502,plain,
    ( sK2 = k1_xboole_0
    | sK3 != k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_3330,c_19])).

cnf(c_8,plain,
    ( r1_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f93])).

cnf(c_0,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_4,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_263,plain,
    ( ~ r2_hidden(X0,X1)
    | k1_xboole_0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_4])).

cnf(c_264,plain,
    ( ~ r2_hidden(X0,k1_xboole_0) ),
    inference(unflattening,[status(thm)],[c_263])).

cnf(c_265,plain,
    ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_264])).

cnf(c_267,plain,
    ( r2_hidden(sK1,k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_265])).

cnf(c_942,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_955,plain,
    ( sK1 = sK1 ),
    inference(instantiation,[status(thm)],[c_942])).

cnf(c_1521,plain,
    ( ~ r1_xboole_0(k1_xboole_0,k1_xboole_0)
    | k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_944,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_1780,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,k1_xboole_0)
    | X2 != X0
    | k1_xboole_0 != X1 ),
    inference(instantiation,[status(thm)],[c_944])).

cnf(c_2011,plain,
    ( ~ r2_hidden(X0,sK2)
    | r2_hidden(X1,k1_xboole_0)
    | X1 != X0
    | k1_xboole_0 != sK2 ),
    inference(instantiation,[status(thm)],[c_1780])).

cnf(c_2012,plain,
    ( X0 != X1
    | k1_xboole_0 != sK2
    | r2_hidden(X1,sK2) != iProver_top
    | r2_hidden(X0,k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2011])).

cnf(c_2014,plain,
    ( sK1 != sK1
    | k1_xboole_0 != sK2
    | r2_hidden(sK1,sK2) != iProver_top
    | r2_hidden(sK1,k1_xboole_0) = iProver_top ),
    inference(instantiation,[status(thm)],[c_2012])).

cnf(c_2087,plain,
    ( ~ r2_hidden(X0,sK3)
    | r2_hidden(X1,k1_xboole_0)
    | X1 != X0
    | k1_xboole_0 != sK3 ),
    inference(instantiation,[status(thm)],[c_1780])).

cnf(c_2097,plain,
    ( X0 != X1
    | k1_xboole_0 != sK3
    | r2_hidden(X1,sK3) != iProver_top
    | r2_hidden(X0,k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2087])).

cnf(c_2099,plain,
    ( sK1 != sK1
    | k1_xboole_0 != sK3
    | r2_hidden(sK1,sK3) != iProver_top
    | r2_hidden(sK1,k1_xboole_0) = iProver_top ),
    inference(instantiation,[status(thm)],[c_2097])).

cnf(c_2172,plain,
    ( r1_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),sK2)
    | r2_hidden(X0,sK2) ),
    inference(instantiation,[status(thm)],[c_15])).

cnf(c_2173,plain,
    ( r1_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),sK2) = iProver_top
    | r2_hidden(X0,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2172])).

cnf(c_2175,plain,
    ( r1_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),sK2) = iProver_top
    | r2_hidden(sK1,sK2) = iProver_top ),
    inference(instantiation,[status(thm)],[c_2173])).

cnf(c_943,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_1526,plain,
    ( k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) != X0
    | k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) = sK2
    | sK2 != X0 ),
    inference(instantiation,[status(thm)],[c_943])).

cnf(c_2223,plain,
    ( k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) = sK2
    | k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) != k1_xboole_0
    | sK2 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1526])).

cnf(c_1528,plain,
    ( sK2 != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = sK2 ),
    inference(instantiation,[status(thm)],[c_943])).

cnf(c_2222,plain,
    ( sK2 != k1_xboole_0
    | k1_xboole_0 = sK2
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1528])).

cnf(c_1725,plain,
    ( X0 != X1
    | k1_xboole_0 != X1
    | k1_xboole_0 = X0 ),
    inference(instantiation,[status(thm)],[c_943])).

cnf(c_1982,plain,
    ( X0 != k1_xboole_0
    | k1_xboole_0 = X0
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1725])).

cnf(c_2741,plain,
    ( sK3 != k1_xboole_0
    | k1_xboole_0 = sK3
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1982])).

cnf(c_3078,plain,
    ( r1_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),sK3)
    | r2_hidden(X0,sK3) ),
    inference(instantiation,[status(thm)],[c_15])).

cnf(c_3079,plain,
    ( r1_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),sK3) = iProver_top
    | r2_hidden(X0,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3078])).

cnf(c_3081,plain,
    ( r1_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),sK3) = iProver_top
    | r2_hidden(sK1,sK3) = iProver_top ),
    inference(instantiation,[status(thm)],[c_3079])).

cnf(c_11,plain,
    ( ~ r1_xboole_0(X0,X1)
    | ~ r1_xboole_0(X0,X2)
    | r1_xboole_0(X0,k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_1390,plain,
    ( r1_xboole_0(X0,X1) != iProver_top
    | r1_xboole_0(X0,X2) != iProver_top
    | r1_xboole_0(X0,k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_2994,plain,
    ( r1_xboole_0(X0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)) = iProver_top
    | r1_xboole_0(X0,sK2) != iProver_top
    | r1_xboole_0(X0,sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_22,c_1390])).

cnf(c_3182,plain,
    ( k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) = k1_xboole_0
    | r1_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),sK2) != iProver_top
    | r1_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_2994,c_1394])).

cnf(c_3704,plain,
    ( sK3 != k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3502,c_19,c_8,c_267,c_955,c_1521,c_2014,c_2099,c_2175,c_2223,c_2222,c_2741,c_3081,c_3182])).

cnf(c_5839,plain,
    ( r2_hidden(sK1,sK3) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5738,c_19,c_8,c_267,c_955,c_1521,c_2014,c_2099,c_2175,c_2223,c_2222,c_2741,c_3081,c_3182,c_3502])).

cnf(c_13,plain,
    ( r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1)
    | ~ r2_hidden(X0,X1) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_1388,plain,
    ( r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1) = iProver_top
    | r2_hidden(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_3484,plain,
    ( sK2 = k1_xboole_0
    | r1_tarski(sK2,X0) = iProver_top
    | r2_hidden(sK1,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_3330,c_1388])).

cnf(c_5844,plain,
    ( sK2 = k1_xboole_0
    | r1_tarski(sK2,sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_5839,c_3484])).

cnf(c_6,plain,
    ( ~ r1_tarski(X0,X1)
    | k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = X1 ),
    inference(cnf_transformation,[],[f78])).

cnf(c_1395,plain,
    ( k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = X1
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_6877,plain,
    ( k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3)) = sK3
    | sK2 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_5844,c_1395])).

cnf(c_6881,plain,
    ( k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) = sK3
    | sK2 = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_6877,c_22])).

cnf(c_21,negated_conjecture,
    ( k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) != sK2
    | k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) != sK3 ),
    inference(cnf_transformation,[],[f91])).

cnf(c_3500,plain,
    ( k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) != sK3
    | sK2 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_3330,c_21])).

cnf(c_20,negated_conjecture,
    ( k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) != sK3
    | k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f90])).

cnf(c_1596,plain,
    ( ~ r1_tarski(sK2,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))
    | k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) = sK2
    | k1_xboole_0 = sK2 ),
    inference(instantiation,[status(thm)],[c_18])).

cnf(c_1817,plain,
    ( r1_tarski(sK2,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_1816])).

cnf(c_3707,plain,
    ( k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) != sK3 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3500,c_21,c_20,c_1596,c_1817])).

cnf(c_7046,plain,
    ( sK2 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_6881,c_21,c_20,c_1596,c_1817])).

cnf(c_7073,plain,
    ( k3_tarski(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,sK3)) = k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) ),
    inference(demodulation,[status(thm)],[c_7046,c_22])).

cnf(c_2,plain,
    ( r1_tarski(X0,X1)
    | r2_hidden(sK0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_1398,plain,
    ( r1_tarski(X0,X1) = iProver_top
    | r2_hidden(sK0(X0,X1),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_1382,plain,
    ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_264])).

cnf(c_1761,plain,
    ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1398,c_1382])).

cnf(c_1933,plain,
    ( k3_tarski(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,X0)) = X0 ),
    inference(superposition,[status(thm)],[c_1761,c_1395])).

cnf(c_7076,plain,
    ( k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) = sK3 ),
    inference(demodulation,[status(thm)],[c_7073,c_1933])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_7076,c_3707])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n010.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 19:10:14 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 2.47/1.11  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.47/1.11  
% 2.47/1.11  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.47/1.11  
% 2.47/1.11  ------  iProver source info
% 2.47/1.11  
% 2.47/1.11  git: date: 2020-06-30 10:37:57 +0100
% 2.47/1.11  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.47/1.11  git: non_committed_changes: false
% 2.47/1.11  git: last_make_outside_of_git: false
% 2.47/1.11  
% 2.47/1.11  ------ 
% 2.47/1.11  
% 2.47/1.11  ------ Input Options
% 2.47/1.11  
% 2.47/1.11  --out_options                           all
% 2.47/1.11  --tptp_safe_out                         true
% 2.47/1.11  --problem_path                          ""
% 2.47/1.11  --include_path                          ""
% 2.47/1.11  --clausifier                            res/vclausify_rel
% 2.47/1.11  --clausifier_options                    --mode clausify
% 2.47/1.11  --stdin                                 false
% 2.47/1.11  --stats_out                             all
% 2.47/1.11  
% 2.47/1.11  ------ General Options
% 2.47/1.11  
% 2.47/1.11  --fof                                   false
% 2.47/1.11  --time_out_real                         305.
% 2.47/1.11  --time_out_virtual                      -1.
% 2.47/1.11  --symbol_type_check                     false
% 2.47/1.11  --clausify_out                          false
% 2.47/1.11  --sig_cnt_out                           false
% 2.47/1.11  --trig_cnt_out                          false
% 2.47/1.11  --trig_cnt_out_tolerance                1.
% 2.47/1.11  --trig_cnt_out_sk_spl                   false
% 2.47/1.11  --abstr_cl_out                          false
% 2.47/1.11  
% 2.47/1.11  ------ Global Options
% 2.47/1.11  
% 2.47/1.11  --schedule                              default
% 2.47/1.11  --add_important_lit                     false
% 2.47/1.11  --prop_solver_per_cl                    1000
% 2.47/1.11  --min_unsat_core                        false
% 2.47/1.11  --soft_assumptions                      false
% 2.47/1.11  --soft_lemma_size                       3
% 2.47/1.11  --prop_impl_unit_size                   0
% 2.47/1.11  --prop_impl_unit                        []
% 2.47/1.11  --share_sel_clauses                     true
% 2.47/1.11  --reset_solvers                         false
% 2.47/1.11  --bc_imp_inh                            [conj_cone]
% 2.47/1.11  --conj_cone_tolerance                   3.
% 2.47/1.11  --extra_neg_conj                        none
% 2.47/1.11  --large_theory_mode                     true
% 2.47/1.11  --prolific_symb_bound                   200
% 2.47/1.11  --lt_threshold                          2000
% 2.47/1.11  --clause_weak_htbl                      true
% 2.47/1.11  --gc_record_bc_elim                     false
% 2.47/1.11  
% 2.47/1.11  ------ Preprocessing Options
% 2.47/1.11  
% 2.47/1.11  --preprocessing_flag                    true
% 2.47/1.11  --time_out_prep_mult                    0.1
% 2.47/1.11  --splitting_mode                        input
% 2.47/1.11  --splitting_grd                         true
% 2.47/1.11  --splitting_cvd                         false
% 2.47/1.11  --splitting_cvd_svl                     false
% 2.47/1.11  --splitting_nvd                         32
% 2.47/1.11  --sub_typing                            true
% 2.47/1.11  --prep_gs_sim                           true
% 2.47/1.11  --prep_unflatten                        true
% 2.47/1.11  --prep_res_sim                          true
% 2.47/1.11  --prep_upred                            true
% 2.47/1.11  --prep_sem_filter                       exhaustive
% 2.47/1.11  --prep_sem_filter_out                   false
% 2.47/1.11  --pred_elim                             true
% 2.47/1.11  --res_sim_input                         true
% 2.47/1.11  --eq_ax_congr_red                       true
% 2.47/1.11  --pure_diseq_elim                       true
% 2.47/1.11  --brand_transform                       false
% 2.47/1.11  --non_eq_to_eq                          false
% 2.47/1.11  --prep_def_merge                        true
% 2.47/1.11  --prep_def_merge_prop_impl              false
% 2.47/1.11  --prep_def_merge_mbd                    true
% 2.47/1.11  --prep_def_merge_tr_red                 false
% 2.47/1.11  --prep_def_merge_tr_cl                  false
% 2.47/1.11  --smt_preprocessing                     true
% 2.47/1.11  --smt_ac_axioms                         fast
% 2.47/1.11  --preprocessed_out                      false
% 2.47/1.11  --preprocessed_stats                    false
% 2.47/1.11  
% 2.47/1.11  ------ Abstraction refinement Options
% 2.47/1.11  
% 2.47/1.11  --abstr_ref                             []
% 2.47/1.11  --abstr_ref_prep                        false
% 2.47/1.11  --abstr_ref_until_sat                   false
% 2.47/1.11  --abstr_ref_sig_restrict                funpre
% 2.47/1.11  --abstr_ref_af_restrict_to_split_sk     false
% 2.47/1.11  --abstr_ref_under                       []
% 2.47/1.11  
% 2.47/1.11  ------ SAT Options
% 2.47/1.11  
% 2.47/1.11  --sat_mode                              false
% 2.47/1.11  --sat_fm_restart_options                ""
% 2.47/1.11  --sat_gr_def                            false
% 2.47/1.11  --sat_epr_types                         true
% 2.47/1.11  --sat_non_cyclic_types                  false
% 2.47/1.11  --sat_finite_models                     false
% 2.47/1.11  --sat_fm_lemmas                         false
% 2.47/1.11  --sat_fm_prep                           false
% 2.47/1.11  --sat_fm_uc_incr                        true
% 2.47/1.11  --sat_out_model                         small
% 2.47/1.11  --sat_out_clauses                       false
% 2.47/1.11  
% 2.47/1.11  ------ QBF Options
% 2.47/1.11  
% 2.47/1.11  --qbf_mode                              false
% 2.47/1.11  --qbf_elim_univ                         false
% 2.47/1.11  --qbf_dom_inst                          none
% 2.47/1.11  --qbf_dom_pre_inst                      false
% 2.47/1.11  --qbf_sk_in                             false
% 2.47/1.11  --qbf_pred_elim                         true
% 2.47/1.11  --qbf_split                             512
% 2.47/1.11  
% 2.47/1.11  ------ BMC1 Options
% 2.47/1.11  
% 2.47/1.11  --bmc1_incremental                      false
% 2.47/1.11  --bmc1_axioms                           reachable_all
% 2.47/1.11  --bmc1_min_bound                        0
% 2.47/1.11  --bmc1_max_bound                        -1
% 2.47/1.11  --bmc1_max_bound_default                -1
% 2.47/1.11  --bmc1_symbol_reachability              true
% 2.47/1.11  --bmc1_property_lemmas                  false
% 2.47/1.11  --bmc1_k_induction                      false
% 2.47/1.11  --bmc1_non_equiv_states                 false
% 2.47/1.11  --bmc1_deadlock                         false
% 2.47/1.11  --bmc1_ucm                              false
% 2.47/1.11  --bmc1_add_unsat_core                   none
% 2.47/1.11  --bmc1_unsat_core_children              false
% 2.47/1.11  --bmc1_unsat_core_extrapolate_axioms    false
% 2.47/1.11  --bmc1_out_stat                         full
% 2.47/1.11  --bmc1_ground_init                      false
% 2.47/1.11  --bmc1_pre_inst_next_state              false
% 2.47/1.11  --bmc1_pre_inst_state                   false
% 2.47/1.11  --bmc1_pre_inst_reach_state             false
% 2.47/1.11  --bmc1_out_unsat_core                   false
% 2.47/1.11  --bmc1_aig_witness_out                  false
% 2.47/1.11  --bmc1_verbose                          false
% 2.47/1.11  --bmc1_dump_clauses_tptp                false
% 2.47/1.11  --bmc1_dump_unsat_core_tptp             false
% 2.47/1.11  --bmc1_dump_file                        -
% 2.47/1.11  --bmc1_ucm_expand_uc_limit              128
% 2.47/1.11  --bmc1_ucm_n_expand_iterations          6
% 2.47/1.11  --bmc1_ucm_extend_mode                  1
% 2.47/1.11  --bmc1_ucm_init_mode                    2
% 2.47/1.11  --bmc1_ucm_cone_mode                    none
% 2.47/1.11  --bmc1_ucm_reduced_relation_type        0
% 2.47/1.11  --bmc1_ucm_relax_model                  4
% 2.47/1.11  --bmc1_ucm_full_tr_after_sat            true
% 2.47/1.11  --bmc1_ucm_expand_neg_assumptions       false
% 2.47/1.11  --bmc1_ucm_layered_model                none
% 2.47/1.11  --bmc1_ucm_max_lemma_size               10
% 2.47/1.11  
% 2.47/1.11  ------ AIG Options
% 2.47/1.11  
% 2.47/1.11  --aig_mode                              false
% 2.47/1.11  
% 2.47/1.11  ------ Instantiation Options
% 2.47/1.11  
% 2.47/1.11  --instantiation_flag                    true
% 2.47/1.11  --inst_sos_flag                         false
% 2.47/1.11  --inst_sos_phase                        true
% 2.47/1.11  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.47/1.11  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.47/1.11  --inst_lit_sel_side                     num_symb
% 2.47/1.11  --inst_solver_per_active                1400
% 2.47/1.11  --inst_solver_calls_frac                1.
% 2.47/1.11  --inst_passive_queue_type               priority_queues
% 2.47/1.11  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.47/1.11  --inst_passive_queues_freq              [25;2]
% 2.47/1.11  --inst_dismatching                      true
% 2.47/1.11  --inst_eager_unprocessed_to_passive     true
% 2.47/1.11  --inst_prop_sim_given                   true
% 2.47/1.11  --inst_prop_sim_new                     false
% 2.47/1.11  --inst_subs_new                         false
% 2.47/1.11  --inst_eq_res_simp                      false
% 2.47/1.11  --inst_subs_given                       false
% 2.47/1.11  --inst_orphan_elimination               true
% 2.47/1.11  --inst_learning_loop_flag               true
% 2.47/1.11  --inst_learning_start                   3000
% 2.47/1.11  --inst_learning_factor                  2
% 2.47/1.11  --inst_start_prop_sim_after_learn       3
% 2.47/1.11  --inst_sel_renew                        solver
% 2.47/1.11  --inst_lit_activity_flag                true
% 2.47/1.11  --inst_restr_to_given                   false
% 2.47/1.11  --inst_activity_threshold               500
% 2.47/1.11  --inst_out_proof                        true
% 2.47/1.11  
% 2.47/1.11  ------ Resolution Options
% 2.47/1.11  
% 2.47/1.11  --resolution_flag                       true
% 2.47/1.11  --res_lit_sel                           adaptive
% 2.47/1.11  --res_lit_sel_side                      none
% 2.47/1.11  --res_ordering                          kbo
% 2.47/1.11  --res_to_prop_solver                    active
% 2.47/1.11  --res_prop_simpl_new                    false
% 2.47/1.11  --res_prop_simpl_given                  true
% 2.47/1.11  --res_passive_queue_type                priority_queues
% 2.47/1.11  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.47/1.11  --res_passive_queues_freq               [15;5]
% 2.47/1.11  --res_forward_subs                      full
% 2.47/1.11  --res_backward_subs                     full
% 2.47/1.11  --res_forward_subs_resolution           true
% 2.47/1.11  --res_backward_subs_resolution          true
% 2.47/1.11  --res_orphan_elimination                true
% 2.47/1.11  --res_time_limit                        2.
% 2.47/1.11  --res_out_proof                         true
% 2.47/1.11  
% 2.47/1.11  ------ Superposition Options
% 2.47/1.11  
% 2.47/1.11  --superposition_flag                    true
% 2.47/1.11  --sup_passive_queue_type                priority_queues
% 2.47/1.11  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.47/1.11  --sup_passive_queues_freq               [8;1;4]
% 2.47/1.11  --demod_completeness_check              fast
% 2.47/1.11  --demod_use_ground                      true
% 2.47/1.11  --sup_to_prop_solver                    passive
% 2.47/1.11  --sup_prop_simpl_new                    true
% 2.47/1.11  --sup_prop_simpl_given                  true
% 2.47/1.11  --sup_fun_splitting                     false
% 2.47/1.11  --sup_smt_interval                      50000
% 2.47/1.11  
% 2.47/1.11  ------ Superposition Simplification Setup
% 2.47/1.11  
% 2.47/1.11  --sup_indices_passive                   []
% 2.47/1.11  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.47/1.11  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.47/1.11  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.47/1.11  --sup_full_triv                         [TrivRules;PropSubs]
% 2.47/1.11  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.47/1.11  --sup_full_bw                           [BwDemod]
% 2.47/1.11  --sup_immed_triv                        [TrivRules]
% 2.47/1.11  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.47/1.11  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.47/1.11  --sup_immed_bw_main                     []
% 2.47/1.11  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.47/1.11  --sup_input_triv                        [Unflattening;TrivRules]
% 2.47/1.11  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.47/1.11  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.47/1.11  
% 2.47/1.11  ------ Combination Options
% 2.47/1.11  
% 2.47/1.11  --comb_res_mult                         3
% 2.47/1.11  --comb_sup_mult                         2
% 2.47/1.11  --comb_inst_mult                        10
% 2.47/1.11  
% 2.47/1.11  ------ Debug Options
% 2.47/1.11  
% 2.47/1.11  --dbg_backtrace                         false
% 2.47/1.11  --dbg_dump_prop_clauses                 false
% 2.47/1.11  --dbg_dump_prop_clauses_file            -
% 2.47/1.11  --dbg_out_stat                          false
% 2.47/1.11  ------ Parsing...
% 2.47/1.11  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.47/1.11  
% 2.47/1.11  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 2.47/1.11  
% 2.47/1.11  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.47/1.11  
% 2.47/1.11  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.47/1.11  ------ Proving...
% 2.47/1.11  ------ Problem Properties 
% 2.47/1.11  
% 2.47/1.11  
% 2.47/1.11  clauses                                 22
% 2.47/1.11  conjectures                             4
% 2.47/1.11  EPR                                     5
% 2.47/1.11  Horn                                    19
% 2.47/1.11  unary                                   6
% 2.47/1.11  binary                                  13
% 2.47/1.11  lits                                    41
% 2.47/1.11  lits eq                                 11
% 2.47/1.11  fd_pure                                 0
% 2.47/1.11  fd_pseudo                               0
% 2.47/1.11  fd_cond                                 1
% 2.47/1.11  fd_pseudo_cond                          1
% 2.47/1.11  AC symbols                              0
% 2.47/1.11  
% 2.47/1.11  ------ Schedule dynamic 5 is on 
% 2.47/1.11  
% 2.47/1.11  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.47/1.11  
% 2.47/1.11  
% 2.47/1.11  ------ 
% 2.47/1.11  Current options:
% 2.47/1.11  ------ 
% 2.47/1.11  
% 2.47/1.11  ------ Input Options
% 2.47/1.11  
% 2.47/1.11  --out_options                           all
% 2.47/1.11  --tptp_safe_out                         true
% 2.47/1.11  --problem_path                          ""
% 2.47/1.11  --include_path                          ""
% 2.47/1.11  --clausifier                            res/vclausify_rel
% 2.47/1.11  --clausifier_options                    --mode clausify
% 2.47/1.11  --stdin                                 false
% 2.47/1.11  --stats_out                             all
% 2.47/1.11  
% 2.47/1.11  ------ General Options
% 2.47/1.11  
% 2.47/1.11  --fof                                   false
% 2.47/1.11  --time_out_real                         305.
% 2.47/1.11  --time_out_virtual                      -1.
% 2.47/1.11  --symbol_type_check                     false
% 2.47/1.11  --clausify_out                          false
% 2.47/1.11  --sig_cnt_out                           false
% 2.47/1.11  --trig_cnt_out                          false
% 2.47/1.11  --trig_cnt_out_tolerance                1.
% 2.47/1.11  --trig_cnt_out_sk_spl                   false
% 2.47/1.11  --abstr_cl_out                          false
% 2.47/1.11  
% 2.47/1.11  ------ Global Options
% 2.47/1.11  
% 2.47/1.11  --schedule                              default
% 2.47/1.11  --add_important_lit                     false
% 2.47/1.11  --prop_solver_per_cl                    1000
% 2.47/1.11  --min_unsat_core                        false
% 2.47/1.11  --soft_assumptions                      false
% 2.47/1.11  --soft_lemma_size                       3
% 2.47/1.11  --prop_impl_unit_size                   0
% 2.47/1.11  --prop_impl_unit                        []
% 2.47/1.11  --share_sel_clauses                     true
% 2.47/1.11  --reset_solvers                         false
% 2.47/1.11  --bc_imp_inh                            [conj_cone]
% 2.47/1.11  --conj_cone_tolerance                   3.
% 2.47/1.11  --extra_neg_conj                        none
% 2.47/1.11  --large_theory_mode                     true
% 2.47/1.11  --prolific_symb_bound                   200
% 2.47/1.11  --lt_threshold                          2000
% 2.47/1.11  --clause_weak_htbl                      true
% 2.47/1.11  --gc_record_bc_elim                     false
% 2.47/1.11  
% 2.47/1.11  ------ Preprocessing Options
% 2.47/1.11  
% 2.47/1.11  --preprocessing_flag                    true
% 2.47/1.11  --time_out_prep_mult                    0.1
% 2.47/1.11  --splitting_mode                        input
% 2.47/1.11  --splitting_grd                         true
% 2.47/1.11  --splitting_cvd                         false
% 2.47/1.11  --splitting_cvd_svl                     false
% 2.47/1.11  --splitting_nvd                         32
% 2.47/1.11  --sub_typing                            true
% 2.47/1.11  --prep_gs_sim                           true
% 2.47/1.11  --prep_unflatten                        true
% 2.47/1.11  --prep_res_sim                          true
% 2.47/1.11  --prep_upred                            true
% 2.47/1.11  --prep_sem_filter                       exhaustive
% 2.47/1.11  --prep_sem_filter_out                   false
% 2.47/1.11  --pred_elim                             true
% 2.47/1.11  --res_sim_input                         true
% 2.47/1.11  --eq_ax_congr_red                       true
% 2.47/1.11  --pure_diseq_elim                       true
% 2.47/1.11  --brand_transform                       false
% 2.47/1.11  --non_eq_to_eq                          false
% 2.47/1.11  --prep_def_merge                        true
% 2.47/1.11  --prep_def_merge_prop_impl              false
% 2.47/1.11  --prep_def_merge_mbd                    true
% 2.47/1.11  --prep_def_merge_tr_red                 false
% 2.47/1.11  --prep_def_merge_tr_cl                  false
% 2.47/1.11  --smt_preprocessing                     true
% 2.47/1.11  --smt_ac_axioms                         fast
% 2.47/1.11  --preprocessed_out                      false
% 2.47/1.11  --preprocessed_stats                    false
% 2.47/1.11  
% 2.47/1.11  ------ Abstraction refinement Options
% 2.47/1.11  
% 2.47/1.11  --abstr_ref                             []
% 2.47/1.11  --abstr_ref_prep                        false
% 2.47/1.11  --abstr_ref_until_sat                   false
% 2.47/1.11  --abstr_ref_sig_restrict                funpre
% 2.47/1.11  --abstr_ref_af_restrict_to_split_sk     false
% 2.47/1.11  --abstr_ref_under                       []
% 2.47/1.11  
% 2.47/1.11  ------ SAT Options
% 2.47/1.11  
% 2.47/1.11  --sat_mode                              false
% 2.47/1.11  --sat_fm_restart_options                ""
% 2.47/1.11  --sat_gr_def                            false
% 2.47/1.11  --sat_epr_types                         true
% 2.47/1.11  --sat_non_cyclic_types                  false
% 2.47/1.11  --sat_finite_models                     false
% 2.47/1.11  --sat_fm_lemmas                         false
% 2.47/1.11  --sat_fm_prep                           false
% 2.47/1.11  --sat_fm_uc_incr                        true
% 2.47/1.11  --sat_out_model                         small
% 2.47/1.11  --sat_out_clauses                       false
% 2.47/1.11  
% 2.47/1.11  ------ QBF Options
% 2.47/1.11  
% 2.47/1.11  --qbf_mode                              false
% 2.47/1.11  --qbf_elim_univ                         false
% 2.47/1.11  --qbf_dom_inst                          none
% 2.47/1.11  --qbf_dom_pre_inst                      false
% 2.47/1.11  --qbf_sk_in                             false
% 2.47/1.11  --qbf_pred_elim                         true
% 2.47/1.11  --qbf_split                             512
% 2.47/1.11  
% 2.47/1.11  ------ BMC1 Options
% 2.47/1.11  
% 2.47/1.11  --bmc1_incremental                      false
% 2.47/1.11  --bmc1_axioms                           reachable_all
% 2.47/1.11  --bmc1_min_bound                        0
% 2.47/1.11  --bmc1_max_bound                        -1
% 2.47/1.11  --bmc1_max_bound_default                -1
% 2.47/1.11  --bmc1_symbol_reachability              true
% 2.47/1.11  --bmc1_property_lemmas                  false
% 2.47/1.11  --bmc1_k_induction                      false
% 2.47/1.11  --bmc1_non_equiv_states                 false
% 2.47/1.11  --bmc1_deadlock                         false
% 2.47/1.11  --bmc1_ucm                              false
% 2.47/1.11  --bmc1_add_unsat_core                   none
% 2.47/1.11  --bmc1_unsat_core_children              false
% 2.47/1.11  --bmc1_unsat_core_extrapolate_axioms    false
% 2.47/1.11  --bmc1_out_stat                         full
% 2.47/1.11  --bmc1_ground_init                      false
% 2.47/1.11  --bmc1_pre_inst_next_state              false
% 2.47/1.11  --bmc1_pre_inst_state                   false
% 2.47/1.11  --bmc1_pre_inst_reach_state             false
% 2.47/1.11  --bmc1_out_unsat_core                   false
% 2.47/1.11  --bmc1_aig_witness_out                  false
% 2.47/1.11  --bmc1_verbose                          false
% 2.47/1.11  --bmc1_dump_clauses_tptp                false
% 2.47/1.11  --bmc1_dump_unsat_core_tptp             false
% 2.47/1.11  --bmc1_dump_file                        -
% 2.47/1.11  --bmc1_ucm_expand_uc_limit              128
% 2.47/1.11  --bmc1_ucm_n_expand_iterations          6
% 2.47/1.11  --bmc1_ucm_extend_mode                  1
% 2.47/1.11  --bmc1_ucm_init_mode                    2
% 2.47/1.11  --bmc1_ucm_cone_mode                    none
% 2.47/1.11  --bmc1_ucm_reduced_relation_type        0
% 2.47/1.11  --bmc1_ucm_relax_model                  4
% 2.47/1.11  --bmc1_ucm_full_tr_after_sat            true
% 2.47/1.11  --bmc1_ucm_expand_neg_assumptions       false
% 2.47/1.11  --bmc1_ucm_layered_model                none
% 2.47/1.11  --bmc1_ucm_max_lemma_size               10
% 2.47/1.11  
% 2.47/1.11  ------ AIG Options
% 2.47/1.11  
% 2.47/1.11  --aig_mode                              false
% 2.47/1.11  
% 2.47/1.11  ------ Instantiation Options
% 2.47/1.11  
% 2.47/1.11  --instantiation_flag                    true
% 2.47/1.11  --inst_sos_flag                         false
% 2.47/1.11  --inst_sos_phase                        true
% 2.47/1.11  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.47/1.11  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.47/1.11  --inst_lit_sel_side                     none
% 2.47/1.11  --inst_solver_per_active                1400
% 2.47/1.11  --inst_solver_calls_frac                1.
% 2.47/1.11  --inst_passive_queue_type               priority_queues
% 2.47/1.11  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.47/1.11  --inst_passive_queues_freq              [25;2]
% 2.47/1.11  --inst_dismatching                      true
% 2.47/1.11  --inst_eager_unprocessed_to_passive     true
% 2.47/1.11  --inst_prop_sim_given                   true
% 2.47/1.11  --inst_prop_sim_new                     false
% 2.47/1.11  --inst_subs_new                         false
% 2.47/1.11  --inst_eq_res_simp                      false
% 2.47/1.11  --inst_subs_given                       false
% 2.47/1.11  --inst_orphan_elimination               true
% 2.47/1.11  --inst_learning_loop_flag               true
% 2.47/1.11  --inst_learning_start                   3000
% 2.47/1.11  --inst_learning_factor                  2
% 2.47/1.11  --inst_start_prop_sim_after_learn       3
% 2.47/1.11  --inst_sel_renew                        solver
% 2.47/1.11  --inst_lit_activity_flag                true
% 2.47/1.11  --inst_restr_to_given                   false
% 2.47/1.11  --inst_activity_threshold               500
% 2.47/1.11  --inst_out_proof                        true
% 2.47/1.11  
% 2.47/1.11  ------ Resolution Options
% 2.47/1.11  
% 2.47/1.11  --resolution_flag                       false
% 2.47/1.11  --res_lit_sel                           adaptive
% 2.47/1.11  --res_lit_sel_side                      none
% 2.47/1.11  --res_ordering                          kbo
% 2.47/1.11  --res_to_prop_solver                    active
% 2.47/1.11  --res_prop_simpl_new                    false
% 2.47/1.11  --res_prop_simpl_given                  true
% 2.47/1.11  --res_passive_queue_type                priority_queues
% 2.47/1.11  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.47/1.11  --res_passive_queues_freq               [15;5]
% 2.47/1.11  --res_forward_subs                      full
% 2.47/1.11  --res_backward_subs                     full
% 2.47/1.11  --res_forward_subs_resolution           true
% 2.47/1.11  --res_backward_subs_resolution          true
% 2.47/1.11  --res_orphan_elimination                true
% 2.47/1.11  --res_time_limit                        2.
% 2.47/1.11  --res_out_proof                         true
% 2.47/1.11  
% 2.47/1.11  ------ Superposition Options
% 2.47/1.11  
% 2.47/1.11  --superposition_flag                    true
% 2.47/1.11  --sup_passive_queue_type                priority_queues
% 2.47/1.11  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.47/1.11  --sup_passive_queues_freq               [8;1;4]
% 2.47/1.11  --demod_completeness_check              fast
% 2.47/1.11  --demod_use_ground                      true
% 2.47/1.11  --sup_to_prop_solver                    passive
% 2.47/1.11  --sup_prop_simpl_new                    true
% 2.47/1.11  --sup_prop_simpl_given                  true
% 2.47/1.11  --sup_fun_splitting                     false
% 2.47/1.11  --sup_smt_interval                      50000
% 2.47/1.11  
% 2.47/1.11  ------ Superposition Simplification Setup
% 2.47/1.11  
% 2.47/1.11  --sup_indices_passive                   []
% 2.47/1.11  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.47/1.11  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.47/1.11  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.47/1.11  --sup_full_triv                         [TrivRules;PropSubs]
% 2.47/1.11  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.47/1.11  --sup_full_bw                           [BwDemod]
% 2.47/1.11  --sup_immed_triv                        [TrivRules]
% 2.47/1.11  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.47/1.11  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.47/1.11  --sup_immed_bw_main                     []
% 2.47/1.11  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.47/1.11  --sup_input_triv                        [Unflattening;TrivRules]
% 2.47/1.11  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.47/1.11  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.47/1.11  
% 2.47/1.11  ------ Combination Options
% 2.47/1.11  
% 2.47/1.11  --comb_res_mult                         3
% 2.47/1.11  --comb_sup_mult                         2
% 2.47/1.11  --comb_inst_mult                        10
% 2.47/1.11  
% 2.47/1.11  ------ Debug Options
% 2.47/1.11  
% 2.47/1.11  --dbg_backtrace                         false
% 2.47/1.11  --dbg_dump_prop_clauses                 false
% 2.47/1.11  --dbg_dump_prop_clauses_file            -
% 2.47/1.11  --dbg_out_stat                          false
% 2.47/1.11  
% 2.47/1.11  
% 2.47/1.11  
% 2.47/1.11  
% 2.47/1.11  ------ Proving...
% 2.47/1.11  
% 2.47/1.11  
% 2.47/1.11  % SZS status Theorem for theBenchmark.p
% 2.47/1.11  
% 2.47/1.11  % SZS output start CNFRefutation for theBenchmark.p
% 2.47/1.11  
% 2.47/1.11  fof(f17,axiom,(
% 2.47/1.11    ! [X0,X1] : (~r2_hidden(X0,X1) => r1_xboole_0(k1_tarski(X0),X1))),
% 2.47/1.11    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.47/1.11  
% 2.47/1.11  fof(f29,plain,(
% 2.47/1.11    ! [X0,X1] : (r1_xboole_0(k1_tarski(X0),X1) | r2_hidden(X0,X1))),
% 2.47/1.11    inference(ennf_transformation,[],[f17])).
% 2.47/1.11  
% 2.47/1.11  fof(f62,plain,(
% 2.47/1.11    ( ! [X0,X1] : (r1_xboole_0(k1_tarski(X0),X1) | r2_hidden(X0,X1)) )),
% 2.47/1.11    inference(cnf_transformation,[],[f29])).
% 2.47/1.11  
% 2.47/1.11  fof(f9,axiom,(
% 2.47/1.11    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 2.47/1.11    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.47/1.11  
% 2.47/1.11  fof(f53,plain,(
% 2.47/1.11    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 2.47/1.11    inference(cnf_transformation,[],[f9])).
% 2.47/1.11  
% 2.47/1.11  fof(f10,axiom,(
% 2.47/1.11    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 2.47/1.11    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.47/1.11  
% 2.47/1.11  fof(f54,plain,(
% 2.47/1.11    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 2.47/1.11    inference(cnf_transformation,[],[f10])).
% 2.47/1.11  
% 2.47/1.11  fof(f11,axiom,(
% 2.47/1.11    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 2.47/1.11    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.47/1.11  
% 2.47/1.11  fof(f55,plain,(
% 2.47/1.11    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 2.47/1.11    inference(cnf_transformation,[],[f11])).
% 2.47/1.11  
% 2.47/1.11  fof(f12,axiom,(
% 2.47/1.11    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 2.47/1.11    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.47/1.11  
% 2.47/1.11  fof(f56,plain,(
% 2.47/1.11    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 2.47/1.11    inference(cnf_transformation,[],[f12])).
% 2.47/1.11  
% 2.47/1.11  fof(f13,axiom,(
% 2.47/1.11    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)),
% 2.47/1.11    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.47/1.11  
% 2.47/1.11  fof(f57,plain,(
% 2.47/1.11    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)) )),
% 2.47/1.11    inference(cnf_transformation,[],[f13])).
% 2.47/1.11  
% 2.47/1.11  fof(f14,axiom,(
% 2.47/1.11    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)),
% 2.47/1.11    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.47/1.11  
% 2.47/1.11  fof(f58,plain,(
% 2.47/1.11    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)) )),
% 2.47/1.11    inference(cnf_transformation,[],[f14])).
% 2.47/1.11  
% 2.47/1.11  fof(f15,axiom,(
% 2.47/1.11    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)),
% 2.47/1.11    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.47/1.11  
% 2.47/1.11  fof(f59,plain,(
% 2.47/1.11    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)) )),
% 2.47/1.11    inference(cnf_transformation,[],[f15])).
% 2.47/1.11  
% 2.47/1.11  fof(f71,plain,(
% 2.47/1.11    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 2.47/1.11    inference(definition_unfolding,[],[f58,f59])).
% 2.47/1.11  
% 2.47/1.11  fof(f72,plain,(
% 2.47/1.11    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 2.47/1.11    inference(definition_unfolding,[],[f57,f71])).
% 2.47/1.11  
% 2.47/1.11  fof(f73,plain,(
% 2.47/1.11    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 2.47/1.11    inference(definition_unfolding,[],[f56,f72])).
% 2.47/1.11  
% 2.47/1.11  fof(f74,plain,(
% 2.47/1.11    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 2.47/1.11    inference(definition_unfolding,[],[f55,f73])).
% 2.47/1.11  
% 2.47/1.11  fof(f75,plain,(
% 2.47/1.11    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 2.47/1.11    inference(definition_unfolding,[],[f54,f74])).
% 2.47/1.11  
% 2.47/1.11  fof(f77,plain,(
% 2.47/1.11    ( ! [X0] : (k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) )),
% 2.47/1.11    inference(definition_unfolding,[],[f53,f75])).
% 2.47/1.11  
% 2.47/1.11  fof(f85,plain,(
% 2.47/1.11    ( ! [X0,X1] : (r1_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1) | r2_hidden(X0,X1)) )),
% 2.47/1.11    inference(definition_unfolding,[],[f62,f77])).
% 2.47/1.11  
% 2.47/1.11  fof(f4,axiom,(
% 2.47/1.11    ! [X0,X1] : (r1_xboole_0(X0,X1) => r1_xboole_0(X1,X0))),
% 2.47/1.11    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.47/1.11  
% 2.47/1.11  fof(f25,plain,(
% 2.47/1.11    ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1))),
% 2.47/1.11    inference(ennf_transformation,[],[f4])).
% 2.47/1.11  
% 2.47/1.11  fof(f45,plain,(
% 2.47/1.11    ( ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1)) )),
% 2.47/1.11    inference(cnf_transformation,[],[f25])).
% 2.47/1.11  
% 2.47/1.11  fof(f20,conjecture,(
% 2.47/1.11    ! [X0,X1,X2] : ~(~(k1_xboole_0 = X2 & k1_tarski(X0) = X1) & ~(k1_tarski(X0) = X2 & k1_xboole_0 = X1) & ~(k1_tarski(X0) = X2 & k1_tarski(X0) = X1) & k2_xboole_0(X1,X2) = k1_tarski(X0))),
% 2.47/1.11    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.47/1.11  
% 2.47/1.11  fof(f21,negated_conjecture,(
% 2.47/1.11    ~! [X0,X1,X2] : ~(~(k1_xboole_0 = X2 & k1_tarski(X0) = X1) & ~(k1_tarski(X0) = X2 & k1_xboole_0 = X1) & ~(k1_tarski(X0) = X2 & k1_tarski(X0) = X1) & k2_xboole_0(X1,X2) = k1_tarski(X0))),
% 2.47/1.11    inference(negated_conjecture,[],[f20])).
% 2.47/1.11  
% 2.47/1.11  fof(f30,plain,(
% 2.47/1.11    ? [X0,X1,X2] : ((k1_xboole_0 != X2 | k1_tarski(X0) != X1) & (k1_tarski(X0) != X2 | k1_xboole_0 != X1) & (k1_tarski(X0) != X2 | k1_tarski(X0) != X1) & k2_xboole_0(X1,X2) = k1_tarski(X0))),
% 2.47/1.11    inference(ennf_transformation,[],[f21])).
% 2.47/1.11  
% 2.47/1.11  fof(f38,plain,(
% 2.47/1.11    ? [X0,X1,X2] : ((k1_xboole_0 != X2 | k1_tarski(X0) != X1) & (k1_tarski(X0) != X2 | k1_xboole_0 != X1) & (k1_tarski(X0) != X2 | k1_tarski(X0) != X1) & k2_xboole_0(X1,X2) = k1_tarski(X0)) => ((k1_xboole_0 != sK3 | k1_tarski(sK1) != sK2) & (k1_tarski(sK1) != sK3 | k1_xboole_0 != sK2) & (k1_tarski(sK1) != sK3 | k1_tarski(sK1) != sK2) & k2_xboole_0(sK2,sK3) = k1_tarski(sK1))),
% 2.47/1.11    introduced(choice_axiom,[])).
% 2.47/1.11  
% 2.47/1.11  fof(f39,plain,(
% 2.47/1.11    (k1_xboole_0 != sK3 | k1_tarski(sK1) != sK2) & (k1_tarski(sK1) != sK3 | k1_xboole_0 != sK2) & (k1_tarski(sK1) != sK3 | k1_tarski(sK1) != sK2) & k2_xboole_0(sK2,sK3) = k1_tarski(sK1)),
% 2.47/1.11    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f30,f38])).
% 2.47/1.11  
% 2.47/1.11  fof(f67,plain,(
% 2.47/1.11    k2_xboole_0(sK2,sK3) = k1_tarski(sK1)),
% 2.47/1.11    inference(cnf_transformation,[],[f39])).
% 2.47/1.11  
% 2.47/1.11  fof(f19,axiom,(
% 2.47/1.11    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 2.47/1.11    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.47/1.11  
% 2.47/1.11  fof(f66,plain,(
% 2.47/1.11    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 2.47/1.11    inference(cnf_transformation,[],[f19])).
% 2.47/1.11  
% 2.47/1.11  fof(f76,plain,(
% 2.47/1.11    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) )),
% 2.47/1.11    inference(definition_unfolding,[],[f66,f75])).
% 2.47/1.11  
% 2.47/1.11  fof(f92,plain,(
% 2.47/1.11    k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) = k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3))),
% 2.47/1.11    inference(definition_unfolding,[],[f67,f76,f77])).
% 2.47/1.11  
% 2.47/1.11  fof(f7,axiom,(
% 2.47/1.11    ! [X0,X1,X2] : (~(r1_xboole_0(X0,k2_xboole_0(X1,X2)) & ~(r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1))) & ~(r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1) & ~r1_xboole_0(X0,k2_xboole_0(X1,X2))))),
% 2.47/1.11    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.47/1.11  
% 2.47/1.11  fof(f28,plain,(
% 2.47/1.11    ! [X0,X1,X2] : ((~r1_xboole_0(X0,k2_xboole_0(X1,X2)) | (r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1))) & (~r1_xboole_0(X0,X2) | ~r1_xboole_0(X0,X1) | r1_xboole_0(X0,k2_xboole_0(X1,X2))))),
% 2.47/1.11    inference(ennf_transformation,[],[f7])).
% 2.47/1.11  
% 2.47/1.11  fof(f51,plain,(
% 2.47/1.11    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,k2_xboole_0(X1,X2)) | r1_xboole_0(X0,X2)) )),
% 2.47/1.11    inference(cnf_transformation,[],[f28])).
% 2.47/1.11  
% 2.47/1.11  fof(f79,plain,(
% 2.47/1.11    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))) | r1_xboole_0(X0,X2)) )),
% 2.47/1.11    inference(definition_unfolding,[],[f51,f76])).
% 2.47/1.11  
% 2.47/1.11  fof(f6,axiom,(
% 2.47/1.11    ! [X0] : (~(r1_xboole_0(X0,X0) & k1_xboole_0 != X0) & ~(k1_xboole_0 = X0 & ~r1_xboole_0(X0,X0)))),
% 2.47/1.11    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.47/1.11  
% 2.47/1.11  fof(f27,plain,(
% 2.47/1.11    ! [X0] : ((~r1_xboole_0(X0,X0) | k1_xboole_0 = X0) & (k1_xboole_0 != X0 | r1_xboole_0(X0,X0)))),
% 2.47/1.11    inference(ennf_transformation,[],[f6])).
% 2.47/1.11  
% 2.47/1.11  fof(f48,plain,(
% 2.47/1.11    ( ! [X0] : (~r1_xboole_0(X0,X0) | k1_xboole_0 = X0) )),
% 2.47/1.11    inference(cnf_transformation,[],[f27])).
% 2.47/1.11  
% 2.47/1.11  fof(f8,axiom,(
% 2.47/1.11    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 2.47/1.11    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.47/1.11  
% 2.47/1.11  fof(f52,plain,(
% 2.47/1.11    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 2.47/1.11    inference(cnf_transformation,[],[f8])).
% 2.47/1.11  
% 2.47/1.11  fof(f82,plain,(
% 2.47/1.11    ( ! [X0,X1] : (r1_tarski(X0,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) )),
% 2.47/1.11    inference(definition_unfolding,[],[f52,f76])).
% 2.47/1.11  
% 2.47/1.11  fof(f18,axiom,(
% 2.47/1.11    ! [X0,X1] : (r1_tarski(X0,k1_tarski(X1)) <=> (k1_tarski(X1) = X0 | k1_xboole_0 = X0))),
% 2.47/1.11    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.47/1.11  
% 2.47/1.11  fof(f36,plain,(
% 2.47/1.11    ! [X0,X1] : ((r1_tarski(X0,k1_tarski(X1)) | (k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & ((k1_tarski(X1) = X0 | k1_xboole_0 = X0) | ~r1_tarski(X0,k1_tarski(X1))))),
% 2.47/1.11    inference(nnf_transformation,[],[f18])).
% 2.47/1.11  
% 2.47/1.11  fof(f37,plain,(
% 2.47/1.11    ! [X0,X1] : ((r1_tarski(X0,k1_tarski(X1)) | (k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & (k1_tarski(X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k1_tarski(X1))))),
% 2.47/1.11    inference(flattening,[],[f36])).
% 2.47/1.11  
% 2.47/1.11  fof(f63,plain,(
% 2.47/1.11    ( ! [X0,X1] : (k1_tarski(X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k1_tarski(X1))) )),
% 2.47/1.11    inference(cnf_transformation,[],[f37])).
% 2.47/1.11  
% 2.47/1.11  fof(f88,plain,(
% 2.47/1.11    ( ! [X0,X1] : (k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))) )),
% 2.47/1.11    inference(definition_unfolding,[],[f63,f77,f77])).
% 2.47/1.11  
% 2.47/1.11  fof(f70,plain,(
% 2.47/1.11    k1_xboole_0 != sK3 | k1_tarski(sK1) != sK2),
% 2.47/1.11    inference(cnf_transformation,[],[f39])).
% 2.47/1.11  
% 2.47/1.11  fof(f89,plain,(
% 2.47/1.11    k1_xboole_0 != sK3 | k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) != sK2),
% 2.47/1.11    inference(definition_unfolding,[],[f70,f77])).
% 2.47/1.11  
% 2.47/1.11  fof(f47,plain,(
% 2.47/1.11    ( ! [X0] : (k1_xboole_0 != X0 | r1_xboole_0(X0,X0)) )),
% 2.47/1.11    inference(cnf_transformation,[],[f27])).
% 2.47/1.11  
% 2.47/1.11  fof(f93,plain,(
% 2.47/1.11    r1_xboole_0(k1_xboole_0,k1_xboole_0)),
% 2.47/1.11    inference(equality_resolution,[],[f47])).
% 2.47/1.11  
% 2.47/1.11  fof(f1,axiom,(
% 2.47/1.11    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 2.47/1.11    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.47/1.11  
% 2.47/1.11  fof(f22,plain,(
% 2.47/1.11    ! [X0] : (v1_xboole_0(X0) => ! [X1] : ~r2_hidden(X1,X0))),
% 2.47/1.11    inference(unused_predicate_definition_removal,[],[f1])).
% 2.47/1.11  
% 2.47/1.11  fof(f23,plain,(
% 2.47/1.11    ! [X0] : (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0))),
% 2.47/1.11    inference(ennf_transformation,[],[f22])).
% 2.47/1.11  
% 2.47/1.11  fof(f40,plain,(
% 2.47/1.11    ( ! [X0,X1] : (~r2_hidden(X1,X0) | ~v1_xboole_0(X0)) )),
% 2.47/1.11    inference(cnf_transformation,[],[f23])).
% 2.47/1.11  
% 2.47/1.11  fof(f3,axiom,(
% 2.47/1.11    v1_xboole_0(k1_xboole_0)),
% 2.47/1.11    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.47/1.11  
% 2.47/1.11  fof(f44,plain,(
% 2.47/1.11    v1_xboole_0(k1_xboole_0)),
% 2.47/1.11    inference(cnf_transformation,[],[f3])).
% 2.47/1.11  
% 2.47/1.11  fof(f49,plain,(
% 2.47/1.11    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X2) | ~r1_xboole_0(X0,X1) | r1_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 2.47/1.11    inference(cnf_transformation,[],[f28])).
% 2.47/1.11  
% 2.47/1.11  fof(f81,plain,(
% 2.47/1.11    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X2) | ~r1_xboole_0(X0,X1) | r1_xboole_0(X0,k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)))) )),
% 2.47/1.11    inference(definition_unfolding,[],[f49,f76])).
% 2.47/1.11  
% 2.47/1.11  fof(f16,axiom,(
% 2.47/1.11    ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) <=> r2_hidden(X0,X1))),
% 2.47/1.11    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.47/1.11  
% 2.47/1.11  fof(f35,plain,(
% 2.47/1.11    ! [X0,X1] : ((r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) & (r2_hidden(X0,X1) | ~r1_tarski(k1_tarski(X0),X1)))),
% 2.47/1.11    inference(nnf_transformation,[],[f16])).
% 2.47/1.11  
% 2.47/1.11  fof(f61,plain,(
% 2.47/1.11    ( ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) )),
% 2.47/1.11    inference(cnf_transformation,[],[f35])).
% 2.47/1.11  
% 2.47/1.11  fof(f83,plain,(
% 2.47/1.11    ( ! [X0,X1] : (r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1) | ~r2_hidden(X0,X1)) )),
% 2.47/1.11    inference(definition_unfolding,[],[f61,f77])).
% 2.47/1.11  
% 2.47/1.11  fof(f5,axiom,(
% 2.47/1.11    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 2.47/1.11    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.47/1.11  
% 2.47/1.11  fof(f26,plain,(
% 2.47/1.11    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 2.47/1.11    inference(ennf_transformation,[],[f5])).
% 2.47/1.11  
% 2.47/1.11  fof(f46,plain,(
% 2.47/1.11    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1)) )),
% 2.47/1.11    inference(cnf_transformation,[],[f26])).
% 2.47/1.11  
% 2.47/1.11  fof(f78,plain,(
% 2.47/1.11    ( ! [X0,X1] : (k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = X1 | ~r1_tarski(X0,X1)) )),
% 2.47/1.11    inference(definition_unfolding,[],[f46,f76])).
% 2.47/1.11  
% 2.47/1.11  fof(f68,plain,(
% 2.47/1.11    k1_tarski(sK1) != sK3 | k1_tarski(sK1) != sK2),
% 2.47/1.11    inference(cnf_transformation,[],[f39])).
% 2.47/1.11  
% 2.47/1.11  fof(f91,plain,(
% 2.47/1.11    k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) != sK3 | k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) != sK2),
% 2.47/1.11    inference(definition_unfolding,[],[f68,f77,f77])).
% 2.47/1.11  
% 2.47/1.11  fof(f69,plain,(
% 2.47/1.11    k1_tarski(sK1) != sK3 | k1_xboole_0 != sK2),
% 2.47/1.11    inference(cnf_transformation,[],[f39])).
% 2.47/1.11  
% 2.47/1.11  fof(f90,plain,(
% 2.47/1.11    k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) != sK3 | k1_xboole_0 != sK2),
% 2.47/1.11    inference(definition_unfolding,[],[f69,f77])).
% 2.47/1.11  
% 2.47/1.11  fof(f2,axiom,(
% 2.47/1.11    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 2.47/1.11    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.47/1.11  
% 2.47/1.11  fof(f24,plain,(
% 2.47/1.11    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 2.47/1.11    inference(ennf_transformation,[],[f2])).
% 2.47/1.11  
% 2.47/1.11  fof(f31,plain,(
% 2.47/1.11    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 2.47/1.11    inference(nnf_transformation,[],[f24])).
% 2.47/1.11  
% 2.47/1.11  fof(f32,plain,(
% 2.47/1.11    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 2.47/1.11    inference(rectify,[],[f31])).
% 2.47/1.11  
% 2.47/1.11  fof(f33,plain,(
% 2.47/1.11    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 2.47/1.11    introduced(choice_axiom,[])).
% 2.47/1.11  
% 2.47/1.11  fof(f34,plain,(
% 2.47/1.11    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 2.47/1.11    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f32,f33])).
% 2.47/1.11  
% 2.47/1.11  fof(f42,plain,(
% 2.47/1.11    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK0(X0,X1),X0)) )),
% 2.47/1.11    inference(cnf_transformation,[],[f34])).
% 2.47/1.11  
% 2.47/1.11  cnf(c_15,plain,
% 2.47/1.11      ( r1_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1)
% 2.47/1.11      | r2_hidden(X0,X1) ),
% 2.47/1.11      inference(cnf_transformation,[],[f85]) ).
% 2.47/1.11  
% 2.47/1.11  cnf(c_1386,plain,
% 2.47/1.11      ( r1_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1) = iProver_top
% 2.47/1.11      | r2_hidden(X0,X1) = iProver_top ),
% 2.47/1.11      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 2.47/1.11  
% 2.47/1.11  cnf(c_5,plain,
% 2.47/1.11      ( ~ r1_xboole_0(X0,X1) | r1_xboole_0(X1,X0) ),
% 2.47/1.11      inference(cnf_transformation,[],[f45]) ).
% 2.47/1.11  
% 2.47/1.11  cnf(c_1396,plain,
% 2.47/1.11      ( r1_xboole_0(X0,X1) != iProver_top
% 2.47/1.11      | r1_xboole_0(X1,X0) = iProver_top ),
% 2.47/1.11      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 2.47/1.11  
% 2.47/1.11  cnf(c_2235,plain,
% 2.47/1.11      ( r1_xboole_0(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)) = iProver_top
% 2.47/1.11      | r2_hidden(X1,X0) = iProver_top ),
% 2.47/1.11      inference(superposition,[status(thm)],[c_1386,c_1396]) ).
% 2.47/1.11  
% 2.47/1.11  cnf(c_22,negated_conjecture,
% 2.47/1.11      ( k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) = k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3)) ),
% 2.47/1.11      inference(cnf_transformation,[],[f92]) ).
% 2.47/1.11  
% 2.47/1.11  cnf(c_9,plain,
% 2.47/1.11      ( r1_xboole_0(X0,X1)
% 2.47/1.11      | ~ r1_xboole_0(X0,k3_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X1))) ),
% 2.47/1.11      inference(cnf_transformation,[],[f79]) ).
% 2.47/1.11  
% 2.47/1.11  cnf(c_1392,plain,
% 2.47/1.11      ( r1_xboole_0(X0,X1) = iProver_top
% 2.47/1.11      | r1_xboole_0(X0,k3_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X1))) != iProver_top ),
% 2.47/1.11      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 2.47/1.11  
% 2.47/1.11  cnf(c_3037,plain,
% 2.47/1.11      ( r1_xboole_0(X0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)) != iProver_top
% 2.47/1.11      | r1_xboole_0(X0,sK3) = iProver_top ),
% 2.47/1.11      inference(superposition,[status(thm)],[c_22,c_1392]) ).
% 2.47/1.11  
% 2.47/1.11  cnf(c_5710,plain,
% 2.47/1.11      ( r1_xboole_0(X0,sK3) = iProver_top
% 2.47/1.11      | r2_hidden(sK1,X0) = iProver_top ),
% 2.47/1.11      inference(superposition,[status(thm)],[c_2235,c_3037]) ).
% 2.47/1.11  
% 2.47/1.11  cnf(c_7,plain,
% 2.47/1.11      ( ~ r1_xboole_0(X0,X0) | k1_xboole_0 = X0 ),
% 2.47/1.11      inference(cnf_transformation,[],[f48]) ).
% 2.47/1.11  
% 2.47/1.11  cnf(c_1394,plain,
% 2.47/1.11      ( k1_xboole_0 = X0 | r1_xboole_0(X0,X0) != iProver_top ),
% 2.47/1.11      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 2.47/1.11  
% 2.47/1.11  cnf(c_5738,plain,
% 2.47/1.11      ( sK3 = k1_xboole_0 | r2_hidden(sK1,sK3) = iProver_top ),
% 2.47/1.11      inference(superposition,[status(thm)],[c_5710,c_1394]) ).
% 2.47/1.11  
% 2.47/1.11  cnf(c_12,plain,
% 2.47/1.11      ( r1_tarski(X0,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) ),
% 2.47/1.11      inference(cnf_transformation,[],[f82]) ).
% 2.47/1.11  
% 2.47/1.11  cnf(c_1389,plain,
% 2.47/1.11      ( r1_tarski(X0,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) = iProver_top ),
% 2.47/1.11      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 2.47/1.11  
% 2.47/1.11  cnf(c_1816,plain,
% 2.47/1.11      ( r1_tarski(sK2,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)) = iProver_top ),
% 2.47/1.11      inference(superposition,[status(thm)],[c_22,c_1389]) ).
% 2.47/1.11  
% 2.47/1.11  cnf(c_18,plain,
% 2.47/1.11      ( ~ r1_tarski(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))
% 2.47/1.11      | k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) = X0
% 2.47/1.11      | k1_xboole_0 = X0 ),
% 2.47/1.11      inference(cnf_transformation,[],[f88]) ).
% 2.47/1.11  
% 2.47/1.11  cnf(c_1383,plain,
% 2.47/1.11      ( k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) = X1
% 2.47/1.11      | k1_xboole_0 = X1
% 2.47/1.11      | r1_tarski(X1,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) != iProver_top ),
% 2.47/1.11      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 2.47/1.11  
% 2.47/1.11  cnf(c_3330,plain,
% 2.47/1.11      ( k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) = sK2
% 2.47/1.11      | sK2 = k1_xboole_0 ),
% 2.47/1.11      inference(superposition,[status(thm)],[c_1816,c_1383]) ).
% 2.47/1.11  
% 2.47/1.11  cnf(c_19,negated_conjecture,
% 2.47/1.11      ( k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) != sK2
% 2.47/1.11      | k1_xboole_0 != sK3 ),
% 2.47/1.11      inference(cnf_transformation,[],[f89]) ).
% 2.47/1.11  
% 2.47/1.11  cnf(c_3502,plain,
% 2.47/1.11      ( sK2 = k1_xboole_0 | sK3 != k1_xboole_0 ),
% 2.47/1.11      inference(superposition,[status(thm)],[c_3330,c_19]) ).
% 2.47/1.11  
% 2.47/1.11  cnf(c_8,plain,
% 2.47/1.11      ( r1_xboole_0(k1_xboole_0,k1_xboole_0) ),
% 2.47/1.11      inference(cnf_transformation,[],[f93]) ).
% 2.47/1.11  
% 2.47/1.11  cnf(c_0,plain,
% 2.47/1.11      ( ~ r2_hidden(X0,X1) | ~ v1_xboole_0(X1) ),
% 2.47/1.11      inference(cnf_transformation,[],[f40]) ).
% 2.47/1.11  
% 2.47/1.11  cnf(c_4,plain,
% 2.47/1.11      ( v1_xboole_0(k1_xboole_0) ),
% 2.47/1.11      inference(cnf_transformation,[],[f44]) ).
% 2.47/1.11  
% 2.47/1.11  cnf(c_263,plain,
% 2.47/1.11      ( ~ r2_hidden(X0,X1) | k1_xboole_0 != X1 ),
% 2.47/1.11      inference(resolution_lifted,[status(thm)],[c_0,c_4]) ).
% 2.47/1.11  
% 2.47/1.11  cnf(c_264,plain,
% 2.47/1.11      ( ~ r2_hidden(X0,k1_xboole_0) ),
% 2.47/1.11      inference(unflattening,[status(thm)],[c_263]) ).
% 2.47/1.11  
% 2.47/1.11  cnf(c_265,plain,
% 2.47/1.11      ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
% 2.47/1.11      inference(predicate_to_equality,[status(thm)],[c_264]) ).
% 2.47/1.11  
% 2.47/1.11  cnf(c_267,plain,
% 2.47/1.11      ( r2_hidden(sK1,k1_xboole_0) != iProver_top ),
% 2.47/1.11      inference(instantiation,[status(thm)],[c_265]) ).
% 2.47/1.11  
% 2.47/1.11  cnf(c_942,plain,( X0 = X0 ),theory(equality) ).
% 2.47/1.11  
% 2.47/1.11  cnf(c_955,plain,
% 2.47/1.11      ( sK1 = sK1 ),
% 2.47/1.11      inference(instantiation,[status(thm)],[c_942]) ).
% 2.47/1.11  
% 2.47/1.11  cnf(c_1521,plain,
% 2.47/1.11      ( ~ r1_xboole_0(k1_xboole_0,k1_xboole_0)
% 2.47/1.11      | k1_xboole_0 = k1_xboole_0 ),
% 2.47/1.11      inference(instantiation,[status(thm)],[c_7]) ).
% 2.47/1.11  
% 2.47/1.11  cnf(c_944,plain,
% 2.47/1.11      ( ~ r2_hidden(X0,X1) | r2_hidden(X2,X3) | X2 != X0 | X3 != X1 ),
% 2.47/1.11      theory(equality) ).
% 2.47/1.11  
% 2.47/1.11  cnf(c_1780,plain,
% 2.47/1.11      ( ~ r2_hidden(X0,X1)
% 2.47/1.11      | r2_hidden(X2,k1_xboole_0)
% 2.47/1.11      | X2 != X0
% 2.47/1.11      | k1_xboole_0 != X1 ),
% 2.47/1.11      inference(instantiation,[status(thm)],[c_944]) ).
% 2.47/1.11  
% 2.47/1.11  cnf(c_2011,plain,
% 2.47/1.11      ( ~ r2_hidden(X0,sK2)
% 2.47/1.11      | r2_hidden(X1,k1_xboole_0)
% 2.47/1.11      | X1 != X0
% 2.47/1.11      | k1_xboole_0 != sK2 ),
% 2.47/1.11      inference(instantiation,[status(thm)],[c_1780]) ).
% 2.47/1.11  
% 2.47/1.11  cnf(c_2012,plain,
% 2.47/1.11      ( X0 != X1
% 2.47/1.11      | k1_xboole_0 != sK2
% 2.47/1.11      | r2_hidden(X1,sK2) != iProver_top
% 2.47/1.11      | r2_hidden(X0,k1_xboole_0) = iProver_top ),
% 2.47/1.11      inference(predicate_to_equality,[status(thm)],[c_2011]) ).
% 2.47/1.11  
% 2.47/1.11  cnf(c_2014,plain,
% 2.47/1.11      ( sK1 != sK1
% 2.47/1.11      | k1_xboole_0 != sK2
% 2.47/1.11      | r2_hidden(sK1,sK2) != iProver_top
% 2.47/1.11      | r2_hidden(sK1,k1_xboole_0) = iProver_top ),
% 2.47/1.11      inference(instantiation,[status(thm)],[c_2012]) ).
% 2.47/1.11  
% 2.47/1.11  cnf(c_2087,plain,
% 2.47/1.11      ( ~ r2_hidden(X0,sK3)
% 2.47/1.11      | r2_hidden(X1,k1_xboole_0)
% 2.47/1.11      | X1 != X0
% 2.47/1.11      | k1_xboole_0 != sK3 ),
% 2.47/1.11      inference(instantiation,[status(thm)],[c_1780]) ).
% 2.47/1.11  
% 2.47/1.11  cnf(c_2097,plain,
% 2.47/1.11      ( X0 != X1
% 2.47/1.11      | k1_xboole_0 != sK3
% 2.47/1.11      | r2_hidden(X1,sK3) != iProver_top
% 2.47/1.11      | r2_hidden(X0,k1_xboole_0) = iProver_top ),
% 2.47/1.11      inference(predicate_to_equality,[status(thm)],[c_2087]) ).
% 2.47/1.11  
% 2.47/1.11  cnf(c_2099,plain,
% 2.47/1.11      ( sK1 != sK1
% 2.47/1.11      | k1_xboole_0 != sK3
% 2.47/1.11      | r2_hidden(sK1,sK3) != iProver_top
% 2.47/1.11      | r2_hidden(sK1,k1_xboole_0) = iProver_top ),
% 2.47/1.11      inference(instantiation,[status(thm)],[c_2097]) ).
% 2.47/1.11  
% 2.47/1.11  cnf(c_2172,plain,
% 2.47/1.11      ( r1_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),sK2)
% 2.47/1.11      | r2_hidden(X0,sK2) ),
% 2.47/1.11      inference(instantiation,[status(thm)],[c_15]) ).
% 2.47/1.11  
% 2.47/1.11  cnf(c_2173,plain,
% 2.47/1.11      ( r1_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),sK2) = iProver_top
% 2.47/1.11      | r2_hidden(X0,sK2) = iProver_top ),
% 2.47/1.11      inference(predicate_to_equality,[status(thm)],[c_2172]) ).
% 2.47/1.11  
% 2.47/1.11  cnf(c_2175,plain,
% 2.47/1.11      ( r1_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),sK2) = iProver_top
% 2.47/1.11      | r2_hidden(sK1,sK2) = iProver_top ),
% 2.47/1.11      inference(instantiation,[status(thm)],[c_2173]) ).
% 2.47/1.11  
% 2.47/1.11  cnf(c_943,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 2.47/1.11  
% 2.47/1.11  cnf(c_1526,plain,
% 2.47/1.11      ( k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) != X0
% 2.47/1.11      | k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) = sK2
% 2.47/1.11      | sK2 != X0 ),
% 2.47/1.11      inference(instantiation,[status(thm)],[c_943]) ).
% 2.47/1.11  
% 2.47/1.11  cnf(c_2223,plain,
% 2.47/1.11      ( k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) = sK2
% 2.47/1.11      | k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) != k1_xboole_0
% 2.47/1.11      | sK2 != k1_xboole_0 ),
% 2.47/1.11      inference(instantiation,[status(thm)],[c_1526]) ).
% 2.47/1.11  
% 2.47/1.11  cnf(c_1528,plain,
% 2.47/1.11      ( sK2 != X0 | k1_xboole_0 != X0 | k1_xboole_0 = sK2 ),
% 2.47/1.11      inference(instantiation,[status(thm)],[c_943]) ).
% 2.47/1.11  
% 2.47/1.11  cnf(c_2222,plain,
% 2.47/1.11      ( sK2 != k1_xboole_0
% 2.47/1.11      | k1_xboole_0 = sK2
% 2.47/1.11      | k1_xboole_0 != k1_xboole_0 ),
% 2.47/1.11      inference(instantiation,[status(thm)],[c_1528]) ).
% 2.47/1.11  
% 2.47/1.11  cnf(c_1725,plain,
% 2.47/1.11      ( X0 != X1 | k1_xboole_0 != X1 | k1_xboole_0 = X0 ),
% 2.47/1.11      inference(instantiation,[status(thm)],[c_943]) ).
% 2.47/1.11  
% 2.47/1.11  cnf(c_1982,plain,
% 2.47/1.11      ( X0 != k1_xboole_0
% 2.47/1.11      | k1_xboole_0 = X0
% 2.47/1.11      | k1_xboole_0 != k1_xboole_0 ),
% 2.47/1.11      inference(instantiation,[status(thm)],[c_1725]) ).
% 2.47/1.11  
% 2.47/1.11  cnf(c_2741,plain,
% 2.47/1.11      ( sK3 != k1_xboole_0
% 2.47/1.11      | k1_xboole_0 = sK3
% 2.47/1.11      | k1_xboole_0 != k1_xboole_0 ),
% 2.47/1.11      inference(instantiation,[status(thm)],[c_1982]) ).
% 2.47/1.11  
% 2.47/1.11  cnf(c_3078,plain,
% 2.47/1.11      ( r1_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),sK3)
% 2.47/1.11      | r2_hidden(X0,sK3) ),
% 2.47/1.11      inference(instantiation,[status(thm)],[c_15]) ).
% 2.47/1.11  
% 2.47/1.11  cnf(c_3079,plain,
% 2.47/1.11      ( r1_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),sK3) = iProver_top
% 2.47/1.11      | r2_hidden(X0,sK3) = iProver_top ),
% 2.47/1.11      inference(predicate_to_equality,[status(thm)],[c_3078]) ).
% 2.47/1.11  
% 2.47/1.11  cnf(c_3081,plain,
% 2.47/1.11      ( r1_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),sK3) = iProver_top
% 2.47/1.11      | r2_hidden(sK1,sK3) = iProver_top ),
% 2.47/1.11      inference(instantiation,[status(thm)],[c_3079]) ).
% 2.47/1.11  
% 2.47/1.11  cnf(c_11,plain,
% 2.47/1.11      ( ~ r1_xboole_0(X0,X1)
% 2.47/1.11      | ~ r1_xboole_0(X0,X2)
% 2.47/1.11      | r1_xboole_0(X0,k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))) ),
% 2.47/1.11      inference(cnf_transformation,[],[f81]) ).
% 2.47/1.11  
% 2.47/1.11  cnf(c_1390,plain,
% 2.47/1.11      ( r1_xboole_0(X0,X1) != iProver_top
% 2.47/1.11      | r1_xboole_0(X0,X2) != iProver_top
% 2.47/1.11      | r1_xboole_0(X0,k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))) = iProver_top ),
% 2.47/1.11      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 2.47/1.11  
% 2.47/1.11  cnf(c_2994,plain,
% 2.47/1.11      ( r1_xboole_0(X0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)) = iProver_top
% 2.47/1.11      | r1_xboole_0(X0,sK2) != iProver_top
% 2.47/1.11      | r1_xboole_0(X0,sK3) != iProver_top ),
% 2.47/1.11      inference(superposition,[status(thm)],[c_22,c_1390]) ).
% 2.47/1.11  
% 2.47/1.11  cnf(c_3182,plain,
% 2.47/1.11      ( k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) = k1_xboole_0
% 2.47/1.11      | r1_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),sK2) != iProver_top
% 2.47/1.11      | r1_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),sK3) != iProver_top ),
% 2.47/1.11      inference(superposition,[status(thm)],[c_2994,c_1394]) ).
% 2.47/1.11  
% 2.47/1.11  cnf(c_3704,plain,
% 2.47/1.11      ( sK3 != k1_xboole_0 ),
% 2.47/1.11      inference(global_propositional_subsumption,
% 2.47/1.11                [status(thm)],
% 2.47/1.11                [c_3502,c_19,c_8,c_267,c_955,c_1521,c_2014,c_2099,c_2175,
% 2.47/1.11                 c_2223,c_2222,c_2741,c_3081,c_3182]) ).
% 2.47/1.11  
% 2.47/1.11  cnf(c_5839,plain,
% 2.47/1.11      ( r2_hidden(sK1,sK3) = iProver_top ),
% 2.47/1.11      inference(global_propositional_subsumption,
% 2.47/1.11                [status(thm)],
% 2.47/1.11                [c_5738,c_19,c_8,c_267,c_955,c_1521,c_2014,c_2099,c_2175,
% 2.47/1.11                 c_2223,c_2222,c_2741,c_3081,c_3182,c_3502]) ).
% 2.47/1.11  
% 2.47/1.11  cnf(c_13,plain,
% 2.47/1.11      ( r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1)
% 2.47/1.11      | ~ r2_hidden(X0,X1) ),
% 2.47/1.11      inference(cnf_transformation,[],[f83]) ).
% 2.47/1.11  
% 2.47/1.11  cnf(c_1388,plain,
% 2.47/1.11      ( r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1) = iProver_top
% 2.47/1.11      | r2_hidden(X0,X1) != iProver_top ),
% 2.47/1.11      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 2.47/1.11  
% 2.47/1.11  cnf(c_3484,plain,
% 2.47/1.11      ( sK2 = k1_xboole_0
% 2.47/1.11      | r1_tarski(sK2,X0) = iProver_top
% 2.47/1.11      | r2_hidden(sK1,X0) != iProver_top ),
% 2.47/1.11      inference(superposition,[status(thm)],[c_3330,c_1388]) ).
% 2.47/1.11  
% 2.47/1.11  cnf(c_5844,plain,
% 2.47/1.11      ( sK2 = k1_xboole_0 | r1_tarski(sK2,sK3) = iProver_top ),
% 2.47/1.11      inference(superposition,[status(thm)],[c_5839,c_3484]) ).
% 2.47/1.11  
% 2.47/1.11  cnf(c_6,plain,
% 2.47/1.11      ( ~ r1_tarski(X0,X1)
% 2.47/1.11      | k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = X1 ),
% 2.47/1.11      inference(cnf_transformation,[],[f78]) ).
% 2.47/1.11  
% 2.47/1.11  cnf(c_1395,plain,
% 2.47/1.11      ( k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = X1
% 2.47/1.11      | r1_tarski(X0,X1) != iProver_top ),
% 2.47/1.11      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 2.47/1.11  
% 2.47/1.11  cnf(c_6877,plain,
% 2.47/1.11      ( k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3)) = sK3
% 2.47/1.11      | sK2 = k1_xboole_0 ),
% 2.47/1.11      inference(superposition,[status(thm)],[c_5844,c_1395]) ).
% 2.47/1.11  
% 2.47/1.11  cnf(c_6881,plain,
% 2.47/1.11      ( k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) = sK3
% 2.47/1.11      | sK2 = k1_xboole_0 ),
% 2.47/1.11      inference(demodulation,[status(thm)],[c_6877,c_22]) ).
% 2.47/1.11  
% 2.47/1.11  cnf(c_21,negated_conjecture,
% 2.47/1.11      ( k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) != sK2
% 2.47/1.11      | k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) != sK3 ),
% 2.47/1.11      inference(cnf_transformation,[],[f91]) ).
% 2.47/1.11  
% 2.47/1.11  cnf(c_3500,plain,
% 2.47/1.11      ( k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) != sK3
% 2.47/1.11      | sK2 = k1_xboole_0 ),
% 2.47/1.11      inference(superposition,[status(thm)],[c_3330,c_21]) ).
% 2.47/1.11  
% 2.47/1.11  cnf(c_20,negated_conjecture,
% 2.47/1.11      ( k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) != sK3
% 2.47/1.11      | k1_xboole_0 != sK2 ),
% 2.47/1.11      inference(cnf_transformation,[],[f90]) ).
% 2.47/1.11  
% 2.47/1.11  cnf(c_1596,plain,
% 2.47/1.11      ( ~ r1_tarski(sK2,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))
% 2.47/1.11      | k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) = sK2
% 2.47/1.11      | k1_xboole_0 = sK2 ),
% 2.47/1.11      inference(instantiation,[status(thm)],[c_18]) ).
% 2.47/1.11  
% 2.47/1.11  cnf(c_1817,plain,
% 2.47/1.11      ( r1_tarski(sK2,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)) ),
% 2.47/1.11      inference(predicate_to_equality_rev,[status(thm)],[c_1816]) ).
% 2.47/1.11  
% 2.47/1.11  cnf(c_3707,plain,
% 2.47/1.11      ( k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) != sK3 ),
% 2.47/1.11      inference(global_propositional_subsumption,
% 2.47/1.11                [status(thm)],
% 2.47/1.11                [c_3500,c_21,c_20,c_1596,c_1817]) ).
% 2.47/1.11  
% 2.47/1.11  cnf(c_7046,plain,
% 2.47/1.11      ( sK2 = k1_xboole_0 ),
% 2.47/1.11      inference(global_propositional_subsumption,
% 2.47/1.11                [status(thm)],
% 2.47/1.11                [c_6881,c_21,c_20,c_1596,c_1817]) ).
% 2.47/1.11  
% 2.47/1.11  cnf(c_7073,plain,
% 2.47/1.11      ( k3_tarski(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,sK3)) = k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) ),
% 2.47/1.11      inference(demodulation,[status(thm)],[c_7046,c_22]) ).
% 2.47/1.11  
% 2.47/1.11  cnf(c_2,plain,
% 2.47/1.11      ( r1_tarski(X0,X1) | r2_hidden(sK0(X0,X1),X0) ),
% 2.47/1.11      inference(cnf_transformation,[],[f42]) ).
% 2.47/1.11  
% 2.47/1.11  cnf(c_1398,plain,
% 2.47/1.11      ( r1_tarski(X0,X1) = iProver_top
% 2.47/1.11      | r2_hidden(sK0(X0,X1),X0) = iProver_top ),
% 2.47/1.11      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 2.47/1.11  
% 2.47/1.11  cnf(c_1382,plain,
% 2.47/1.11      ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
% 2.47/1.11      inference(predicate_to_equality,[status(thm)],[c_264]) ).
% 2.47/1.11  
% 2.47/1.11  cnf(c_1761,plain,
% 2.47/1.11      ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
% 2.47/1.11      inference(superposition,[status(thm)],[c_1398,c_1382]) ).
% 2.47/1.11  
% 2.47/1.11  cnf(c_1933,plain,
% 2.47/1.11      ( k3_tarski(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,X0)) = X0 ),
% 2.47/1.11      inference(superposition,[status(thm)],[c_1761,c_1395]) ).
% 2.47/1.11  
% 2.47/1.11  cnf(c_7076,plain,
% 2.47/1.11      ( k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) = sK3 ),
% 2.47/1.11      inference(demodulation,[status(thm)],[c_7073,c_1933]) ).
% 2.47/1.11  
% 2.47/1.11  cnf(contradiction,plain,
% 2.47/1.11      ( $false ),
% 2.47/1.11      inference(minisat,[status(thm)],[c_7076,c_3707]) ).
% 2.47/1.11  
% 2.47/1.11  
% 2.47/1.11  % SZS output end CNFRefutation for theBenchmark.p
% 2.47/1.11  
% 2.47/1.11  ------                               Statistics
% 2.47/1.11  
% 2.47/1.11  ------ General
% 2.47/1.11  
% 2.47/1.11  abstr_ref_over_cycles:                  0
% 2.47/1.11  abstr_ref_under_cycles:                 0
% 2.47/1.11  gc_basic_clause_elim:                   0
% 2.47/1.11  forced_gc_time:                         0
% 2.47/1.11  parsing_time:                           0.017
% 2.47/1.11  unif_index_cands_time:                  0.
% 2.47/1.11  unif_index_add_time:                    0.
% 2.47/1.11  orderings_time:                         0.
% 2.47/1.11  out_proof_time:                         0.009
% 2.47/1.11  total_time:                             0.368
% 2.47/1.11  num_of_symbols:                         42
% 2.47/1.11  num_of_terms:                           4788
% 2.47/1.11  
% 2.47/1.11  ------ Preprocessing
% 2.47/1.11  
% 2.47/1.11  num_of_splits:                          0
% 2.47/1.11  num_of_split_atoms:                     0
% 2.47/1.11  num_of_reused_defs:                     0
% 2.47/1.11  num_eq_ax_congr_red:                    7
% 2.47/1.11  num_of_sem_filtered_clauses:            1
% 2.47/1.11  num_of_subtypes:                        0
% 2.47/1.11  monotx_restored_types:                  0
% 2.47/1.11  sat_num_of_epr_types:                   0
% 2.47/1.11  sat_num_of_non_cyclic_types:            0
% 2.47/1.11  sat_guarded_non_collapsed_types:        0
% 2.47/1.11  num_pure_diseq_elim:                    0
% 2.47/1.11  simp_replaced_by:                       0
% 2.47/1.11  res_preprocessed:                       104
% 2.47/1.11  prep_upred:                             0
% 2.47/1.11  prep_unflattend:                        67
% 2.47/1.11  smt_new_axioms:                         0
% 2.47/1.11  pred_elim_cands:                        3
% 2.47/1.11  pred_elim:                              1
% 2.47/1.11  pred_elim_cl:                           1
% 2.47/1.11  pred_elim_cycles:                       3
% 2.47/1.11  merged_defs:                            8
% 2.47/1.11  merged_defs_ncl:                        0
% 2.47/1.11  bin_hyper_res:                          8
% 2.47/1.11  prep_cycles:                            4
% 2.47/1.11  pred_elim_time:                         0.011
% 2.47/1.11  splitting_time:                         0.
% 2.47/1.11  sem_filter_time:                        0.
% 2.47/1.11  monotx_time:                            0.
% 2.47/1.11  subtype_inf_time:                       0.
% 2.47/1.11  
% 2.47/1.11  ------ Problem properties
% 2.47/1.11  
% 2.47/1.11  clauses:                                22
% 2.47/1.11  conjectures:                            4
% 2.47/1.11  epr:                                    5
% 2.47/1.11  horn:                                   19
% 2.47/1.11  ground:                                 5
% 2.47/1.11  unary:                                  6
% 2.47/1.11  binary:                                 13
% 2.47/1.11  lits:                                   41
% 2.47/1.11  lits_eq:                                11
% 2.47/1.11  fd_pure:                                0
% 2.47/1.11  fd_pseudo:                              0
% 2.47/1.11  fd_cond:                                1
% 2.47/1.11  fd_pseudo_cond:                         1
% 2.47/1.11  ac_symbols:                             0
% 2.47/1.11  
% 2.47/1.11  ------ Propositional Solver
% 2.47/1.11  
% 2.47/1.11  prop_solver_calls:                      30
% 2.47/1.11  prop_fast_solver_calls:                 760
% 2.47/1.11  smt_solver_calls:                       0
% 2.47/1.11  smt_fast_solver_calls:                  0
% 2.47/1.11  prop_num_of_clauses:                    2563
% 2.47/1.11  prop_preprocess_simplified:             6497
% 2.47/1.11  prop_fo_subsumed:                       17
% 2.47/1.11  prop_solver_time:                       0.
% 2.47/1.11  smt_solver_time:                        0.
% 2.47/1.11  smt_fast_solver_time:                   0.
% 2.47/1.11  prop_fast_solver_time:                  0.
% 2.47/1.11  prop_unsat_core_time:                   0.
% 2.47/1.11  
% 2.47/1.11  ------ QBF
% 2.47/1.11  
% 2.47/1.11  qbf_q_res:                              0
% 2.47/1.11  qbf_num_tautologies:                    0
% 2.47/1.11  qbf_prep_cycles:                        0
% 2.47/1.11  
% 2.47/1.11  ------ BMC1
% 2.47/1.11  
% 2.47/1.11  bmc1_current_bound:                     -1
% 2.47/1.11  bmc1_last_solved_bound:                 -1
% 2.47/1.11  bmc1_unsat_core_size:                   -1
% 2.47/1.11  bmc1_unsat_core_parents_size:           -1
% 2.47/1.11  bmc1_merge_next_fun:                    0
% 2.47/1.11  bmc1_unsat_core_clauses_time:           0.
% 2.47/1.11  
% 2.47/1.11  ------ Instantiation
% 2.47/1.11  
% 2.47/1.11  inst_num_of_clauses:                    772
% 2.47/1.11  inst_num_in_passive:                    183
% 2.47/1.11  inst_num_in_active:                     339
% 2.47/1.11  inst_num_in_unprocessed:                250
% 2.47/1.11  inst_num_of_loops:                      440
% 2.47/1.11  inst_num_of_learning_restarts:          0
% 2.47/1.11  inst_num_moves_active_passive:          97
% 2.47/1.11  inst_lit_activity:                      0
% 2.47/1.11  inst_lit_activity_moves:                0
% 2.47/1.11  inst_num_tautologies:                   0
% 2.47/1.11  inst_num_prop_implied:                  0
% 2.47/1.11  inst_num_existing_simplified:           0
% 2.47/1.11  inst_num_eq_res_simplified:             0
% 2.47/1.11  inst_num_child_elim:                    0
% 2.47/1.11  inst_num_of_dismatching_blockings:      155
% 2.47/1.11  inst_num_of_non_proper_insts:           777
% 2.47/1.11  inst_num_of_duplicates:                 0
% 2.47/1.11  inst_inst_num_from_inst_to_res:         0
% 2.47/1.11  inst_dismatching_checking_time:         0.
% 2.47/1.11  
% 2.47/1.11  ------ Resolution
% 2.47/1.11  
% 2.47/1.11  res_num_of_clauses:                     0
% 2.47/1.11  res_num_in_passive:                     0
% 2.47/1.11  res_num_in_active:                      0
% 2.47/1.11  res_num_of_loops:                       108
% 2.47/1.11  res_forward_subset_subsumed:            96
% 2.47/1.11  res_backward_subset_subsumed:           0
% 2.47/1.11  res_forward_subsumed:                   0
% 2.47/1.11  res_backward_subsumed:                  0
% 2.47/1.11  res_forward_subsumption_resolution:     0
% 2.47/1.11  res_backward_subsumption_resolution:    0
% 2.47/1.11  res_clause_to_clause_subsumption:       667
% 2.47/1.11  res_orphan_elimination:                 0
% 2.47/1.11  res_tautology_del:                      64
% 2.47/1.11  res_num_eq_res_simplified:              0
% 2.47/1.11  res_num_sel_changes:                    0
% 2.47/1.11  res_moves_from_active_to_pass:          0
% 2.47/1.11  
% 2.47/1.11  ------ Superposition
% 2.47/1.11  
% 2.47/1.11  sup_time_total:                         0.
% 2.47/1.11  sup_time_generating:                    0.
% 2.47/1.11  sup_time_sim_full:                      0.
% 2.47/1.11  sup_time_sim_immed:                     0.
% 2.47/1.11  
% 2.47/1.11  sup_num_of_clauses:                     71
% 2.47/1.11  sup_num_in_active:                      41
% 2.47/1.11  sup_num_in_passive:                     30
% 2.47/1.11  sup_num_of_loops:                       86
% 2.47/1.11  sup_fw_superposition:                   121
% 2.47/1.11  sup_bw_superposition:                   154
% 2.47/1.11  sup_immediate_simplified:               78
% 2.47/1.11  sup_given_eliminated:                   0
% 2.47/1.11  comparisons_done:                       0
% 2.47/1.11  comparisons_avoided:                    6
% 2.47/1.11  
% 2.47/1.11  ------ Simplifications
% 2.47/1.11  
% 2.47/1.11  
% 2.47/1.11  sim_fw_subset_subsumed:                 35
% 2.47/1.11  sim_bw_subset_subsumed:                 45
% 2.47/1.11  sim_fw_subsumed:                        24
% 2.47/1.11  sim_bw_subsumed:                        1
% 2.47/1.11  sim_fw_subsumption_res:                 4
% 2.47/1.11  sim_bw_subsumption_res:                 0
% 2.47/1.11  sim_tautology_del:                      29
% 2.47/1.11  sim_eq_tautology_del:                   13
% 2.47/1.11  sim_eq_res_simp:                        0
% 2.47/1.11  sim_fw_demodulated:                     8
% 2.47/1.11  sim_bw_demodulated:                     26
% 2.47/1.11  sim_light_normalised:                   19
% 2.47/1.11  sim_joinable_taut:                      0
% 2.47/1.11  sim_joinable_simp:                      0
% 2.47/1.11  sim_ac_normalised:                      0
% 2.47/1.11  sim_smt_subsumption:                    0
% 2.47/1.11  
%------------------------------------------------------------------------------
