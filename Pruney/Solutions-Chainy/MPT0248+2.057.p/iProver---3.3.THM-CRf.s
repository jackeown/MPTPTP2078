%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:32:16 EST 2020

% Result     : Theorem 35.43s
% Output     : CNFRefutation 35.43s
% Verified   : 
% Statistics : Number of formulae       :  237 ( 819 expanded)
%              Number of clauses        :  141 ( 225 expanded)
%              Number of leaves         :   32 ( 225 expanded)
%              Depth                    :   18
%              Number of atoms          :  512 (1414 expanded)
%              Number of equality atoms :  329 (1074 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal clause size      :   14 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f10,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f61,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f50,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] : ~ r2_hidden(X1,X0)
     => v1_xboole_0(X0) ) ),
    inference(unused_predicate_definition_removal,[],[f2])).

fof(f31,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
      | ? [X1] : r2_hidden(X1,X0) ) ),
    inference(ennf_transformation,[],[f30])).

fof(f42,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK0(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f43,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
      | r2_hidden(sK0(X0),X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f31,f42])).

fof(f51,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
      | r2_hidden(sK0(X0),X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f52,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f24,axiom,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
     => r1_xboole_0(k1_tarski(X0),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f76,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f16,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f67,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f16])).

fof(f17,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f68,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f17])).

fof(f18,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f69,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f18])).

fof(f19,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f70,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f19])).

fof(f20,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f71,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f20])).

fof(f21,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f72,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f21])).

fof(f22,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f73,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f22])).

fof(f83,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f72,f73])).

fof(f84,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f71,f83])).

fof(f85,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f70,f84])).

fof(f86,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f69,f85])).

fof(f87,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f68,f86])).

fof(f89,plain,(
    ! [X0] : k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f67,f87])).

fof(f98,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f76,f89])).

fof(f11,axiom,(
    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f62,plain,(
    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f11])).

fof(f13,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f64,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f13])).

fof(f6,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f57,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f94,plain,(
    ! [X0,X1] : r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X0) ),
    inference(definition_unfolding,[],[f64,f57])).

fof(f14,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f65,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f14])).

fof(f27,conjecture,(
    ! [X0,X1,X2] :
      ~ ( ~ ( k1_xboole_0 = X2
            & k1_tarski(X0) = X1 )
        & ~ ( k1_tarski(X0) = X2
            & k1_xboole_0 = X1 )
        & ~ ( k1_tarski(X0) = X2
            & k1_tarski(X0) = X1 )
        & k2_xboole_0(X1,X2) = k1_tarski(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ~ ( ~ ( k1_xboole_0 = X2
              & k1_tarski(X0) = X1 )
          & ~ ( k1_tarski(X0) = X2
              & k1_xboole_0 = X1 )
          & ~ ( k1_tarski(X0) = X2
              & k1_tarski(X0) = X1 )
          & k2_xboole_0(X1,X2) = k1_tarski(X0) ) ),
    inference(negated_conjecture,[],[f27])).

fof(f41,plain,(
    ? [X0,X1,X2] :
      ( ( k1_xboole_0 != X2
        | k1_tarski(X0) != X1 )
      & ( k1_tarski(X0) != X2
        | k1_xboole_0 != X1 )
      & ( k1_tarski(X0) != X2
        | k1_tarski(X0) != X1 )
      & k2_xboole_0(X1,X2) = k1_tarski(X0) ) ),
    inference(ennf_transformation,[],[f28])).

fof(f48,plain,
    ( ? [X0,X1,X2] :
        ( ( k1_xboole_0 != X2
          | k1_tarski(X0) != X1 )
        & ( k1_tarski(X0) != X2
          | k1_xboole_0 != X1 )
        & ( k1_tarski(X0) != X2
          | k1_tarski(X0) != X1 )
        & k2_xboole_0(X1,X2) = k1_tarski(X0) )
   => ( ( k1_xboole_0 != sK4
        | k1_tarski(sK2) != sK3 )
      & ( k1_tarski(sK2) != sK4
        | k1_xboole_0 != sK3 )
      & ( k1_tarski(sK2) != sK4
        | k1_tarski(sK2) != sK3 )
      & k2_xboole_0(sK3,sK4) = k1_tarski(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f49,plain,
    ( ( k1_xboole_0 != sK4
      | k1_tarski(sK2) != sK3 )
    & ( k1_tarski(sK2) != sK4
      | k1_xboole_0 != sK3 )
    & ( k1_tarski(sK2) != sK4
      | k1_tarski(sK2) != sK3 )
    & k2_xboole_0(sK3,sK4) = k1_tarski(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f41,f48])).

fof(f79,plain,(
    k2_xboole_0(sK3,sK4) = k1_tarski(sK2) ),
    inference(cnf_transformation,[],[f49])).

fof(f26,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f78,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f26])).

fof(f88,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f78,f87])).

fof(f103,plain,(
    k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) = k3_tarski(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4)) ),
    inference(definition_unfolding,[],[f79,f88,f89])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_tarski(X0,k2_xboole_0(X2,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k2_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f92,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k3_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X1)))
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f58,f88])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f4])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f29])).

fof(f44,plain,(
    ! [X1,X0] :
      ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
     => r2_hidden(sK1(X0,X1),k3_xboole_0(X0,X1)) ) ),
    introduced(choice_axiom,[])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( r2_hidden(sK1(X0,X1),k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f33,f44])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,k3_xboole_0(X0,X1)) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f36])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,X1)
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k4_xboole_0(X0,X1)
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k1_xboole_0 != k4_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f56,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f90,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k5_xboole_0(X0,k3_xboole_0(X0,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f56,f57])).

fof(f55,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | k1_xboole_0 != k4_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f91,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | k1_xboole_0 != k5_xboole_0(X0,k3_xboole_0(X0,X1)) ) ),
    inference(definition_unfolding,[],[f55,f57])).

fof(f15,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f66,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f15])).

fof(f95,plain,(
    ! [X0,X1] : r1_tarski(X0,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) ),
    inference(definition_unfolding,[],[f66,f88])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f59,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f93,plain,(
    ! [X0,X1] :
      ( k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f59,f88])).

fof(f23,axiom,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
    <=> r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f47,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(k1_tarski(X0),X1)
        | ~ r2_hidden(X0,X1) )
      & ( r2_hidden(X0,X1)
        | ~ r1_tarski(k1_tarski(X0),X1) ) ) ),
    inference(nnf_transformation,[],[f23])).

fof(f75,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f96,plain,(
    ! [X0,X1] :
      ( r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f75,f89])).

fof(f12,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f63,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f12])).

fof(f82,plain,
    ( k1_xboole_0 != sK4
    | k1_tarski(sK2) != sK3 ),
    inference(cnf_transformation,[],[f49])).

fof(f100,plain,
    ( k1_xboole_0 != sK4
    | k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) != sK3 ),
    inference(definition_unfolding,[],[f82,f89])).

fof(f81,plain,
    ( k1_tarski(sK2) != sK4
    | k1_xboole_0 != sK3 ),
    inference(cnf_transformation,[],[f49])).

fof(f101,plain,
    ( k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) != sK4
    | k1_xboole_0 != sK3 ),
    inference(definition_unfolding,[],[f81,f89])).

fof(f80,plain,
    ( k1_tarski(sK2) != sK4
    | k1_tarski(sK2) != sK3 ),
    inference(cnf_transformation,[],[f49])).

fof(f102,plain,
    ( k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) != sK4
    | k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) != sK3 ),
    inference(definition_unfolding,[],[f80,f89,f89])).

cnf(c_773,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_1360,plain,
    ( k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) != X0
    | k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) = sK3
    | sK3 != X0 ),
    inference(instantiation,[status(thm)],[c_773])).

cnf(c_4611,plain,
    ( k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) != k3_xboole_0(X0,X1)
    | k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) = sK3
    | sK3 != k3_xboole_0(X0,X1) ),
    inference(instantiation,[status(thm)],[c_1360])).

cnf(c_51646,plain,
    ( k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) != k3_xboole_0(k3_tarski(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,X0)),sK3)
    | k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) = sK3
    | sK3 != k3_xboole_0(k3_tarski(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,X0)),sK3) ),
    inference(instantiation,[status(thm)],[c_4611])).

cnf(c_114879,plain,
    ( k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) != k3_xboole_0(k3_tarski(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4)),sK3)
    | k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) = sK3
    | sK3 != k3_xboole_0(k3_tarski(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4)),sK3) ),
    inference(instantiation,[status(thm)],[c_51646])).

cnf(c_2953,plain,
    ( X0 != X1
    | k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2) != X1
    | k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2) = X0 ),
    inference(instantiation,[status(thm)],[c_773])).

cnf(c_10344,plain,
    ( X0 != k3_tarski(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4))
    | k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) = X0
    | k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) != k3_tarski(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4)) ),
    inference(instantiation,[status(thm)],[c_2953])).

cnf(c_11303,plain,
    ( k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) = k3_xboole_0(k3_tarski(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4)),X0)
    | k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) != k3_tarski(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4))
    | k3_xboole_0(k3_tarski(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4)),X0) != k3_tarski(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4)) ),
    inference(instantiation,[status(thm)],[c_10344])).

cnf(c_114878,plain,
    ( k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) = k3_xboole_0(k3_tarski(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4)),sK3)
    | k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) != k3_tarski(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4))
    | k3_xboole_0(k3_tarski(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4)),sK3) != k3_tarski(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4)) ),
    inference(instantiation,[status(thm)],[c_11303])).

cnf(c_778,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_1836,plain,
    ( r1_tarski(X0,X1)
    | ~ r1_tarski(k5_xboole_0(X2,k3_xboole_0(X2,X3)),X4)
    | X1 != X4
    | X0 != k5_xboole_0(X2,k3_xboole_0(X2,X3)) ),
    inference(instantiation,[status(thm)],[c_778])).

cnf(c_2968,plain,
    ( r1_tarski(X0,sK4)
    | ~ r1_tarski(k5_xboole_0(X1,k3_xboole_0(X1,X2)),X3)
    | X0 != k5_xboole_0(X1,k3_xboole_0(X1,X2))
    | sK4 != X3 ),
    inference(instantiation,[status(thm)],[c_1836])).

cnf(c_7792,plain,
    ( r1_tarski(X0,sK4)
    | ~ r1_tarski(k5_xboole_0(X1,k3_xboole_0(X1,X2)),sK4)
    | X0 != k5_xboole_0(X1,k3_xboole_0(X1,X2))
    | sK4 != sK4 ),
    inference(instantiation,[status(thm)],[c_2968])).

cnf(c_111942,plain,
    ( ~ r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),sK4)
    | r1_tarski(sK3,sK4)
    | sK3 != k5_xboole_0(X0,k3_xboole_0(X0,X1))
    | sK4 != sK4 ),
    inference(instantiation,[status(thm)],[c_7792])).

cnf(c_111961,plain,
    ( ~ r1_tarski(k5_xboole_0(sK2,k3_xboole_0(sK2,sK2)),sK4)
    | r1_tarski(sK3,sK4)
    | sK3 != k5_xboole_0(sK2,k3_xboole_0(sK2,sK2))
    | sK4 != sK4 ),
    inference(instantiation,[status(thm)],[c_111942])).

cnf(c_1494,plain,
    ( X0 != X1
    | sK4 != X1
    | sK4 = X0 ),
    inference(instantiation,[status(thm)],[c_773])).

cnf(c_1942,plain,
    ( X0 != sK4
    | sK4 = X0
    | sK4 != sK4 ),
    inference(instantiation,[status(thm)],[c_1494])).

cnf(c_101807,plain,
    ( k3_tarski(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4)) != sK4
    | sK4 = k3_tarski(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4))
    | sK4 != sK4 ),
    inference(instantiation,[status(thm)],[c_1942])).

cnf(c_101641,plain,
    ( k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) != k3_tarski(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4))
    | k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) = sK4
    | sK4 != k3_tarski(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4)) ),
    inference(instantiation,[status(thm)],[c_10344])).

cnf(c_1476,plain,
    ( X0 != X1
    | sK3 != X1
    | sK3 = X0 ),
    inference(instantiation,[status(thm)],[c_773])).

cnf(c_1495,plain,
    ( X0 != sK3
    | sK3 = X0
    | sK3 != sK3 ),
    inference(instantiation,[status(thm)],[c_1476])).

cnf(c_1954,plain,
    ( k3_xboole_0(sK3,k3_tarski(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,X0))) != sK3
    | sK3 = k3_xboole_0(sK3,k3_tarski(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,X0)))
    | sK3 != sK3 ),
    inference(instantiation,[status(thm)],[c_1495])).

cnf(c_98322,plain,
    ( k3_xboole_0(sK3,k3_tarski(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4))) != sK3
    | sK3 = k3_xboole_0(sK3,k3_tarski(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4)))
    | sK3 != sK3 ),
    inference(instantiation,[status(thm)],[c_1954])).

cnf(c_10,plain,
    ( ~ r1_tarski(X0,X1)
    | k3_xboole_0(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f61])).

cnf(c_11304,plain,
    ( ~ r1_tarski(k3_tarski(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4)),X0)
    | k3_xboole_0(k3_tarski(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4)),X0) = k3_tarski(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4)) ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_71846,plain,
    ( ~ r1_tarski(k3_tarski(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4)),sK3)
    | k3_xboole_0(k3_tarski(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4)),sK3) = k3_tarski(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4)) ),
    inference(instantiation,[status(thm)],[c_11304])).

cnf(c_71852,plain,
    ( k3_xboole_0(k3_tarski(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4)),sK3) = k3_tarski(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4))
    | r1_tarski(k3_tarski(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4)),sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_71846])).

cnf(c_4121,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,sK3)
    | X2 != X0
    | sK3 != X1 ),
    inference(instantiation,[status(thm)],[c_778])).

cnf(c_9387,plain,
    ( ~ r1_tarski(X0,sK3)
    | r1_tarski(X1,sK3)
    | X1 != X0
    | sK3 != sK3 ),
    inference(instantiation,[status(thm)],[c_4121])).

cnf(c_21640,plain,
    ( r1_tarski(X0,sK3)
    | ~ r1_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),sK3)
    | X0 != k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)
    | sK3 != sK3 ),
    inference(instantiation,[status(thm)],[c_9387])).

cnf(c_65069,plain,
    ( ~ r1_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3)
    | r1_tarski(k3_tarski(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4)),sK3)
    | k3_tarski(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4)) != k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)
    | sK3 != sK3 ),
    inference(instantiation,[status(thm)],[c_21640])).

cnf(c_65070,plain,
    ( k3_tarski(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4)) != k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)
    | sK3 != sK3
    | r1_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3) != iProver_top
    | r1_tarski(k3_tarski(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4)),sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_65069])).

cnf(c_8354,plain,
    ( X0 != k3_xboole_0(sK3,k3_tarski(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,X1)))
    | sK3 = X0
    | sK3 != k3_xboole_0(sK3,k3_tarski(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,X1))) ),
    inference(instantiation,[status(thm)],[c_1476])).

cnf(c_15408,plain,
    ( k3_xboole_0(k3_tarski(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,X0)),sK3) != k3_xboole_0(sK3,k3_tarski(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,X0)))
    | sK3 = k3_xboole_0(k3_tarski(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,X0)),sK3)
    | sK3 != k3_xboole_0(sK3,k3_tarski(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,X0))) ),
    inference(instantiation,[status(thm)],[c_8354])).

cnf(c_51638,plain,
    ( k3_xboole_0(k3_tarski(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4)),sK3) != k3_xboole_0(sK3,k3_tarski(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4)))
    | sK3 = k3_xboole_0(k3_tarski(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4)),sK3)
    | sK3 != k3_xboole_0(sK3,k3_tarski(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4))) ),
    inference(instantiation,[status(thm)],[c_15408])).

cnf(c_0,plain,
    ( k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_15409,plain,
    ( k3_xboole_0(k3_tarski(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,X0)),sK3) = k3_xboole_0(sK3,k3_tarski(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,X0))) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_46767,plain,
    ( k3_xboole_0(k3_tarski(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4)),sK3) = k3_xboole_0(sK3,k3_tarski(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4))) ),
    inference(instantiation,[status(thm)],[c_15409])).

cnf(c_1,plain,
    ( r2_hidden(sK0(X0),X0)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_2,plain,
    ( ~ v1_xboole_0(X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f52])).

cnf(c_262,plain,
    ( r2_hidden(sK0(X0),X0)
    | k1_xboole_0 = X0 ),
    inference(resolution,[status(thm)],[c_1,c_2])).

cnf(c_1205,plain,
    ( k1_xboole_0 = X0
    | r2_hidden(sK0(X0),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_262])).

cnf(c_18,plain,
    ( r1_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1)
    | r2_hidden(X0,X1) ),
    inference(cnf_transformation,[],[f98])).

cnf(c_1207,plain,
    ( r1_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1) = iProver_top
    | r2_hidden(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_11,plain,
    ( k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f62])).

cnf(c_13,plain,
    ( r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X0) ),
    inference(cnf_transformation,[],[f94])).

cnf(c_1211,plain,
    ( r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_1625,plain,
    ( r1_tarski(k5_xboole_0(X0,k1_xboole_0),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_11,c_1211])).

cnf(c_14,plain,
    ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f65])).

cnf(c_1630,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1625,c_14])).

cnf(c_23,negated_conjecture,
    ( k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) = k3_tarski(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4)) ),
    inference(cnf_transformation,[],[f103])).

cnf(c_7,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X0,k3_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X1))) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_1216,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X0,k3_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_8867,plain,
    ( r1_tarski(X0,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)) = iProver_top
    | r1_tarski(X0,sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_23,c_1216])).

cnf(c_1213,plain,
    ( k3_xboole_0(X0,X1) = X0
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_9063,plain,
    ( k3_xboole_0(X0,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)) = X0
    | r1_tarski(X0,sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_8867,c_1213])).

cnf(c_9410,plain,
    ( k3_xboole_0(sK4,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)) = sK4 ),
    inference(superposition,[status(thm)],[c_1630,c_9063])).

cnf(c_3,plain,
    ( ~ r1_xboole_0(X0,X1)
    | ~ r2_hidden(X2,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_1220,plain,
    ( r1_xboole_0(X0,X1) != iProver_top
    | r2_hidden(X2,k3_xboole_0(X0,X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_7057,plain,
    ( r1_xboole_0(X0,X1) != iProver_top
    | r2_hidden(X2,k3_xboole_0(X1,X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_0,c_1220])).

cnf(c_11407,plain,
    ( r1_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK4) != iProver_top
    | r2_hidden(X0,sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_9410,c_7057])).

cnf(c_23323,plain,
    ( r2_hidden(X0,sK4) != iProver_top
    | r2_hidden(sK2,sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_1207,c_11407])).

cnf(c_24455,plain,
    ( sK4 = k1_xboole_0
    | r2_hidden(sK2,sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_1205,c_23323])).

cnf(c_24456,plain,
    ( r2_hidden(sK2,sK4)
    | sK4 = k1_xboole_0 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_24455])).

cnf(c_3221,plain,
    ( X0 != X1
    | k3_tarski(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4)) != X1
    | k3_tarski(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4)) = X0 ),
    inference(instantiation,[status(thm)],[c_773])).

cnf(c_7042,plain,
    ( X0 != k3_tarski(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4))
    | k3_tarski(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4)) = X0
    | k3_tarski(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4)) != k3_tarski(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4)) ),
    inference(instantiation,[status(thm)],[c_3221])).

cnf(c_20458,plain,
    ( k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) != k3_tarski(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4))
    | k3_tarski(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4)) = k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)
    | k3_tarski(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4)) != k3_tarski(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4)) ),
    inference(instantiation,[status(thm)],[c_7042])).

cnf(c_9,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X2)
    | r1_tarski(X0,X2) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_2984,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,sK4)
    | r1_tarski(X0,sK4) ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_6939,plain,
    ( r1_tarski(X0,sK4)
    | ~ r1_tarski(X0,k1_xboole_0)
    | ~ r1_tarski(k1_xboole_0,sK4) ),
    inference(instantiation,[status(thm)],[c_2984])).

cnf(c_20344,plain,
    ( r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),sK4)
    | ~ r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),k1_xboole_0)
    | ~ r1_tarski(k1_xboole_0,sK4) ),
    inference(instantiation,[status(thm)],[c_6939])).

cnf(c_20347,plain,
    ( r1_tarski(k5_xboole_0(sK2,k3_xboole_0(sK2,sK2)),sK4)
    | ~ r1_tarski(k5_xboole_0(sK2,k3_xboole_0(sK2,sK2)),k1_xboole_0)
    | ~ r1_tarski(k1_xboole_0,sK4) ),
    inference(instantiation,[status(thm)],[c_20344])).

cnf(c_5,plain,
    ( ~ r1_tarski(X0,X1)
    | k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f90])).

cnf(c_1218,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k1_xboole_0
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_5891,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),k3_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X0)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1211,c_1218])).

cnf(c_1623,plain,
    ( r1_tarski(k5_xboole_0(X0,k3_xboole_0(X1,X0)),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_0,c_1211])).

cnf(c_1824,plain,
    ( k3_xboole_0(k5_xboole_0(X0,k3_xboole_0(X1,X0)),X0) = k5_xboole_0(X0,k3_xboole_0(X1,X0)) ),
    inference(superposition,[status(thm)],[c_1623,c_1213])).

cnf(c_3145,plain,
    ( k3_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X0) = k5_xboole_0(X0,k3_xboole_0(X1,X0)) ),
    inference(superposition,[status(thm)],[c_0,c_1824])).

cnf(c_5946,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),k5_xboole_0(X0,k3_xboole_0(X1,X0))) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_5891,c_3145])).

cnf(c_17207,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),k5_xboole_0(X0,k3_xboole_0(X0,X1))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_0,c_5946])).

cnf(c_1825,plain,
    ( k3_xboole_0(X0,X0) = X0 ),
    inference(superposition,[status(thm)],[c_1630,c_1213])).

cnf(c_2014,plain,
    ( r1_tarski(k5_xboole_0(X0,X0),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1825,c_1211])).

cnf(c_2022,plain,
    ( k3_xboole_0(k5_xboole_0(X0,X0),X0) = k5_xboole_0(X0,X0) ),
    inference(superposition,[status(thm)],[c_2014,c_1213])).

cnf(c_2097,plain,
    ( k3_xboole_0(X0,k5_xboole_0(X0,X0)) = k5_xboole_0(X0,X0) ),
    inference(superposition,[status(thm)],[c_2022,c_0])).

cnf(c_6,plain,
    ( r1_tarski(X0,X1)
    | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f91])).

cnf(c_1217,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) != k1_xboole_0
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_5789,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X0,X0)) != k1_xboole_0
    | r1_tarski(X0,k5_xboole_0(X0,X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2097,c_1217])).

cnf(c_19561,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),k1_xboole_0) != k1_xboole_0
    | r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),k5_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),k5_xboole_0(X0,k3_xboole_0(X0,X1)))) = iProver_top ),
    inference(superposition,[status(thm)],[c_17207,c_5789])).

cnf(c_19613,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),k1_xboole_0) != k1_xboole_0
    | r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),k1_xboole_0) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_19561,c_17207])).

cnf(c_19614,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) != k1_xboole_0
    | r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),k1_xboole_0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_19613,c_14])).

cnf(c_19631,plain,
    ( r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),k1_xboole_0)
    | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != k1_xboole_0 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_19614])).

cnf(c_19633,plain,
    ( r1_tarski(k5_xboole_0(sK2,k3_xboole_0(sK2,sK2)),k1_xboole_0)
    | k5_xboole_0(sK2,k3_xboole_0(sK2,sK2)) != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_19631])).

cnf(c_15,plain,
    ( r1_tarski(X0,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) ),
    inference(cnf_transformation,[],[f95])).

cnf(c_1210,plain,
    ( r1_tarski(X0,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_4347,plain,
    ( r1_tarski(sK3,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_23,c_1210])).

cnf(c_4550,plain,
    ( k3_xboole_0(sK3,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)) = sK3 ),
    inference(superposition,[status(thm)],[c_4347,c_1213])).

cnf(c_8496,plain,
    ( r1_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3) != iProver_top
    | r2_hidden(X0,sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_4550,c_7057])).

cnf(c_11837,plain,
    ( r2_hidden(X0,sK3) != iProver_top
    | r2_hidden(sK2,sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_1207,c_8496])).

cnf(c_16079,plain,
    ( sK3 = k1_xboole_0
    | r2_hidden(sK2,sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_1205,c_11837])).

cnf(c_1585,plain,
    ( X0 != X1
    | X0 = k5_xboole_0(X2,k3_xboole_0(X2,X3))
    | k5_xboole_0(X2,k3_xboole_0(X2,X3)) != X1 ),
    inference(instantiation,[status(thm)],[c_773])).

cnf(c_7985,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X2
    | sK3 != X2
    | sK3 = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(instantiation,[status(thm)],[c_1585])).

cnf(c_12289,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) != k1_xboole_0
    | sK3 = k5_xboole_0(X0,k3_xboole_0(X0,X1))
    | sK3 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_7985])).

cnf(c_12290,plain,
    ( k5_xboole_0(sK2,k3_xboole_0(sK2,sK2)) != k1_xboole_0
    | sK3 = k5_xboole_0(sK2,k3_xboole_0(sK2,sK2))
    | sK3 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_12289])).

cnf(c_8,plain,
    ( ~ r1_tarski(X0,X1)
    | k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = X1 ),
    inference(cnf_transformation,[],[f93])).

cnf(c_3109,plain,
    ( ~ r1_tarski(X0,sK4)
    | k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,sK4)) = sK4 ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_11767,plain,
    ( ~ r1_tarski(sK3,sK4)
    | k3_tarski(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4)) = sK4 ),
    inference(instantiation,[status(thm)],[c_3109])).

cnf(c_4032,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(sK3,X0)
    | r1_tarski(sK3,X1) ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_9137,plain,
    ( ~ r1_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),X0)
    | r1_tarski(sK3,X0)
    | ~ r1_tarski(sK3,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)) ),
    inference(instantiation,[status(thm)],[c_4032])).

cnf(c_11766,plain,
    ( ~ r1_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK4)
    | ~ r1_tarski(sK3,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))
    | r1_tarski(sK3,sK4) ),
    inference(instantiation,[status(thm)],[c_9137])).

cnf(c_16,plain,
    ( r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1)
    | ~ r2_hidden(X0,X1) ),
    inference(cnf_transformation,[],[f96])).

cnf(c_11368,plain,
    ( r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),sK3)
    | ~ r2_hidden(X0,sK3) ),
    inference(instantiation,[status(thm)],[c_16])).

cnf(c_11371,plain,
    ( r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),sK3) = iProver_top
    | r2_hidden(X0,sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11368])).

cnf(c_11373,plain,
    ( r1_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3) = iProver_top
    | r2_hidden(sK2,sK3) != iProver_top ),
    inference(instantiation,[status(thm)],[c_11371])).

cnf(c_11338,plain,
    ( r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),sK4)
    | ~ r2_hidden(X0,sK4) ),
    inference(instantiation,[status(thm)],[c_16])).

cnf(c_11343,plain,
    ( r1_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK4)
    | ~ r2_hidden(sK2,sK4) ),
    inference(instantiation,[status(thm)],[c_11338])).

cnf(c_12,plain,
    ( r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_6940,plain,
    ( r1_tarski(k1_xboole_0,sK4) ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_1358,plain,
    ( sK4 != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = sK4 ),
    inference(instantiation,[status(thm)],[c_773])).

cnf(c_6613,plain,
    ( sK4 != k1_xboole_0
    | k1_xboole_0 = sK4
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1358])).

cnf(c_1362,plain,
    ( sK3 != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = sK3 ),
    inference(instantiation,[status(thm)],[c_773])).

cnf(c_5424,plain,
    ( sK3 != k1_xboole_0
    | k1_xboole_0 = sK3
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1362])).

cnf(c_1373,plain,
    ( ~ r1_tarski(X0,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))
    | k3_xboole_0(X0,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) = X0 ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_1955,plain,
    ( ~ r1_tarski(sK3,k3_tarski(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,X0)))
    | k3_xboole_0(sK3,k3_tarski(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,X0))) = sK3 ),
    inference(instantiation,[status(thm)],[c_1373])).

cnf(c_4010,plain,
    ( ~ r1_tarski(sK3,k3_tarski(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4)))
    | k3_xboole_0(sK3,k3_tarski(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4))) = sK3 ),
    inference(instantiation,[status(thm)],[c_1955])).

cnf(c_772,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_1698,plain,
    ( k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ),
    inference(instantiation,[status(thm)],[c_772])).

cnf(c_3349,plain,
    ( k3_tarski(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4)) = k3_tarski(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4)) ),
    inference(instantiation,[status(thm)],[c_1698])).

cnf(c_3084,plain,
    ( k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_772])).

cnf(c_1372,plain,
    ( r1_tarski(X0,X1)
    | ~ r1_tarski(X2,k3_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X3)))
    | X0 != X2
    | X1 != k3_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X3)) ),
    inference(instantiation,[status(thm)],[c_778])).

cnf(c_1692,plain,
    ( r1_tarski(X0,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))
    | ~ r1_tarski(sK3,k3_tarski(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4)))
    | X0 != sK3
    | k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) != k3_tarski(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4)) ),
    inference(instantiation,[status(thm)],[c_1372])).

cnf(c_2838,plain,
    ( r1_tarski(sK3,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))
    | ~ r1_tarski(sK3,k3_tarski(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4)))
    | k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) != k3_tarski(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4))
    | sK3 != sK3 ),
    inference(instantiation,[status(thm)],[c_1692])).

cnf(c_1943,plain,
    ( sK4 = sK4 ),
    inference(instantiation,[status(thm)],[c_772])).

cnf(c_1904,plain,
    ( r1_tarski(sK3,k3_tarski(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4))) ),
    inference(instantiation,[status(thm)],[c_15])).

cnf(c_1636,plain,
    ( r1_tarski(sK2,sK2) = iProver_top ),
    inference(instantiation,[status(thm)],[c_1630])).

cnf(c_1496,plain,
    ( sK3 = sK3 ),
    inference(instantiation,[status(thm)],[c_772])).

cnf(c_58,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k1_xboole_0
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_60,plain,
    ( k5_xboole_0(sK2,k3_xboole_0(sK2,sK2)) = k1_xboole_0
    | r1_tarski(sK2,sK2) != iProver_top ),
    inference(instantiation,[status(thm)],[c_58])).

cnf(c_20,negated_conjecture,
    ( k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) != sK3
    | k1_xboole_0 != sK4 ),
    inference(cnf_transformation,[],[f100])).

cnf(c_21,negated_conjecture,
    ( k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) != sK4
    | k1_xboole_0 != sK3 ),
    inference(cnf_transformation,[],[f101])).

cnf(c_22,negated_conjecture,
    ( k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) != sK3
    | k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) != sK4 ),
    inference(cnf_transformation,[],[f102])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_114879,c_114878,c_111961,c_101807,c_101641,c_98322,c_71852,c_65070,c_51638,c_46767,c_24456,c_20458,c_20347,c_19633,c_16079,c_12290,c_11767,c_11766,c_11373,c_11343,c_6940,c_6613,c_5424,c_4010,c_3349,c_3084,c_2838,c_1943,c_1904,c_1636,c_1496,c_60,c_20,c_21,c_22,c_23])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n015.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 11:01:08 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 35.43/5.01  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 35.43/5.01  
% 35.43/5.01  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 35.43/5.01  
% 35.43/5.01  ------  iProver source info
% 35.43/5.01  
% 35.43/5.01  git: date: 2020-06-30 10:37:57 +0100
% 35.43/5.01  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 35.43/5.01  git: non_committed_changes: false
% 35.43/5.01  git: last_make_outside_of_git: false
% 35.43/5.01  
% 35.43/5.01  ------ 
% 35.43/5.01  
% 35.43/5.01  ------ Input Options
% 35.43/5.01  
% 35.43/5.01  --out_options                           all
% 35.43/5.01  --tptp_safe_out                         true
% 35.43/5.01  --problem_path                          ""
% 35.43/5.01  --include_path                          ""
% 35.43/5.01  --clausifier                            res/vclausify_rel
% 35.43/5.01  --clausifier_options                    --mode clausify
% 35.43/5.01  --stdin                                 false
% 35.43/5.01  --stats_out                             all
% 35.43/5.01  
% 35.43/5.01  ------ General Options
% 35.43/5.01  
% 35.43/5.01  --fof                                   false
% 35.43/5.01  --time_out_real                         305.
% 35.43/5.01  --time_out_virtual                      -1.
% 35.43/5.01  --symbol_type_check                     false
% 35.43/5.01  --clausify_out                          false
% 35.43/5.01  --sig_cnt_out                           false
% 35.43/5.01  --trig_cnt_out                          false
% 35.43/5.01  --trig_cnt_out_tolerance                1.
% 35.43/5.01  --trig_cnt_out_sk_spl                   false
% 35.43/5.01  --abstr_cl_out                          false
% 35.43/5.01  
% 35.43/5.01  ------ Global Options
% 35.43/5.01  
% 35.43/5.01  --schedule                              default
% 35.43/5.01  --add_important_lit                     false
% 35.43/5.01  --prop_solver_per_cl                    1000
% 35.43/5.01  --min_unsat_core                        false
% 35.43/5.01  --soft_assumptions                      false
% 35.43/5.01  --soft_lemma_size                       3
% 35.43/5.01  --prop_impl_unit_size                   0
% 35.43/5.01  --prop_impl_unit                        []
% 35.43/5.01  --share_sel_clauses                     true
% 35.43/5.01  --reset_solvers                         false
% 35.43/5.01  --bc_imp_inh                            [conj_cone]
% 35.43/5.01  --conj_cone_tolerance                   3.
% 35.43/5.01  --extra_neg_conj                        none
% 35.43/5.01  --large_theory_mode                     true
% 35.43/5.01  --prolific_symb_bound                   200
% 35.43/5.01  --lt_threshold                          2000
% 35.43/5.01  --clause_weak_htbl                      true
% 35.43/5.01  --gc_record_bc_elim                     false
% 35.43/5.01  
% 35.43/5.01  ------ Preprocessing Options
% 35.43/5.01  
% 35.43/5.01  --preprocessing_flag                    true
% 35.43/5.01  --time_out_prep_mult                    0.1
% 35.43/5.01  --splitting_mode                        input
% 35.43/5.01  --splitting_grd                         true
% 35.43/5.01  --splitting_cvd                         false
% 35.43/5.01  --splitting_cvd_svl                     false
% 35.43/5.01  --splitting_nvd                         32
% 35.43/5.01  --sub_typing                            true
% 35.43/5.01  --prep_gs_sim                           true
% 35.43/5.01  --prep_unflatten                        true
% 35.43/5.01  --prep_res_sim                          true
% 35.43/5.01  --prep_upred                            true
% 35.43/5.01  --prep_sem_filter                       exhaustive
% 35.43/5.01  --prep_sem_filter_out                   false
% 35.43/5.01  --pred_elim                             true
% 35.43/5.01  --res_sim_input                         true
% 35.43/5.01  --eq_ax_congr_red                       true
% 35.43/5.01  --pure_diseq_elim                       true
% 35.43/5.01  --brand_transform                       false
% 35.43/5.01  --non_eq_to_eq                          false
% 35.43/5.01  --prep_def_merge                        true
% 35.43/5.01  --prep_def_merge_prop_impl              false
% 35.43/5.01  --prep_def_merge_mbd                    true
% 35.43/5.01  --prep_def_merge_tr_red                 false
% 35.43/5.01  --prep_def_merge_tr_cl                  false
% 35.43/5.01  --smt_preprocessing                     true
% 35.43/5.01  --smt_ac_axioms                         fast
% 35.43/5.01  --preprocessed_out                      false
% 35.43/5.01  --preprocessed_stats                    false
% 35.43/5.01  
% 35.43/5.01  ------ Abstraction refinement Options
% 35.43/5.01  
% 35.43/5.01  --abstr_ref                             []
% 35.43/5.01  --abstr_ref_prep                        false
% 35.43/5.01  --abstr_ref_until_sat                   false
% 35.43/5.01  --abstr_ref_sig_restrict                funpre
% 35.43/5.01  --abstr_ref_af_restrict_to_split_sk     false
% 35.43/5.01  --abstr_ref_under                       []
% 35.43/5.01  
% 35.43/5.01  ------ SAT Options
% 35.43/5.01  
% 35.43/5.01  --sat_mode                              false
% 35.43/5.01  --sat_fm_restart_options                ""
% 35.43/5.01  --sat_gr_def                            false
% 35.43/5.01  --sat_epr_types                         true
% 35.43/5.01  --sat_non_cyclic_types                  false
% 35.43/5.01  --sat_finite_models                     false
% 35.43/5.01  --sat_fm_lemmas                         false
% 35.43/5.01  --sat_fm_prep                           false
% 35.43/5.01  --sat_fm_uc_incr                        true
% 35.43/5.01  --sat_out_model                         small
% 35.43/5.01  --sat_out_clauses                       false
% 35.43/5.01  
% 35.43/5.01  ------ QBF Options
% 35.43/5.01  
% 35.43/5.01  --qbf_mode                              false
% 35.43/5.01  --qbf_elim_univ                         false
% 35.43/5.01  --qbf_dom_inst                          none
% 35.43/5.01  --qbf_dom_pre_inst                      false
% 35.43/5.01  --qbf_sk_in                             false
% 35.43/5.01  --qbf_pred_elim                         true
% 35.43/5.01  --qbf_split                             512
% 35.43/5.01  
% 35.43/5.01  ------ BMC1 Options
% 35.43/5.01  
% 35.43/5.01  --bmc1_incremental                      false
% 35.43/5.01  --bmc1_axioms                           reachable_all
% 35.43/5.01  --bmc1_min_bound                        0
% 35.43/5.01  --bmc1_max_bound                        -1
% 35.43/5.01  --bmc1_max_bound_default                -1
% 35.43/5.01  --bmc1_symbol_reachability              true
% 35.43/5.01  --bmc1_property_lemmas                  false
% 35.43/5.01  --bmc1_k_induction                      false
% 35.43/5.01  --bmc1_non_equiv_states                 false
% 35.43/5.01  --bmc1_deadlock                         false
% 35.43/5.01  --bmc1_ucm                              false
% 35.43/5.01  --bmc1_add_unsat_core                   none
% 35.43/5.01  --bmc1_unsat_core_children              false
% 35.43/5.01  --bmc1_unsat_core_extrapolate_axioms    false
% 35.43/5.01  --bmc1_out_stat                         full
% 35.43/5.01  --bmc1_ground_init                      false
% 35.43/5.01  --bmc1_pre_inst_next_state              false
% 35.43/5.01  --bmc1_pre_inst_state                   false
% 35.43/5.01  --bmc1_pre_inst_reach_state             false
% 35.43/5.01  --bmc1_out_unsat_core                   false
% 35.43/5.01  --bmc1_aig_witness_out                  false
% 35.43/5.01  --bmc1_verbose                          false
% 35.43/5.01  --bmc1_dump_clauses_tptp                false
% 35.43/5.01  --bmc1_dump_unsat_core_tptp             false
% 35.43/5.01  --bmc1_dump_file                        -
% 35.43/5.01  --bmc1_ucm_expand_uc_limit              128
% 35.43/5.01  --bmc1_ucm_n_expand_iterations          6
% 35.43/5.01  --bmc1_ucm_extend_mode                  1
% 35.43/5.01  --bmc1_ucm_init_mode                    2
% 35.43/5.01  --bmc1_ucm_cone_mode                    none
% 35.43/5.01  --bmc1_ucm_reduced_relation_type        0
% 35.43/5.01  --bmc1_ucm_relax_model                  4
% 35.43/5.01  --bmc1_ucm_full_tr_after_sat            true
% 35.43/5.01  --bmc1_ucm_expand_neg_assumptions       false
% 35.43/5.01  --bmc1_ucm_layered_model                none
% 35.43/5.01  --bmc1_ucm_max_lemma_size               10
% 35.43/5.01  
% 35.43/5.01  ------ AIG Options
% 35.43/5.01  
% 35.43/5.01  --aig_mode                              false
% 35.43/5.01  
% 35.43/5.01  ------ Instantiation Options
% 35.43/5.01  
% 35.43/5.01  --instantiation_flag                    true
% 35.43/5.01  --inst_sos_flag                         false
% 35.43/5.01  --inst_sos_phase                        true
% 35.43/5.01  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 35.43/5.01  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 35.43/5.01  --inst_lit_sel_side                     num_symb
% 35.43/5.01  --inst_solver_per_active                1400
% 35.43/5.01  --inst_solver_calls_frac                1.
% 35.43/5.01  --inst_passive_queue_type               priority_queues
% 35.43/5.01  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 35.43/5.01  --inst_passive_queues_freq              [25;2]
% 35.43/5.01  --inst_dismatching                      true
% 35.43/5.01  --inst_eager_unprocessed_to_passive     true
% 35.43/5.01  --inst_prop_sim_given                   true
% 35.43/5.01  --inst_prop_sim_new                     false
% 35.43/5.01  --inst_subs_new                         false
% 35.43/5.01  --inst_eq_res_simp                      false
% 35.43/5.01  --inst_subs_given                       false
% 35.43/5.01  --inst_orphan_elimination               true
% 35.43/5.01  --inst_learning_loop_flag               true
% 35.43/5.01  --inst_learning_start                   3000
% 35.43/5.01  --inst_learning_factor                  2
% 35.43/5.01  --inst_start_prop_sim_after_learn       3
% 35.43/5.01  --inst_sel_renew                        solver
% 35.43/5.01  --inst_lit_activity_flag                true
% 35.43/5.01  --inst_restr_to_given                   false
% 35.43/5.01  --inst_activity_threshold               500
% 35.43/5.01  --inst_out_proof                        true
% 35.43/5.01  
% 35.43/5.01  ------ Resolution Options
% 35.43/5.01  
% 35.43/5.01  --resolution_flag                       true
% 35.43/5.01  --res_lit_sel                           adaptive
% 35.43/5.01  --res_lit_sel_side                      none
% 35.43/5.01  --res_ordering                          kbo
% 35.43/5.01  --res_to_prop_solver                    active
% 35.43/5.01  --res_prop_simpl_new                    false
% 35.43/5.01  --res_prop_simpl_given                  true
% 35.43/5.01  --res_passive_queue_type                priority_queues
% 35.43/5.01  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 35.43/5.01  --res_passive_queues_freq               [15;5]
% 35.43/5.01  --res_forward_subs                      full
% 35.43/5.01  --res_backward_subs                     full
% 35.43/5.01  --res_forward_subs_resolution           true
% 35.43/5.01  --res_backward_subs_resolution          true
% 35.43/5.01  --res_orphan_elimination                true
% 35.43/5.01  --res_time_limit                        2.
% 35.43/5.01  --res_out_proof                         true
% 35.43/5.01  
% 35.43/5.01  ------ Superposition Options
% 35.43/5.01  
% 35.43/5.01  --superposition_flag                    true
% 35.43/5.01  --sup_passive_queue_type                priority_queues
% 35.43/5.01  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 35.43/5.01  --sup_passive_queues_freq               [8;1;4]
% 35.43/5.01  --demod_completeness_check              fast
% 35.43/5.01  --demod_use_ground                      true
% 35.43/5.01  --sup_to_prop_solver                    passive
% 35.43/5.01  --sup_prop_simpl_new                    true
% 35.43/5.01  --sup_prop_simpl_given                  true
% 35.43/5.01  --sup_fun_splitting                     false
% 35.43/5.01  --sup_smt_interval                      50000
% 35.43/5.01  
% 35.43/5.01  ------ Superposition Simplification Setup
% 35.43/5.01  
% 35.43/5.01  --sup_indices_passive                   []
% 35.43/5.01  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 35.43/5.01  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 35.43/5.01  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 35.43/5.01  --sup_full_triv                         [TrivRules;PropSubs]
% 35.43/5.01  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 35.43/5.01  --sup_full_bw                           [BwDemod]
% 35.43/5.01  --sup_immed_triv                        [TrivRules]
% 35.43/5.01  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 35.43/5.01  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 35.43/5.01  --sup_immed_bw_main                     []
% 35.43/5.01  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 35.43/5.01  --sup_input_triv                        [Unflattening;TrivRules]
% 35.43/5.01  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 35.43/5.01  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 35.43/5.01  
% 35.43/5.01  ------ Combination Options
% 35.43/5.01  
% 35.43/5.01  --comb_res_mult                         3
% 35.43/5.01  --comb_sup_mult                         2
% 35.43/5.01  --comb_inst_mult                        10
% 35.43/5.01  
% 35.43/5.01  ------ Debug Options
% 35.43/5.01  
% 35.43/5.01  --dbg_backtrace                         false
% 35.43/5.01  --dbg_dump_prop_clauses                 false
% 35.43/5.01  --dbg_dump_prop_clauses_file            -
% 35.43/5.01  --dbg_out_stat                          false
% 35.43/5.01  ------ Parsing...
% 35.43/5.01  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 35.43/5.01  
% 35.43/5.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 35.43/5.01  
% 35.43/5.01  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 35.43/5.01  
% 35.43/5.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 35.43/5.01  ------ Proving...
% 35.43/5.01  ------ Problem Properties 
% 35.43/5.01  
% 35.43/5.01  
% 35.43/5.01  clauses                                 23
% 35.43/5.01  conjectures                             4
% 35.43/5.01  EPR                                     2
% 35.43/5.01  Horn                                    20
% 35.43/5.01  unary                                   7
% 35.43/5.01  binary                                  15
% 35.43/5.01  lits                                    40
% 35.43/5.01  lits eq                                 16
% 35.43/5.01  fd_pure                                 0
% 35.43/5.01  fd_pseudo                               0
% 35.43/5.01  fd_cond                                 1
% 35.43/5.01  fd_pseudo_cond                          0
% 35.43/5.01  AC symbols                              0
% 35.43/5.01  
% 35.43/5.01  ------ Schedule dynamic 5 is on 
% 35.43/5.01  
% 35.43/5.01  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 35.43/5.01  
% 35.43/5.01  
% 35.43/5.01  ------ 
% 35.43/5.01  Current options:
% 35.43/5.01  ------ 
% 35.43/5.01  
% 35.43/5.01  ------ Input Options
% 35.43/5.01  
% 35.43/5.01  --out_options                           all
% 35.43/5.01  --tptp_safe_out                         true
% 35.43/5.01  --problem_path                          ""
% 35.43/5.01  --include_path                          ""
% 35.43/5.01  --clausifier                            res/vclausify_rel
% 35.43/5.01  --clausifier_options                    --mode clausify
% 35.43/5.01  --stdin                                 false
% 35.43/5.01  --stats_out                             all
% 35.43/5.01  
% 35.43/5.01  ------ General Options
% 35.43/5.01  
% 35.43/5.01  --fof                                   false
% 35.43/5.01  --time_out_real                         305.
% 35.43/5.01  --time_out_virtual                      -1.
% 35.43/5.01  --symbol_type_check                     false
% 35.43/5.01  --clausify_out                          false
% 35.43/5.01  --sig_cnt_out                           false
% 35.43/5.01  --trig_cnt_out                          false
% 35.43/5.01  --trig_cnt_out_tolerance                1.
% 35.43/5.01  --trig_cnt_out_sk_spl                   false
% 35.43/5.01  --abstr_cl_out                          false
% 35.43/5.01  
% 35.43/5.01  ------ Global Options
% 35.43/5.01  
% 35.43/5.01  --schedule                              default
% 35.43/5.01  --add_important_lit                     false
% 35.43/5.01  --prop_solver_per_cl                    1000
% 35.43/5.01  --min_unsat_core                        false
% 35.43/5.01  --soft_assumptions                      false
% 35.43/5.01  --soft_lemma_size                       3
% 35.43/5.01  --prop_impl_unit_size                   0
% 35.43/5.01  --prop_impl_unit                        []
% 35.43/5.01  --share_sel_clauses                     true
% 35.43/5.01  --reset_solvers                         false
% 35.43/5.01  --bc_imp_inh                            [conj_cone]
% 35.43/5.01  --conj_cone_tolerance                   3.
% 35.43/5.01  --extra_neg_conj                        none
% 35.43/5.01  --large_theory_mode                     true
% 35.43/5.01  --prolific_symb_bound                   200
% 35.43/5.01  --lt_threshold                          2000
% 35.43/5.01  --clause_weak_htbl                      true
% 35.43/5.01  --gc_record_bc_elim                     false
% 35.43/5.01  
% 35.43/5.01  ------ Preprocessing Options
% 35.43/5.01  
% 35.43/5.01  --preprocessing_flag                    true
% 35.43/5.01  --time_out_prep_mult                    0.1
% 35.43/5.01  --splitting_mode                        input
% 35.43/5.01  --splitting_grd                         true
% 35.43/5.01  --splitting_cvd                         false
% 35.43/5.01  --splitting_cvd_svl                     false
% 35.43/5.01  --splitting_nvd                         32
% 35.43/5.01  --sub_typing                            true
% 35.43/5.01  --prep_gs_sim                           true
% 35.43/5.01  --prep_unflatten                        true
% 35.43/5.01  --prep_res_sim                          true
% 35.43/5.01  --prep_upred                            true
% 35.43/5.01  --prep_sem_filter                       exhaustive
% 35.43/5.01  --prep_sem_filter_out                   false
% 35.43/5.01  --pred_elim                             true
% 35.43/5.01  --res_sim_input                         true
% 35.43/5.01  --eq_ax_congr_red                       true
% 35.43/5.01  --pure_diseq_elim                       true
% 35.43/5.01  --brand_transform                       false
% 35.43/5.01  --non_eq_to_eq                          false
% 35.43/5.01  --prep_def_merge                        true
% 35.43/5.01  --prep_def_merge_prop_impl              false
% 35.43/5.01  --prep_def_merge_mbd                    true
% 35.43/5.01  --prep_def_merge_tr_red                 false
% 35.43/5.01  --prep_def_merge_tr_cl                  false
% 35.43/5.01  --smt_preprocessing                     true
% 35.43/5.01  --smt_ac_axioms                         fast
% 35.43/5.01  --preprocessed_out                      false
% 35.43/5.01  --preprocessed_stats                    false
% 35.43/5.01  
% 35.43/5.01  ------ Abstraction refinement Options
% 35.43/5.01  
% 35.43/5.01  --abstr_ref                             []
% 35.43/5.01  --abstr_ref_prep                        false
% 35.43/5.01  --abstr_ref_until_sat                   false
% 35.43/5.01  --abstr_ref_sig_restrict                funpre
% 35.43/5.01  --abstr_ref_af_restrict_to_split_sk     false
% 35.43/5.01  --abstr_ref_under                       []
% 35.43/5.01  
% 35.43/5.01  ------ SAT Options
% 35.43/5.01  
% 35.43/5.01  --sat_mode                              false
% 35.43/5.01  --sat_fm_restart_options                ""
% 35.43/5.01  --sat_gr_def                            false
% 35.43/5.01  --sat_epr_types                         true
% 35.43/5.01  --sat_non_cyclic_types                  false
% 35.43/5.01  --sat_finite_models                     false
% 35.43/5.01  --sat_fm_lemmas                         false
% 35.43/5.01  --sat_fm_prep                           false
% 35.43/5.01  --sat_fm_uc_incr                        true
% 35.43/5.01  --sat_out_model                         small
% 35.43/5.01  --sat_out_clauses                       false
% 35.43/5.01  
% 35.43/5.01  ------ QBF Options
% 35.43/5.01  
% 35.43/5.01  --qbf_mode                              false
% 35.43/5.01  --qbf_elim_univ                         false
% 35.43/5.01  --qbf_dom_inst                          none
% 35.43/5.01  --qbf_dom_pre_inst                      false
% 35.43/5.01  --qbf_sk_in                             false
% 35.43/5.01  --qbf_pred_elim                         true
% 35.43/5.01  --qbf_split                             512
% 35.43/5.01  
% 35.43/5.01  ------ BMC1 Options
% 35.43/5.01  
% 35.43/5.01  --bmc1_incremental                      false
% 35.43/5.01  --bmc1_axioms                           reachable_all
% 35.43/5.01  --bmc1_min_bound                        0
% 35.43/5.01  --bmc1_max_bound                        -1
% 35.43/5.01  --bmc1_max_bound_default                -1
% 35.43/5.01  --bmc1_symbol_reachability              true
% 35.43/5.01  --bmc1_property_lemmas                  false
% 35.43/5.01  --bmc1_k_induction                      false
% 35.43/5.01  --bmc1_non_equiv_states                 false
% 35.43/5.01  --bmc1_deadlock                         false
% 35.43/5.01  --bmc1_ucm                              false
% 35.43/5.01  --bmc1_add_unsat_core                   none
% 35.43/5.01  --bmc1_unsat_core_children              false
% 35.43/5.01  --bmc1_unsat_core_extrapolate_axioms    false
% 35.43/5.01  --bmc1_out_stat                         full
% 35.43/5.01  --bmc1_ground_init                      false
% 35.43/5.01  --bmc1_pre_inst_next_state              false
% 35.43/5.01  --bmc1_pre_inst_state                   false
% 35.43/5.01  --bmc1_pre_inst_reach_state             false
% 35.43/5.01  --bmc1_out_unsat_core                   false
% 35.43/5.01  --bmc1_aig_witness_out                  false
% 35.43/5.01  --bmc1_verbose                          false
% 35.43/5.01  --bmc1_dump_clauses_tptp                false
% 35.43/5.01  --bmc1_dump_unsat_core_tptp             false
% 35.43/5.01  --bmc1_dump_file                        -
% 35.43/5.01  --bmc1_ucm_expand_uc_limit              128
% 35.43/5.01  --bmc1_ucm_n_expand_iterations          6
% 35.43/5.01  --bmc1_ucm_extend_mode                  1
% 35.43/5.01  --bmc1_ucm_init_mode                    2
% 35.43/5.01  --bmc1_ucm_cone_mode                    none
% 35.43/5.01  --bmc1_ucm_reduced_relation_type        0
% 35.43/5.01  --bmc1_ucm_relax_model                  4
% 35.43/5.01  --bmc1_ucm_full_tr_after_sat            true
% 35.43/5.01  --bmc1_ucm_expand_neg_assumptions       false
% 35.43/5.01  --bmc1_ucm_layered_model                none
% 35.43/5.01  --bmc1_ucm_max_lemma_size               10
% 35.43/5.01  
% 35.43/5.01  ------ AIG Options
% 35.43/5.01  
% 35.43/5.01  --aig_mode                              false
% 35.43/5.01  
% 35.43/5.01  ------ Instantiation Options
% 35.43/5.01  
% 35.43/5.01  --instantiation_flag                    true
% 35.43/5.01  --inst_sos_flag                         false
% 35.43/5.01  --inst_sos_phase                        true
% 35.43/5.01  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 35.43/5.01  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 35.43/5.01  --inst_lit_sel_side                     none
% 35.43/5.01  --inst_solver_per_active                1400
% 35.43/5.01  --inst_solver_calls_frac                1.
% 35.43/5.01  --inst_passive_queue_type               priority_queues
% 35.43/5.01  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 35.43/5.01  --inst_passive_queues_freq              [25;2]
% 35.43/5.01  --inst_dismatching                      true
% 35.43/5.01  --inst_eager_unprocessed_to_passive     true
% 35.43/5.01  --inst_prop_sim_given                   true
% 35.43/5.01  --inst_prop_sim_new                     false
% 35.43/5.01  --inst_subs_new                         false
% 35.43/5.01  --inst_eq_res_simp                      false
% 35.43/5.01  --inst_subs_given                       false
% 35.43/5.01  --inst_orphan_elimination               true
% 35.43/5.01  --inst_learning_loop_flag               true
% 35.43/5.01  --inst_learning_start                   3000
% 35.43/5.01  --inst_learning_factor                  2
% 35.43/5.01  --inst_start_prop_sim_after_learn       3
% 35.43/5.01  --inst_sel_renew                        solver
% 35.43/5.01  --inst_lit_activity_flag                true
% 35.43/5.01  --inst_restr_to_given                   false
% 35.43/5.01  --inst_activity_threshold               500
% 35.43/5.01  --inst_out_proof                        true
% 35.43/5.01  
% 35.43/5.01  ------ Resolution Options
% 35.43/5.01  
% 35.43/5.01  --resolution_flag                       false
% 35.43/5.01  --res_lit_sel                           adaptive
% 35.43/5.01  --res_lit_sel_side                      none
% 35.43/5.01  --res_ordering                          kbo
% 35.43/5.01  --res_to_prop_solver                    active
% 35.43/5.01  --res_prop_simpl_new                    false
% 35.43/5.01  --res_prop_simpl_given                  true
% 35.43/5.01  --res_passive_queue_type                priority_queues
% 35.43/5.01  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 35.43/5.01  --res_passive_queues_freq               [15;5]
% 35.43/5.01  --res_forward_subs                      full
% 35.43/5.01  --res_backward_subs                     full
% 35.43/5.01  --res_forward_subs_resolution           true
% 35.43/5.01  --res_backward_subs_resolution          true
% 35.43/5.01  --res_orphan_elimination                true
% 35.43/5.01  --res_time_limit                        2.
% 35.43/5.01  --res_out_proof                         true
% 35.43/5.01  
% 35.43/5.01  ------ Superposition Options
% 35.43/5.01  
% 35.43/5.01  --superposition_flag                    true
% 35.43/5.01  --sup_passive_queue_type                priority_queues
% 35.43/5.01  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 35.43/5.01  --sup_passive_queues_freq               [8;1;4]
% 35.43/5.01  --demod_completeness_check              fast
% 35.43/5.01  --demod_use_ground                      true
% 35.43/5.01  --sup_to_prop_solver                    passive
% 35.43/5.01  --sup_prop_simpl_new                    true
% 35.43/5.01  --sup_prop_simpl_given                  true
% 35.43/5.01  --sup_fun_splitting                     false
% 35.43/5.01  --sup_smt_interval                      50000
% 35.43/5.01  
% 35.43/5.01  ------ Superposition Simplification Setup
% 35.43/5.01  
% 35.43/5.01  --sup_indices_passive                   []
% 35.43/5.01  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 35.43/5.01  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 35.43/5.01  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 35.43/5.01  --sup_full_triv                         [TrivRules;PropSubs]
% 35.43/5.01  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 35.43/5.01  --sup_full_bw                           [BwDemod]
% 35.43/5.01  --sup_immed_triv                        [TrivRules]
% 35.43/5.01  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 35.43/5.01  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 35.43/5.01  --sup_immed_bw_main                     []
% 35.43/5.01  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 35.43/5.01  --sup_input_triv                        [Unflattening;TrivRules]
% 35.43/5.01  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 35.43/5.01  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 35.43/5.01  
% 35.43/5.01  ------ Combination Options
% 35.43/5.01  
% 35.43/5.01  --comb_res_mult                         3
% 35.43/5.01  --comb_sup_mult                         2
% 35.43/5.01  --comb_inst_mult                        10
% 35.43/5.01  
% 35.43/5.01  ------ Debug Options
% 35.43/5.01  
% 35.43/5.01  --dbg_backtrace                         false
% 35.43/5.01  --dbg_dump_prop_clauses                 false
% 35.43/5.01  --dbg_dump_prop_clauses_file            -
% 35.43/5.01  --dbg_out_stat                          false
% 35.43/5.01  
% 35.43/5.01  
% 35.43/5.01  
% 35.43/5.01  
% 35.43/5.01  ------ Proving...
% 35.43/5.01  
% 35.43/5.01  
% 35.43/5.01  % SZS status Theorem for theBenchmark.p
% 35.43/5.01  
% 35.43/5.01  % SZS output start CNFRefutation for theBenchmark.p
% 35.43/5.01  
% 35.43/5.01  fof(f10,axiom,(
% 35.43/5.01    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 35.43/5.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 35.43/5.01  
% 35.43/5.01  fof(f38,plain,(
% 35.43/5.01    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 35.43/5.01    inference(ennf_transformation,[],[f10])).
% 35.43/5.01  
% 35.43/5.01  fof(f61,plain,(
% 35.43/5.01    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 35.43/5.01    inference(cnf_transformation,[],[f38])).
% 35.43/5.01  
% 35.43/5.01  fof(f1,axiom,(
% 35.43/5.01    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 35.43/5.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 35.43/5.01  
% 35.43/5.01  fof(f50,plain,(
% 35.43/5.01    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 35.43/5.01    inference(cnf_transformation,[],[f1])).
% 35.43/5.01  
% 35.43/5.01  fof(f2,axiom,(
% 35.43/5.01    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 35.43/5.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 35.43/5.01  
% 35.43/5.01  fof(f30,plain,(
% 35.43/5.01    ! [X0] : (! [X1] : ~r2_hidden(X1,X0) => v1_xboole_0(X0))),
% 35.43/5.01    inference(unused_predicate_definition_removal,[],[f2])).
% 35.43/5.01  
% 35.43/5.01  fof(f31,plain,(
% 35.43/5.01    ! [X0] : (v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0))),
% 35.43/5.01    inference(ennf_transformation,[],[f30])).
% 35.43/5.01  
% 35.43/5.01  fof(f42,plain,(
% 35.43/5.01    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK0(X0),X0))),
% 35.43/5.01    introduced(choice_axiom,[])).
% 35.43/5.01  
% 35.43/5.01  fof(f43,plain,(
% 35.43/5.01    ! [X0] : (v1_xboole_0(X0) | r2_hidden(sK0(X0),X0))),
% 35.43/5.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f31,f42])).
% 35.43/5.01  
% 35.43/5.01  fof(f51,plain,(
% 35.43/5.01    ( ! [X0] : (v1_xboole_0(X0) | r2_hidden(sK0(X0),X0)) )),
% 35.43/5.01    inference(cnf_transformation,[],[f43])).
% 35.43/5.01  
% 35.43/5.01  fof(f3,axiom,(
% 35.43/5.01    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 35.43/5.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 35.43/5.01  
% 35.43/5.01  fof(f32,plain,(
% 35.43/5.01    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 35.43/5.01    inference(ennf_transformation,[],[f3])).
% 35.43/5.01  
% 35.43/5.01  fof(f52,plain,(
% 35.43/5.01    ( ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0)) )),
% 35.43/5.01    inference(cnf_transformation,[],[f32])).
% 35.43/5.01  
% 35.43/5.01  fof(f24,axiom,(
% 35.43/5.01    ! [X0,X1] : (~r2_hidden(X0,X1) => r1_xboole_0(k1_tarski(X0),X1))),
% 35.43/5.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 35.43/5.01  
% 35.43/5.01  fof(f39,plain,(
% 35.43/5.01    ! [X0,X1] : (r1_xboole_0(k1_tarski(X0),X1) | r2_hidden(X0,X1))),
% 35.43/5.01    inference(ennf_transformation,[],[f24])).
% 35.43/5.01  
% 35.43/5.01  fof(f76,plain,(
% 35.43/5.01    ( ! [X0,X1] : (r1_xboole_0(k1_tarski(X0),X1) | r2_hidden(X0,X1)) )),
% 35.43/5.01    inference(cnf_transformation,[],[f39])).
% 35.43/5.01  
% 35.43/5.01  fof(f16,axiom,(
% 35.43/5.01    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 35.43/5.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 35.43/5.01  
% 35.43/5.01  fof(f67,plain,(
% 35.43/5.01    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 35.43/5.01    inference(cnf_transformation,[],[f16])).
% 35.43/5.01  
% 35.43/5.01  fof(f17,axiom,(
% 35.43/5.01    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 35.43/5.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 35.43/5.01  
% 35.43/5.01  fof(f68,plain,(
% 35.43/5.01    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 35.43/5.01    inference(cnf_transformation,[],[f17])).
% 35.43/5.01  
% 35.43/5.01  fof(f18,axiom,(
% 35.43/5.01    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 35.43/5.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 35.43/5.01  
% 35.43/5.01  fof(f69,plain,(
% 35.43/5.01    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 35.43/5.01    inference(cnf_transformation,[],[f18])).
% 35.43/5.01  
% 35.43/5.01  fof(f19,axiom,(
% 35.43/5.01    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 35.43/5.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 35.43/5.01  
% 35.43/5.01  fof(f70,plain,(
% 35.43/5.01    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 35.43/5.01    inference(cnf_transformation,[],[f19])).
% 35.43/5.01  
% 35.43/5.01  fof(f20,axiom,(
% 35.43/5.01    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)),
% 35.43/5.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 35.43/5.01  
% 35.43/5.01  fof(f71,plain,(
% 35.43/5.01    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)) )),
% 35.43/5.01    inference(cnf_transformation,[],[f20])).
% 35.43/5.01  
% 35.43/5.01  fof(f21,axiom,(
% 35.43/5.01    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)),
% 35.43/5.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 35.43/5.01  
% 35.43/5.01  fof(f72,plain,(
% 35.43/5.01    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)) )),
% 35.43/5.01    inference(cnf_transformation,[],[f21])).
% 35.43/5.01  
% 35.43/5.01  fof(f22,axiom,(
% 35.43/5.01    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)),
% 35.43/5.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 35.43/5.01  
% 35.43/5.01  fof(f73,plain,(
% 35.43/5.01    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)) )),
% 35.43/5.01    inference(cnf_transformation,[],[f22])).
% 35.43/5.01  
% 35.43/5.01  fof(f83,plain,(
% 35.43/5.01    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 35.43/5.01    inference(definition_unfolding,[],[f72,f73])).
% 35.43/5.01  
% 35.43/5.01  fof(f84,plain,(
% 35.43/5.01    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 35.43/5.01    inference(definition_unfolding,[],[f71,f83])).
% 35.43/5.01  
% 35.43/5.01  fof(f85,plain,(
% 35.43/5.01    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 35.43/5.01    inference(definition_unfolding,[],[f70,f84])).
% 35.43/5.01  
% 35.43/5.01  fof(f86,plain,(
% 35.43/5.01    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 35.43/5.01    inference(definition_unfolding,[],[f69,f85])).
% 35.43/5.01  
% 35.43/5.01  fof(f87,plain,(
% 35.43/5.01    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 35.43/5.01    inference(definition_unfolding,[],[f68,f86])).
% 35.43/5.01  
% 35.43/5.01  fof(f89,plain,(
% 35.43/5.01    ( ! [X0] : (k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) )),
% 35.43/5.01    inference(definition_unfolding,[],[f67,f87])).
% 35.43/5.01  
% 35.43/5.01  fof(f98,plain,(
% 35.43/5.01    ( ! [X0,X1] : (r1_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1) | r2_hidden(X0,X1)) )),
% 35.43/5.01    inference(definition_unfolding,[],[f76,f89])).
% 35.43/5.01  
% 35.43/5.01  fof(f11,axiom,(
% 35.43/5.01    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0),
% 35.43/5.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 35.43/5.01  
% 35.43/5.01  fof(f62,plain,(
% 35.43/5.01    ( ! [X0] : (k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0) )),
% 35.43/5.01    inference(cnf_transformation,[],[f11])).
% 35.43/5.01  
% 35.43/5.01  fof(f13,axiom,(
% 35.43/5.01    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 35.43/5.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 35.43/5.01  
% 35.43/5.01  fof(f64,plain,(
% 35.43/5.01    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 35.43/5.01    inference(cnf_transformation,[],[f13])).
% 35.43/5.01  
% 35.43/5.01  fof(f6,axiom,(
% 35.43/5.01    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 35.43/5.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 35.43/5.01  
% 35.43/5.01  fof(f57,plain,(
% 35.43/5.01    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 35.43/5.01    inference(cnf_transformation,[],[f6])).
% 35.43/5.01  
% 35.43/5.01  fof(f94,plain,(
% 35.43/5.01    ( ! [X0,X1] : (r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X0)) )),
% 35.43/5.01    inference(definition_unfolding,[],[f64,f57])).
% 35.43/5.01  
% 35.43/5.01  fof(f14,axiom,(
% 35.43/5.01    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 35.43/5.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 35.43/5.01  
% 35.43/5.01  fof(f65,plain,(
% 35.43/5.01    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 35.43/5.01    inference(cnf_transformation,[],[f14])).
% 35.43/5.01  
% 35.43/5.01  fof(f27,conjecture,(
% 35.43/5.01    ! [X0,X1,X2] : ~(~(k1_xboole_0 = X2 & k1_tarski(X0) = X1) & ~(k1_tarski(X0) = X2 & k1_xboole_0 = X1) & ~(k1_tarski(X0) = X2 & k1_tarski(X0) = X1) & k2_xboole_0(X1,X2) = k1_tarski(X0))),
% 35.43/5.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 35.43/5.01  
% 35.43/5.01  fof(f28,negated_conjecture,(
% 35.43/5.01    ~! [X0,X1,X2] : ~(~(k1_xboole_0 = X2 & k1_tarski(X0) = X1) & ~(k1_tarski(X0) = X2 & k1_xboole_0 = X1) & ~(k1_tarski(X0) = X2 & k1_tarski(X0) = X1) & k2_xboole_0(X1,X2) = k1_tarski(X0))),
% 35.43/5.01    inference(negated_conjecture,[],[f27])).
% 35.43/5.01  
% 35.43/5.01  fof(f41,plain,(
% 35.43/5.01    ? [X0,X1,X2] : ((k1_xboole_0 != X2 | k1_tarski(X0) != X1) & (k1_tarski(X0) != X2 | k1_xboole_0 != X1) & (k1_tarski(X0) != X2 | k1_tarski(X0) != X1) & k2_xboole_0(X1,X2) = k1_tarski(X0))),
% 35.43/5.01    inference(ennf_transformation,[],[f28])).
% 35.43/5.01  
% 35.43/5.01  fof(f48,plain,(
% 35.43/5.01    ? [X0,X1,X2] : ((k1_xboole_0 != X2 | k1_tarski(X0) != X1) & (k1_tarski(X0) != X2 | k1_xboole_0 != X1) & (k1_tarski(X0) != X2 | k1_tarski(X0) != X1) & k2_xboole_0(X1,X2) = k1_tarski(X0)) => ((k1_xboole_0 != sK4 | k1_tarski(sK2) != sK3) & (k1_tarski(sK2) != sK4 | k1_xboole_0 != sK3) & (k1_tarski(sK2) != sK4 | k1_tarski(sK2) != sK3) & k2_xboole_0(sK3,sK4) = k1_tarski(sK2))),
% 35.43/5.01    introduced(choice_axiom,[])).
% 35.43/5.01  
% 35.43/5.01  fof(f49,plain,(
% 35.43/5.01    (k1_xboole_0 != sK4 | k1_tarski(sK2) != sK3) & (k1_tarski(sK2) != sK4 | k1_xboole_0 != sK3) & (k1_tarski(sK2) != sK4 | k1_tarski(sK2) != sK3) & k2_xboole_0(sK3,sK4) = k1_tarski(sK2)),
% 35.43/5.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f41,f48])).
% 35.43/5.01  
% 35.43/5.01  fof(f79,plain,(
% 35.43/5.01    k2_xboole_0(sK3,sK4) = k1_tarski(sK2)),
% 35.43/5.01    inference(cnf_transformation,[],[f49])).
% 35.43/5.01  
% 35.43/5.01  fof(f26,axiom,(
% 35.43/5.01    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 35.43/5.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 35.43/5.01  
% 35.43/5.01  fof(f78,plain,(
% 35.43/5.01    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 35.43/5.01    inference(cnf_transformation,[],[f26])).
% 35.43/5.01  
% 35.43/5.01  fof(f88,plain,(
% 35.43/5.01    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) )),
% 35.43/5.01    inference(definition_unfolding,[],[f78,f87])).
% 35.43/5.01  
% 35.43/5.01  fof(f103,plain,(
% 35.43/5.01    k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) = k3_tarski(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4))),
% 35.43/5.01    inference(definition_unfolding,[],[f79,f88,f89])).
% 35.43/5.01  
% 35.43/5.01  fof(f7,axiom,(
% 35.43/5.01    ! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_tarski(X0,k2_xboole_0(X2,X1)))),
% 35.43/5.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 35.43/5.01  
% 35.43/5.01  fof(f34,plain,(
% 35.43/5.01    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X2,X1)) | ~r1_tarski(X0,X1))),
% 35.43/5.01    inference(ennf_transformation,[],[f7])).
% 35.43/5.01  
% 35.43/5.01  fof(f58,plain,(
% 35.43/5.01    ( ! [X2,X0,X1] : (r1_tarski(X0,k2_xboole_0(X2,X1)) | ~r1_tarski(X0,X1)) )),
% 35.43/5.01    inference(cnf_transformation,[],[f34])).
% 35.43/5.01  
% 35.43/5.01  fof(f92,plain,(
% 35.43/5.01    ( ! [X2,X0,X1] : (r1_tarski(X0,k3_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X1))) | ~r1_tarski(X0,X1)) )),
% 35.43/5.01    inference(definition_unfolding,[],[f58,f88])).
% 35.43/5.01  
% 35.43/5.01  fof(f4,axiom,(
% 35.43/5.01    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 35.43/5.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 35.43/5.01  
% 35.43/5.01  fof(f29,plain,(
% 35.43/5.01    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X3] : ~r2_hidden(X3,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 35.43/5.01    inference(rectify,[],[f4])).
% 35.43/5.01  
% 35.43/5.01  fof(f33,plain,(
% 35.43/5.01    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 35.43/5.01    inference(ennf_transformation,[],[f29])).
% 35.43/5.01  
% 35.43/5.01  fof(f44,plain,(
% 35.43/5.01    ! [X1,X0] : (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) => r2_hidden(sK1(X0,X1),k3_xboole_0(X0,X1)))),
% 35.43/5.01    introduced(choice_axiom,[])).
% 35.43/5.01  
% 35.43/5.01  fof(f45,plain,(
% 35.43/5.01    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (r2_hidden(sK1(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 35.43/5.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f33,f44])).
% 35.43/5.01  
% 35.43/5.01  fof(f54,plain,(
% 35.43/5.01    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,k3_xboole_0(X0,X1))) )),
% 35.43/5.01    inference(cnf_transformation,[],[f45])).
% 35.43/5.01  
% 35.43/5.01  fof(f9,axiom,(
% 35.43/5.01    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 35.43/5.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 35.43/5.01  
% 35.43/5.01  fof(f36,plain,(
% 35.43/5.01    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 35.43/5.01    inference(ennf_transformation,[],[f9])).
% 35.43/5.01  
% 35.43/5.01  fof(f37,plain,(
% 35.43/5.01    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 35.43/5.01    inference(flattening,[],[f36])).
% 35.43/5.01  
% 35.43/5.01  fof(f60,plain,(
% 35.43/5.01    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)) )),
% 35.43/5.01    inference(cnf_transformation,[],[f37])).
% 35.43/5.01  
% 35.43/5.01  fof(f5,axiom,(
% 35.43/5.01    ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,X1) <=> r1_tarski(X0,X1))),
% 35.43/5.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 35.43/5.01  
% 35.43/5.01  fof(f46,plain,(
% 35.43/5.01    ! [X0,X1] : ((k1_xboole_0 = k4_xboole_0(X0,X1) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k1_xboole_0 != k4_xboole_0(X0,X1)))),
% 35.43/5.01    inference(nnf_transformation,[],[f5])).
% 35.43/5.01  
% 35.43/5.01  fof(f56,plain,(
% 35.43/5.01    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,X1) | ~r1_tarski(X0,X1)) )),
% 35.43/5.01    inference(cnf_transformation,[],[f46])).
% 35.43/5.01  
% 35.43/5.01  fof(f90,plain,(
% 35.43/5.01    ( ! [X0,X1] : (k1_xboole_0 = k5_xboole_0(X0,k3_xboole_0(X0,X1)) | ~r1_tarski(X0,X1)) )),
% 35.43/5.01    inference(definition_unfolding,[],[f56,f57])).
% 35.43/5.01  
% 35.43/5.01  fof(f55,plain,(
% 35.43/5.01    ( ! [X0,X1] : (r1_tarski(X0,X1) | k1_xboole_0 != k4_xboole_0(X0,X1)) )),
% 35.43/5.01    inference(cnf_transformation,[],[f46])).
% 35.43/5.01  
% 35.43/5.01  fof(f91,plain,(
% 35.43/5.01    ( ! [X0,X1] : (r1_tarski(X0,X1) | k1_xboole_0 != k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 35.43/5.01    inference(definition_unfolding,[],[f55,f57])).
% 35.43/5.01  
% 35.43/5.01  fof(f15,axiom,(
% 35.43/5.01    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 35.43/5.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 35.43/5.01  
% 35.43/5.01  fof(f66,plain,(
% 35.43/5.01    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 35.43/5.01    inference(cnf_transformation,[],[f15])).
% 35.43/5.01  
% 35.43/5.01  fof(f95,plain,(
% 35.43/5.01    ( ! [X0,X1] : (r1_tarski(X0,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) )),
% 35.43/5.01    inference(definition_unfolding,[],[f66,f88])).
% 35.43/5.01  
% 35.43/5.01  fof(f8,axiom,(
% 35.43/5.01    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 35.43/5.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 35.43/5.01  
% 35.43/5.01  fof(f35,plain,(
% 35.43/5.01    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 35.43/5.01    inference(ennf_transformation,[],[f8])).
% 35.43/5.01  
% 35.43/5.01  fof(f59,plain,(
% 35.43/5.01    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1)) )),
% 35.43/5.01    inference(cnf_transformation,[],[f35])).
% 35.43/5.01  
% 35.43/5.01  fof(f93,plain,(
% 35.43/5.01    ( ! [X0,X1] : (k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = X1 | ~r1_tarski(X0,X1)) )),
% 35.43/5.01    inference(definition_unfolding,[],[f59,f88])).
% 35.43/5.01  
% 35.43/5.01  fof(f23,axiom,(
% 35.43/5.01    ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) <=> r2_hidden(X0,X1))),
% 35.43/5.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 35.43/5.01  
% 35.43/5.01  fof(f47,plain,(
% 35.43/5.01    ! [X0,X1] : ((r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) & (r2_hidden(X0,X1) | ~r1_tarski(k1_tarski(X0),X1)))),
% 35.43/5.01    inference(nnf_transformation,[],[f23])).
% 35.43/5.01  
% 35.43/5.01  fof(f75,plain,(
% 35.43/5.01    ( ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) )),
% 35.43/5.01    inference(cnf_transformation,[],[f47])).
% 35.43/5.01  
% 35.43/5.01  fof(f96,plain,(
% 35.43/5.01    ( ! [X0,X1] : (r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1) | ~r2_hidden(X0,X1)) )),
% 35.43/5.01    inference(definition_unfolding,[],[f75,f89])).
% 35.43/5.01  
% 35.43/5.01  fof(f12,axiom,(
% 35.43/5.01    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 35.43/5.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 35.43/5.01  
% 35.43/5.01  fof(f63,plain,(
% 35.43/5.01    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 35.43/5.01    inference(cnf_transformation,[],[f12])).
% 35.43/5.01  
% 35.43/5.01  fof(f82,plain,(
% 35.43/5.01    k1_xboole_0 != sK4 | k1_tarski(sK2) != sK3),
% 35.43/5.01    inference(cnf_transformation,[],[f49])).
% 35.43/5.01  
% 35.43/5.01  fof(f100,plain,(
% 35.43/5.01    k1_xboole_0 != sK4 | k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) != sK3),
% 35.43/5.01    inference(definition_unfolding,[],[f82,f89])).
% 35.43/5.01  
% 35.43/5.01  fof(f81,plain,(
% 35.43/5.01    k1_tarski(sK2) != sK4 | k1_xboole_0 != sK3),
% 35.43/5.01    inference(cnf_transformation,[],[f49])).
% 35.43/5.01  
% 35.43/5.01  fof(f101,plain,(
% 35.43/5.01    k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) != sK4 | k1_xboole_0 != sK3),
% 35.43/5.01    inference(definition_unfolding,[],[f81,f89])).
% 35.43/5.01  
% 35.43/5.01  fof(f80,plain,(
% 35.43/5.01    k1_tarski(sK2) != sK4 | k1_tarski(sK2) != sK3),
% 35.43/5.01    inference(cnf_transformation,[],[f49])).
% 35.43/5.01  
% 35.43/5.01  fof(f102,plain,(
% 35.43/5.01    k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) != sK4 | k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) != sK3),
% 35.43/5.01    inference(definition_unfolding,[],[f80,f89,f89])).
% 35.43/5.01  
% 35.43/5.01  cnf(c_773,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 35.43/5.01  
% 35.43/5.01  cnf(c_1360,plain,
% 35.43/5.01      ( k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) != X0
% 35.43/5.01      | k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) = sK3
% 35.43/5.01      | sK3 != X0 ),
% 35.43/5.01      inference(instantiation,[status(thm)],[c_773]) ).
% 35.43/5.01  
% 35.43/5.01  cnf(c_4611,plain,
% 35.43/5.01      ( k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) != k3_xboole_0(X0,X1)
% 35.43/5.01      | k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) = sK3
% 35.43/5.01      | sK3 != k3_xboole_0(X0,X1) ),
% 35.43/5.01      inference(instantiation,[status(thm)],[c_1360]) ).
% 35.43/5.01  
% 35.43/5.01  cnf(c_51646,plain,
% 35.43/5.01      ( k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) != k3_xboole_0(k3_tarski(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,X0)),sK3)
% 35.43/5.01      | k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) = sK3
% 35.43/5.01      | sK3 != k3_xboole_0(k3_tarski(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,X0)),sK3) ),
% 35.43/5.01      inference(instantiation,[status(thm)],[c_4611]) ).
% 35.43/5.01  
% 35.43/5.01  cnf(c_114879,plain,
% 35.43/5.01      ( k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) != k3_xboole_0(k3_tarski(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4)),sK3)
% 35.43/5.01      | k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) = sK3
% 35.43/5.01      | sK3 != k3_xboole_0(k3_tarski(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4)),sK3) ),
% 35.43/5.01      inference(instantiation,[status(thm)],[c_51646]) ).
% 35.43/5.01  
% 35.43/5.01  cnf(c_2953,plain,
% 35.43/5.01      ( X0 != X1
% 35.43/5.01      | k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2) != X1
% 35.43/5.01      | k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2) = X0 ),
% 35.43/5.01      inference(instantiation,[status(thm)],[c_773]) ).
% 35.43/5.01  
% 35.43/5.01  cnf(c_10344,plain,
% 35.43/5.01      ( X0 != k3_tarski(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4))
% 35.43/5.01      | k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) = X0
% 35.43/5.01      | k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) != k3_tarski(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4)) ),
% 35.43/5.01      inference(instantiation,[status(thm)],[c_2953]) ).
% 35.43/5.01  
% 35.43/5.01  cnf(c_11303,plain,
% 35.43/5.01      ( k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) = k3_xboole_0(k3_tarski(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4)),X0)
% 35.43/5.01      | k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) != k3_tarski(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4))
% 35.43/5.01      | k3_xboole_0(k3_tarski(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4)),X0) != k3_tarski(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4)) ),
% 35.43/5.01      inference(instantiation,[status(thm)],[c_10344]) ).
% 35.43/5.01  
% 35.43/5.01  cnf(c_114878,plain,
% 35.43/5.01      ( k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) = k3_xboole_0(k3_tarski(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4)),sK3)
% 35.43/5.01      | k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) != k3_tarski(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4))
% 35.43/5.01      | k3_xboole_0(k3_tarski(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4)),sK3) != k3_tarski(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4)) ),
% 35.43/5.01      inference(instantiation,[status(thm)],[c_11303]) ).
% 35.43/5.01  
% 35.43/5.01  cnf(c_778,plain,
% 35.43/5.01      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,X3) | X2 != X0 | X3 != X1 ),
% 35.43/5.01      theory(equality) ).
% 35.43/5.01  
% 35.43/5.01  cnf(c_1836,plain,
% 35.43/5.01      ( r1_tarski(X0,X1)
% 35.43/5.01      | ~ r1_tarski(k5_xboole_0(X2,k3_xboole_0(X2,X3)),X4)
% 35.43/5.01      | X1 != X4
% 35.43/5.01      | X0 != k5_xboole_0(X2,k3_xboole_0(X2,X3)) ),
% 35.43/5.01      inference(instantiation,[status(thm)],[c_778]) ).
% 35.43/5.01  
% 35.43/5.01  cnf(c_2968,plain,
% 35.43/5.01      ( r1_tarski(X0,sK4)
% 35.43/5.01      | ~ r1_tarski(k5_xboole_0(X1,k3_xboole_0(X1,X2)),X3)
% 35.43/5.01      | X0 != k5_xboole_0(X1,k3_xboole_0(X1,X2))
% 35.43/5.01      | sK4 != X3 ),
% 35.43/5.01      inference(instantiation,[status(thm)],[c_1836]) ).
% 35.43/5.01  
% 35.43/5.01  cnf(c_7792,plain,
% 35.43/5.01      ( r1_tarski(X0,sK4)
% 35.43/5.01      | ~ r1_tarski(k5_xboole_0(X1,k3_xboole_0(X1,X2)),sK4)
% 35.43/5.01      | X0 != k5_xboole_0(X1,k3_xboole_0(X1,X2))
% 35.43/5.01      | sK4 != sK4 ),
% 35.43/5.01      inference(instantiation,[status(thm)],[c_2968]) ).
% 35.43/5.01  
% 35.43/5.01  cnf(c_111942,plain,
% 35.43/5.01      ( ~ r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),sK4)
% 35.43/5.01      | r1_tarski(sK3,sK4)
% 35.43/5.01      | sK3 != k5_xboole_0(X0,k3_xboole_0(X0,X1))
% 35.43/5.01      | sK4 != sK4 ),
% 35.43/5.01      inference(instantiation,[status(thm)],[c_7792]) ).
% 35.43/5.01  
% 35.43/5.01  cnf(c_111961,plain,
% 35.43/5.01      ( ~ r1_tarski(k5_xboole_0(sK2,k3_xboole_0(sK2,sK2)),sK4)
% 35.43/5.01      | r1_tarski(sK3,sK4)
% 35.43/5.01      | sK3 != k5_xboole_0(sK2,k3_xboole_0(sK2,sK2))
% 35.43/5.01      | sK4 != sK4 ),
% 35.43/5.01      inference(instantiation,[status(thm)],[c_111942]) ).
% 35.43/5.01  
% 35.43/5.01  cnf(c_1494,plain,
% 35.43/5.01      ( X0 != X1 | sK4 != X1 | sK4 = X0 ),
% 35.43/5.01      inference(instantiation,[status(thm)],[c_773]) ).
% 35.43/5.01  
% 35.43/5.01  cnf(c_1942,plain,
% 35.43/5.01      ( X0 != sK4 | sK4 = X0 | sK4 != sK4 ),
% 35.43/5.01      inference(instantiation,[status(thm)],[c_1494]) ).
% 35.43/5.01  
% 35.43/5.01  cnf(c_101807,plain,
% 35.43/5.01      ( k3_tarski(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4)) != sK4
% 35.43/5.01      | sK4 = k3_tarski(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4))
% 35.43/5.01      | sK4 != sK4 ),
% 35.43/5.01      inference(instantiation,[status(thm)],[c_1942]) ).
% 35.43/5.01  
% 35.43/5.01  cnf(c_101641,plain,
% 35.43/5.01      ( k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) != k3_tarski(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4))
% 35.43/5.01      | k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) = sK4
% 35.43/5.01      | sK4 != k3_tarski(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4)) ),
% 35.43/5.01      inference(instantiation,[status(thm)],[c_10344]) ).
% 35.43/5.01  
% 35.43/5.01  cnf(c_1476,plain,
% 35.43/5.01      ( X0 != X1 | sK3 != X1 | sK3 = X0 ),
% 35.43/5.01      inference(instantiation,[status(thm)],[c_773]) ).
% 35.43/5.01  
% 35.43/5.01  cnf(c_1495,plain,
% 35.43/5.01      ( X0 != sK3 | sK3 = X0 | sK3 != sK3 ),
% 35.43/5.01      inference(instantiation,[status(thm)],[c_1476]) ).
% 35.43/5.01  
% 35.43/5.01  cnf(c_1954,plain,
% 35.43/5.01      ( k3_xboole_0(sK3,k3_tarski(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,X0))) != sK3
% 35.43/5.01      | sK3 = k3_xboole_0(sK3,k3_tarski(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,X0)))
% 35.43/5.01      | sK3 != sK3 ),
% 35.43/5.01      inference(instantiation,[status(thm)],[c_1495]) ).
% 35.43/5.01  
% 35.43/5.01  cnf(c_98322,plain,
% 35.43/5.01      ( k3_xboole_0(sK3,k3_tarski(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4))) != sK3
% 35.43/5.01      | sK3 = k3_xboole_0(sK3,k3_tarski(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4)))
% 35.43/5.01      | sK3 != sK3 ),
% 35.43/5.01      inference(instantiation,[status(thm)],[c_1954]) ).
% 35.43/5.01  
% 35.43/5.01  cnf(c_10,plain,
% 35.43/5.01      ( ~ r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0 ),
% 35.43/5.01      inference(cnf_transformation,[],[f61]) ).
% 35.43/5.01  
% 35.43/5.01  cnf(c_11304,plain,
% 35.43/5.01      ( ~ r1_tarski(k3_tarski(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4)),X0)
% 35.43/5.01      | k3_xboole_0(k3_tarski(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4)),X0) = k3_tarski(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4)) ),
% 35.43/5.01      inference(instantiation,[status(thm)],[c_10]) ).
% 35.43/5.01  
% 35.43/5.01  cnf(c_71846,plain,
% 35.43/5.01      ( ~ r1_tarski(k3_tarski(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4)),sK3)
% 35.43/5.01      | k3_xboole_0(k3_tarski(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4)),sK3) = k3_tarski(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4)) ),
% 35.43/5.01      inference(instantiation,[status(thm)],[c_11304]) ).
% 35.43/5.01  
% 35.43/5.01  cnf(c_71852,plain,
% 35.43/5.01      ( k3_xboole_0(k3_tarski(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4)),sK3) = k3_tarski(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4))
% 35.43/5.01      | r1_tarski(k3_tarski(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4)),sK3) != iProver_top ),
% 35.43/5.01      inference(predicate_to_equality,[status(thm)],[c_71846]) ).
% 35.43/5.01  
% 35.43/5.01  cnf(c_4121,plain,
% 35.43/5.01      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,sK3) | X2 != X0 | sK3 != X1 ),
% 35.43/5.01      inference(instantiation,[status(thm)],[c_778]) ).
% 35.43/5.01  
% 35.43/5.01  cnf(c_9387,plain,
% 35.43/5.01      ( ~ r1_tarski(X0,sK3) | r1_tarski(X1,sK3) | X1 != X0 | sK3 != sK3 ),
% 35.43/5.01      inference(instantiation,[status(thm)],[c_4121]) ).
% 35.43/5.01  
% 35.43/5.01  cnf(c_21640,plain,
% 35.43/5.01      ( r1_tarski(X0,sK3)
% 35.43/5.01      | ~ r1_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),sK3)
% 35.43/5.01      | X0 != k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)
% 35.43/5.01      | sK3 != sK3 ),
% 35.43/5.01      inference(instantiation,[status(thm)],[c_9387]) ).
% 35.43/5.01  
% 35.43/5.01  cnf(c_65069,plain,
% 35.43/5.01      ( ~ r1_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3)
% 35.43/5.01      | r1_tarski(k3_tarski(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4)),sK3)
% 35.43/5.01      | k3_tarski(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4)) != k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)
% 35.43/5.01      | sK3 != sK3 ),
% 35.43/5.01      inference(instantiation,[status(thm)],[c_21640]) ).
% 35.43/5.01  
% 35.43/5.01  cnf(c_65070,plain,
% 35.43/5.01      ( k3_tarski(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4)) != k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)
% 35.43/5.01      | sK3 != sK3
% 35.43/5.01      | r1_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3) != iProver_top
% 35.43/5.01      | r1_tarski(k3_tarski(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4)),sK3) = iProver_top ),
% 35.43/5.01      inference(predicate_to_equality,[status(thm)],[c_65069]) ).
% 35.43/5.01  
% 35.43/5.01  cnf(c_8354,plain,
% 35.43/5.01      ( X0 != k3_xboole_0(sK3,k3_tarski(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,X1)))
% 35.43/5.01      | sK3 = X0
% 35.43/5.01      | sK3 != k3_xboole_0(sK3,k3_tarski(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,X1))) ),
% 35.43/5.01      inference(instantiation,[status(thm)],[c_1476]) ).
% 35.43/5.01  
% 35.43/5.01  cnf(c_15408,plain,
% 35.43/5.01      ( k3_xboole_0(k3_tarski(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,X0)),sK3) != k3_xboole_0(sK3,k3_tarski(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,X0)))
% 35.43/5.01      | sK3 = k3_xboole_0(k3_tarski(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,X0)),sK3)
% 35.43/5.01      | sK3 != k3_xboole_0(sK3,k3_tarski(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,X0))) ),
% 35.43/5.01      inference(instantiation,[status(thm)],[c_8354]) ).
% 35.43/5.01  
% 35.43/5.01  cnf(c_51638,plain,
% 35.43/5.01      ( k3_xboole_0(k3_tarski(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4)),sK3) != k3_xboole_0(sK3,k3_tarski(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4)))
% 35.43/5.01      | sK3 = k3_xboole_0(k3_tarski(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4)),sK3)
% 35.43/5.01      | sK3 != k3_xboole_0(sK3,k3_tarski(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4))) ),
% 35.43/5.01      inference(instantiation,[status(thm)],[c_15408]) ).
% 35.43/5.01  
% 35.43/5.01  cnf(c_0,plain,
% 35.43/5.01      ( k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
% 35.43/5.01      inference(cnf_transformation,[],[f50]) ).
% 35.43/5.01  
% 35.43/5.01  cnf(c_15409,plain,
% 35.43/5.01      ( k3_xboole_0(k3_tarski(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,X0)),sK3) = k3_xboole_0(sK3,k3_tarski(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,X0))) ),
% 35.43/5.01      inference(instantiation,[status(thm)],[c_0]) ).
% 35.43/5.01  
% 35.43/5.01  cnf(c_46767,plain,
% 35.43/5.01      ( k3_xboole_0(k3_tarski(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4)),sK3) = k3_xboole_0(sK3,k3_tarski(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4))) ),
% 35.43/5.01      inference(instantiation,[status(thm)],[c_15409]) ).
% 35.43/5.01  
% 35.43/5.01  cnf(c_1,plain,
% 35.43/5.01      ( r2_hidden(sK0(X0),X0) | v1_xboole_0(X0) ),
% 35.43/5.01      inference(cnf_transformation,[],[f51]) ).
% 35.43/5.01  
% 35.43/5.01  cnf(c_2,plain,
% 35.43/5.01      ( ~ v1_xboole_0(X0) | k1_xboole_0 = X0 ),
% 35.43/5.01      inference(cnf_transformation,[],[f52]) ).
% 35.43/5.01  
% 35.43/5.01  cnf(c_262,plain,
% 35.43/5.01      ( r2_hidden(sK0(X0),X0) | k1_xboole_0 = X0 ),
% 35.43/5.01      inference(resolution,[status(thm)],[c_1,c_2]) ).
% 35.43/5.01  
% 35.43/5.01  cnf(c_1205,plain,
% 35.43/5.01      ( k1_xboole_0 = X0 | r2_hidden(sK0(X0),X0) = iProver_top ),
% 35.43/5.01      inference(predicate_to_equality,[status(thm)],[c_262]) ).
% 35.43/5.01  
% 35.43/5.01  cnf(c_18,plain,
% 35.43/5.01      ( r1_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1)
% 35.43/5.01      | r2_hidden(X0,X1) ),
% 35.43/5.01      inference(cnf_transformation,[],[f98]) ).
% 35.43/5.01  
% 35.43/5.01  cnf(c_1207,plain,
% 35.43/5.01      ( r1_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1) = iProver_top
% 35.43/5.01      | r2_hidden(X0,X1) = iProver_top ),
% 35.43/5.01      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 35.43/5.01  
% 35.43/5.01  cnf(c_11,plain,
% 35.43/5.01      ( k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
% 35.43/5.01      inference(cnf_transformation,[],[f62]) ).
% 35.43/5.01  
% 35.43/5.01  cnf(c_13,plain,
% 35.43/5.01      ( r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X0) ),
% 35.43/5.01      inference(cnf_transformation,[],[f94]) ).
% 35.43/5.01  
% 35.43/5.01  cnf(c_1211,plain,
% 35.43/5.01      ( r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X0) = iProver_top ),
% 35.43/5.01      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 35.43/5.01  
% 35.43/5.01  cnf(c_1625,plain,
% 35.43/5.01      ( r1_tarski(k5_xboole_0(X0,k1_xboole_0),X0) = iProver_top ),
% 35.43/5.01      inference(superposition,[status(thm)],[c_11,c_1211]) ).
% 35.43/5.01  
% 35.43/5.01  cnf(c_14,plain,
% 35.43/5.01      ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
% 35.43/5.01      inference(cnf_transformation,[],[f65]) ).
% 35.43/5.01  
% 35.43/5.01  cnf(c_1630,plain,
% 35.43/5.01      ( r1_tarski(X0,X0) = iProver_top ),
% 35.43/5.01      inference(light_normalisation,[status(thm)],[c_1625,c_14]) ).
% 35.43/5.01  
% 35.43/5.01  cnf(c_23,negated_conjecture,
% 35.43/5.01      ( k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) = k3_tarski(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4)) ),
% 35.43/5.01      inference(cnf_transformation,[],[f103]) ).
% 35.43/5.01  
% 35.43/5.01  cnf(c_7,plain,
% 35.43/5.01      ( ~ r1_tarski(X0,X1)
% 35.43/5.01      | r1_tarski(X0,k3_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X1))) ),
% 35.43/5.01      inference(cnf_transformation,[],[f92]) ).
% 35.43/5.01  
% 35.43/5.01  cnf(c_1216,plain,
% 35.43/5.01      ( r1_tarski(X0,X1) != iProver_top
% 35.43/5.01      | r1_tarski(X0,k3_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X1))) = iProver_top ),
% 35.43/5.01      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 35.43/5.01  
% 35.43/5.01  cnf(c_8867,plain,
% 35.43/5.01      ( r1_tarski(X0,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)) = iProver_top
% 35.43/5.01      | r1_tarski(X0,sK4) != iProver_top ),
% 35.43/5.01      inference(superposition,[status(thm)],[c_23,c_1216]) ).
% 35.43/5.01  
% 35.43/5.01  cnf(c_1213,plain,
% 35.43/5.01      ( k3_xboole_0(X0,X1) = X0 | r1_tarski(X0,X1) != iProver_top ),
% 35.43/5.01      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 35.43/5.01  
% 35.43/5.01  cnf(c_9063,plain,
% 35.43/5.01      ( k3_xboole_0(X0,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)) = X0
% 35.43/5.01      | r1_tarski(X0,sK4) != iProver_top ),
% 35.43/5.01      inference(superposition,[status(thm)],[c_8867,c_1213]) ).
% 35.43/5.01  
% 35.43/5.01  cnf(c_9410,plain,
% 35.43/5.01      ( k3_xboole_0(sK4,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)) = sK4 ),
% 35.43/5.01      inference(superposition,[status(thm)],[c_1630,c_9063]) ).
% 35.43/5.01  
% 35.43/5.01  cnf(c_3,plain,
% 35.43/5.01      ( ~ r1_xboole_0(X0,X1) | ~ r2_hidden(X2,k3_xboole_0(X0,X1)) ),
% 35.43/5.01      inference(cnf_transformation,[],[f54]) ).
% 35.43/5.01  
% 35.43/5.01  cnf(c_1220,plain,
% 35.43/5.01      ( r1_xboole_0(X0,X1) != iProver_top
% 35.43/5.01      | r2_hidden(X2,k3_xboole_0(X0,X1)) != iProver_top ),
% 35.43/5.01      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 35.43/5.01  
% 35.43/5.01  cnf(c_7057,plain,
% 35.43/5.01      ( r1_xboole_0(X0,X1) != iProver_top
% 35.43/5.01      | r2_hidden(X2,k3_xboole_0(X1,X0)) != iProver_top ),
% 35.43/5.01      inference(superposition,[status(thm)],[c_0,c_1220]) ).
% 35.43/5.01  
% 35.43/5.01  cnf(c_11407,plain,
% 35.43/5.01      ( r1_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK4) != iProver_top
% 35.43/5.01      | r2_hidden(X0,sK4) != iProver_top ),
% 35.43/5.01      inference(superposition,[status(thm)],[c_9410,c_7057]) ).
% 35.43/5.01  
% 35.43/5.01  cnf(c_23323,plain,
% 35.43/5.01      ( r2_hidden(X0,sK4) != iProver_top
% 35.43/5.01      | r2_hidden(sK2,sK4) = iProver_top ),
% 35.43/5.01      inference(superposition,[status(thm)],[c_1207,c_11407]) ).
% 35.43/5.01  
% 35.43/5.01  cnf(c_24455,plain,
% 35.43/5.01      ( sK4 = k1_xboole_0 | r2_hidden(sK2,sK4) = iProver_top ),
% 35.43/5.01      inference(superposition,[status(thm)],[c_1205,c_23323]) ).
% 35.43/5.01  
% 35.43/5.01  cnf(c_24456,plain,
% 35.43/5.01      ( r2_hidden(sK2,sK4) | sK4 = k1_xboole_0 ),
% 35.43/5.01      inference(predicate_to_equality_rev,[status(thm)],[c_24455]) ).
% 35.43/5.01  
% 35.43/5.01  cnf(c_3221,plain,
% 35.43/5.01      ( X0 != X1
% 35.43/5.01      | k3_tarski(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4)) != X1
% 35.43/5.01      | k3_tarski(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4)) = X0 ),
% 35.43/5.01      inference(instantiation,[status(thm)],[c_773]) ).
% 35.43/5.01  
% 35.43/5.01  cnf(c_7042,plain,
% 35.43/5.01      ( X0 != k3_tarski(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4))
% 35.43/5.01      | k3_tarski(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4)) = X0
% 35.43/5.01      | k3_tarski(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4)) != k3_tarski(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4)) ),
% 35.43/5.01      inference(instantiation,[status(thm)],[c_3221]) ).
% 35.43/5.01  
% 35.43/5.01  cnf(c_20458,plain,
% 35.43/5.01      ( k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) != k3_tarski(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4))
% 35.43/5.01      | k3_tarski(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4)) = k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)
% 35.43/5.01      | k3_tarski(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4)) != k3_tarski(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4)) ),
% 35.43/5.01      inference(instantiation,[status(thm)],[c_7042]) ).
% 35.43/5.01  
% 35.43/5.01  cnf(c_9,plain,
% 35.43/5.01      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X2) | r1_tarski(X0,X2) ),
% 35.43/5.01      inference(cnf_transformation,[],[f60]) ).
% 35.43/5.01  
% 35.43/5.01  cnf(c_2984,plain,
% 35.43/5.01      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,sK4) | r1_tarski(X0,sK4) ),
% 35.43/5.01      inference(instantiation,[status(thm)],[c_9]) ).
% 35.43/5.01  
% 35.43/5.01  cnf(c_6939,plain,
% 35.43/5.01      ( r1_tarski(X0,sK4)
% 35.43/5.01      | ~ r1_tarski(X0,k1_xboole_0)
% 35.43/5.01      | ~ r1_tarski(k1_xboole_0,sK4) ),
% 35.43/5.01      inference(instantiation,[status(thm)],[c_2984]) ).
% 35.43/5.01  
% 35.43/5.01  cnf(c_20344,plain,
% 35.43/5.01      ( r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),sK4)
% 35.43/5.01      | ~ r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),k1_xboole_0)
% 35.43/5.01      | ~ r1_tarski(k1_xboole_0,sK4) ),
% 35.43/5.01      inference(instantiation,[status(thm)],[c_6939]) ).
% 35.43/5.01  
% 35.43/5.01  cnf(c_20347,plain,
% 35.43/5.01      ( r1_tarski(k5_xboole_0(sK2,k3_xboole_0(sK2,sK2)),sK4)
% 35.43/5.01      | ~ r1_tarski(k5_xboole_0(sK2,k3_xboole_0(sK2,sK2)),k1_xboole_0)
% 35.43/5.01      | ~ r1_tarski(k1_xboole_0,sK4) ),
% 35.43/5.01      inference(instantiation,[status(thm)],[c_20344]) ).
% 35.43/5.01  
% 35.43/5.01  cnf(c_5,plain,
% 35.43/5.01      ( ~ r1_tarski(X0,X1)
% 35.43/5.01      | k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k1_xboole_0 ),
% 35.43/5.01      inference(cnf_transformation,[],[f90]) ).
% 35.43/5.01  
% 35.43/5.01  cnf(c_1218,plain,
% 35.43/5.01      ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k1_xboole_0
% 35.43/5.01      | r1_tarski(X0,X1) != iProver_top ),
% 35.43/5.01      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 35.43/5.01  
% 35.43/5.01  cnf(c_5891,plain,
% 35.43/5.01      ( k5_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),k3_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X0)) = k1_xboole_0 ),
% 35.43/5.01      inference(superposition,[status(thm)],[c_1211,c_1218]) ).
% 35.43/5.01  
% 35.43/5.01  cnf(c_1623,plain,
% 35.43/5.01      ( r1_tarski(k5_xboole_0(X0,k3_xboole_0(X1,X0)),X0) = iProver_top ),
% 35.43/5.01      inference(superposition,[status(thm)],[c_0,c_1211]) ).
% 35.43/5.01  
% 35.43/5.01  cnf(c_1824,plain,
% 35.43/5.01      ( k3_xboole_0(k5_xboole_0(X0,k3_xboole_0(X1,X0)),X0) = k5_xboole_0(X0,k3_xboole_0(X1,X0)) ),
% 35.43/5.01      inference(superposition,[status(thm)],[c_1623,c_1213]) ).
% 35.43/5.01  
% 35.43/5.01  cnf(c_3145,plain,
% 35.43/5.01      ( k3_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X0) = k5_xboole_0(X0,k3_xboole_0(X1,X0)) ),
% 35.43/5.01      inference(superposition,[status(thm)],[c_0,c_1824]) ).
% 35.43/5.01  
% 35.43/5.01  cnf(c_5946,plain,
% 35.43/5.01      ( k5_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),k5_xboole_0(X0,k3_xboole_0(X1,X0))) = k1_xboole_0 ),
% 35.43/5.01      inference(light_normalisation,[status(thm)],[c_5891,c_3145]) ).
% 35.43/5.01  
% 35.43/5.01  cnf(c_17207,plain,
% 35.43/5.01      ( k5_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),k5_xboole_0(X0,k3_xboole_0(X0,X1))) = k1_xboole_0 ),
% 35.43/5.01      inference(superposition,[status(thm)],[c_0,c_5946]) ).
% 35.43/5.01  
% 35.43/5.01  cnf(c_1825,plain,
% 35.43/5.01      ( k3_xboole_0(X0,X0) = X0 ),
% 35.43/5.01      inference(superposition,[status(thm)],[c_1630,c_1213]) ).
% 35.43/5.01  
% 35.43/5.01  cnf(c_2014,plain,
% 35.43/5.01      ( r1_tarski(k5_xboole_0(X0,X0),X0) = iProver_top ),
% 35.43/5.01      inference(superposition,[status(thm)],[c_1825,c_1211]) ).
% 35.43/5.01  
% 35.43/5.01  cnf(c_2022,plain,
% 35.43/5.01      ( k3_xboole_0(k5_xboole_0(X0,X0),X0) = k5_xboole_0(X0,X0) ),
% 35.43/5.01      inference(superposition,[status(thm)],[c_2014,c_1213]) ).
% 35.43/5.01  
% 35.43/5.01  cnf(c_2097,plain,
% 35.43/5.01      ( k3_xboole_0(X0,k5_xboole_0(X0,X0)) = k5_xboole_0(X0,X0) ),
% 35.43/5.01      inference(superposition,[status(thm)],[c_2022,c_0]) ).
% 35.43/5.01  
% 35.43/5.01  cnf(c_6,plain,
% 35.43/5.01      ( r1_tarski(X0,X1)
% 35.43/5.01      | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != k1_xboole_0 ),
% 35.43/5.01      inference(cnf_transformation,[],[f91]) ).
% 35.43/5.01  
% 35.43/5.01  cnf(c_1217,plain,
% 35.43/5.01      ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) != k1_xboole_0
% 35.43/5.01      | r1_tarski(X0,X1) = iProver_top ),
% 35.43/5.01      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 35.43/5.01  
% 35.43/5.01  cnf(c_5789,plain,
% 35.43/5.01      ( k5_xboole_0(X0,k5_xboole_0(X0,X0)) != k1_xboole_0
% 35.43/5.01      | r1_tarski(X0,k5_xboole_0(X0,X0)) = iProver_top ),
% 35.43/5.01      inference(superposition,[status(thm)],[c_2097,c_1217]) ).
% 35.43/5.01  
% 35.43/5.01  cnf(c_19561,plain,
% 35.43/5.01      ( k5_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),k1_xboole_0) != k1_xboole_0
% 35.43/5.01      | r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),k5_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),k5_xboole_0(X0,k3_xboole_0(X0,X1)))) = iProver_top ),
% 35.43/5.01      inference(superposition,[status(thm)],[c_17207,c_5789]) ).
% 35.43/5.01  
% 35.43/5.01  cnf(c_19613,plain,
% 35.43/5.01      ( k5_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),k1_xboole_0) != k1_xboole_0
% 35.43/5.01      | r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),k1_xboole_0) = iProver_top ),
% 35.43/5.01      inference(light_normalisation,[status(thm)],[c_19561,c_17207]) ).
% 35.43/5.01  
% 35.43/5.01  cnf(c_19614,plain,
% 35.43/5.01      ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) != k1_xboole_0
% 35.43/5.01      | r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),k1_xboole_0) = iProver_top ),
% 35.43/5.01      inference(demodulation,[status(thm)],[c_19613,c_14]) ).
% 35.43/5.01  
% 35.43/5.01  cnf(c_19631,plain,
% 35.43/5.01      ( r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),k1_xboole_0)
% 35.43/5.01      | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != k1_xboole_0 ),
% 35.43/5.01      inference(predicate_to_equality_rev,[status(thm)],[c_19614]) ).
% 35.43/5.01  
% 35.43/5.01  cnf(c_19633,plain,
% 35.43/5.01      ( r1_tarski(k5_xboole_0(sK2,k3_xboole_0(sK2,sK2)),k1_xboole_0)
% 35.43/5.01      | k5_xboole_0(sK2,k3_xboole_0(sK2,sK2)) != k1_xboole_0 ),
% 35.43/5.01      inference(instantiation,[status(thm)],[c_19631]) ).
% 35.43/5.01  
% 35.43/5.01  cnf(c_15,plain,
% 35.43/5.01      ( r1_tarski(X0,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) ),
% 35.43/5.01      inference(cnf_transformation,[],[f95]) ).
% 35.43/5.01  
% 35.43/5.01  cnf(c_1210,plain,
% 35.43/5.01      ( r1_tarski(X0,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) = iProver_top ),
% 35.43/5.01      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 35.43/5.01  
% 35.43/5.01  cnf(c_4347,plain,
% 35.43/5.01      ( r1_tarski(sK3,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)) = iProver_top ),
% 35.43/5.01      inference(superposition,[status(thm)],[c_23,c_1210]) ).
% 35.43/5.01  
% 35.43/5.01  cnf(c_4550,plain,
% 35.43/5.01      ( k3_xboole_0(sK3,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)) = sK3 ),
% 35.43/5.01      inference(superposition,[status(thm)],[c_4347,c_1213]) ).
% 35.43/5.01  
% 35.43/5.01  cnf(c_8496,plain,
% 35.43/5.01      ( r1_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3) != iProver_top
% 35.43/5.01      | r2_hidden(X0,sK3) != iProver_top ),
% 35.43/5.01      inference(superposition,[status(thm)],[c_4550,c_7057]) ).
% 35.43/5.01  
% 35.43/5.01  cnf(c_11837,plain,
% 35.43/5.01      ( r2_hidden(X0,sK3) != iProver_top
% 35.43/5.01      | r2_hidden(sK2,sK3) = iProver_top ),
% 35.43/5.01      inference(superposition,[status(thm)],[c_1207,c_8496]) ).
% 35.43/5.01  
% 35.43/5.01  cnf(c_16079,plain,
% 35.43/5.01      ( sK3 = k1_xboole_0 | r2_hidden(sK2,sK3) = iProver_top ),
% 35.43/5.01      inference(superposition,[status(thm)],[c_1205,c_11837]) ).
% 35.43/5.01  
% 35.43/5.01  cnf(c_1585,plain,
% 35.43/5.01      ( X0 != X1
% 35.43/5.01      | X0 = k5_xboole_0(X2,k3_xboole_0(X2,X3))
% 35.43/5.01      | k5_xboole_0(X2,k3_xboole_0(X2,X3)) != X1 ),
% 35.43/5.01      inference(instantiation,[status(thm)],[c_773]) ).
% 35.43/5.01  
% 35.43/5.01  cnf(c_7985,plain,
% 35.43/5.01      ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X2
% 35.43/5.01      | sK3 != X2
% 35.43/5.01      | sK3 = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
% 35.43/5.01      inference(instantiation,[status(thm)],[c_1585]) ).
% 35.43/5.01  
% 35.43/5.01  cnf(c_12289,plain,
% 35.43/5.01      ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) != k1_xboole_0
% 35.43/5.01      | sK3 = k5_xboole_0(X0,k3_xboole_0(X0,X1))
% 35.43/5.01      | sK3 != k1_xboole_0 ),
% 35.43/5.01      inference(instantiation,[status(thm)],[c_7985]) ).
% 35.43/5.01  
% 35.43/5.01  cnf(c_12290,plain,
% 35.43/5.01      ( k5_xboole_0(sK2,k3_xboole_0(sK2,sK2)) != k1_xboole_0
% 35.43/5.01      | sK3 = k5_xboole_0(sK2,k3_xboole_0(sK2,sK2))
% 35.43/5.01      | sK3 != k1_xboole_0 ),
% 35.43/5.01      inference(instantiation,[status(thm)],[c_12289]) ).
% 35.43/5.01  
% 35.43/5.01  cnf(c_8,plain,
% 35.43/5.01      ( ~ r1_tarski(X0,X1)
% 35.43/5.01      | k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = X1 ),
% 35.43/5.01      inference(cnf_transformation,[],[f93]) ).
% 35.43/5.01  
% 35.43/5.01  cnf(c_3109,plain,
% 35.43/5.01      ( ~ r1_tarski(X0,sK4)
% 35.43/5.01      | k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,sK4)) = sK4 ),
% 35.43/5.01      inference(instantiation,[status(thm)],[c_8]) ).
% 35.43/5.01  
% 35.43/5.01  cnf(c_11767,plain,
% 35.43/5.01      ( ~ r1_tarski(sK3,sK4)
% 35.43/5.01      | k3_tarski(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4)) = sK4 ),
% 35.43/5.01      inference(instantiation,[status(thm)],[c_3109]) ).
% 35.43/5.01  
% 35.43/5.01  cnf(c_4032,plain,
% 35.43/5.01      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(sK3,X0) | r1_tarski(sK3,X1) ),
% 35.43/5.01      inference(instantiation,[status(thm)],[c_9]) ).
% 35.43/5.01  
% 35.43/5.01  cnf(c_9137,plain,
% 35.43/5.01      ( ~ r1_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),X0)
% 35.43/5.01      | r1_tarski(sK3,X0)
% 35.43/5.01      | ~ r1_tarski(sK3,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)) ),
% 35.43/5.01      inference(instantiation,[status(thm)],[c_4032]) ).
% 35.43/5.01  
% 35.43/5.01  cnf(c_11766,plain,
% 35.43/5.01      ( ~ r1_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK4)
% 35.43/5.01      | ~ r1_tarski(sK3,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))
% 35.43/5.01      | r1_tarski(sK3,sK4) ),
% 35.43/5.01      inference(instantiation,[status(thm)],[c_9137]) ).
% 35.43/5.01  
% 35.43/5.01  cnf(c_16,plain,
% 35.43/5.01      ( r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1)
% 35.43/5.01      | ~ r2_hidden(X0,X1) ),
% 35.43/5.01      inference(cnf_transformation,[],[f96]) ).
% 35.43/5.01  
% 35.43/5.01  cnf(c_11368,plain,
% 35.43/5.01      ( r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),sK3)
% 35.43/5.01      | ~ r2_hidden(X0,sK3) ),
% 35.43/5.01      inference(instantiation,[status(thm)],[c_16]) ).
% 35.43/5.01  
% 35.43/5.01  cnf(c_11371,plain,
% 35.43/5.01      ( r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),sK3) = iProver_top
% 35.43/5.01      | r2_hidden(X0,sK3) != iProver_top ),
% 35.43/5.01      inference(predicate_to_equality,[status(thm)],[c_11368]) ).
% 35.43/5.01  
% 35.43/5.01  cnf(c_11373,plain,
% 35.43/5.01      ( r1_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3) = iProver_top
% 35.43/5.01      | r2_hidden(sK2,sK3) != iProver_top ),
% 35.43/5.01      inference(instantiation,[status(thm)],[c_11371]) ).
% 35.43/5.01  
% 35.43/5.01  cnf(c_11338,plain,
% 35.43/5.01      ( r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),sK4)
% 35.43/5.01      | ~ r2_hidden(X0,sK4) ),
% 35.43/5.01      inference(instantiation,[status(thm)],[c_16]) ).
% 35.43/5.01  
% 35.43/5.01  cnf(c_11343,plain,
% 35.43/5.01      ( r1_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK4)
% 35.43/5.01      | ~ r2_hidden(sK2,sK4) ),
% 35.43/5.01      inference(instantiation,[status(thm)],[c_11338]) ).
% 35.43/5.01  
% 35.43/5.01  cnf(c_12,plain,
% 35.43/5.01      ( r1_tarski(k1_xboole_0,X0) ),
% 35.43/5.01      inference(cnf_transformation,[],[f63]) ).
% 35.43/5.01  
% 35.43/5.01  cnf(c_6940,plain,
% 35.43/5.01      ( r1_tarski(k1_xboole_0,sK4) ),
% 35.43/5.01      inference(instantiation,[status(thm)],[c_12]) ).
% 35.43/5.01  
% 35.43/5.01  cnf(c_1358,plain,
% 35.43/5.01      ( sK4 != X0 | k1_xboole_0 != X0 | k1_xboole_0 = sK4 ),
% 35.43/5.01      inference(instantiation,[status(thm)],[c_773]) ).
% 35.43/5.01  
% 35.43/5.01  cnf(c_6613,plain,
% 35.43/5.01      ( sK4 != k1_xboole_0
% 35.43/5.01      | k1_xboole_0 = sK4
% 35.43/5.01      | k1_xboole_0 != k1_xboole_0 ),
% 35.43/5.01      inference(instantiation,[status(thm)],[c_1358]) ).
% 35.43/5.01  
% 35.43/5.01  cnf(c_1362,plain,
% 35.43/5.01      ( sK3 != X0 | k1_xboole_0 != X0 | k1_xboole_0 = sK3 ),
% 35.43/5.01      inference(instantiation,[status(thm)],[c_773]) ).
% 35.43/5.01  
% 35.43/5.01  cnf(c_5424,plain,
% 35.43/5.01      ( sK3 != k1_xboole_0
% 35.43/5.01      | k1_xboole_0 = sK3
% 35.43/5.01      | k1_xboole_0 != k1_xboole_0 ),
% 35.43/5.01      inference(instantiation,[status(thm)],[c_1362]) ).
% 35.43/5.01  
% 35.43/5.01  cnf(c_1373,plain,
% 35.43/5.01      ( ~ r1_tarski(X0,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))
% 35.43/5.01      | k3_xboole_0(X0,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) = X0 ),
% 35.43/5.01      inference(instantiation,[status(thm)],[c_10]) ).
% 35.43/5.01  
% 35.43/5.01  cnf(c_1955,plain,
% 35.43/5.01      ( ~ r1_tarski(sK3,k3_tarski(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,X0)))
% 35.43/5.01      | k3_xboole_0(sK3,k3_tarski(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,X0))) = sK3 ),
% 35.43/5.01      inference(instantiation,[status(thm)],[c_1373]) ).
% 35.43/5.01  
% 35.43/5.01  cnf(c_4010,plain,
% 35.43/5.01      ( ~ r1_tarski(sK3,k3_tarski(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4)))
% 35.43/5.01      | k3_xboole_0(sK3,k3_tarski(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4))) = sK3 ),
% 35.43/5.01      inference(instantiation,[status(thm)],[c_1955]) ).
% 35.43/5.01  
% 35.43/5.01  cnf(c_772,plain,( X0 = X0 ),theory(equality) ).
% 35.43/5.01  
% 35.43/5.01  cnf(c_1698,plain,
% 35.43/5.01      ( k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ),
% 35.43/5.01      inference(instantiation,[status(thm)],[c_772]) ).
% 35.43/5.01  
% 35.43/5.01  cnf(c_3349,plain,
% 35.43/5.01      ( k3_tarski(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4)) = k3_tarski(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4)) ),
% 35.43/5.01      inference(instantiation,[status(thm)],[c_1698]) ).
% 35.43/5.01  
% 35.43/5.01  cnf(c_3084,plain,
% 35.43/5.01      ( k1_xboole_0 = k1_xboole_0 ),
% 35.43/5.01      inference(instantiation,[status(thm)],[c_772]) ).
% 35.43/5.01  
% 35.43/5.01  cnf(c_1372,plain,
% 35.43/5.01      ( r1_tarski(X0,X1)
% 35.43/5.01      | ~ r1_tarski(X2,k3_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X3)))
% 35.43/5.01      | X0 != X2
% 35.43/5.01      | X1 != k3_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X3)) ),
% 35.43/5.01      inference(instantiation,[status(thm)],[c_778]) ).
% 35.43/5.01  
% 35.43/5.01  cnf(c_1692,plain,
% 35.43/5.01      ( r1_tarski(X0,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))
% 35.43/5.01      | ~ r1_tarski(sK3,k3_tarski(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4)))
% 35.43/5.01      | X0 != sK3
% 35.43/5.01      | k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) != k3_tarski(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4)) ),
% 35.43/5.01      inference(instantiation,[status(thm)],[c_1372]) ).
% 35.43/5.01  
% 35.43/5.01  cnf(c_2838,plain,
% 35.43/5.01      ( r1_tarski(sK3,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))
% 35.43/5.01      | ~ r1_tarski(sK3,k3_tarski(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4)))
% 35.43/5.01      | k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) != k3_tarski(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4))
% 35.43/5.01      | sK3 != sK3 ),
% 35.43/5.01      inference(instantiation,[status(thm)],[c_1692]) ).
% 35.43/5.01  
% 35.43/5.01  cnf(c_1943,plain,
% 35.43/5.01      ( sK4 = sK4 ),
% 35.43/5.01      inference(instantiation,[status(thm)],[c_772]) ).
% 35.43/5.01  
% 35.43/5.01  cnf(c_1904,plain,
% 35.43/5.01      ( r1_tarski(sK3,k3_tarski(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4))) ),
% 35.43/5.01      inference(instantiation,[status(thm)],[c_15]) ).
% 35.43/5.01  
% 35.43/5.01  cnf(c_1636,plain,
% 35.43/5.01      ( r1_tarski(sK2,sK2) = iProver_top ),
% 35.43/5.01      inference(instantiation,[status(thm)],[c_1630]) ).
% 35.43/5.01  
% 35.43/5.01  cnf(c_1496,plain,
% 35.43/5.01      ( sK3 = sK3 ),
% 35.43/5.01      inference(instantiation,[status(thm)],[c_772]) ).
% 35.43/5.01  
% 35.43/5.01  cnf(c_58,plain,
% 35.43/5.01      ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k1_xboole_0
% 35.43/5.01      | r1_tarski(X0,X1) != iProver_top ),
% 35.43/5.01      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 35.43/5.01  
% 35.43/5.01  cnf(c_60,plain,
% 35.43/5.01      ( k5_xboole_0(sK2,k3_xboole_0(sK2,sK2)) = k1_xboole_0
% 35.43/5.01      | r1_tarski(sK2,sK2) != iProver_top ),
% 35.43/5.01      inference(instantiation,[status(thm)],[c_58]) ).
% 35.43/5.01  
% 35.43/5.01  cnf(c_20,negated_conjecture,
% 35.43/5.01      ( k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) != sK3
% 35.43/5.01      | k1_xboole_0 != sK4 ),
% 35.43/5.01      inference(cnf_transformation,[],[f100]) ).
% 35.43/5.01  
% 35.43/5.01  cnf(c_21,negated_conjecture,
% 35.43/5.01      ( k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) != sK4
% 35.43/5.01      | k1_xboole_0 != sK3 ),
% 35.43/5.01      inference(cnf_transformation,[],[f101]) ).
% 35.43/5.01  
% 35.43/5.01  cnf(c_22,negated_conjecture,
% 35.43/5.01      ( k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) != sK3
% 35.43/5.01      | k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) != sK4 ),
% 35.43/5.01      inference(cnf_transformation,[],[f102]) ).
% 35.43/5.01  
% 35.43/5.01  cnf(contradiction,plain,
% 35.43/5.01      ( $false ),
% 35.43/5.01      inference(minisat,
% 35.43/5.01                [status(thm)],
% 35.43/5.01                [c_114879,c_114878,c_111961,c_101807,c_101641,c_98322,
% 35.43/5.01                 c_71852,c_65070,c_51638,c_46767,c_24456,c_20458,c_20347,
% 35.43/5.01                 c_19633,c_16079,c_12290,c_11767,c_11766,c_11373,c_11343,
% 35.43/5.01                 c_6940,c_6613,c_5424,c_4010,c_3349,c_3084,c_2838,c_1943,
% 35.43/5.01                 c_1904,c_1636,c_1496,c_60,c_20,c_21,c_22,c_23]) ).
% 35.43/5.01  
% 35.43/5.01  
% 35.43/5.01  % SZS output end CNFRefutation for theBenchmark.p
% 35.43/5.01  
% 35.43/5.01  ------                               Statistics
% 35.43/5.01  
% 35.43/5.01  ------ General
% 35.43/5.01  
% 35.43/5.01  abstr_ref_over_cycles:                  0
% 35.43/5.01  abstr_ref_under_cycles:                 0
% 35.43/5.01  gc_basic_clause_elim:                   0
% 35.43/5.01  forced_gc_time:                         0
% 35.43/5.01  parsing_time:                           0.011
% 35.43/5.01  unif_index_cands_time:                  0.
% 35.43/5.01  unif_index_add_time:                    0.
% 35.43/5.01  orderings_time:                         0.
% 35.43/5.01  out_proof_time:                         0.018
% 35.43/5.01  total_time:                             4.381
% 35.43/5.01  num_of_symbols:                         45
% 35.43/5.01  num_of_terms:                           100025
% 35.43/5.01  
% 35.43/5.01  ------ Preprocessing
% 35.43/5.01  
% 35.43/5.01  num_of_splits:                          0
% 35.43/5.01  num_of_split_atoms:                     0
% 35.43/5.01  num_of_reused_defs:                     0
% 35.43/5.01  num_eq_ax_congr_red:                    19
% 35.43/5.01  num_of_sem_filtered_clauses:            1
% 35.43/5.01  num_of_subtypes:                        0
% 35.43/5.01  monotx_restored_types:                  0
% 35.43/5.01  sat_num_of_epr_types:                   0
% 35.43/5.01  sat_num_of_non_cyclic_types:            0
% 35.43/5.01  sat_guarded_non_collapsed_types:        0
% 35.43/5.01  num_pure_diseq_elim:                    0
% 35.43/5.01  simp_replaced_by:                       0
% 35.43/5.01  res_preprocessed:                       112
% 35.43/5.01  prep_upred:                             0
% 35.43/5.01  prep_unflattend:                        34
% 35.43/5.01  smt_new_axioms:                         0
% 35.43/5.01  pred_elim_cands:                        3
% 35.43/5.01  pred_elim:                              1
% 35.43/5.01  pred_elim_cl:                           1
% 35.43/5.01  pred_elim_cycles:                       5
% 35.43/5.01  merged_defs:                            16
% 35.43/5.01  merged_defs_ncl:                        0
% 35.43/5.01  bin_hyper_res:                          16
% 35.43/5.01  prep_cycles:                            4
% 35.43/5.01  pred_elim_time:                         0.005
% 35.43/5.01  splitting_time:                         0.
% 35.43/5.01  sem_filter_time:                        0.
% 35.43/5.01  monotx_time:                            0.
% 35.43/5.01  subtype_inf_time:                       0.
% 35.43/5.01  
% 35.43/5.01  ------ Problem properties
% 35.43/5.01  
% 35.43/5.01  clauses:                                23
% 35.43/5.01  conjectures:                            4
% 35.43/5.01  epr:                                    2
% 35.43/5.01  horn:                                   20
% 35.43/5.01  ground:                                 4
% 35.43/5.01  unary:                                  7
% 35.43/5.01  binary:                                 15
% 35.43/5.01  lits:                                   40
% 35.43/5.01  lits_eq:                                16
% 35.43/5.01  fd_pure:                                0
% 35.43/5.01  fd_pseudo:                              0
% 35.43/5.01  fd_cond:                                1
% 35.43/5.01  fd_pseudo_cond:                         0
% 35.43/5.01  ac_symbols:                             0
% 35.43/5.01  
% 35.43/5.01  ------ Propositional Solver
% 35.43/5.01  
% 35.43/5.01  prop_solver_calls:                      34
% 35.43/5.01  prop_fast_solver_calls:                 1457
% 35.43/5.01  smt_solver_calls:                       0
% 35.43/5.01  smt_fast_solver_calls:                  0
% 35.43/5.01  prop_num_of_clauses:                    33007
% 35.43/5.01  prop_preprocess_simplified:             46623
% 35.43/5.01  prop_fo_subsumed:                       16
% 35.43/5.01  prop_solver_time:                       0.
% 35.43/5.01  smt_solver_time:                        0.
% 35.43/5.01  smt_fast_solver_time:                   0.
% 35.43/5.01  prop_fast_solver_time:                  0.
% 35.43/5.01  prop_unsat_core_time:                   0.004
% 35.43/5.01  
% 35.43/5.01  ------ QBF
% 35.43/5.01  
% 35.43/5.01  qbf_q_res:                              0
% 35.43/5.01  qbf_num_tautologies:                    0
% 35.43/5.01  qbf_prep_cycles:                        0
% 35.43/5.01  
% 35.43/5.01  ------ BMC1
% 35.43/5.01  
% 35.43/5.01  bmc1_current_bound:                     -1
% 35.43/5.01  bmc1_last_solved_bound:                 -1
% 35.43/5.01  bmc1_unsat_core_size:                   -1
% 35.43/5.01  bmc1_unsat_core_parents_size:           -1
% 35.43/5.01  bmc1_merge_next_fun:                    0
% 35.43/5.01  bmc1_unsat_core_clauses_time:           0.
% 35.43/5.01  
% 35.43/5.01  ------ Instantiation
% 35.43/5.01  
% 35.43/5.01  inst_num_of_clauses:                    7357
% 35.43/5.01  inst_num_in_passive:                    2851
% 35.43/5.01  inst_num_in_active:                     1774
% 35.43/5.01  inst_num_in_unprocessed:                2749
% 35.43/5.01  inst_num_of_loops:                      2530
% 35.43/5.01  inst_num_of_learning_restarts:          0
% 35.43/5.01  inst_num_moves_active_passive:          749
% 35.43/5.01  inst_lit_activity:                      0
% 35.43/5.01  inst_lit_activity_moves:                2
% 35.43/5.01  inst_num_tautologies:                   0
% 35.43/5.01  inst_num_prop_implied:                  0
% 35.43/5.01  inst_num_existing_simplified:           0
% 35.43/5.01  inst_num_eq_res_simplified:             0
% 35.43/5.01  inst_num_child_elim:                    0
% 35.43/5.01  inst_num_of_dismatching_blockings:      9987
% 35.43/5.01  inst_num_of_non_proper_insts:           7959
% 35.43/5.01  inst_num_of_duplicates:                 0
% 35.43/5.01  inst_inst_num_from_inst_to_res:         0
% 35.43/5.01  inst_dismatching_checking_time:         0.
% 35.43/5.01  
% 35.43/5.01  ------ Resolution
% 35.43/5.01  
% 35.43/5.01  res_num_of_clauses:                     0
% 35.43/5.01  res_num_in_passive:                     0
% 35.43/5.01  res_num_in_active:                      0
% 35.43/5.01  res_num_of_loops:                       116
% 35.43/5.01  res_forward_subset_subsumed:            1391
% 35.43/5.01  res_backward_subset_subsumed:           78
% 35.43/5.01  res_forward_subsumed:                   0
% 35.43/5.01  res_backward_subsumed:                  0
% 35.43/5.01  res_forward_subsumption_resolution:     0
% 35.43/5.01  res_backward_subsumption_resolution:    0
% 35.43/5.01  res_clause_to_clause_subsumption:       34291
% 35.43/5.01  res_orphan_elimination:                 0
% 35.43/5.01  res_tautology_del:                      552
% 35.43/5.01  res_num_eq_res_simplified:              0
% 35.43/5.01  res_num_sel_changes:                    0
% 35.43/5.01  res_moves_from_active_to_pass:          0
% 35.43/5.01  
% 35.43/5.01  ------ Superposition
% 35.43/5.01  
% 35.43/5.01  sup_time_total:                         0.
% 35.43/5.01  sup_time_generating:                    0.
% 35.43/5.01  sup_time_sim_full:                      0.
% 35.43/5.01  sup_time_sim_immed:                     0.
% 35.43/5.01  
% 35.43/5.01  sup_num_of_clauses:                     3585
% 35.43/5.01  sup_num_in_active:                      442
% 35.43/5.01  sup_num_in_passive:                     3143
% 35.43/5.01  sup_num_of_loops:                       504
% 35.43/5.01  sup_fw_superposition:                   16780
% 35.43/5.01  sup_bw_superposition:                   6358
% 35.43/5.01  sup_immediate_simplified:               8140
% 35.43/5.01  sup_given_eliminated:                   3
% 35.43/5.01  comparisons_done:                       0
% 35.43/5.01  comparisons_avoided:                    4
% 35.43/5.01  
% 35.43/5.01  ------ Simplifications
% 35.43/5.01  
% 35.43/5.01  
% 35.43/5.01  sim_fw_subset_subsumed:                 239
% 35.43/5.01  sim_bw_subset_subsumed:                 163
% 35.43/5.01  sim_fw_subsumed:                        885
% 35.43/5.01  sim_bw_subsumed:                        91
% 35.43/5.01  sim_fw_subsumption_res:                 0
% 35.43/5.01  sim_bw_subsumption_res:                 0
% 35.43/5.01  sim_tautology_del:                      44
% 35.43/5.01  sim_eq_tautology_del:                   2615
% 35.43/5.01  sim_eq_res_simp:                        288
% 35.43/5.01  sim_fw_demodulated:                     4662
% 35.43/5.01  sim_bw_demodulated:                     141
% 35.43/5.01  sim_light_normalised:                   4924
% 35.43/5.01  sim_joinable_taut:                      0
% 35.43/5.01  sim_joinable_simp:                      0
% 35.43/5.01  sim_ac_normalised:                      0
% 35.43/5.01  sim_smt_subsumption:                    0
% 35.43/5.01  
%------------------------------------------------------------------------------
