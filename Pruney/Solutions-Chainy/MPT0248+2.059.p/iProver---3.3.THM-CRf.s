%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:32:17 EST 2020

% Result     : Theorem 39.65s
% Output     : CNFRefutation 39.65s
% Verified   : 
% Statistics : ERROR: Analysing output (Could not find formula named c_119963)

% Comments   : 
%------------------------------------------------------------------------------
fof(f24,conjecture,(
    ! [X0,X1,X2] :
      ~ ( ~ ( k1_xboole_0 = X2
            & k1_tarski(X0) = X1 )
        & ~ ( k1_tarski(X0) = X2
            & k1_xboole_0 = X1 )
        & ~ ( k1_tarski(X0) = X2
            & k1_tarski(X0) = X1 )
        & k2_xboole_0(X1,X2) = k1_tarski(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ~ ( ~ ( k1_xboole_0 = X2
              & k1_tarski(X0) = X1 )
          & ~ ( k1_tarski(X0) = X2
              & k1_xboole_0 = X1 )
          & ~ ( k1_tarski(X0) = X2
              & k1_tarski(X0) = X1 )
          & k2_xboole_0(X1,X2) = k1_tarski(X0) ) ),
    inference(negated_conjecture,[],[f24])).

fof(f38,plain,(
    ? [X0,X1,X2] :
      ( ( k1_xboole_0 != X2
        | k1_tarski(X0) != X1 )
      & ( k1_tarski(X0) != X2
        | k1_xboole_0 != X1 )
      & ( k1_tarski(X0) != X2
        | k1_tarski(X0) != X1 )
      & k2_xboole_0(X1,X2) = k1_tarski(X0) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f46,plain,
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

fof(f47,plain,
    ( ( k1_xboole_0 != sK4
      | k1_tarski(sK2) != sK3 )
    & ( k1_tarski(sK2) != sK4
      | k1_xboole_0 != sK3 )
    & ( k1_tarski(sK2) != sK4
      | k1_tarski(sK2) != sK3 )
    & k2_xboole_0(sK3,sK4) = k1_tarski(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f38,f46])).

fof(f77,plain,(
    k2_xboole_0(sK3,sK4) = k1_tarski(sK2) ),
    inference(cnf_transformation,[],[f47])).

fof(f23,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f76,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f23])).

fof(f83,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k4_enumset1(X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f76,f82])).

fof(f17,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f70,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f17])).

fof(f18,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f71,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f18])).

fof(f20,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f73,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f20])).

fof(f19,axiom,(
    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f72,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f19])).

fof(f81,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k4_enumset1(X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f73,f72])).

fof(f82,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k4_enumset1(X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f71,f81])).

fof(f84,plain,(
    ! [X0] : k1_tarski(X0) = k4_enumset1(X0,X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f70,f82])).

fof(f98,plain,(
    k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK2) = k3_tarski(k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK4)) ),
    inference(definition_unfolding,[],[f77,f83,f84])).

fof(f15,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f67,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f15])).

fof(f90,plain,(
    ! [X0,X1] : r1_tarski(X0,k3_tarski(k4_enumset1(X0,X0,X0,X0,X0,X1))) ),
    inference(definition_unfolding,[],[f67,f83])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f63,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f5])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f26])).

fof(f42,plain,(
    ! [X1,X0] :
      ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
     => r2_hidden(sK1(X0,X1),k3_xboole_0(X0,X1)) ) ),
    introduced(choice_axiom,[])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( r2_hidden(sK1(X0,X1),k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f31,f42])).

fof(f55,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK1(X0,X1),k3_xboole_0(X0,X1))
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f22,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => k3_xboole_0(X1,k1_tarski(X0)) = k1_tarski(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X1,k1_tarski(X0)) = k1_tarski(X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f75,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X1,k1_tarski(X0)) = k1_tarski(X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f94,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X1,k4_enumset1(X0,X0,X0,X0,X0,X0)) = k4_enumset1(X0,X0,X0,X0,X0,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f75,f84,f84])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f12,axiom,(
    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f64,plain,(
    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f12])).

fof(f13,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f65,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f13])).

fof(f7,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f59,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f7])).

fof(f89,plain,(
    ! [X0,X1] : r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X0) ),
    inference(definition_unfolding,[],[f65,f59])).

fof(f14,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f66,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f14])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
     => r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
      | ~ r1_tarski(X0,k3_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r1_tarski(X0,k3_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,k3_xboole_0(X0,X1)) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f80,plain,
    ( k1_xboole_0 != sK4
    | k1_tarski(sK2) != sK3 ),
    inference(cnf_transformation,[],[f47])).

fof(f95,plain,
    ( k1_xboole_0 != sK4
    | k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK2) != sK3 ),
    inference(definition_unfolding,[],[f80,f84])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,X1)
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k4_xboole_0(X0,X1)
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k1_xboole_0 != k4_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f58,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f85,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k5_xboole_0(X0,k3_xboole_0(X0,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f58,f59])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] : ~ r2_hidden(X1,X0)
     => v1_xboole_0(X0) ) ),
    inference(unused_predicate_definition_removal,[],[f2])).

fof(f28,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
      | ? [X1] : r2_hidden(X1,X0) ) ),
    inference(ennf_transformation,[],[f27])).

fof(f39,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK0(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
      | r2_hidden(sK0(X0),X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f28,f39])).

fof(f49,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
      | r2_hidden(sK0(X0),X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f50,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k4_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k4_xboole_0(X0,X1) != X0 )
      & ( k4_xboole_0(X0,X1) = X0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f16])).

fof(f69,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k4_xboole_0(X0,X1) != X0 ) ),
    inference(cnf_transformation,[],[f45])).

fof(f91,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X0 ) ),
    inference(definition_unfolding,[],[f69,f59])).

fof(f21,axiom,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
     => r1_xboole_0(k1_tarski(X0),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f74,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f93,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k4_enumset1(X0,X0,X0,X0,X0,X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f74,f84])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_tarski(X0,k2_xboole_0(X2,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k2_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f87,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k3_tarski(k4_enumset1(X2,X2,X2,X2,X2,X1)))
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f60,f83])).

fof(f78,plain,
    ( k1_tarski(sK2) != sK4
    | k1_tarski(sK2) != sK3 ),
    inference(cnf_transformation,[],[f47])).

fof(f97,plain,
    ( k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK2) != sK4
    | k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK2) != sK3 ),
    inference(definition_unfolding,[],[f78,f84,f84])).

fof(f79,plain,
    ( k1_tarski(sK2) != sK4
    | k1_xboole_0 != sK3 ),
    inference(cnf_transformation,[],[f47])).

fof(f96,plain,
    ( k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK2) != sK4
    | k1_xboole_0 != sK3 ),
    inference(definition_unfolding,[],[f79,f84])).

fof(f68,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = X0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f92,plain,(
    ! [X0,X1] :
      ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(definition_unfolding,[],[f68,f59])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f61,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f88,plain,(
    ! [X0,X1] :
      ( k3_tarski(k4_enumset1(X0,X0,X0,X0,X0,X1)) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f61,f83])).

cnf(c_26,negated_conjecture,
    ( k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK2) = k3_tarski(k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK4)) ),
    inference(cnf_transformation,[],[f98])).

cnf(c_18,plain,
    ( r1_tarski(X0,k3_tarski(k4_enumset1(X0,X0,X0,X0,X0,X1))) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_1084,plain,
    ( r1_tarski(X0,k3_tarski(k4_enumset1(X0,X0,X0,X0,X0,X1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_1713,plain,
    ( r1_tarski(sK3,k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_26,c_1084])).

cnf(c_14,plain,
    ( ~ r1_tarski(X0,X1)
    | k3_xboole_0(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f63])).

cnf(c_1086,plain,
    ( k3_xboole_0(X0,X1) = X0
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_1805,plain,
    ( k3_xboole_0(sK3,k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK2)) = sK3 ),
    inference(superposition,[status(thm)],[c_1713,c_1086])).

cnf(c_8,plain,
    ( r1_xboole_0(X0,X1)
    | r2_hidden(sK1(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_1092,plain,
    ( r1_xboole_0(X0,X1) = iProver_top
    | r2_hidden(sK1(X0,X1),k3_xboole_0(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_5288,plain,
    ( r1_xboole_0(sK3,k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK2)) = iProver_top
    | r2_hidden(sK1(sK3,k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK2)),sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_1805,c_1092])).

cnf(c_22,plain,
    ( ~ r2_hidden(X0,X1)
    | k3_xboole_0(X1,k4_enumset1(X0,X0,X0,X0,X0,X0)) = k4_enumset1(X0,X0,X0,X0,X0,X0) ),
    inference(cnf_transformation,[],[f94])).

cnf(c_1080,plain,
    ( k3_xboole_0(X0,k4_enumset1(X1,X1,X1,X1,X1,X1)) = k4_enumset1(X1,X1,X1,X1,X1,X1)
    | r2_hidden(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_5296,plain,
    ( k3_xboole_0(k3_xboole_0(X0,X1),k4_enumset1(sK1(X0,X1),sK1(X0,X1),sK1(X0,X1),sK1(X0,X1),sK1(X0,X1),sK1(X0,X1))) = k4_enumset1(sK1(X0,X1),sK1(X0,X1),sK1(X0,X1),sK1(X0,X1),sK1(X0,X1),sK1(X0,X1))
    | r1_xboole_0(X0,X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_1092,c_1080])).

cnf(c_1802,plain,
    ( k3_xboole_0(X0,k3_tarski(k4_enumset1(X0,X0,X0,X0,X0,X1))) = X0 ),
    inference(superposition,[status(thm)],[c_1084,c_1086])).

cnf(c_0,plain,
    ( k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_15,plain,
    ( k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f64])).

cnf(c_16,plain,
    ( r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X0) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_1085,plain,
    ( r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_1470,plain,
    ( r1_tarski(k5_xboole_0(X0,k1_xboole_0),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_15,c_1085])).

cnf(c_17,plain,
    ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f66])).

cnf(c_1473,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1470,c_17])).

cnf(c_13,plain,
    ( r1_tarski(X0,X1)
    | ~ r1_tarski(X0,k3_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_1087,plain,
    ( r1_tarski(X0,X1) = iProver_top
    | r1_tarski(X0,k3_xboole_0(X1,X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_2417,plain,
    ( r1_tarski(X0,X1) = iProver_top
    | r1_tarski(X0,k3_xboole_0(X2,X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_0,c_1087])).

cnf(c_4224,plain,
    ( r1_tarski(k3_xboole_0(X0,X1),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_1473,c_2417])).

cnf(c_4229,plain,
    ( r1_tarski(X0,k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK2)) = iProver_top
    | r1_tarski(X0,sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1805,c_2417])).

cnf(c_4391,plain,
    ( k3_xboole_0(X0,k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK2)) = X0
    | r1_tarski(X0,sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_4229,c_1086])).

cnf(c_14313,plain,
    ( k3_xboole_0(k3_xboole_0(X0,sK3),k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK2)) = k3_xboole_0(X0,sK3) ),
    inference(superposition,[status(thm)],[c_4224,c_4391])).

cnf(c_50205,plain,
    ( k3_xboole_0(k3_xboole_0(sK3,X0),k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK2)) = k3_xboole_0(X0,sK3) ),
    inference(superposition,[status(thm)],[c_0,c_14313])).

cnf(c_55525,plain,
    ( k3_xboole_0(k3_tarski(k4_enumset1(sK3,sK3,sK3,sK3,sK3,X0)),sK3) = k3_xboole_0(sK3,k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK2)) ),
    inference(superposition,[status(thm)],[c_1802,c_50205])).

cnf(c_55613,plain,
    ( k3_xboole_0(k3_tarski(k4_enumset1(sK3,sK3,sK3,sK3,sK3,X0)),sK3) = sK3 ),
    inference(light_normalisation,[status(thm)],[c_55525,c_1805])).

cnf(c_7,plain,
    ( ~ r1_xboole_0(X0,X1)
    | ~ r2_hidden(X2,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_1093,plain,
    ( r1_xboole_0(X0,X1) != iProver_top
    | r2_hidden(X2,k3_xboole_0(X0,X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_56882,plain,
    ( r1_xboole_0(k3_tarski(k4_enumset1(sK3,sK3,sK3,sK3,sK3,X0)),sK3) != iProver_top
    | r2_hidden(X1,sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_55613,c_1093])).

cnf(c_170407,plain,
    ( k3_xboole_0(k3_xboole_0(k3_tarski(k4_enumset1(sK3,sK3,sK3,sK3,sK3,X0)),sK3),k4_enumset1(sK1(k3_tarski(k4_enumset1(sK3,sK3,sK3,sK3,sK3,X0)),sK3),sK1(k3_tarski(k4_enumset1(sK3,sK3,sK3,sK3,sK3,X0)),sK3),sK1(k3_tarski(k4_enumset1(sK3,sK3,sK3,sK3,sK3,X0)),sK3),sK1(k3_tarski(k4_enumset1(sK3,sK3,sK3,sK3,sK3,X0)),sK3),sK1(k3_tarski(k4_enumset1(sK3,sK3,sK3,sK3,sK3,X0)),sK3),sK1(k3_tarski(k4_enumset1(sK3,sK3,sK3,sK3,sK3,X0)),sK3))) = k4_enumset1(sK1(k3_tarski(k4_enumset1(sK3,sK3,sK3,sK3,sK3,X0)),sK3),sK1(k3_tarski(k4_enumset1(sK3,sK3,sK3,sK3,sK3,X0)),sK3),sK1(k3_tarski(k4_enumset1(sK3,sK3,sK3,sK3,sK3,X0)),sK3),sK1(k3_tarski(k4_enumset1(sK3,sK3,sK3,sK3,sK3,X0)),sK3),sK1(k3_tarski(k4_enumset1(sK3,sK3,sK3,sK3,sK3,X0)),sK3),sK1(k3_tarski(k4_enumset1(sK3,sK3,sK3,sK3,sK3,X0)),sK3))
    | r2_hidden(X1,sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_5296,c_56882])).

cnf(c_170410,plain,
    ( k3_xboole_0(sK3,k4_enumset1(sK1(k3_tarski(k4_enumset1(sK3,sK3,sK3,sK3,sK3,X0)),sK3),sK1(k3_tarski(k4_enumset1(sK3,sK3,sK3,sK3,sK3,X0)),sK3),sK1(k3_tarski(k4_enumset1(sK3,sK3,sK3,sK3,sK3,X0)),sK3),sK1(k3_tarski(k4_enumset1(sK3,sK3,sK3,sK3,sK3,X0)),sK3),sK1(k3_tarski(k4_enumset1(sK3,sK3,sK3,sK3,sK3,X0)),sK3),sK1(k3_tarski(k4_enumset1(sK3,sK3,sK3,sK3,sK3,X0)),sK3))) = k4_enumset1(sK1(k3_tarski(k4_enumset1(sK3,sK3,sK3,sK3,sK3,X0)),sK3),sK1(k3_tarski(k4_enumset1(sK3,sK3,sK3,sK3,sK3,X0)),sK3),sK1(k3_tarski(k4_enumset1(sK3,sK3,sK3,sK3,sK3,X0)),sK3),sK1(k3_tarski(k4_enumset1(sK3,sK3,sK3,sK3,sK3,X0)),sK3),sK1(k3_tarski(k4_enumset1(sK3,sK3,sK3,sK3,sK3,X0)),sK3),sK1(k3_tarski(k4_enumset1(sK3,sK3,sK3,sK3,sK3,X0)),sK3))
    | r2_hidden(X1,sK3) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_170407,c_55613])).

cnf(c_177160,plain,
    ( k3_xboole_0(sK3,k4_enumset1(sK1(k3_tarski(k4_enumset1(sK3,sK3,sK3,sK3,sK3,X0)),sK3),sK1(k3_tarski(k4_enumset1(sK3,sK3,sK3,sK3,sK3,X0)),sK3),sK1(k3_tarski(k4_enumset1(sK3,sK3,sK3,sK3,sK3,X0)),sK3),sK1(k3_tarski(k4_enumset1(sK3,sK3,sK3,sK3,sK3,X0)),sK3),sK1(k3_tarski(k4_enumset1(sK3,sK3,sK3,sK3,sK3,X0)),sK3),sK1(k3_tarski(k4_enumset1(sK3,sK3,sK3,sK3,sK3,X0)),sK3))) = k4_enumset1(sK1(k3_tarski(k4_enumset1(sK3,sK3,sK3,sK3,sK3,X0)),sK3),sK1(k3_tarski(k4_enumset1(sK3,sK3,sK3,sK3,sK3,X0)),sK3),sK1(k3_tarski(k4_enumset1(sK3,sK3,sK3,sK3,sK3,X0)),sK3),sK1(k3_tarski(k4_enumset1(sK3,sK3,sK3,sK3,sK3,X0)),sK3),sK1(k3_tarski(k4_enumset1(sK3,sK3,sK3,sK3,sK3,X0)),sK3),sK1(k3_tarski(k4_enumset1(sK3,sK3,sK3,sK3,sK3,X0)),sK3))
    | r1_xboole_0(sK3,k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_5288,c_170410])).

cnf(c_23,negated_conjecture,
    ( k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK2) != sK3
    | k1_xboole_0 != sK4 ),
    inference(cnf_transformation,[],[f95])).

cnf(c_9,plain,
    ( ~ r1_tarski(X0,X1)
    | k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f85])).

cnf(c_60,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k1_xboole_0
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_62,plain,
    ( k5_xboole_0(sK2,k3_xboole_0(sK2,sK2)) = k1_xboole_0
    | r1_tarski(sK2,sK2) != iProver_top ),
    inference(instantiation,[status(thm)],[c_60])).

cnf(c_629,plain,
    ( X0 != X1
    | X2 != X3
    | X4 != X5
    | X6 != X7
    | X8 != X9
    | X10 != X11
    | k4_enumset1(X0,X2,X4,X6,X8,X10) = k4_enumset1(X1,X3,X5,X7,X9,X11) ),
    theory(equality)).

cnf(c_635,plain,
    ( k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK2) = k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK2)
    | sK2 != sK2 ),
    inference(instantiation,[status(thm)],[c_629])).

cnf(c_622,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_638,plain,
    ( sK2 = sK2 ),
    inference(instantiation,[status(thm)],[c_622])).

cnf(c_1230,plain,
    ( sK3 = sK3 ),
    inference(instantiation,[status(thm)],[c_622])).

cnf(c_1476,plain,
    ( r1_tarski(sK2,sK2) = iProver_top ),
    inference(instantiation,[status(thm)],[c_1473])).

cnf(c_623,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_1175,plain,
    ( X0 != X1
    | sK4 != X1
    | sK4 = X0 ),
    inference(instantiation,[status(thm)],[c_623])).

cnf(c_1787,plain,
    ( X0 != k1_xboole_0
    | sK4 = X0
    | sK4 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1175])).

cnf(c_2028,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) != k1_xboole_0
    | sK4 = k5_xboole_0(X0,k3_xboole_0(X0,X1))
    | sK4 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1787])).

cnf(c_2029,plain,
    ( k5_xboole_0(sK2,k3_xboole_0(sK2,sK2)) != k1_xboole_0
    | sK4 = k5_xboole_0(sK2,k3_xboole_0(sK2,sK2))
    | sK4 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_2028])).

cnf(c_1,plain,
    ( r2_hidden(sK0(X0),X0)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_2,plain,
    ( ~ v1_xboole_0(X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f50])).

cnf(c_297,plain,
    ( r2_hidden(sK0(X0),X0)
    | k1_xboole_0 = X0 ),
    inference(resolution,[status(thm)],[c_1,c_2])).

cnf(c_1079,plain,
    ( k1_xboole_0 = X0
    | r2_hidden(sK0(X0),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_297])).

cnf(c_5791,plain,
    ( r1_xboole_0(X0,k1_xboole_0) != iProver_top
    | r2_hidden(X1,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_15,c_1093])).

cnf(c_19,plain,
    ( r1_xboole_0(X0,X1)
    | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X0 ),
    inference(cnf_transformation,[],[f91])).

cnf(c_1083,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X0
    | r1_xboole_0(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_2392,plain,
    ( k5_xboole_0(X0,k1_xboole_0) != X0
    | r1_xboole_0(X0,k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_15,c_1083])).

cnf(c_2400,plain,
    ( X0 != X0
    | r1_xboole_0(X0,k1_xboole_0) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2392,c_17])).

cnf(c_2401,plain,
    ( r1_xboole_0(X0,k1_xboole_0) = iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_2400])).

cnf(c_5966,plain,
    ( r2_hidden(X1,k1_xboole_0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5791,c_2401])).

cnf(c_5967,plain,
    ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
    inference(renaming,[status(thm)],[c_5966])).

cnf(c_5972,plain,
    ( k1_xboole_0 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1079,c_5967])).

cnf(c_21,plain,
    ( r1_xboole_0(k4_enumset1(X0,X0,X0,X0,X0,X0),X1)
    | r2_hidden(X0,X1) ),
    inference(cnf_transformation,[],[f93])).

cnf(c_1081,plain,
    ( r1_xboole_0(k4_enumset1(X0,X0,X0,X0,X0,X0),X1) = iProver_top
    | r2_hidden(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_5789,plain,
    ( r1_xboole_0(X0,X1) != iProver_top
    | r2_hidden(X2,k3_xboole_0(X1,X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_0,c_1093])).

cnf(c_7026,plain,
    ( r1_xboole_0(k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK2),sK3) != iProver_top
    | r2_hidden(X0,sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1805,c_5789])).

cnf(c_7056,plain,
    ( r2_hidden(X0,sK3) != iProver_top
    | r2_hidden(sK2,sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_1081,c_7026])).

cnf(c_8609,plain,
    ( r1_xboole_0(sK3,k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK2)) = iProver_top
    | r2_hidden(sK2,sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_5288,c_7056])).

cnf(c_1120,plain,
    ( sK4 != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = sK4 ),
    inference(instantiation,[status(thm)],[c_623])).

cnf(c_28727,plain,
    ( sK4 != k5_xboole_0(X0,k3_xboole_0(X0,X1))
    | k1_xboole_0 != k5_xboole_0(X0,k3_xboole_0(X0,X1))
    | k1_xboole_0 = sK4 ),
    inference(instantiation,[status(thm)],[c_1120])).

cnf(c_28728,plain,
    ( sK4 != k5_xboole_0(sK2,k3_xboole_0(sK2,sK2))
    | k1_xboole_0 != k5_xboole_0(sK2,k3_xboole_0(sK2,sK2))
    | k1_xboole_0 = sK4 ),
    inference(instantiation,[status(thm)],[c_28727])).

cnf(c_6498,plain,
    ( X0 != X1
    | k1_xboole_0 != X1
    | k1_xboole_0 = X0 ),
    inference(instantiation,[status(thm)],[c_623])).

cnf(c_51873,plain,
    ( X0 != k1_xboole_0
    | k1_xboole_0 = X0
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_6498])).

cnf(c_80192,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) != k1_xboole_0
    | k1_xboole_0 = k5_xboole_0(X0,k3_xboole_0(X0,X1))
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_51873])).

cnf(c_80193,plain,
    ( k5_xboole_0(sK2,k3_xboole_0(sK2,sK2)) != k1_xboole_0
    | k1_xboole_0 = k5_xboole_0(sK2,k3_xboole_0(sK2,sK2))
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_80192])).

cnf(c_1127,plain,
    ( k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK2) != X0
    | k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK2) = sK3
    | sK3 != X0 ),
    inference(instantiation,[status(thm)],[c_623])).

cnf(c_33893,plain,
    ( k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK2) != k3_xboole_0(X0,k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK2))
    | k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK2) = sK3
    | sK3 != k3_xboole_0(X0,k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK2)) ),
    inference(instantiation,[status(thm)],[c_1127])).

cnf(c_81240,plain,
    ( k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK2) != k3_xboole_0(sK3,k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK2))
    | k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK2) = sK3
    | sK3 != k3_xboole_0(sK3,k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK2)) ),
    inference(instantiation,[status(thm)],[c_33893])).

cnf(c_1145,plain,
    ( X0 != X1
    | sK3 != X1
    | sK3 = X0 ),
    inference(instantiation,[status(thm)],[c_623])).

cnf(c_1176,plain,
    ( X0 != sK3
    | sK3 = X0
    | sK3 != sK3 ),
    inference(instantiation,[status(thm)],[c_1145])).

cnf(c_1555,plain,
    ( k3_xboole_0(sK3,X0) != sK3
    | sK3 = k3_xboole_0(sK3,X0)
    | sK3 != sK3 ),
    inference(instantiation,[status(thm)],[c_1176])).

cnf(c_81241,plain,
    ( k3_xboole_0(sK3,k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK2)) != sK3
    | sK3 = k3_xboole_0(sK3,k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK2))
    | sK3 != sK3 ),
    inference(instantiation,[status(thm)],[c_1555])).

cnf(c_2900,plain,
    ( X0 != X1
    | k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK2) != X1
    | k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK2) = X0 ),
    inference(instantiation,[status(thm)],[c_623])).

cnf(c_2983,plain,
    ( X0 != k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK2)
    | k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK2) = X0
    | k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK2) != k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK2) ),
    inference(instantiation,[status(thm)],[c_2900])).

cnf(c_6083,plain,
    ( k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK2) != k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK2)
    | k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK2) = k3_xboole_0(X0,k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK2))
    | k3_xboole_0(X0,k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK2)) != k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK2) ),
    inference(instantiation,[status(thm)],[c_2983])).

cnf(c_92074,plain,
    ( k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK2) != k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK2)
    | k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK2) = k3_xboole_0(sK3,k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK2))
    | k3_xboole_0(sK3,k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK2)) != k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK2) ),
    inference(instantiation,[status(thm)],[c_6083])).

cnf(c_180155,plain,
    ( ~ r2_hidden(sK2,sK3)
    | k3_xboole_0(sK3,k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK2)) = k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK2) ),
    inference(instantiation,[status(thm)],[c_22])).

cnf(c_180157,plain,
    ( k3_xboole_0(sK3,k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK2)) = k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK2)
    | r2_hidden(sK2,sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_180155])).

cnf(c_2152,plain,
    ( k3_xboole_0(X0,k4_enumset1(sK0(X0),sK0(X0),sK0(X0),sK0(X0),sK0(X0),sK0(X0))) = k4_enumset1(sK0(X0),sK0(X0),sK0(X0),sK0(X0),sK0(X0),sK0(X0))
    | k1_xboole_0 = X0 ),
    inference(superposition,[status(thm)],[c_1079,c_1080])).

cnf(c_2416,plain,
    ( r1_tarski(k3_xboole_0(X0,X1),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1473,c_1087])).

cnf(c_11,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X0,k3_tarski(k4_enumset1(X2,X2,X2,X2,X2,X1))) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_1089,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X0,k3_tarski(k4_enumset1(X2,X2,X2,X2,X2,X1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_5269,plain,
    ( r1_tarski(X0,k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK2)) = iProver_top
    | r1_tarski(X0,sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_26,c_1089])).

cnf(c_1091,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k1_xboole_0
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_5272,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,k3_tarski(k4_enumset1(X1,X1,X1,X1,X1,X2)))) = k1_xboole_0
    | r1_tarski(X0,X2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1089,c_1091])).

cnf(c_156033,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,k3_tarski(k4_enumset1(X1,X1,X1,X1,X1,k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK2))))) = k1_xboole_0
    | r1_tarski(X0,sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_5269,c_5272])).

cnf(c_158780,plain,
    ( k5_xboole_0(k3_xboole_0(sK4,X0),k3_xboole_0(k3_xboole_0(sK4,X0),k3_tarski(k4_enumset1(X1,X1,X1,X1,X1,k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK2))))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2416,c_156033])).

cnf(c_159254,plain,
    ( k5_xboole_0(k4_enumset1(sK0(sK4),sK0(sK4),sK0(sK4),sK0(sK4),sK0(sK4),sK0(sK4)),k3_xboole_0(k4_enumset1(sK0(sK4),sK0(sK4),sK0(sK4),sK0(sK4),sK0(sK4),sK0(sK4)),k3_tarski(k4_enumset1(X0,X0,X0,X0,X0,k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK2))))) = k1_xboole_0
    | sK4 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2152,c_158780])).

cnf(c_25,negated_conjecture,
    ( k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK2) != sK3
    | k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK2) != sK4 ),
    inference(cnf_transformation,[],[f97])).

cnf(c_24,negated_conjecture,
    ( k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK2) != sK4
    | k1_xboole_0 != sK3 ),
    inference(cnf_transformation,[],[f96])).

cnf(c_1361,plain,
    ( sK4 = sK4 ),
    inference(instantiation,[status(thm)],[c_622])).

cnf(c_5976,plain,
    ( k3_xboole_0(X0,k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK2)) = X0
    | r1_tarski(X0,sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_5269,c_1086])).

cnf(c_6055,plain,
    ( k3_xboole_0(sK4,k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK2)) = sK4 ),
    inference(superposition,[status(thm)],[c_1473,c_5976])).

cnf(c_8608,plain,
    ( sK3 = k1_xboole_0
    | r2_hidden(sK2,sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_1079,c_7056])).

cnf(c_8612,plain,
    ( r2_hidden(sK2,sK3)
    | sK3 = k1_xboole_0 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_8608])).

cnf(c_1561,plain,
    ( X0 != X1
    | X0 = sK3
    | sK3 != X1 ),
    inference(instantiation,[status(thm)],[c_623])).

cnf(c_6883,plain,
    ( X0 = sK3
    | X0 != k1_xboole_0
    | sK3 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1561])).

cnf(c_30490,plain,
    ( sK3 != k1_xboole_0
    | k1_xboole_0 = sK3
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_6883])).

cnf(c_7036,plain,
    ( r1_xboole_0(k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK2),sK4) != iProver_top
    | r2_hidden(X0,sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_6055,c_5789])).

cnf(c_10103,plain,
    ( r2_hidden(X0,sK4) != iProver_top
    | r2_hidden(sK2,sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_1081,c_7036])).

cnf(c_44189,plain,
    ( sK4 = k1_xboole_0
    | r2_hidden(sK2,sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_1079,c_10103])).

cnf(c_44193,plain,
    ( r2_hidden(sK2,sK4)
    | sK4 = k1_xboole_0 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_44189])).

cnf(c_1141,plain,
    ( k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK2) != X0
    | k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK2) = sK4
    | sK4 != X0 ),
    inference(instantiation,[status(thm)],[c_623])).

cnf(c_33891,plain,
    ( k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK2) != k3_xboole_0(X0,k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK2))
    | k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK2) = sK4
    | sK4 != k3_xboole_0(X0,k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK2)) ),
    inference(instantiation,[status(thm)],[c_1141])).

cnf(c_81237,plain,
    ( k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK2) != k3_xboole_0(sK4,k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK2))
    | k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK2) = sK4
    | sK4 != k3_xboole_0(sK4,k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK2)) ),
    inference(instantiation,[status(thm)],[c_33891])).

cnf(c_1211,plain,
    ( X0 != sK4
    | sK4 = X0
    | sK4 != sK4 ),
    inference(instantiation,[status(thm)],[c_1175])).

cnf(c_1577,plain,
    ( k3_xboole_0(sK4,X0) != sK4
    | sK4 = k3_xboole_0(sK4,X0)
    | sK4 != sK4 ),
    inference(instantiation,[status(thm)],[c_1211])).

cnf(c_81238,plain,
    ( k3_xboole_0(sK4,k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK2)) != sK4
    | sK4 = k3_xboole_0(sK4,k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK2))
    | sK4 != sK4 ),
    inference(instantiation,[status(thm)],[c_1577])).

cnf(c_92890,plain,
    ( k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK2) != k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK2)
    | k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK2) = k3_xboole_0(sK4,k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK2))
    | k3_xboole_0(sK4,k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK2)) != k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK2) ),
    inference(instantiation,[status(thm)],[c_6083])).

cnf(c_180141,plain,
    ( ~ r2_hidden(sK2,sK4)
    | k3_xboole_0(sK4,k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK2)) = k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK2) ),
    inference(instantiation,[status(thm)],[c_22])).

cnf(c_180257,plain,
    ( sK4 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_159254,c_25,c_24,c_635,c_638,c_1230,c_1361,c_1805,c_5972,c_6055,c_8612,c_30490,c_44193,c_81237,c_81238,c_81240,c_81241,c_92074,c_92890,c_180141,c_180155])).

cnf(c_182286,plain,
    ( r1_xboole_0(sK3,k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK2)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_177160,c_25,c_24,c_23,c_62,c_635,c_638,c_1230,c_1361,c_1476,c_1805,c_2029,c_5972,c_6055,c_8612,c_28728,c_30490,c_44193,c_80193,c_81237,c_81238,c_81240,c_81241,c_92074,c_92890,c_119963,c_180141,c_180155])).

cnf(c_20,plain,
    ( ~ r1_xboole_0(X0,X1)
    | k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f92])).

cnf(c_1082,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X0
    | r1_xboole_0(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_182291,plain,
    ( k5_xboole_0(sK3,k3_xboole_0(sK3,k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK2))) = sK3 ),
    inference(superposition,[status(thm)],[c_182286,c_1082])).

cnf(c_182293,plain,
    ( k5_xboole_0(sK3,sK3) = sK3 ),
    inference(light_normalisation,[status(thm)],[c_182291,c_1805])).

cnf(c_4037,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,X0)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1473,c_1091])).

cnf(c_1804,plain,
    ( k3_xboole_0(X0,X0) = X0 ),
    inference(superposition,[status(thm)],[c_1473,c_1086])).

cnf(c_4061,plain,
    ( k5_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_4037,c_1804])).

cnf(c_182294,plain,
    ( sK3 = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_182293,c_4061])).

cnf(c_180651,plain,
    ( k3_tarski(k4_enumset1(sK3,sK3,sK3,sK3,sK3,k1_xboole_0)) = k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK2) ),
    inference(demodulation,[status(thm)],[c_180257,c_26])).

cnf(c_182411,plain,
    ( k3_tarski(k4_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0)) = k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK2) ),
    inference(demodulation,[status(thm)],[c_182294,c_180651])).

cnf(c_6053,plain,
    ( k3_xboole_0(k5_xboole_0(sK4,k3_xboole_0(sK4,X0)),k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK2)) = k5_xboole_0(sK4,k3_xboole_0(sK4,X0)) ),
    inference(superposition,[status(thm)],[c_1085,c_5976])).

cnf(c_6353,plain,
    ( k3_xboole_0(k5_xboole_0(sK4,k3_xboole_0(X0,sK4)),k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK2)) = k5_xboole_0(sK4,k3_xboole_0(sK4,X0)) ),
    inference(superposition,[status(thm)],[c_0,c_6053])).

cnf(c_14227,plain,
    ( k3_xboole_0(k3_xboole_0(X0,X1),X0) = k3_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_2416,c_1086])).

cnf(c_15154,plain,
    ( k3_xboole_0(k5_xboole_0(sK4,k3_xboole_0(X0,sK4)),k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK2)) = k3_xboole_0(k5_xboole_0(sK4,k3_xboole_0(sK4,X0)),k5_xboole_0(sK4,k3_xboole_0(X0,sK4))) ),
    inference(superposition,[status(thm)],[c_6353,c_14227])).

cnf(c_15228,plain,
    ( k3_xboole_0(k5_xboole_0(sK4,k3_xboole_0(sK4,X0)),k5_xboole_0(sK4,k3_xboole_0(X0,sK4))) = k5_xboole_0(sK4,k3_xboole_0(sK4,X0)) ),
    inference(light_normalisation,[status(thm)],[c_15154,c_6353])).

cnf(c_12,plain,
    ( ~ r1_tarski(X0,X1)
    | k3_tarski(k4_enumset1(X0,X0,X0,X0,X0,X1)) = X1 ),
    inference(cnf_transformation,[],[f88])).

cnf(c_1088,plain,
    ( k3_tarski(k4_enumset1(X0,X0,X0,X0,X0,X1)) = X1
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_3831,plain,
    ( k3_tarski(k4_enumset1(k5_xboole_0(X0,k3_xboole_0(X0,X1)),k5_xboole_0(X0,k3_xboole_0(X0,X1)),k5_xboole_0(X0,k3_xboole_0(X0,X1)),k5_xboole_0(X0,k3_xboole_0(X0,X1)),k5_xboole_0(X0,k3_xboole_0(X0,X1)),X0)) = X0 ),
    inference(superposition,[status(thm)],[c_1085,c_1088])).

cnf(c_79982,plain,
    ( k3_tarski(k4_enumset1(k5_xboole_0(k5_xboole_0(sK4,k3_xboole_0(sK4,X0)),k5_xboole_0(sK4,k3_xboole_0(sK4,X0))),k5_xboole_0(k5_xboole_0(sK4,k3_xboole_0(sK4,X0)),k5_xboole_0(sK4,k3_xboole_0(sK4,X0))),k5_xboole_0(k5_xboole_0(sK4,k3_xboole_0(sK4,X0)),k5_xboole_0(sK4,k3_xboole_0(sK4,X0))),k5_xboole_0(k5_xboole_0(sK4,k3_xboole_0(sK4,X0)),k5_xboole_0(sK4,k3_xboole_0(sK4,X0))),k5_xboole_0(k5_xboole_0(sK4,k3_xboole_0(sK4,X0)),k5_xboole_0(sK4,k3_xboole_0(sK4,X0))),k5_xboole_0(sK4,k3_xboole_0(sK4,X0)))) = k5_xboole_0(sK4,k3_xboole_0(sK4,X0)) ),
    inference(superposition,[status(thm)],[c_15228,c_3831])).

cnf(c_5974,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK2))) = k1_xboole_0
    | r1_tarski(X0,sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_5269,c_1091])).

cnf(c_6059,plain,
    ( k5_xboole_0(k5_xboole_0(sK4,k3_xboole_0(sK4,X0)),k3_xboole_0(k5_xboole_0(sK4,k3_xboole_0(sK4,X0)),k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK2))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1085,c_5974])).

cnf(c_6064,plain,
    ( k5_xboole_0(k5_xboole_0(sK4,k3_xboole_0(sK4,X0)),k5_xboole_0(sK4,k3_xboole_0(sK4,X0))) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_6059,c_6053])).

cnf(c_80059,plain,
    ( k3_tarski(k4_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k5_xboole_0(sK4,k3_xboole_0(sK4,X0)))) = k5_xboole_0(sK4,k3_xboole_0(sK4,X0)) ),
    inference(light_normalisation,[status(thm)],[c_79982,c_6064])).

cnf(c_91851,plain,
    ( k5_xboole_0(sK4,k3_xboole_0(sK4,k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK2))) = k3_tarski(k4_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k5_xboole_0(sK4,sK4))) ),
    inference(superposition,[status(thm)],[c_6055,c_80059])).

cnf(c_6061,plain,
    ( k5_xboole_0(sK4,k3_xboole_0(sK4,k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK2))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1473,c_5974])).

cnf(c_6062,plain,
    ( k5_xboole_0(sK4,sK4) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_6061,c_6055])).

cnf(c_91874,plain,
    ( k3_tarski(k4_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0)) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_91851,c_6055,c_6062])).

cnf(c_182573,plain,
    ( k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK2) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_182411,c_91874])).

cnf(c_1782,plain,
    ( k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK2) = sK3
    | k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK2) != k1_xboole_0
    | sK3 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1127])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_182573,c_180257,c_180155,c_92074,c_81241,c_81240,c_80193,c_28728,c_8612,c_5972,c_2029,c_1805,c_1782,c_1476,c_1230,c_638,c_635,c_62,c_23])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.14/0.13  % Command    : iproveropt_run.sh %d %s
% 0.14/0.34  % Computer   : n020.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 20:05:52 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.20/0.34  % Running in FOF mode
% 39.65/5.51  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 39.65/5.51  
% 39.65/5.51  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 39.65/5.51  
% 39.65/5.51  ------  iProver source info
% 39.65/5.51  
% 39.65/5.51  git: date: 2020-06-30 10:37:57 +0100
% 39.65/5.51  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 39.65/5.51  git: non_committed_changes: false
% 39.65/5.51  git: last_make_outside_of_git: false
% 39.65/5.51  
% 39.65/5.51  ------ 
% 39.65/5.51  
% 39.65/5.51  ------ Input Options
% 39.65/5.51  
% 39.65/5.51  --out_options                           all
% 39.65/5.51  --tptp_safe_out                         true
% 39.65/5.51  --problem_path                          ""
% 39.65/5.51  --include_path                          ""
% 39.65/5.51  --clausifier                            res/vclausify_rel
% 39.65/5.51  --clausifier_options                    ""
% 39.65/5.51  --stdin                                 false
% 39.65/5.51  --stats_out                             all
% 39.65/5.51  
% 39.65/5.51  ------ General Options
% 39.65/5.51  
% 39.65/5.51  --fof                                   false
% 39.65/5.51  --time_out_real                         305.
% 39.65/5.51  --time_out_virtual                      -1.
% 39.65/5.51  --symbol_type_check                     false
% 39.65/5.51  --clausify_out                          false
% 39.65/5.51  --sig_cnt_out                           false
% 39.65/5.51  --trig_cnt_out                          false
% 39.65/5.51  --trig_cnt_out_tolerance                1.
% 39.65/5.51  --trig_cnt_out_sk_spl                   false
% 39.65/5.51  --abstr_cl_out                          false
% 39.65/5.51  
% 39.65/5.51  ------ Global Options
% 39.65/5.51  
% 39.65/5.51  --schedule                              default
% 39.65/5.51  --add_important_lit                     false
% 39.65/5.51  --prop_solver_per_cl                    1000
% 39.65/5.51  --min_unsat_core                        false
% 39.65/5.51  --soft_assumptions                      false
% 39.65/5.51  --soft_lemma_size                       3
% 39.65/5.51  --prop_impl_unit_size                   0
% 39.65/5.51  --prop_impl_unit                        []
% 39.65/5.51  --share_sel_clauses                     true
% 39.65/5.51  --reset_solvers                         false
% 39.65/5.51  --bc_imp_inh                            [conj_cone]
% 39.65/5.51  --conj_cone_tolerance                   3.
% 39.65/5.51  --extra_neg_conj                        none
% 39.65/5.51  --large_theory_mode                     true
% 39.65/5.51  --prolific_symb_bound                   200
% 39.65/5.51  --lt_threshold                          2000
% 39.65/5.51  --clause_weak_htbl                      true
% 39.65/5.51  --gc_record_bc_elim                     false
% 39.65/5.51  
% 39.65/5.51  ------ Preprocessing Options
% 39.65/5.51  
% 39.65/5.51  --preprocessing_flag                    true
% 39.65/5.51  --time_out_prep_mult                    0.1
% 39.65/5.51  --splitting_mode                        input
% 39.65/5.51  --splitting_grd                         true
% 39.65/5.51  --splitting_cvd                         false
% 39.65/5.51  --splitting_cvd_svl                     false
% 39.65/5.51  --splitting_nvd                         32
% 39.65/5.51  --sub_typing                            true
% 39.65/5.51  --prep_gs_sim                           true
% 39.65/5.51  --prep_unflatten                        true
% 39.65/5.51  --prep_res_sim                          true
% 39.65/5.51  --prep_upred                            true
% 39.65/5.51  --prep_sem_filter                       exhaustive
% 39.65/5.51  --prep_sem_filter_out                   false
% 39.65/5.51  --pred_elim                             true
% 39.65/5.51  --res_sim_input                         true
% 39.65/5.51  --eq_ax_congr_red                       true
% 39.65/5.51  --pure_diseq_elim                       true
% 39.65/5.51  --brand_transform                       false
% 39.65/5.51  --non_eq_to_eq                          false
% 39.65/5.51  --prep_def_merge                        true
% 39.65/5.51  --prep_def_merge_prop_impl              false
% 39.65/5.51  --prep_def_merge_mbd                    true
% 39.65/5.51  --prep_def_merge_tr_red                 false
% 39.65/5.51  --prep_def_merge_tr_cl                  false
% 39.65/5.51  --smt_preprocessing                     true
% 39.65/5.51  --smt_ac_axioms                         fast
% 39.65/5.51  --preprocessed_out                      false
% 39.65/5.51  --preprocessed_stats                    false
% 39.65/5.51  
% 39.65/5.51  ------ Abstraction refinement Options
% 39.65/5.51  
% 39.65/5.51  --abstr_ref                             []
% 39.65/5.51  --abstr_ref_prep                        false
% 39.65/5.51  --abstr_ref_until_sat                   false
% 39.65/5.51  --abstr_ref_sig_restrict                funpre
% 39.65/5.51  --abstr_ref_af_restrict_to_split_sk     false
% 39.65/5.51  --abstr_ref_under                       []
% 39.65/5.51  
% 39.65/5.51  ------ SAT Options
% 39.65/5.51  
% 39.65/5.51  --sat_mode                              false
% 39.65/5.51  --sat_fm_restart_options                ""
% 39.65/5.51  --sat_gr_def                            false
% 39.65/5.51  --sat_epr_types                         true
% 39.65/5.51  --sat_non_cyclic_types                  false
% 39.65/5.51  --sat_finite_models                     false
% 39.65/5.51  --sat_fm_lemmas                         false
% 39.65/5.51  --sat_fm_prep                           false
% 39.65/5.51  --sat_fm_uc_incr                        true
% 39.65/5.51  --sat_out_model                         small
% 39.65/5.51  --sat_out_clauses                       false
% 39.65/5.51  
% 39.65/5.51  ------ QBF Options
% 39.65/5.51  
% 39.65/5.51  --qbf_mode                              false
% 39.65/5.51  --qbf_elim_univ                         false
% 39.65/5.51  --qbf_dom_inst                          none
% 39.65/5.51  --qbf_dom_pre_inst                      false
% 39.65/5.51  --qbf_sk_in                             false
% 39.65/5.51  --qbf_pred_elim                         true
% 39.65/5.51  --qbf_split                             512
% 39.65/5.51  
% 39.65/5.51  ------ BMC1 Options
% 39.65/5.51  
% 39.65/5.51  --bmc1_incremental                      false
% 39.65/5.51  --bmc1_axioms                           reachable_all
% 39.65/5.51  --bmc1_min_bound                        0
% 39.65/5.51  --bmc1_max_bound                        -1
% 39.65/5.51  --bmc1_max_bound_default                -1
% 39.65/5.51  --bmc1_symbol_reachability              true
% 39.65/5.51  --bmc1_property_lemmas                  false
% 39.65/5.51  --bmc1_k_induction                      false
% 39.65/5.51  --bmc1_non_equiv_states                 false
% 39.65/5.51  --bmc1_deadlock                         false
% 39.65/5.51  --bmc1_ucm                              false
% 39.65/5.51  --bmc1_add_unsat_core                   none
% 39.65/5.51  --bmc1_unsat_core_children              false
% 39.65/5.51  --bmc1_unsat_core_extrapolate_axioms    false
% 39.65/5.51  --bmc1_out_stat                         full
% 39.65/5.51  --bmc1_ground_init                      false
% 39.65/5.51  --bmc1_pre_inst_next_state              false
% 39.65/5.51  --bmc1_pre_inst_state                   false
% 39.65/5.51  --bmc1_pre_inst_reach_state             false
% 39.65/5.51  --bmc1_out_unsat_core                   false
% 39.65/5.51  --bmc1_aig_witness_out                  false
% 39.65/5.51  --bmc1_verbose                          false
% 39.65/5.51  --bmc1_dump_clauses_tptp                false
% 39.65/5.51  --bmc1_dump_unsat_core_tptp             false
% 39.65/5.51  --bmc1_dump_file                        -
% 39.65/5.51  --bmc1_ucm_expand_uc_limit              128
% 39.65/5.51  --bmc1_ucm_n_expand_iterations          6
% 39.65/5.51  --bmc1_ucm_extend_mode                  1
% 39.65/5.51  --bmc1_ucm_init_mode                    2
% 39.65/5.51  --bmc1_ucm_cone_mode                    none
% 39.65/5.51  --bmc1_ucm_reduced_relation_type        0
% 39.65/5.51  --bmc1_ucm_relax_model                  4
% 39.65/5.51  --bmc1_ucm_full_tr_after_sat            true
% 39.65/5.51  --bmc1_ucm_expand_neg_assumptions       false
% 39.65/5.51  --bmc1_ucm_layered_model                none
% 39.65/5.51  --bmc1_ucm_max_lemma_size               10
% 39.65/5.51  
% 39.65/5.51  ------ AIG Options
% 39.65/5.51  
% 39.65/5.51  --aig_mode                              false
% 39.65/5.51  
% 39.65/5.51  ------ Instantiation Options
% 39.65/5.51  
% 39.65/5.51  --instantiation_flag                    true
% 39.65/5.51  --inst_sos_flag                         true
% 39.65/5.51  --inst_sos_phase                        true
% 39.65/5.51  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 39.65/5.51  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 39.65/5.51  --inst_lit_sel_side                     num_symb
% 39.65/5.51  --inst_solver_per_active                1400
% 39.65/5.51  --inst_solver_calls_frac                1.
% 39.65/5.51  --inst_passive_queue_type               priority_queues
% 39.65/5.51  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 39.65/5.51  --inst_passive_queues_freq              [25;2]
% 39.65/5.51  --inst_dismatching                      true
% 39.65/5.51  --inst_eager_unprocessed_to_passive     true
% 39.65/5.51  --inst_prop_sim_given                   true
% 39.65/5.51  --inst_prop_sim_new                     false
% 39.65/5.51  --inst_subs_new                         false
% 39.65/5.51  --inst_eq_res_simp                      false
% 39.65/5.51  --inst_subs_given                       false
% 39.65/5.51  --inst_orphan_elimination               true
% 39.65/5.51  --inst_learning_loop_flag               true
% 39.65/5.51  --inst_learning_start                   3000
% 39.65/5.51  --inst_learning_factor                  2
% 39.65/5.51  --inst_start_prop_sim_after_learn       3
% 39.65/5.51  --inst_sel_renew                        solver
% 39.65/5.51  --inst_lit_activity_flag                true
% 39.65/5.51  --inst_restr_to_given                   false
% 39.65/5.51  --inst_activity_threshold               500
% 39.65/5.51  --inst_out_proof                        true
% 39.65/5.51  
% 39.65/5.51  ------ Resolution Options
% 39.65/5.51  
% 39.65/5.51  --resolution_flag                       true
% 39.65/5.51  --res_lit_sel                           adaptive
% 39.65/5.51  --res_lit_sel_side                      none
% 39.65/5.51  --res_ordering                          kbo
% 39.65/5.51  --res_to_prop_solver                    active
% 39.65/5.51  --res_prop_simpl_new                    false
% 39.65/5.51  --res_prop_simpl_given                  true
% 39.65/5.51  --res_passive_queue_type                priority_queues
% 39.65/5.51  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 39.65/5.51  --res_passive_queues_freq               [15;5]
% 39.65/5.51  --res_forward_subs                      full
% 39.65/5.51  --res_backward_subs                     full
% 39.65/5.51  --res_forward_subs_resolution           true
% 39.65/5.51  --res_backward_subs_resolution          true
% 39.65/5.51  --res_orphan_elimination                true
% 39.65/5.51  --res_time_limit                        2.
% 39.65/5.51  --res_out_proof                         true
% 39.65/5.51  
% 39.65/5.51  ------ Superposition Options
% 39.65/5.51  
% 39.65/5.51  --superposition_flag                    true
% 39.65/5.51  --sup_passive_queue_type                priority_queues
% 39.65/5.51  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 39.65/5.51  --sup_passive_queues_freq               [8;1;4]
% 39.65/5.51  --demod_completeness_check              fast
% 39.65/5.51  --demod_use_ground                      true
% 39.65/5.51  --sup_to_prop_solver                    passive
% 39.65/5.51  --sup_prop_simpl_new                    true
% 39.65/5.51  --sup_prop_simpl_given                  true
% 39.65/5.51  --sup_fun_splitting                     true
% 39.65/5.51  --sup_smt_interval                      50000
% 39.65/5.51  
% 39.65/5.51  ------ Superposition Simplification Setup
% 39.65/5.51  
% 39.65/5.51  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 39.65/5.51  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 39.65/5.51  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 39.65/5.51  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 39.65/5.51  --sup_full_triv                         [TrivRules;PropSubs]
% 39.65/5.51  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 39.65/5.51  --sup_full_bw                           [BwDemod;BwSubsumption]
% 39.65/5.51  --sup_immed_triv                        [TrivRules]
% 39.65/5.51  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 39.65/5.51  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 39.65/5.51  --sup_immed_bw_main                     []
% 39.65/5.51  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 39.65/5.51  --sup_input_triv                        [Unflattening;TrivRules]
% 39.65/5.51  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 39.65/5.51  --sup_input_bw                          []
% 39.65/5.51  
% 39.65/5.51  ------ Combination Options
% 39.65/5.51  
% 39.65/5.51  --comb_res_mult                         3
% 39.65/5.51  --comb_sup_mult                         2
% 39.65/5.51  --comb_inst_mult                        10
% 39.65/5.51  
% 39.65/5.51  ------ Debug Options
% 39.65/5.51  
% 39.65/5.51  --dbg_backtrace                         false
% 39.65/5.51  --dbg_dump_prop_clauses                 false
% 39.65/5.51  --dbg_dump_prop_clauses_file            -
% 39.65/5.51  --dbg_out_stat                          false
% 39.65/5.51  ------ Parsing...
% 39.65/5.51  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 39.65/5.51  
% 39.65/5.51  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 39.65/5.51  
% 39.65/5.51  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 39.65/5.51  
% 39.65/5.51  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 39.65/5.51  ------ Proving...
% 39.65/5.51  ------ Problem Properties 
% 39.65/5.51  
% 39.65/5.51  
% 39.65/5.51  clauses                                 26
% 39.65/5.51  conjectures                             4
% 39.65/5.51  EPR                                     0
% 39.65/5.51  Horn                                    20
% 39.65/5.51  unary                                   6
% 39.65/5.51  binary                                  16
% 39.65/5.51  lits                                    50
% 39.65/5.51  lits eq                                 18
% 39.65/5.51  fd_pure                                 0
% 39.65/5.51  fd_pseudo                               0
% 39.65/5.51  fd_cond                                 1
% 39.65/5.51  fd_pseudo_cond                          0
% 39.65/5.51  AC symbols                              0
% 39.65/5.51  
% 39.65/5.51  ------ Schedule dynamic 5 is on 
% 39.65/5.51  
% 39.65/5.51  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 39.65/5.51  
% 39.65/5.51  
% 39.65/5.51  ------ 
% 39.65/5.51  Current options:
% 39.65/5.51  ------ 
% 39.65/5.51  
% 39.65/5.51  ------ Input Options
% 39.65/5.51  
% 39.65/5.51  --out_options                           all
% 39.65/5.51  --tptp_safe_out                         true
% 39.65/5.51  --problem_path                          ""
% 39.65/5.51  --include_path                          ""
% 39.65/5.51  --clausifier                            res/vclausify_rel
% 39.65/5.51  --clausifier_options                    ""
% 39.65/5.51  --stdin                                 false
% 39.65/5.51  --stats_out                             all
% 39.65/5.51  
% 39.65/5.51  ------ General Options
% 39.65/5.51  
% 39.65/5.51  --fof                                   false
% 39.65/5.51  --time_out_real                         305.
% 39.65/5.51  --time_out_virtual                      -1.
% 39.65/5.51  --symbol_type_check                     false
% 39.65/5.51  --clausify_out                          false
% 39.65/5.51  --sig_cnt_out                           false
% 39.65/5.51  --trig_cnt_out                          false
% 39.65/5.51  --trig_cnt_out_tolerance                1.
% 39.65/5.51  --trig_cnt_out_sk_spl                   false
% 39.65/5.51  --abstr_cl_out                          false
% 39.65/5.51  
% 39.65/5.51  ------ Global Options
% 39.65/5.51  
% 39.65/5.51  --schedule                              default
% 39.65/5.51  --add_important_lit                     false
% 39.65/5.51  --prop_solver_per_cl                    1000
% 39.65/5.51  --min_unsat_core                        false
% 39.65/5.51  --soft_assumptions                      false
% 39.65/5.51  --soft_lemma_size                       3
% 39.65/5.51  --prop_impl_unit_size                   0
% 39.65/5.51  --prop_impl_unit                        []
% 39.65/5.51  --share_sel_clauses                     true
% 39.65/5.51  --reset_solvers                         false
% 39.65/5.51  --bc_imp_inh                            [conj_cone]
% 39.65/5.51  --conj_cone_tolerance                   3.
% 39.65/5.51  --extra_neg_conj                        none
% 39.65/5.51  --large_theory_mode                     true
% 39.65/5.51  --prolific_symb_bound                   200
% 39.65/5.51  --lt_threshold                          2000
% 39.65/5.51  --clause_weak_htbl                      true
% 39.65/5.51  --gc_record_bc_elim                     false
% 39.65/5.51  
% 39.65/5.51  ------ Preprocessing Options
% 39.65/5.51  
% 39.65/5.51  --preprocessing_flag                    true
% 39.65/5.51  --time_out_prep_mult                    0.1
% 39.65/5.51  --splitting_mode                        input
% 39.65/5.51  --splitting_grd                         true
% 39.65/5.51  --splitting_cvd                         false
% 39.65/5.51  --splitting_cvd_svl                     false
% 39.65/5.51  --splitting_nvd                         32
% 39.65/5.51  --sub_typing                            true
% 39.65/5.51  --prep_gs_sim                           true
% 39.65/5.51  --prep_unflatten                        true
% 39.65/5.51  --prep_res_sim                          true
% 39.65/5.51  --prep_upred                            true
% 39.65/5.51  --prep_sem_filter                       exhaustive
% 39.65/5.51  --prep_sem_filter_out                   false
% 39.65/5.51  --pred_elim                             true
% 39.65/5.51  --res_sim_input                         true
% 39.65/5.51  --eq_ax_congr_red                       true
% 39.65/5.51  --pure_diseq_elim                       true
% 39.65/5.51  --brand_transform                       false
% 39.65/5.51  --non_eq_to_eq                          false
% 39.65/5.51  --prep_def_merge                        true
% 39.65/5.51  --prep_def_merge_prop_impl              false
% 39.65/5.51  --prep_def_merge_mbd                    true
% 39.65/5.51  --prep_def_merge_tr_red                 false
% 39.65/5.51  --prep_def_merge_tr_cl                  false
% 39.65/5.51  --smt_preprocessing                     true
% 39.65/5.51  --smt_ac_axioms                         fast
% 39.65/5.51  --preprocessed_out                      false
% 39.65/5.51  --preprocessed_stats                    false
% 39.65/5.51  
% 39.65/5.51  ------ Abstraction refinement Options
% 39.65/5.51  
% 39.65/5.51  --abstr_ref                             []
% 39.65/5.51  --abstr_ref_prep                        false
% 39.65/5.51  --abstr_ref_until_sat                   false
% 39.65/5.51  --abstr_ref_sig_restrict                funpre
% 39.65/5.51  --abstr_ref_af_restrict_to_split_sk     false
% 39.65/5.51  --abstr_ref_under                       []
% 39.65/5.51  
% 39.65/5.51  ------ SAT Options
% 39.65/5.51  
% 39.65/5.51  --sat_mode                              false
% 39.65/5.51  --sat_fm_restart_options                ""
% 39.65/5.51  --sat_gr_def                            false
% 39.65/5.51  --sat_epr_types                         true
% 39.65/5.51  --sat_non_cyclic_types                  false
% 39.65/5.51  --sat_finite_models                     false
% 39.65/5.51  --sat_fm_lemmas                         false
% 39.65/5.51  --sat_fm_prep                           false
% 39.65/5.51  --sat_fm_uc_incr                        true
% 39.65/5.51  --sat_out_model                         small
% 39.65/5.51  --sat_out_clauses                       false
% 39.65/5.51  
% 39.65/5.51  ------ QBF Options
% 39.65/5.51  
% 39.65/5.51  --qbf_mode                              false
% 39.65/5.51  --qbf_elim_univ                         false
% 39.65/5.51  --qbf_dom_inst                          none
% 39.65/5.51  --qbf_dom_pre_inst                      false
% 39.65/5.51  --qbf_sk_in                             false
% 39.65/5.51  --qbf_pred_elim                         true
% 39.65/5.51  --qbf_split                             512
% 39.65/5.51  
% 39.65/5.51  ------ BMC1 Options
% 39.65/5.51  
% 39.65/5.51  --bmc1_incremental                      false
% 39.65/5.51  --bmc1_axioms                           reachable_all
% 39.65/5.51  --bmc1_min_bound                        0
% 39.65/5.51  --bmc1_max_bound                        -1
% 39.65/5.51  --bmc1_max_bound_default                -1
% 39.65/5.51  --bmc1_symbol_reachability              true
% 39.65/5.51  --bmc1_property_lemmas                  false
% 39.65/5.51  --bmc1_k_induction                      false
% 39.65/5.51  --bmc1_non_equiv_states                 false
% 39.65/5.51  --bmc1_deadlock                         false
% 39.65/5.51  --bmc1_ucm                              false
% 39.65/5.51  --bmc1_add_unsat_core                   none
% 39.65/5.51  --bmc1_unsat_core_children              false
% 39.65/5.51  --bmc1_unsat_core_extrapolate_axioms    false
% 39.65/5.51  --bmc1_out_stat                         full
% 39.65/5.51  --bmc1_ground_init                      false
% 39.65/5.51  --bmc1_pre_inst_next_state              false
% 39.65/5.51  --bmc1_pre_inst_state                   false
% 39.65/5.51  --bmc1_pre_inst_reach_state             false
% 39.65/5.51  --bmc1_out_unsat_core                   false
% 39.65/5.51  --bmc1_aig_witness_out                  false
% 39.65/5.51  --bmc1_verbose                          false
% 39.65/5.51  --bmc1_dump_clauses_tptp                false
% 39.65/5.51  --bmc1_dump_unsat_core_tptp             false
% 39.65/5.51  --bmc1_dump_file                        -
% 39.65/5.51  --bmc1_ucm_expand_uc_limit              128
% 39.65/5.51  --bmc1_ucm_n_expand_iterations          6
% 39.65/5.51  --bmc1_ucm_extend_mode                  1
% 39.65/5.51  --bmc1_ucm_init_mode                    2
% 39.65/5.51  --bmc1_ucm_cone_mode                    none
% 39.65/5.51  --bmc1_ucm_reduced_relation_type        0
% 39.65/5.51  --bmc1_ucm_relax_model                  4
% 39.65/5.51  --bmc1_ucm_full_tr_after_sat            true
% 39.65/5.51  --bmc1_ucm_expand_neg_assumptions       false
% 39.65/5.51  --bmc1_ucm_layered_model                none
% 39.65/5.51  --bmc1_ucm_max_lemma_size               10
% 39.65/5.51  
% 39.65/5.51  ------ AIG Options
% 39.65/5.51  
% 39.65/5.51  --aig_mode                              false
% 39.65/5.51  
% 39.65/5.51  ------ Instantiation Options
% 39.65/5.51  
% 39.65/5.51  --instantiation_flag                    true
% 39.65/5.51  --inst_sos_flag                         true
% 39.65/5.51  --inst_sos_phase                        true
% 39.65/5.51  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 39.65/5.51  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 39.65/5.51  --inst_lit_sel_side                     none
% 39.65/5.51  --inst_solver_per_active                1400
% 39.65/5.51  --inst_solver_calls_frac                1.
% 39.65/5.51  --inst_passive_queue_type               priority_queues
% 39.65/5.51  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 39.65/5.51  --inst_passive_queues_freq              [25;2]
% 39.65/5.51  --inst_dismatching                      true
% 39.65/5.51  --inst_eager_unprocessed_to_passive     true
% 39.65/5.51  --inst_prop_sim_given                   true
% 39.65/5.51  --inst_prop_sim_new                     false
% 39.65/5.51  --inst_subs_new                         false
% 39.65/5.51  --inst_eq_res_simp                      false
% 39.65/5.51  --inst_subs_given                       false
% 39.65/5.51  --inst_orphan_elimination               true
% 39.65/5.51  --inst_learning_loop_flag               true
% 39.65/5.51  --inst_learning_start                   3000
% 39.65/5.51  --inst_learning_factor                  2
% 39.65/5.51  --inst_start_prop_sim_after_learn       3
% 39.65/5.51  --inst_sel_renew                        solver
% 39.65/5.51  --inst_lit_activity_flag                true
% 39.65/5.51  --inst_restr_to_given                   false
% 39.65/5.51  --inst_activity_threshold               500
% 39.65/5.51  --inst_out_proof                        true
% 39.65/5.51  
% 39.65/5.51  ------ Resolution Options
% 39.65/5.51  
% 39.65/5.51  --resolution_flag                       false
% 39.65/5.51  --res_lit_sel                           adaptive
% 39.65/5.51  --res_lit_sel_side                      none
% 39.65/5.51  --res_ordering                          kbo
% 39.65/5.51  --res_to_prop_solver                    active
% 39.65/5.51  --res_prop_simpl_new                    false
% 39.65/5.51  --res_prop_simpl_given                  true
% 39.65/5.51  --res_passive_queue_type                priority_queues
% 39.65/5.51  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 39.65/5.51  --res_passive_queues_freq               [15;5]
% 39.65/5.51  --res_forward_subs                      full
% 39.65/5.51  --res_backward_subs                     full
% 39.65/5.51  --res_forward_subs_resolution           true
% 39.65/5.51  --res_backward_subs_resolution          true
% 39.65/5.51  --res_orphan_elimination                true
% 39.65/5.51  --res_time_limit                        2.
% 39.65/5.51  --res_out_proof                         true
% 39.65/5.51  
% 39.65/5.51  ------ Superposition Options
% 39.65/5.51  
% 39.65/5.51  --superposition_flag                    true
% 39.65/5.51  --sup_passive_queue_type                priority_queues
% 39.65/5.51  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 39.65/5.51  --sup_passive_queues_freq               [8;1;4]
% 39.65/5.51  --demod_completeness_check              fast
% 39.65/5.51  --demod_use_ground                      true
% 39.65/5.51  --sup_to_prop_solver                    passive
% 39.65/5.51  --sup_prop_simpl_new                    true
% 39.65/5.51  --sup_prop_simpl_given                  true
% 39.65/5.51  --sup_fun_splitting                     true
% 39.65/5.51  --sup_smt_interval                      50000
% 39.65/5.51  
% 39.65/5.51  ------ Superposition Simplification Setup
% 39.65/5.51  
% 39.65/5.51  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 39.65/5.51  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 39.65/5.51  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 39.65/5.51  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 39.65/5.51  --sup_full_triv                         [TrivRules;PropSubs]
% 39.65/5.51  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 39.65/5.51  --sup_full_bw                           [BwDemod;BwSubsumption]
% 39.65/5.51  --sup_immed_triv                        [TrivRules]
% 39.65/5.51  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 39.65/5.51  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 39.65/5.51  --sup_immed_bw_main                     []
% 39.65/5.51  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 39.65/5.51  --sup_input_triv                        [Unflattening;TrivRules]
% 39.65/5.51  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 39.65/5.51  --sup_input_bw                          []
% 39.65/5.51  
% 39.65/5.51  ------ Combination Options
% 39.65/5.51  
% 39.65/5.51  --comb_res_mult                         3
% 39.65/5.51  --comb_sup_mult                         2
% 39.65/5.51  --comb_inst_mult                        10
% 39.65/5.51  
% 39.65/5.51  ------ Debug Options
% 39.65/5.51  
% 39.65/5.51  --dbg_backtrace                         false
% 39.65/5.51  --dbg_dump_prop_clauses                 false
% 39.65/5.51  --dbg_dump_prop_clauses_file            -
% 39.65/5.51  --dbg_out_stat                          false
% 39.65/5.51  
% 39.65/5.51  
% 39.65/5.51  
% 39.65/5.51  
% 39.65/5.51  ------ Proving...
% 39.65/5.51  
% 39.65/5.51  
% 39.65/5.51  % SZS status Theorem for theBenchmark.p
% 39.65/5.51  
% 39.65/5.51  % SZS output start CNFRefutation for theBenchmark.p
% 39.65/5.51  
% 39.65/5.51  fof(f24,conjecture,(
% 39.65/5.51    ! [X0,X1,X2] : ~(~(k1_xboole_0 = X2 & k1_tarski(X0) = X1) & ~(k1_tarski(X0) = X2 & k1_xboole_0 = X1) & ~(k1_tarski(X0) = X2 & k1_tarski(X0) = X1) & k2_xboole_0(X1,X2) = k1_tarski(X0))),
% 39.65/5.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 39.65/5.51  
% 39.65/5.51  fof(f25,negated_conjecture,(
% 39.65/5.51    ~! [X0,X1,X2] : ~(~(k1_xboole_0 = X2 & k1_tarski(X0) = X1) & ~(k1_tarski(X0) = X2 & k1_xboole_0 = X1) & ~(k1_tarski(X0) = X2 & k1_tarski(X0) = X1) & k2_xboole_0(X1,X2) = k1_tarski(X0))),
% 39.65/5.51    inference(negated_conjecture,[],[f24])).
% 39.65/5.51  
% 39.65/5.51  fof(f38,plain,(
% 39.65/5.51    ? [X0,X1,X2] : ((k1_xboole_0 != X2 | k1_tarski(X0) != X1) & (k1_tarski(X0) != X2 | k1_xboole_0 != X1) & (k1_tarski(X0) != X2 | k1_tarski(X0) != X1) & k2_xboole_0(X1,X2) = k1_tarski(X0))),
% 39.65/5.51    inference(ennf_transformation,[],[f25])).
% 39.65/5.51  
% 39.65/5.51  fof(f46,plain,(
% 39.65/5.51    ? [X0,X1,X2] : ((k1_xboole_0 != X2 | k1_tarski(X0) != X1) & (k1_tarski(X0) != X2 | k1_xboole_0 != X1) & (k1_tarski(X0) != X2 | k1_tarski(X0) != X1) & k2_xboole_0(X1,X2) = k1_tarski(X0)) => ((k1_xboole_0 != sK4 | k1_tarski(sK2) != sK3) & (k1_tarski(sK2) != sK4 | k1_xboole_0 != sK3) & (k1_tarski(sK2) != sK4 | k1_tarski(sK2) != sK3) & k2_xboole_0(sK3,sK4) = k1_tarski(sK2))),
% 39.65/5.51    introduced(choice_axiom,[])).
% 39.65/5.51  
% 39.65/5.51  fof(f47,plain,(
% 39.65/5.51    (k1_xboole_0 != sK4 | k1_tarski(sK2) != sK3) & (k1_tarski(sK2) != sK4 | k1_xboole_0 != sK3) & (k1_tarski(sK2) != sK4 | k1_tarski(sK2) != sK3) & k2_xboole_0(sK3,sK4) = k1_tarski(sK2)),
% 39.65/5.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f38,f46])).
% 39.65/5.51  
% 39.65/5.51  fof(f77,plain,(
% 39.65/5.51    k2_xboole_0(sK3,sK4) = k1_tarski(sK2)),
% 39.65/5.51    inference(cnf_transformation,[],[f47])).
% 39.65/5.51  
% 39.65/5.51  fof(f23,axiom,(
% 39.65/5.51    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 39.65/5.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 39.65/5.51  
% 39.65/5.51  fof(f76,plain,(
% 39.65/5.51    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 39.65/5.51    inference(cnf_transformation,[],[f23])).
% 39.65/5.51  
% 39.65/5.51  fof(f83,plain,(
% 39.65/5.51    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k4_enumset1(X0,X0,X0,X0,X0,X1))) )),
% 39.65/5.51    inference(definition_unfolding,[],[f76,f82])).
% 39.65/5.51  
% 39.65/5.51  fof(f17,axiom,(
% 39.65/5.51    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 39.65/5.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 39.65/5.51  
% 39.65/5.51  fof(f70,plain,(
% 39.65/5.51    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 39.65/5.51    inference(cnf_transformation,[],[f17])).
% 39.65/5.51  
% 39.65/5.51  fof(f18,axiom,(
% 39.65/5.51    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 39.65/5.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 39.65/5.51  
% 39.65/5.51  fof(f71,plain,(
% 39.65/5.51    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 39.65/5.51    inference(cnf_transformation,[],[f18])).
% 39.65/5.51  
% 39.65/5.51  fof(f20,axiom,(
% 39.65/5.51    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2)),
% 39.65/5.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 39.65/5.51  
% 39.65/5.51  fof(f73,plain,(
% 39.65/5.51    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2)) )),
% 39.65/5.51    inference(cnf_transformation,[],[f20])).
% 39.65/5.51  
% 39.65/5.51  fof(f19,axiom,(
% 39.65/5.51    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)),
% 39.65/5.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 39.65/5.51  
% 39.65/5.51  fof(f72,plain,(
% 39.65/5.51    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 39.65/5.51    inference(cnf_transformation,[],[f19])).
% 39.65/5.51  
% 39.65/5.51  fof(f81,plain,(
% 39.65/5.51    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k4_enumset1(X0,X0,X0,X0,X1,X2)) )),
% 39.65/5.51    inference(definition_unfolding,[],[f73,f72])).
% 39.65/5.51  
% 39.65/5.51  fof(f82,plain,(
% 39.65/5.51    ( ! [X0,X1] : (k2_tarski(X0,X1) = k4_enumset1(X0,X0,X0,X0,X0,X1)) )),
% 39.65/5.51    inference(definition_unfolding,[],[f71,f81])).
% 39.65/5.51  
% 39.65/5.51  fof(f84,plain,(
% 39.65/5.51    ( ! [X0] : (k1_tarski(X0) = k4_enumset1(X0,X0,X0,X0,X0,X0)) )),
% 39.65/5.51    inference(definition_unfolding,[],[f70,f82])).
% 39.65/5.51  
% 39.65/5.51  fof(f98,plain,(
% 39.65/5.51    k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK2) = k3_tarski(k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK4))),
% 39.65/5.51    inference(definition_unfolding,[],[f77,f83,f84])).
% 39.65/5.51  
% 39.65/5.51  fof(f15,axiom,(
% 39.65/5.51    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 39.65/5.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 39.65/5.51  
% 39.65/5.51  fof(f67,plain,(
% 39.65/5.51    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 39.65/5.51    inference(cnf_transformation,[],[f15])).
% 39.65/5.51  
% 39.65/5.51  fof(f90,plain,(
% 39.65/5.51    ( ! [X0,X1] : (r1_tarski(X0,k3_tarski(k4_enumset1(X0,X0,X0,X0,X0,X1)))) )),
% 39.65/5.51    inference(definition_unfolding,[],[f67,f83])).
% 39.65/5.51  
% 39.65/5.51  fof(f11,axiom,(
% 39.65/5.51    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 39.65/5.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 39.65/5.51  
% 39.65/5.51  fof(f35,plain,(
% 39.65/5.51    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 39.65/5.51    inference(ennf_transformation,[],[f11])).
% 39.65/5.51  
% 39.65/5.51  fof(f63,plain,(
% 39.65/5.51    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 39.65/5.51    inference(cnf_transformation,[],[f35])).
% 39.65/5.51  
% 39.65/5.51  fof(f5,axiom,(
% 39.65/5.51    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 39.65/5.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 39.65/5.51  
% 39.65/5.51  fof(f26,plain,(
% 39.65/5.51    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X3] : ~r2_hidden(X3,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 39.65/5.51    inference(rectify,[],[f5])).
% 39.65/5.51  
% 39.65/5.51  fof(f31,plain,(
% 39.65/5.51    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 39.65/5.51    inference(ennf_transformation,[],[f26])).
% 39.65/5.51  
% 39.65/5.51  fof(f42,plain,(
% 39.65/5.51    ! [X1,X0] : (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) => r2_hidden(sK1(X0,X1),k3_xboole_0(X0,X1)))),
% 39.65/5.51    introduced(choice_axiom,[])).
% 39.65/5.51  
% 39.65/5.51  fof(f43,plain,(
% 39.65/5.51    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (r2_hidden(sK1(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 39.65/5.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f31,f42])).
% 39.65/5.51  
% 39.65/5.51  fof(f55,plain,(
% 39.65/5.51    ( ! [X0,X1] : (r2_hidden(sK1(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)) )),
% 39.65/5.51    inference(cnf_transformation,[],[f43])).
% 39.65/5.51  
% 39.65/5.51  fof(f22,axiom,(
% 39.65/5.51    ! [X0,X1] : (r2_hidden(X0,X1) => k3_xboole_0(X1,k1_tarski(X0)) = k1_tarski(X0))),
% 39.65/5.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 39.65/5.51  
% 39.65/5.51  fof(f37,plain,(
% 39.65/5.51    ! [X0,X1] : (k3_xboole_0(X1,k1_tarski(X0)) = k1_tarski(X0) | ~r2_hidden(X0,X1))),
% 39.65/5.51    inference(ennf_transformation,[],[f22])).
% 39.65/5.51  
% 39.65/5.51  fof(f75,plain,(
% 39.65/5.51    ( ! [X0,X1] : (k3_xboole_0(X1,k1_tarski(X0)) = k1_tarski(X0) | ~r2_hidden(X0,X1)) )),
% 39.65/5.51    inference(cnf_transformation,[],[f37])).
% 39.65/5.51  
% 39.65/5.51  fof(f94,plain,(
% 39.65/5.51    ( ! [X0,X1] : (k3_xboole_0(X1,k4_enumset1(X0,X0,X0,X0,X0,X0)) = k4_enumset1(X0,X0,X0,X0,X0,X0) | ~r2_hidden(X0,X1)) )),
% 39.65/5.51    inference(definition_unfolding,[],[f75,f84,f84])).
% 39.65/5.51  
% 39.65/5.51  fof(f1,axiom,(
% 39.65/5.51    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 39.65/5.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 39.65/5.51  
% 39.65/5.51  fof(f48,plain,(
% 39.65/5.51    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 39.65/5.51    inference(cnf_transformation,[],[f1])).
% 39.65/5.51  
% 39.65/5.51  fof(f12,axiom,(
% 39.65/5.51    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0),
% 39.65/5.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 39.65/5.51  
% 39.65/5.51  fof(f64,plain,(
% 39.65/5.51    ( ! [X0] : (k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0) )),
% 39.65/5.51    inference(cnf_transformation,[],[f12])).
% 39.65/5.51  
% 39.65/5.51  fof(f13,axiom,(
% 39.65/5.51    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 39.65/5.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 39.65/5.51  
% 39.65/5.51  fof(f65,plain,(
% 39.65/5.51    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 39.65/5.51    inference(cnf_transformation,[],[f13])).
% 39.65/5.51  
% 39.65/5.51  fof(f7,axiom,(
% 39.65/5.51    ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1)),
% 39.65/5.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 39.65/5.51  
% 39.65/5.51  fof(f59,plain,(
% 39.65/5.51    ( ! [X0,X1] : (k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1)) )),
% 39.65/5.51    inference(cnf_transformation,[],[f7])).
% 39.65/5.51  
% 39.65/5.51  fof(f89,plain,(
% 39.65/5.51    ( ! [X0,X1] : (r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X0)) )),
% 39.65/5.51    inference(definition_unfolding,[],[f65,f59])).
% 39.65/5.51  
% 39.65/5.51  fof(f14,axiom,(
% 39.65/5.51    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 39.65/5.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 39.65/5.51  
% 39.65/5.51  fof(f66,plain,(
% 39.65/5.51    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 39.65/5.51    inference(cnf_transformation,[],[f14])).
% 39.65/5.51  
% 39.65/5.51  fof(f10,axiom,(
% 39.65/5.51    ! [X0,X1,X2] : (r1_tarski(X0,k3_xboole_0(X1,X2)) => r1_tarski(X0,X1))),
% 39.65/5.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 39.65/5.51  
% 39.65/5.51  fof(f34,plain,(
% 39.65/5.51    ! [X0,X1,X2] : (r1_tarski(X0,X1) | ~r1_tarski(X0,k3_xboole_0(X1,X2)))),
% 39.65/5.51    inference(ennf_transformation,[],[f10])).
% 39.65/5.51  
% 39.65/5.51  fof(f62,plain,(
% 39.65/5.51    ( ! [X2,X0,X1] : (r1_tarski(X0,X1) | ~r1_tarski(X0,k3_xboole_0(X1,X2))) )),
% 39.65/5.51    inference(cnf_transformation,[],[f34])).
% 39.65/5.51  
% 39.65/5.51  fof(f56,plain,(
% 39.65/5.51    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,k3_xboole_0(X0,X1))) )),
% 39.65/5.51    inference(cnf_transformation,[],[f43])).
% 39.65/5.51  
% 39.65/5.51  fof(f80,plain,(
% 39.65/5.51    k1_xboole_0 != sK4 | k1_tarski(sK2) != sK3),
% 39.65/5.51    inference(cnf_transformation,[],[f47])).
% 39.65/5.51  
% 39.65/5.51  fof(f95,plain,(
% 39.65/5.51    k1_xboole_0 != sK4 | k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK2) != sK3),
% 39.65/5.51    inference(definition_unfolding,[],[f80,f84])).
% 39.65/5.51  
% 39.65/5.51  fof(f6,axiom,(
% 39.65/5.51    ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,X1) <=> r1_tarski(X0,X1))),
% 39.65/5.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 39.65/5.51  
% 39.65/5.51  fof(f44,plain,(
% 39.65/5.51    ! [X0,X1] : ((k1_xboole_0 = k4_xboole_0(X0,X1) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k1_xboole_0 != k4_xboole_0(X0,X1)))),
% 39.65/5.51    inference(nnf_transformation,[],[f6])).
% 39.65/5.51  
% 39.65/5.51  fof(f58,plain,(
% 39.65/5.51    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,X1) | ~r1_tarski(X0,X1)) )),
% 39.65/5.51    inference(cnf_transformation,[],[f44])).
% 39.65/5.51  
% 39.65/5.51  fof(f85,plain,(
% 39.65/5.51    ( ! [X0,X1] : (k1_xboole_0 = k5_xboole_0(X0,k3_xboole_0(X0,X1)) | ~r1_tarski(X0,X1)) )),
% 39.65/5.51    inference(definition_unfolding,[],[f58,f59])).
% 39.65/5.51  
% 39.65/5.51  fof(f2,axiom,(
% 39.65/5.51    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 39.65/5.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 39.65/5.51  
% 39.65/5.51  fof(f27,plain,(
% 39.65/5.51    ! [X0] : (! [X1] : ~r2_hidden(X1,X0) => v1_xboole_0(X0))),
% 39.65/5.51    inference(unused_predicate_definition_removal,[],[f2])).
% 39.65/5.51  
% 39.65/5.51  fof(f28,plain,(
% 39.65/5.51    ! [X0] : (v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0))),
% 39.65/5.51    inference(ennf_transformation,[],[f27])).
% 39.65/5.51  
% 39.65/5.51  fof(f39,plain,(
% 39.65/5.51    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK0(X0),X0))),
% 39.65/5.51    introduced(choice_axiom,[])).
% 39.65/5.51  
% 39.65/5.51  fof(f40,plain,(
% 39.65/5.51    ! [X0] : (v1_xboole_0(X0) | r2_hidden(sK0(X0),X0))),
% 39.65/5.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f28,f39])).
% 39.65/5.51  
% 39.65/5.51  fof(f49,plain,(
% 39.65/5.51    ( ! [X0] : (v1_xboole_0(X0) | r2_hidden(sK0(X0),X0)) )),
% 39.65/5.51    inference(cnf_transformation,[],[f40])).
% 39.65/5.51  
% 39.65/5.51  fof(f3,axiom,(
% 39.65/5.51    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 39.65/5.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 39.65/5.51  
% 39.65/5.51  fof(f29,plain,(
% 39.65/5.51    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 39.65/5.51    inference(ennf_transformation,[],[f3])).
% 39.65/5.51  
% 39.65/5.51  fof(f50,plain,(
% 39.65/5.51    ( ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0)) )),
% 39.65/5.51    inference(cnf_transformation,[],[f29])).
% 39.65/5.51  
% 39.65/5.51  fof(f16,axiom,(
% 39.65/5.51    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k4_xboole_0(X0,X1) = X0)),
% 39.65/5.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 39.65/5.51  
% 39.65/5.51  fof(f45,plain,(
% 39.65/5.51    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) != X0) & (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)))),
% 39.65/5.51    inference(nnf_transformation,[],[f16])).
% 39.65/5.51  
% 39.65/5.51  fof(f69,plain,(
% 39.65/5.51    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) != X0) )),
% 39.65/5.51    inference(cnf_transformation,[],[f45])).
% 39.65/5.51  
% 39.65/5.51  fof(f91,plain,(
% 39.65/5.51    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X0) )),
% 39.65/5.51    inference(definition_unfolding,[],[f69,f59])).
% 39.65/5.51  
% 39.65/5.51  fof(f21,axiom,(
% 39.65/5.51    ! [X0,X1] : (~r2_hidden(X0,X1) => r1_xboole_0(k1_tarski(X0),X1))),
% 39.65/5.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 39.65/5.51  
% 39.65/5.51  fof(f36,plain,(
% 39.65/5.51    ! [X0,X1] : (r1_xboole_0(k1_tarski(X0),X1) | r2_hidden(X0,X1))),
% 39.65/5.51    inference(ennf_transformation,[],[f21])).
% 39.65/5.51  
% 39.65/5.51  fof(f74,plain,(
% 39.65/5.51    ( ! [X0,X1] : (r1_xboole_0(k1_tarski(X0),X1) | r2_hidden(X0,X1)) )),
% 39.65/5.51    inference(cnf_transformation,[],[f36])).
% 39.65/5.51  
% 39.65/5.51  fof(f93,plain,(
% 39.65/5.51    ( ! [X0,X1] : (r1_xboole_0(k4_enumset1(X0,X0,X0,X0,X0,X0),X1) | r2_hidden(X0,X1)) )),
% 39.65/5.51    inference(definition_unfolding,[],[f74,f84])).
% 39.65/5.51  
% 39.65/5.51  fof(f8,axiom,(
% 39.65/5.51    ! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_tarski(X0,k2_xboole_0(X2,X1)))),
% 39.65/5.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 39.65/5.51  
% 39.65/5.51  fof(f32,plain,(
% 39.65/5.51    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X2,X1)) | ~r1_tarski(X0,X1))),
% 39.65/5.51    inference(ennf_transformation,[],[f8])).
% 39.65/5.51  
% 39.65/5.51  fof(f60,plain,(
% 39.65/5.51    ( ! [X2,X0,X1] : (r1_tarski(X0,k2_xboole_0(X2,X1)) | ~r1_tarski(X0,X1)) )),
% 39.65/5.51    inference(cnf_transformation,[],[f32])).
% 39.65/5.51  
% 39.65/5.51  fof(f87,plain,(
% 39.65/5.51    ( ! [X2,X0,X1] : (r1_tarski(X0,k3_tarski(k4_enumset1(X2,X2,X2,X2,X2,X1))) | ~r1_tarski(X0,X1)) )),
% 39.65/5.51    inference(definition_unfolding,[],[f60,f83])).
% 39.65/5.51  
% 39.65/5.51  fof(f78,plain,(
% 39.65/5.51    k1_tarski(sK2) != sK4 | k1_tarski(sK2) != sK3),
% 39.65/5.51    inference(cnf_transformation,[],[f47])).
% 39.65/5.51  
% 39.65/5.51  fof(f97,plain,(
% 39.65/5.51    k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK2) != sK4 | k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK2) != sK3),
% 39.65/5.51    inference(definition_unfolding,[],[f78,f84,f84])).
% 39.65/5.51  
% 39.65/5.51  fof(f79,plain,(
% 39.65/5.51    k1_tarski(sK2) != sK4 | k1_xboole_0 != sK3),
% 39.65/5.51    inference(cnf_transformation,[],[f47])).
% 39.65/5.51  
% 39.65/5.51  fof(f96,plain,(
% 39.65/5.51    k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK2) != sK4 | k1_xboole_0 != sK3),
% 39.65/5.51    inference(definition_unfolding,[],[f79,f84])).
% 39.65/5.51  
% 39.65/5.51  fof(f68,plain,(
% 39.65/5.51    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)) )),
% 39.65/5.51    inference(cnf_transformation,[],[f45])).
% 39.65/5.51  
% 39.65/5.51  fof(f92,plain,(
% 39.65/5.51    ( ! [X0,X1] : (k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 | ~r1_xboole_0(X0,X1)) )),
% 39.65/5.51    inference(definition_unfolding,[],[f68,f59])).
% 39.65/5.51  
% 39.65/5.51  fof(f9,axiom,(
% 39.65/5.51    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 39.65/5.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 39.65/5.51  
% 39.65/5.51  fof(f33,plain,(
% 39.65/5.51    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 39.65/5.51    inference(ennf_transformation,[],[f9])).
% 39.65/5.51  
% 39.65/5.51  fof(f61,plain,(
% 39.65/5.51    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1)) )),
% 39.65/5.51    inference(cnf_transformation,[],[f33])).
% 39.65/5.51  
% 39.65/5.51  fof(f88,plain,(
% 39.65/5.51    ( ! [X0,X1] : (k3_tarski(k4_enumset1(X0,X0,X0,X0,X0,X1)) = X1 | ~r1_tarski(X0,X1)) )),
% 39.65/5.51    inference(definition_unfolding,[],[f61,f83])).
% 39.65/5.51  
% 39.65/5.51  cnf(c_26,negated_conjecture,
% 39.65/5.51      ( k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK2) = k3_tarski(k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK4)) ),
% 39.65/5.51      inference(cnf_transformation,[],[f98]) ).
% 39.65/5.51  
% 39.65/5.51  cnf(c_18,plain,
% 39.65/5.51      ( r1_tarski(X0,k3_tarski(k4_enumset1(X0,X0,X0,X0,X0,X1))) ),
% 39.65/5.51      inference(cnf_transformation,[],[f90]) ).
% 39.65/5.51  
% 39.65/5.51  cnf(c_1084,plain,
% 39.65/5.51      ( r1_tarski(X0,k3_tarski(k4_enumset1(X0,X0,X0,X0,X0,X1))) = iProver_top ),
% 39.65/5.51      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 39.65/5.51  
% 39.65/5.51  cnf(c_1713,plain,
% 39.65/5.51      ( r1_tarski(sK3,k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK2)) = iProver_top ),
% 39.65/5.51      inference(superposition,[status(thm)],[c_26,c_1084]) ).
% 39.65/5.51  
% 39.65/5.51  cnf(c_14,plain,
% 39.65/5.51      ( ~ r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0 ),
% 39.65/5.51      inference(cnf_transformation,[],[f63]) ).
% 39.65/5.51  
% 39.65/5.51  cnf(c_1086,plain,
% 39.65/5.51      ( k3_xboole_0(X0,X1) = X0 | r1_tarski(X0,X1) != iProver_top ),
% 39.65/5.51      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 39.65/5.51  
% 39.65/5.51  cnf(c_1805,plain,
% 39.65/5.51      ( k3_xboole_0(sK3,k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK2)) = sK3 ),
% 39.65/5.51      inference(superposition,[status(thm)],[c_1713,c_1086]) ).
% 39.65/5.51  
% 39.65/5.51  cnf(c_8,plain,
% 39.65/5.51      ( r1_xboole_0(X0,X1) | r2_hidden(sK1(X0,X1),k3_xboole_0(X0,X1)) ),
% 39.65/5.51      inference(cnf_transformation,[],[f55]) ).
% 39.65/5.51  
% 39.65/5.51  cnf(c_1092,plain,
% 39.65/5.51      ( r1_xboole_0(X0,X1) = iProver_top
% 39.65/5.51      | r2_hidden(sK1(X0,X1),k3_xboole_0(X0,X1)) = iProver_top ),
% 39.65/5.51      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 39.65/5.51  
% 39.65/5.51  cnf(c_5288,plain,
% 39.65/5.51      ( r1_xboole_0(sK3,k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK2)) = iProver_top
% 39.65/5.51      | r2_hidden(sK1(sK3,k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK2)),sK3) = iProver_top ),
% 39.65/5.51      inference(superposition,[status(thm)],[c_1805,c_1092]) ).
% 39.65/5.51  
% 39.65/5.51  cnf(c_22,plain,
% 39.65/5.51      ( ~ r2_hidden(X0,X1)
% 39.65/5.51      | k3_xboole_0(X1,k4_enumset1(X0,X0,X0,X0,X0,X0)) = k4_enumset1(X0,X0,X0,X0,X0,X0) ),
% 39.65/5.51      inference(cnf_transformation,[],[f94]) ).
% 39.65/5.51  
% 39.65/5.51  cnf(c_1080,plain,
% 39.65/5.51      ( k3_xboole_0(X0,k4_enumset1(X1,X1,X1,X1,X1,X1)) = k4_enumset1(X1,X1,X1,X1,X1,X1)
% 39.65/5.51      | r2_hidden(X1,X0) != iProver_top ),
% 39.65/5.51      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 39.65/5.51  
% 39.65/5.51  cnf(c_5296,plain,
% 39.65/5.51      ( k3_xboole_0(k3_xboole_0(X0,X1),k4_enumset1(sK1(X0,X1),sK1(X0,X1),sK1(X0,X1),sK1(X0,X1),sK1(X0,X1),sK1(X0,X1))) = k4_enumset1(sK1(X0,X1),sK1(X0,X1),sK1(X0,X1),sK1(X0,X1),sK1(X0,X1),sK1(X0,X1))
% 39.65/5.51      | r1_xboole_0(X0,X1) = iProver_top ),
% 39.65/5.51      inference(superposition,[status(thm)],[c_1092,c_1080]) ).
% 39.65/5.51  
% 39.65/5.51  cnf(c_1802,plain,
% 39.65/5.51      ( k3_xboole_0(X0,k3_tarski(k4_enumset1(X0,X0,X0,X0,X0,X1))) = X0 ),
% 39.65/5.51      inference(superposition,[status(thm)],[c_1084,c_1086]) ).
% 39.65/5.51  
% 39.65/5.51  cnf(c_0,plain,
% 39.65/5.51      ( k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
% 39.65/5.51      inference(cnf_transformation,[],[f48]) ).
% 39.65/5.51  
% 39.65/5.51  cnf(c_15,plain,
% 39.65/5.51      ( k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
% 39.65/5.51      inference(cnf_transformation,[],[f64]) ).
% 39.65/5.51  
% 39.65/5.51  cnf(c_16,plain,
% 39.65/5.51      ( r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X0) ),
% 39.65/5.51      inference(cnf_transformation,[],[f89]) ).
% 39.65/5.51  
% 39.65/5.51  cnf(c_1085,plain,
% 39.65/5.51      ( r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X0) = iProver_top ),
% 39.65/5.51      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 39.65/5.51  
% 39.65/5.51  cnf(c_1470,plain,
% 39.65/5.51      ( r1_tarski(k5_xboole_0(X0,k1_xboole_0),X0) = iProver_top ),
% 39.65/5.51      inference(superposition,[status(thm)],[c_15,c_1085]) ).
% 39.65/5.51  
% 39.65/5.51  cnf(c_17,plain,
% 39.65/5.51      ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
% 39.65/5.51      inference(cnf_transformation,[],[f66]) ).
% 39.65/5.51  
% 39.65/5.51  cnf(c_1473,plain,
% 39.65/5.51      ( r1_tarski(X0,X0) = iProver_top ),
% 39.65/5.51      inference(light_normalisation,[status(thm)],[c_1470,c_17]) ).
% 39.65/5.51  
% 39.65/5.51  cnf(c_13,plain,
% 39.65/5.51      ( r1_tarski(X0,X1) | ~ r1_tarski(X0,k3_xboole_0(X1,X2)) ),
% 39.65/5.51      inference(cnf_transformation,[],[f62]) ).
% 39.65/5.51  
% 39.65/5.51  cnf(c_1087,plain,
% 39.65/5.51      ( r1_tarski(X0,X1) = iProver_top
% 39.65/5.51      | r1_tarski(X0,k3_xboole_0(X1,X2)) != iProver_top ),
% 39.65/5.51      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 39.65/5.51  
% 39.65/5.51  cnf(c_2417,plain,
% 39.65/5.51      ( r1_tarski(X0,X1) = iProver_top
% 39.65/5.51      | r1_tarski(X0,k3_xboole_0(X2,X1)) != iProver_top ),
% 39.65/5.51      inference(superposition,[status(thm)],[c_0,c_1087]) ).
% 39.65/5.51  
% 39.65/5.51  cnf(c_4224,plain,
% 39.65/5.51      ( r1_tarski(k3_xboole_0(X0,X1),X1) = iProver_top ),
% 39.65/5.51      inference(superposition,[status(thm)],[c_1473,c_2417]) ).
% 39.65/5.51  
% 39.65/5.51  cnf(c_4229,plain,
% 39.65/5.51      ( r1_tarski(X0,k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK2)) = iProver_top
% 39.65/5.51      | r1_tarski(X0,sK3) != iProver_top ),
% 39.65/5.51      inference(superposition,[status(thm)],[c_1805,c_2417]) ).
% 39.65/5.51  
% 39.65/5.51  cnf(c_4391,plain,
% 39.65/5.51      ( k3_xboole_0(X0,k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK2)) = X0
% 39.65/5.51      | r1_tarski(X0,sK3) != iProver_top ),
% 39.65/5.51      inference(superposition,[status(thm)],[c_4229,c_1086]) ).
% 39.65/5.51  
% 39.65/5.51  cnf(c_14313,plain,
% 39.65/5.51      ( k3_xboole_0(k3_xboole_0(X0,sK3),k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK2)) = k3_xboole_0(X0,sK3) ),
% 39.65/5.51      inference(superposition,[status(thm)],[c_4224,c_4391]) ).
% 39.65/5.51  
% 39.65/5.51  cnf(c_50205,plain,
% 39.65/5.51      ( k3_xboole_0(k3_xboole_0(sK3,X0),k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK2)) = k3_xboole_0(X0,sK3) ),
% 39.65/5.51      inference(superposition,[status(thm)],[c_0,c_14313]) ).
% 39.65/5.51  
% 39.65/5.51  cnf(c_55525,plain,
% 39.65/5.51      ( k3_xboole_0(k3_tarski(k4_enumset1(sK3,sK3,sK3,sK3,sK3,X0)),sK3) = k3_xboole_0(sK3,k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK2)) ),
% 39.65/5.51      inference(superposition,[status(thm)],[c_1802,c_50205]) ).
% 39.65/5.51  
% 39.65/5.51  cnf(c_55613,plain,
% 39.65/5.51      ( k3_xboole_0(k3_tarski(k4_enumset1(sK3,sK3,sK3,sK3,sK3,X0)),sK3) = sK3 ),
% 39.65/5.51      inference(light_normalisation,[status(thm)],[c_55525,c_1805]) ).
% 39.65/5.51  
% 39.65/5.51  cnf(c_7,plain,
% 39.65/5.51      ( ~ r1_xboole_0(X0,X1) | ~ r2_hidden(X2,k3_xboole_0(X0,X1)) ),
% 39.65/5.51      inference(cnf_transformation,[],[f56]) ).
% 39.65/5.51  
% 39.65/5.51  cnf(c_1093,plain,
% 39.65/5.51      ( r1_xboole_0(X0,X1) != iProver_top
% 39.65/5.51      | r2_hidden(X2,k3_xboole_0(X0,X1)) != iProver_top ),
% 39.65/5.51      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 39.65/5.51  
% 39.65/5.51  cnf(c_56882,plain,
% 39.65/5.51      ( r1_xboole_0(k3_tarski(k4_enumset1(sK3,sK3,sK3,sK3,sK3,X0)),sK3) != iProver_top
% 39.65/5.51      | r2_hidden(X1,sK3) != iProver_top ),
% 39.65/5.51      inference(superposition,[status(thm)],[c_55613,c_1093]) ).
% 39.65/5.51  
% 39.65/5.51  cnf(c_170407,plain,
% 39.65/5.51      ( k3_xboole_0(k3_xboole_0(k3_tarski(k4_enumset1(sK3,sK3,sK3,sK3,sK3,X0)),sK3),k4_enumset1(sK1(k3_tarski(k4_enumset1(sK3,sK3,sK3,sK3,sK3,X0)),sK3),sK1(k3_tarski(k4_enumset1(sK3,sK3,sK3,sK3,sK3,X0)),sK3),sK1(k3_tarski(k4_enumset1(sK3,sK3,sK3,sK3,sK3,X0)),sK3),sK1(k3_tarski(k4_enumset1(sK3,sK3,sK3,sK3,sK3,X0)),sK3),sK1(k3_tarski(k4_enumset1(sK3,sK3,sK3,sK3,sK3,X0)),sK3),sK1(k3_tarski(k4_enumset1(sK3,sK3,sK3,sK3,sK3,X0)),sK3))) = k4_enumset1(sK1(k3_tarski(k4_enumset1(sK3,sK3,sK3,sK3,sK3,X0)),sK3),sK1(k3_tarski(k4_enumset1(sK3,sK3,sK3,sK3,sK3,X0)),sK3),sK1(k3_tarski(k4_enumset1(sK3,sK3,sK3,sK3,sK3,X0)),sK3),sK1(k3_tarski(k4_enumset1(sK3,sK3,sK3,sK3,sK3,X0)),sK3),sK1(k3_tarski(k4_enumset1(sK3,sK3,sK3,sK3,sK3,X0)),sK3),sK1(k3_tarski(k4_enumset1(sK3,sK3,sK3,sK3,sK3,X0)),sK3))
% 39.65/5.51      | r2_hidden(X1,sK3) != iProver_top ),
% 39.65/5.51      inference(superposition,[status(thm)],[c_5296,c_56882]) ).
% 39.65/5.51  
% 39.65/5.51  cnf(c_170410,plain,
% 39.65/5.51      ( k3_xboole_0(sK3,k4_enumset1(sK1(k3_tarski(k4_enumset1(sK3,sK3,sK3,sK3,sK3,X0)),sK3),sK1(k3_tarski(k4_enumset1(sK3,sK3,sK3,sK3,sK3,X0)),sK3),sK1(k3_tarski(k4_enumset1(sK3,sK3,sK3,sK3,sK3,X0)),sK3),sK1(k3_tarski(k4_enumset1(sK3,sK3,sK3,sK3,sK3,X0)),sK3),sK1(k3_tarski(k4_enumset1(sK3,sK3,sK3,sK3,sK3,X0)),sK3),sK1(k3_tarski(k4_enumset1(sK3,sK3,sK3,sK3,sK3,X0)),sK3))) = k4_enumset1(sK1(k3_tarski(k4_enumset1(sK3,sK3,sK3,sK3,sK3,X0)),sK3),sK1(k3_tarski(k4_enumset1(sK3,sK3,sK3,sK3,sK3,X0)),sK3),sK1(k3_tarski(k4_enumset1(sK3,sK3,sK3,sK3,sK3,X0)),sK3),sK1(k3_tarski(k4_enumset1(sK3,sK3,sK3,sK3,sK3,X0)),sK3),sK1(k3_tarski(k4_enumset1(sK3,sK3,sK3,sK3,sK3,X0)),sK3),sK1(k3_tarski(k4_enumset1(sK3,sK3,sK3,sK3,sK3,X0)),sK3))
% 39.65/5.51      | r2_hidden(X1,sK3) != iProver_top ),
% 39.65/5.51      inference(light_normalisation,[status(thm)],[c_170407,c_55613]) ).
% 39.65/5.51  
% 39.65/5.51  cnf(c_177160,plain,
% 39.65/5.51      ( k3_xboole_0(sK3,k4_enumset1(sK1(k3_tarski(k4_enumset1(sK3,sK3,sK3,sK3,sK3,X0)),sK3),sK1(k3_tarski(k4_enumset1(sK3,sK3,sK3,sK3,sK3,X0)),sK3),sK1(k3_tarski(k4_enumset1(sK3,sK3,sK3,sK3,sK3,X0)),sK3),sK1(k3_tarski(k4_enumset1(sK3,sK3,sK3,sK3,sK3,X0)),sK3),sK1(k3_tarski(k4_enumset1(sK3,sK3,sK3,sK3,sK3,X0)),sK3),sK1(k3_tarski(k4_enumset1(sK3,sK3,sK3,sK3,sK3,X0)),sK3))) = k4_enumset1(sK1(k3_tarski(k4_enumset1(sK3,sK3,sK3,sK3,sK3,X0)),sK3),sK1(k3_tarski(k4_enumset1(sK3,sK3,sK3,sK3,sK3,X0)),sK3),sK1(k3_tarski(k4_enumset1(sK3,sK3,sK3,sK3,sK3,X0)),sK3),sK1(k3_tarski(k4_enumset1(sK3,sK3,sK3,sK3,sK3,X0)),sK3),sK1(k3_tarski(k4_enumset1(sK3,sK3,sK3,sK3,sK3,X0)),sK3),sK1(k3_tarski(k4_enumset1(sK3,sK3,sK3,sK3,sK3,X0)),sK3))
% 39.65/5.51      | r1_xboole_0(sK3,k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK2)) = iProver_top ),
% 39.65/5.51      inference(superposition,[status(thm)],[c_5288,c_170410]) ).
% 39.65/5.51  
% 39.65/5.51  cnf(c_23,negated_conjecture,
% 39.65/5.51      ( k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK2) != sK3
% 39.65/5.51      | k1_xboole_0 != sK4 ),
% 39.65/5.51      inference(cnf_transformation,[],[f95]) ).
% 39.65/5.51  
% 39.65/5.51  cnf(c_9,plain,
% 39.65/5.51      ( ~ r1_tarski(X0,X1)
% 39.65/5.51      | k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k1_xboole_0 ),
% 39.65/5.51      inference(cnf_transformation,[],[f85]) ).
% 39.65/5.51  
% 39.65/5.51  cnf(c_60,plain,
% 39.65/5.51      ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k1_xboole_0
% 39.65/5.51      | r1_tarski(X0,X1) != iProver_top ),
% 39.65/5.51      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 39.65/5.51  
% 39.65/5.51  cnf(c_62,plain,
% 39.65/5.51      ( k5_xboole_0(sK2,k3_xboole_0(sK2,sK2)) = k1_xboole_0
% 39.65/5.51      | r1_tarski(sK2,sK2) != iProver_top ),
% 39.65/5.51      inference(instantiation,[status(thm)],[c_60]) ).
% 39.65/5.51  
% 39.65/5.51  cnf(c_629,plain,
% 39.65/5.51      ( X0 != X1
% 39.65/5.51      | X2 != X3
% 39.65/5.51      | X4 != X5
% 39.65/5.51      | X6 != X7
% 39.65/5.51      | X8 != X9
% 39.65/5.51      | X10 != X11
% 39.65/5.51      | k4_enumset1(X0,X2,X4,X6,X8,X10) = k4_enumset1(X1,X3,X5,X7,X9,X11) ),
% 39.65/5.51      theory(equality) ).
% 39.65/5.51  
% 39.65/5.51  cnf(c_635,plain,
% 39.65/5.51      ( k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK2) = k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK2)
% 39.65/5.51      | sK2 != sK2 ),
% 39.65/5.51      inference(instantiation,[status(thm)],[c_629]) ).
% 39.65/5.51  
% 39.65/5.51  cnf(c_622,plain,( X0 = X0 ),theory(equality) ).
% 39.65/5.51  
% 39.65/5.51  cnf(c_638,plain,
% 39.65/5.51      ( sK2 = sK2 ),
% 39.65/5.51      inference(instantiation,[status(thm)],[c_622]) ).
% 39.65/5.51  
% 39.65/5.51  cnf(c_1230,plain,
% 39.65/5.51      ( sK3 = sK3 ),
% 39.65/5.51      inference(instantiation,[status(thm)],[c_622]) ).
% 39.65/5.51  
% 39.65/5.51  cnf(c_1476,plain,
% 39.65/5.51      ( r1_tarski(sK2,sK2) = iProver_top ),
% 39.65/5.51      inference(instantiation,[status(thm)],[c_1473]) ).
% 39.65/5.51  
% 39.65/5.51  cnf(c_623,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 39.65/5.51  
% 39.65/5.51  cnf(c_1175,plain,
% 39.65/5.51      ( X0 != X1 | sK4 != X1 | sK4 = X0 ),
% 39.65/5.51      inference(instantiation,[status(thm)],[c_623]) ).
% 39.65/5.51  
% 39.65/5.51  cnf(c_1787,plain,
% 39.65/5.51      ( X0 != k1_xboole_0 | sK4 = X0 | sK4 != k1_xboole_0 ),
% 39.65/5.51      inference(instantiation,[status(thm)],[c_1175]) ).
% 39.65/5.51  
% 39.65/5.51  cnf(c_2028,plain,
% 39.65/5.51      ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) != k1_xboole_0
% 39.65/5.51      | sK4 = k5_xboole_0(X0,k3_xboole_0(X0,X1))
% 39.65/5.51      | sK4 != k1_xboole_0 ),
% 39.65/5.51      inference(instantiation,[status(thm)],[c_1787]) ).
% 39.65/5.51  
% 39.65/5.51  cnf(c_2029,plain,
% 39.65/5.51      ( k5_xboole_0(sK2,k3_xboole_0(sK2,sK2)) != k1_xboole_0
% 39.65/5.51      | sK4 = k5_xboole_0(sK2,k3_xboole_0(sK2,sK2))
% 39.65/5.51      | sK4 != k1_xboole_0 ),
% 39.65/5.51      inference(instantiation,[status(thm)],[c_2028]) ).
% 39.65/5.51  
% 39.65/5.51  cnf(c_1,plain,
% 39.65/5.51      ( r2_hidden(sK0(X0),X0) | v1_xboole_0(X0) ),
% 39.65/5.51      inference(cnf_transformation,[],[f49]) ).
% 39.65/5.51  
% 39.65/5.51  cnf(c_2,plain,
% 39.65/5.51      ( ~ v1_xboole_0(X0) | k1_xboole_0 = X0 ),
% 39.65/5.51      inference(cnf_transformation,[],[f50]) ).
% 39.65/5.51  
% 39.65/5.51  cnf(c_297,plain,
% 39.65/5.51      ( r2_hidden(sK0(X0),X0) | k1_xboole_0 = X0 ),
% 39.65/5.51      inference(resolution,[status(thm)],[c_1,c_2]) ).
% 39.65/5.51  
% 39.65/5.51  cnf(c_1079,plain,
% 39.65/5.51      ( k1_xboole_0 = X0 | r2_hidden(sK0(X0),X0) = iProver_top ),
% 39.65/5.51      inference(predicate_to_equality,[status(thm)],[c_297]) ).
% 39.65/5.51  
% 39.65/5.51  cnf(c_5791,plain,
% 39.65/5.51      ( r1_xboole_0(X0,k1_xboole_0) != iProver_top
% 39.65/5.51      | r2_hidden(X1,k1_xboole_0) != iProver_top ),
% 39.65/5.51      inference(superposition,[status(thm)],[c_15,c_1093]) ).
% 39.65/5.51  
% 39.65/5.51  cnf(c_19,plain,
% 39.65/5.51      ( r1_xboole_0(X0,X1) | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X0 ),
% 39.65/5.51      inference(cnf_transformation,[],[f91]) ).
% 39.65/5.51  
% 39.65/5.51  cnf(c_1083,plain,
% 39.65/5.51      ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X0
% 39.65/5.51      | r1_xboole_0(X0,X1) = iProver_top ),
% 39.65/5.51      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 39.65/5.51  
% 39.65/5.51  cnf(c_2392,plain,
% 39.65/5.51      ( k5_xboole_0(X0,k1_xboole_0) != X0
% 39.65/5.51      | r1_xboole_0(X0,k1_xboole_0) = iProver_top ),
% 39.65/5.51      inference(superposition,[status(thm)],[c_15,c_1083]) ).
% 39.65/5.51  
% 39.65/5.51  cnf(c_2400,plain,
% 39.65/5.51      ( X0 != X0 | r1_xboole_0(X0,k1_xboole_0) = iProver_top ),
% 39.65/5.51      inference(light_normalisation,[status(thm)],[c_2392,c_17]) ).
% 39.65/5.51  
% 39.65/5.51  cnf(c_2401,plain,
% 39.65/5.51      ( r1_xboole_0(X0,k1_xboole_0) = iProver_top ),
% 39.65/5.51      inference(equality_resolution_simp,[status(thm)],[c_2400]) ).
% 39.65/5.51  
% 39.65/5.51  cnf(c_5966,plain,
% 39.65/5.51      ( r2_hidden(X1,k1_xboole_0) != iProver_top ),
% 39.65/5.51      inference(global_propositional_subsumption,
% 39.65/5.51                [status(thm)],
% 39.65/5.51                [c_5791,c_2401]) ).
% 39.65/5.51  
% 39.65/5.51  cnf(c_5967,plain,
% 39.65/5.51      ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
% 39.65/5.51      inference(renaming,[status(thm)],[c_5966]) ).
% 39.65/5.51  
% 39.65/5.51  cnf(c_5972,plain,
% 39.65/5.51      ( k1_xboole_0 = k1_xboole_0 ),
% 39.65/5.51      inference(superposition,[status(thm)],[c_1079,c_5967]) ).
% 39.65/5.51  
% 39.65/5.51  cnf(c_21,plain,
% 39.65/5.51      ( r1_xboole_0(k4_enumset1(X0,X0,X0,X0,X0,X0),X1)
% 39.65/5.51      | r2_hidden(X0,X1) ),
% 39.65/5.51      inference(cnf_transformation,[],[f93]) ).
% 39.65/5.51  
% 39.65/5.51  cnf(c_1081,plain,
% 39.65/5.51      ( r1_xboole_0(k4_enumset1(X0,X0,X0,X0,X0,X0),X1) = iProver_top
% 39.65/5.52      | r2_hidden(X0,X1) = iProver_top ),
% 39.65/5.52      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 39.65/5.52  
% 39.65/5.52  cnf(c_5789,plain,
% 39.65/5.52      ( r1_xboole_0(X0,X1) != iProver_top
% 39.65/5.52      | r2_hidden(X2,k3_xboole_0(X1,X0)) != iProver_top ),
% 39.65/5.52      inference(superposition,[status(thm)],[c_0,c_1093]) ).
% 39.65/5.52  
% 39.65/5.52  cnf(c_7026,plain,
% 39.65/5.52      ( r1_xboole_0(k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK2),sK3) != iProver_top
% 39.65/5.52      | r2_hidden(X0,sK3) != iProver_top ),
% 39.65/5.52      inference(superposition,[status(thm)],[c_1805,c_5789]) ).
% 39.65/5.52  
% 39.65/5.52  cnf(c_7056,plain,
% 39.65/5.52      ( r2_hidden(X0,sK3) != iProver_top
% 39.65/5.52      | r2_hidden(sK2,sK3) = iProver_top ),
% 39.65/5.52      inference(superposition,[status(thm)],[c_1081,c_7026]) ).
% 39.65/5.52  
% 39.65/5.52  cnf(c_8609,plain,
% 39.65/5.52      ( r1_xboole_0(sK3,k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK2)) = iProver_top
% 39.65/5.52      | r2_hidden(sK2,sK3) = iProver_top ),
% 39.65/5.52      inference(superposition,[status(thm)],[c_5288,c_7056]) ).
% 39.65/5.52  
% 39.65/5.52  cnf(c_1120,plain,
% 39.65/5.52      ( sK4 != X0 | k1_xboole_0 != X0 | k1_xboole_0 = sK4 ),
% 39.65/5.52      inference(instantiation,[status(thm)],[c_623]) ).
% 39.65/5.52  
% 39.65/5.52  cnf(c_28727,plain,
% 39.65/5.52      ( sK4 != k5_xboole_0(X0,k3_xboole_0(X0,X1))
% 39.65/5.52      | k1_xboole_0 != k5_xboole_0(X0,k3_xboole_0(X0,X1))
% 39.65/5.52      | k1_xboole_0 = sK4 ),
% 39.65/5.52      inference(instantiation,[status(thm)],[c_1120]) ).
% 39.65/5.52  
% 39.65/5.52  cnf(c_28728,plain,
% 39.65/5.52      ( sK4 != k5_xboole_0(sK2,k3_xboole_0(sK2,sK2))
% 39.65/5.52      | k1_xboole_0 != k5_xboole_0(sK2,k3_xboole_0(sK2,sK2))
% 39.65/5.52      | k1_xboole_0 = sK4 ),
% 39.65/5.52      inference(instantiation,[status(thm)],[c_28727]) ).
% 39.65/5.52  
% 39.65/5.52  cnf(c_6498,plain,
% 39.65/5.52      ( X0 != X1 | k1_xboole_0 != X1 | k1_xboole_0 = X0 ),
% 39.65/5.52      inference(instantiation,[status(thm)],[c_623]) ).
% 39.65/5.52  
% 39.65/5.52  cnf(c_51873,plain,
% 39.65/5.52      ( X0 != k1_xboole_0
% 39.65/5.52      | k1_xboole_0 = X0
% 39.65/5.52      | k1_xboole_0 != k1_xboole_0 ),
% 39.65/5.52      inference(instantiation,[status(thm)],[c_6498]) ).
% 39.65/5.52  
% 39.65/5.52  cnf(c_80192,plain,
% 39.65/5.52      ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) != k1_xboole_0
% 39.65/5.52      | k1_xboole_0 = k5_xboole_0(X0,k3_xboole_0(X0,X1))
% 39.65/5.52      | k1_xboole_0 != k1_xboole_0 ),
% 39.65/5.52      inference(instantiation,[status(thm)],[c_51873]) ).
% 39.65/5.52  
% 39.65/5.52  cnf(c_80193,plain,
% 39.65/5.52      ( k5_xboole_0(sK2,k3_xboole_0(sK2,sK2)) != k1_xboole_0
% 39.65/5.52      | k1_xboole_0 = k5_xboole_0(sK2,k3_xboole_0(sK2,sK2))
% 39.65/5.52      | k1_xboole_0 != k1_xboole_0 ),
% 39.65/5.52      inference(instantiation,[status(thm)],[c_80192]) ).
% 39.65/5.52  
% 39.65/5.52  cnf(c_1127,plain,
% 39.65/5.52      ( k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK2) != X0
% 39.65/5.52      | k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK2) = sK3
% 39.65/5.52      | sK3 != X0 ),
% 39.65/5.52      inference(instantiation,[status(thm)],[c_623]) ).
% 39.65/5.52  
% 39.65/5.52  cnf(c_33893,plain,
% 39.65/5.52      ( k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK2) != k3_xboole_0(X0,k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK2))
% 39.65/5.52      | k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK2) = sK3
% 39.65/5.52      | sK3 != k3_xboole_0(X0,k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK2)) ),
% 39.65/5.52      inference(instantiation,[status(thm)],[c_1127]) ).
% 39.65/5.52  
% 39.65/5.52  cnf(c_81240,plain,
% 39.65/5.52      ( k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK2) != k3_xboole_0(sK3,k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK2))
% 39.65/5.52      | k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK2) = sK3
% 39.65/5.52      | sK3 != k3_xboole_0(sK3,k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK2)) ),
% 39.65/5.52      inference(instantiation,[status(thm)],[c_33893]) ).
% 39.65/5.52  
% 39.65/5.52  cnf(c_1145,plain,
% 39.65/5.52      ( X0 != X1 | sK3 != X1 | sK3 = X0 ),
% 39.65/5.52      inference(instantiation,[status(thm)],[c_623]) ).
% 39.65/5.52  
% 39.65/5.52  cnf(c_1176,plain,
% 39.65/5.52      ( X0 != sK3 | sK3 = X0 | sK3 != sK3 ),
% 39.65/5.52      inference(instantiation,[status(thm)],[c_1145]) ).
% 39.65/5.52  
% 39.65/5.52  cnf(c_1555,plain,
% 39.65/5.52      ( k3_xboole_0(sK3,X0) != sK3
% 39.65/5.52      | sK3 = k3_xboole_0(sK3,X0)
% 39.65/5.52      | sK3 != sK3 ),
% 39.65/5.52      inference(instantiation,[status(thm)],[c_1176]) ).
% 39.65/5.52  
% 39.65/5.52  cnf(c_81241,plain,
% 39.65/5.52      ( k3_xboole_0(sK3,k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK2)) != sK3
% 39.65/5.52      | sK3 = k3_xboole_0(sK3,k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK2))
% 39.65/5.52      | sK3 != sK3 ),
% 39.65/5.52      inference(instantiation,[status(thm)],[c_1555]) ).
% 39.65/5.52  
% 39.65/5.52  cnf(c_2900,plain,
% 39.65/5.52      ( X0 != X1
% 39.65/5.52      | k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK2) != X1
% 39.65/5.52      | k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK2) = X0 ),
% 39.65/5.52      inference(instantiation,[status(thm)],[c_623]) ).
% 39.65/5.52  
% 39.65/5.52  cnf(c_2983,plain,
% 39.65/5.52      ( X0 != k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK2)
% 39.65/5.52      | k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK2) = X0
% 39.65/5.52      | k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK2) != k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK2) ),
% 39.65/5.52      inference(instantiation,[status(thm)],[c_2900]) ).
% 39.65/5.52  
% 39.65/5.52  cnf(c_6083,plain,
% 39.65/5.52      ( k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK2) != k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK2)
% 39.65/5.52      | k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK2) = k3_xboole_0(X0,k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK2))
% 39.65/5.52      | k3_xboole_0(X0,k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK2)) != k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK2) ),
% 39.65/5.52      inference(instantiation,[status(thm)],[c_2983]) ).
% 39.65/5.52  
% 39.65/5.52  cnf(c_92074,plain,
% 39.65/5.52      ( k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK2) != k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK2)
% 39.65/5.52      | k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK2) = k3_xboole_0(sK3,k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK2))
% 39.65/5.52      | k3_xboole_0(sK3,k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK2)) != k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK2) ),
% 39.65/5.52      inference(instantiation,[status(thm)],[c_6083]) ).
% 39.65/5.52  
% 39.65/5.52  cnf(c_180155,plain,
% 39.65/5.52      ( ~ r2_hidden(sK2,sK3)
% 39.65/5.52      | k3_xboole_0(sK3,k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK2)) = k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK2) ),
% 39.65/5.52      inference(instantiation,[status(thm)],[c_22]) ).
% 39.65/5.52  
% 39.65/5.52  cnf(c_180157,plain,
% 39.65/5.52      ( k3_xboole_0(sK3,k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK2)) = k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK2)
% 39.65/5.52      | r2_hidden(sK2,sK3) != iProver_top ),
% 39.65/5.52      inference(predicate_to_equality,[status(thm)],[c_180155]) ).
% 39.65/5.52  
% 39.65/5.52  cnf(c_2152,plain,
% 39.65/5.52      ( k3_xboole_0(X0,k4_enumset1(sK0(X0),sK0(X0),sK0(X0),sK0(X0),sK0(X0),sK0(X0))) = k4_enumset1(sK0(X0),sK0(X0),sK0(X0),sK0(X0),sK0(X0),sK0(X0))
% 39.65/5.52      | k1_xboole_0 = X0 ),
% 39.65/5.52      inference(superposition,[status(thm)],[c_1079,c_1080]) ).
% 39.65/5.52  
% 39.65/5.52  cnf(c_2416,plain,
% 39.65/5.52      ( r1_tarski(k3_xboole_0(X0,X1),X0) = iProver_top ),
% 39.65/5.52      inference(superposition,[status(thm)],[c_1473,c_1087]) ).
% 39.65/5.52  
% 39.65/5.52  cnf(c_11,plain,
% 39.65/5.52      ( ~ r1_tarski(X0,X1)
% 39.65/5.52      | r1_tarski(X0,k3_tarski(k4_enumset1(X2,X2,X2,X2,X2,X1))) ),
% 39.65/5.52      inference(cnf_transformation,[],[f87]) ).
% 39.65/5.52  
% 39.65/5.52  cnf(c_1089,plain,
% 39.65/5.52      ( r1_tarski(X0,X1) != iProver_top
% 39.65/5.52      | r1_tarski(X0,k3_tarski(k4_enumset1(X2,X2,X2,X2,X2,X1))) = iProver_top ),
% 39.65/5.52      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 39.65/5.52  
% 39.65/5.52  cnf(c_5269,plain,
% 39.65/5.52      ( r1_tarski(X0,k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK2)) = iProver_top
% 39.65/5.52      | r1_tarski(X0,sK4) != iProver_top ),
% 39.65/5.52      inference(superposition,[status(thm)],[c_26,c_1089]) ).
% 39.65/5.52  
% 39.65/5.52  cnf(c_1091,plain,
% 39.65/5.52      ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k1_xboole_0
% 39.65/5.52      | r1_tarski(X0,X1) != iProver_top ),
% 39.65/5.52      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 39.65/5.52  
% 39.65/5.52  cnf(c_5272,plain,
% 39.65/5.52      ( k5_xboole_0(X0,k3_xboole_0(X0,k3_tarski(k4_enumset1(X1,X1,X1,X1,X1,X2)))) = k1_xboole_0
% 39.65/5.52      | r1_tarski(X0,X2) != iProver_top ),
% 39.65/5.52      inference(superposition,[status(thm)],[c_1089,c_1091]) ).
% 39.65/5.52  
% 39.65/5.52  cnf(c_156033,plain,
% 39.65/5.52      ( k5_xboole_0(X0,k3_xboole_0(X0,k3_tarski(k4_enumset1(X1,X1,X1,X1,X1,k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK2))))) = k1_xboole_0
% 39.65/5.52      | r1_tarski(X0,sK4) != iProver_top ),
% 39.65/5.52      inference(superposition,[status(thm)],[c_5269,c_5272]) ).
% 39.65/5.52  
% 39.65/5.52  cnf(c_158780,plain,
% 39.65/5.52      ( k5_xboole_0(k3_xboole_0(sK4,X0),k3_xboole_0(k3_xboole_0(sK4,X0),k3_tarski(k4_enumset1(X1,X1,X1,X1,X1,k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK2))))) = k1_xboole_0 ),
% 39.65/5.52      inference(superposition,[status(thm)],[c_2416,c_156033]) ).
% 39.65/5.52  
% 39.65/5.52  cnf(c_159254,plain,
% 39.65/5.52      ( k5_xboole_0(k4_enumset1(sK0(sK4),sK0(sK4),sK0(sK4),sK0(sK4),sK0(sK4),sK0(sK4)),k3_xboole_0(k4_enumset1(sK0(sK4),sK0(sK4),sK0(sK4),sK0(sK4),sK0(sK4),sK0(sK4)),k3_tarski(k4_enumset1(X0,X0,X0,X0,X0,k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK2))))) = k1_xboole_0
% 39.65/5.52      | sK4 = k1_xboole_0 ),
% 39.65/5.52      inference(superposition,[status(thm)],[c_2152,c_158780]) ).
% 39.65/5.52  
% 39.65/5.52  cnf(c_25,negated_conjecture,
% 39.65/5.52      ( k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK2) != sK3
% 39.65/5.52      | k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK2) != sK4 ),
% 39.65/5.52      inference(cnf_transformation,[],[f97]) ).
% 39.65/5.52  
% 39.65/5.52  cnf(c_24,negated_conjecture,
% 39.65/5.52      ( k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK2) != sK4
% 39.65/5.52      | k1_xboole_0 != sK3 ),
% 39.65/5.52      inference(cnf_transformation,[],[f96]) ).
% 39.65/5.52  
% 39.65/5.52  cnf(c_1361,plain,
% 39.65/5.52      ( sK4 = sK4 ),
% 39.65/5.52      inference(instantiation,[status(thm)],[c_622]) ).
% 39.65/5.52  
% 39.65/5.52  cnf(c_5976,plain,
% 39.65/5.52      ( k3_xboole_0(X0,k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK2)) = X0
% 39.65/5.52      | r1_tarski(X0,sK4) != iProver_top ),
% 39.65/5.52      inference(superposition,[status(thm)],[c_5269,c_1086]) ).
% 39.65/5.52  
% 39.65/5.52  cnf(c_6055,plain,
% 39.65/5.52      ( k3_xboole_0(sK4,k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK2)) = sK4 ),
% 39.65/5.52      inference(superposition,[status(thm)],[c_1473,c_5976]) ).
% 39.65/5.52  
% 39.65/5.52  cnf(c_8608,plain,
% 39.65/5.52      ( sK3 = k1_xboole_0 | r2_hidden(sK2,sK3) = iProver_top ),
% 39.65/5.52      inference(superposition,[status(thm)],[c_1079,c_7056]) ).
% 39.65/5.52  
% 39.65/5.52  cnf(c_8612,plain,
% 39.65/5.52      ( r2_hidden(sK2,sK3) | sK3 = k1_xboole_0 ),
% 39.65/5.52      inference(predicate_to_equality_rev,[status(thm)],[c_8608]) ).
% 39.65/5.52  
% 39.65/5.52  cnf(c_1561,plain,
% 39.65/5.52      ( X0 != X1 | X0 = sK3 | sK3 != X1 ),
% 39.65/5.52      inference(instantiation,[status(thm)],[c_623]) ).
% 39.65/5.52  
% 39.65/5.52  cnf(c_6883,plain,
% 39.65/5.52      ( X0 = sK3 | X0 != k1_xboole_0 | sK3 != k1_xboole_0 ),
% 39.65/5.52      inference(instantiation,[status(thm)],[c_1561]) ).
% 39.65/5.52  
% 39.65/5.52  cnf(c_30490,plain,
% 39.65/5.52      ( sK3 != k1_xboole_0
% 39.65/5.52      | k1_xboole_0 = sK3
% 39.65/5.52      | k1_xboole_0 != k1_xboole_0 ),
% 39.65/5.52      inference(instantiation,[status(thm)],[c_6883]) ).
% 39.65/5.52  
% 39.65/5.52  cnf(c_7036,plain,
% 39.65/5.52      ( r1_xboole_0(k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK2),sK4) != iProver_top
% 39.65/5.52      | r2_hidden(X0,sK4) != iProver_top ),
% 39.65/5.52      inference(superposition,[status(thm)],[c_6055,c_5789]) ).
% 39.65/5.52  
% 39.65/5.52  cnf(c_10103,plain,
% 39.65/5.52      ( r2_hidden(X0,sK4) != iProver_top
% 39.65/5.52      | r2_hidden(sK2,sK4) = iProver_top ),
% 39.65/5.52      inference(superposition,[status(thm)],[c_1081,c_7036]) ).
% 39.65/5.52  
% 39.65/5.52  cnf(c_44189,plain,
% 39.65/5.52      ( sK4 = k1_xboole_0 | r2_hidden(sK2,sK4) = iProver_top ),
% 39.65/5.52      inference(superposition,[status(thm)],[c_1079,c_10103]) ).
% 39.65/5.52  
% 39.65/5.52  cnf(c_44193,plain,
% 39.65/5.52      ( r2_hidden(sK2,sK4) | sK4 = k1_xboole_0 ),
% 39.65/5.52      inference(predicate_to_equality_rev,[status(thm)],[c_44189]) ).
% 39.65/5.52  
% 39.65/5.52  cnf(c_1141,plain,
% 39.65/5.52      ( k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK2) != X0
% 39.65/5.52      | k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK2) = sK4
% 39.65/5.52      | sK4 != X0 ),
% 39.65/5.52      inference(instantiation,[status(thm)],[c_623]) ).
% 39.65/5.52  
% 39.65/5.52  cnf(c_33891,plain,
% 39.65/5.52      ( k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK2) != k3_xboole_0(X0,k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK2))
% 39.65/5.52      | k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK2) = sK4
% 39.65/5.52      | sK4 != k3_xboole_0(X0,k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK2)) ),
% 39.65/5.52      inference(instantiation,[status(thm)],[c_1141]) ).
% 39.65/5.52  
% 39.65/5.52  cnf(c_81237,plain,
% 39.65/5.52      ( k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK2) != k3_xboole_0(sK4,k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK2))
% 39.65/5.52      | k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK2) = sK4
% 39.65/5.52      | sK4 != k3_xboole_0(sK4,k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK2)) ),
% 39.65/5.52      inference(instantiation,[status(thm)],[c_33891]) ).
% 39.65/5.52  
% 39.65/5.52  cnf(c_1211,plain,
% 39.65/5.52      ( X0 != sK4 | sK4 = X0 | sK4 != sK4 ),
% 39.65/5.52      inference(instantiation,[status(thm)],[c_1175]) ).
% 39.65/5.52  
% 39.65/5.52  cnf(c_1577,plain,
% 39.65/5.52      ( k3_xboole_0(sK4,X0) != sK4
% 39.65/5.52      | sK4 = k3_xboole_0(sK4,X0)
% 39.65/5.52      | sK4 != sK4 ),
% 39.65/5.52      inference(instantiation,[status(thm)],[c_1211]) ).
% 39.65/5.52  
% 39.65/5.52  cnf(c_81238,plain,
% 39.65/5.52      ( k3_xboole_0(sK4,k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK2)) != sK4
% 39.65/5.52      | sK4 = k3_xboole_0(sK4,k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK2))
% 39.65/5.52      | sK4 != sK4 ),
% 39.65/5.52      inference(instantiation,[status(thm)],[c_1577]) ).
% 39.65/5.52  
% 39.65/5.52  cnf(c_92890,plain,
% 39.65/5.52      ( k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK2) != k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK2)
% 39.65/5.52      | k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK2) = k3_xboole_0(sK4,k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK2))
% 39.65/5.52      | k3_xboole_0(sK4,k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK2)) != k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK2) ),
% 39.65/5.52      inference(instantiation,[status(thm)],[c_6083]) ).
% 39.65/5.52  
% 39.65/5.52  cnf(c_180141,plain,
% 39.65/5.52      ( ~ r2_hidden(sK2,sK4)
% 39.65/5.52      | k3_xboole_0(sK4,k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK2)) = k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK2) ),
% 39.65/5.52      inference(instantiation,[status(thm)],[c_22]) ).
% 39.65/5.52  
% 39.65/5.52  cnf(c_180257,plain,
% 39.65/5.52      ( sK4 = k1_xboole_0 ),
% 39.65/5.52      inference(global_propositional_subsumption,
% 39.65/5.52                [status(thm)],
% 39.65/5.52                [c_159254,c_25,c_24,c_635,c_638,c_1230,c_1361,c_1805,
% 39.65/5.52                 c_5972,c_6055,c_8612,c_30490,c_44193,c_81237,c_81238,
% 39.65/5.52                 c_81240,c_81241,c_92074,c_92890,c_180141,c_180155]) ).
% 39.65/5.52  
% 39.65/5.52  cnf(c_182286,plain,
% 39.65/5.52      ( r1_xboole_0(sK3,k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK2)) = iProver_top ),
% 39.65/5.52      inference(global_propositional_subsumption,
% 39.65/5.52                [status(thm)],
% 39.65/5.52                [c_177160,c_25,c_24,c_23,c_62,c_635,c_638,c_1230,c_1361,
% 39.65/5.52                 c_1476,c_1805,c_2029,c_5972,c_6055,c_8612,c_28728,
% 39.65/5.52                 c_30490,c_44193,c_80193,c_81237,c_81238,c_81240,c_81241,
% 39.65/5.52                 c_92074,c_92890,c_119963,c_180141,c_180155]) ).
% 39.65/5.52  
% 39.65/5.52  cnf(c_20,plain,
% 39.65/5.52      ( ~ r1_xboole_0(X0,X1) | k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ),
% 39.65/5.52      inference(cnf_transformation,[],[f92]) ).
% 39.65/5.52  
% 39.65/5.52  cnf(c_1082,plain,
% 39.65/5.52      ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X0
% 39.65/5.52      | r1_xboole_0(X0,X1) != iProver_top ),
% 39.65/5.52      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 39.65/5.52  
% 39.65/5.52  cnf(c_182291,plain,
% 39.65/5.52      ( k5_xboole_0(sK3,k3_xboole_0(sK3,k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK2))) = sK3 ),
% 39.65/5.52      inference(superposition,[status(thm)],[c_182286,c_1082]) ).
% 39.65/5.52  
% 39.65/5.52  cnf(c_182293,plain,
% 39.65/5.52      ( k5_xboole_0(sK3,sK3) = sK3 ),
% 39.65/5.52      inference(light_normalisation,[status(thm)],[c_182291,c_1805]) ).
% 39.65/5.52  
% 39.65/5.52  cnf(c_4037,plain,
% 39.65/5.52      ( k5_xboole_0(X0,k3_xboole_0(X0,X0)) = k1_xboole_0 ),
% 39.65/5.52      inference(superposition,[status(thm)],[c_1473,c_1091]) ).
% 39.65/5.52  
% 39.65/5.52  cnf(c_1804,plain,
% 39.65/5.52      ( k3_xboole_0(X0,X0) = X0 ),
% 39.65/5.52      inference(superposition,[status(thm)],[c_1473,c_1086]) ).
% 39.65/5.52  
% 39.65/5.52  cnf(c_4061,plain,
% 39.65/5.52      ( k5_xboole_0(X0,X0) = k1_xboole_0 ),
% 39.65/5.52      inference(light_normalisation,[status(thm)],[c_4037,c_1804]) ).
% 39.65/5.52  
% 39.65/5.52  cnf(c_182294,plain,
% 39.65/5.52      ( sK3 = k1_xboole_0 ),
% 39.65/5.52      inference(demodulation,[status(thm)],[c_182293,c_4061]) ).
% 39.65/5.52  
% 39.65/5.52  cnf(c_180651,plain,
% 39.65/5.52      ( k3_tarski(k4_enumset1(sK3,sK3,sK3,sK3,sK3,k1_xboole_0)) = k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK2) ),
% 39.65/5.52      inference(demodulation,[status(thm)],[c_180257,c_26]) ).
% 39.65/5.52  
% 39.65/5.52  cnf(c_182411,plain,
% 39.65/5.52      ( k3_tarski(k4_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0)) = k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK2) ),
% 39.65/5.52      inference(demodulation,[status(thm)],[c_182294,c_180651]) ).
% 39.65/5.52  
% 39.65/5.52  cnf(c_6053,plain,
% 39.65/5.52      ( k3_xboole_0(k5_xboole_0(sK4,k3_xboole_0(sK4,X0)),k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK2)) = k5_xboole_0(sK4,k3_xboole_0(sK4,X0)) ),
% 39.65/5.52      inference(superposition,[status(thm)],[c_1085,c_5976]) ).
% 39.65/5.52  
% 39.65/5.52  cnf(c_6353,plain,
% 39.65/5.52      ( k3_xboole_0(k5_xboole_0(sK4,k3_xboole_0(X0,sK4)),k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK2)) = k5_xboole_0(sK4,k3_xboole_0(sK4,X0)) ),
% 39.65/5.52      inference(superposition,[status(thm)],[c_0,c_6053]) ).
% 39.65/5.52  
% 39.65/5.52  cnf(c_14227,plain,
% 39.65/5.52      ( k3_xboole_0(k3_xboole_0(X0,X1),X0) = k3_xboole_0(X0,X1) ),
% 39.65/5.52      inference(superposition,[status(thm)],[c_2416,c_1086]) ).
% 39.65/5.52  
% 39.65/5.52  cnf(c_15154,plain,
% 39.65/5.52      ( k3_xboole_0(k5_xboole_0(sK4,k3_xboole_0(X0,sK4)),k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK2)) = k3_xboole_0(k5_xboole_0(sK4,k3_xboole_0(sK4,X0)),k5_xboole_0(sK4,k3_xboole_0(X0,sK4))) ),
% 39.65/5.52      inference(superposition,[status(thm)],[c_6353,c_14227]) ).
% 39.65/5.52  
% 39.65/5.52  cnf(c_15228,plain,
% 39.65/5.52      ( k3_xboole_0(k5_xboole_0(sK4,k3_xboole_0(sK4,X0)),k5_xboole_0(sK4,k3_xboole_0(X0,sK4))) = k5_xboole_0(sK4,k3_xboole_0(sK4,X0)) ),
% 39.65/5.52      inference(light_normalisation,[status(thm)],[c_15154,c_6353]) ).
% 39.65/5.52  
% 39.65/5.52  cnf(c_12,plain,
% 39.65/5.52      ( ~ r1_tarski(X0,X1)
% 39.65/5.52      | k3_tarski(k4_enumset1(X0,X0,X0,X0,X0,X1)) = X1 ),
% 39.65/5.52      inference(cnf_transformation,[],[f88]) ).
% 39.65/5.52  
% 39.65/5.52  cnf(c_1088,plain,
% 39.65/5.52      ( k3_tarski(k4_enumset1(X0,X0,X0,X0,X0,X1)) = X1
% 39.65/5.52      | r1_tarski(X0,X1) != iProver_top ),
% 39.65/5.52      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 39.65/5.52  
% 39.65/5.52  cnf(c_3831,plain,
% 39.65/5.52      ( k3_tarski(k4_enumset1(k5_xboole_0(X0,k3_xboole_0(X0,X1)),k5_xboole_0(X0,k3_xboole_0(X0,X1)),k5_xboole_0(X0,k3_xboole_0(X0,X1)),k5_xboole_0(X0,k3_xboole_0(X0,X1)),k5_xboole_0(X0,k3_xboole_0(X0,X1)),X0)) = X0 ),
% 39.65/5.52      inference(superposition,[status(thm)],[c_1085,c_1088]) ).
% 39.65/5.52  
% 39.65/5.52  cnf(c_79982,plain,
% 39.65/5.52      ( k3_tarski(k4_enumset1(k5_xboole_0(k5_xboole_0(sK4,k3_xboole_0(sK4,X0)),k5_xboole_0(sK4,k3_xboole_0(sK4,X0))),k5_xboole_0(k5_xboole_0(sK4,k3_xboole_0(sK4,X0)),k5_xboole_0(sK4,k3_xboole_0(sK4,X0))),k5_xboole_0(k5_xboole_0(sK4,k3_xboole_0(sK4,X0)),k5_xboole_0(sK4,k3_xboole_0(sK4,X0))),k5_xboole_0(k5_xboole_0(sK4,k3_xboole_0(sK4,X0)),k5_xboole_0(sK4,k3_xboole_0(sK4,X0))),k5_xboole_0(k5_xboole_0(sK4,k3_xboole_0(sK4,X0)),k5_xboole_0(sK4,k3_xboole_0(sK4,X0))),k5_xboole_0(sK4,k3_xboole_0(sK4,X0)))) = k5_xboole_0(sK4,k3_xboole_0(sK4,X0)) ),
% 39.65/5.52      inference(superposition,[status(thm)],[c_15228,c_3831]) ).
% 39.65/5.52  
% 39.65/5.52  cnf(c_5974,plain,
% 39.65/5.52      ( k5_xboole_0(X0,k3_xboole_0(X0,k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK2))) = k1_xboole_0
% 39.65/5.52      | r1_tarski(X0,sK4) != iProver_top ),
% 39.65/5.52      inference(superposition,[status(thm)],[c_5269,c_1091]) ).
% 39.65/5.52  
% 39.65/5.52  cnf(c_6059,plain,
% 39.65/5.52      ( k5_xboole_0(k5_xboole_0(sK4,k3_xboole_0(sK4,X0)),k3_xboole_0(k5_xboole_0(sK4,k3_xboole_0(sK4,X0)),k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK2))) = k1_xboole_0 ),
% 39.65/5.52      inference(superposition,[status(thm)],[c_1085,c_5974]) ).
% 39.65/5.52  
% 39.65/5.52  cnf(c_6064,plain,
% 39.65/5.52      ( k5_xboole_0(k5_xboole_0(sK4,k3_xboole_0(sK4,X0)),k5_xboole_0(sK4,k3_xboole_0(sK4,X0))) = k1_xboole_0 ),
% 39.65/5.52      inference(light_normalisation,[status(thm)],[c_6059,c_6053]) ).
% 39.65/5.52  
% 39.65/5.52  cnf(c_80059,plain,
% 39.65/5.52      ( k3_tarski(k4_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k5_xboole_0(sK4,k3_xboole_0(sK4,X0)))) = k5_xboole_0(sK4,k3_xboole_0(sK4,X0)) ),
% 39.65/5.52      inference(light_normalisation,[status(thm)],[c_79982,c_6064]) ).
% 39.65/5.52  
% 39.65/5.52  cnf(c_91851,plain,
% 39.65/5.52      ( k5_xboole_0(sK4,k3_xboole_0(sK4,k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK2))) = k3_tarski(k4_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k5_xboole_0(sK4,sK4))) ),
% 39.65/5.52      inference(superposition,[status(thm)],[c_6055,c_80059]) ).
% 39.65/5.52  
% 39.65/5.52  cnf(c_6061,plain,
% 39.65/5.52      ( k5_xboole_0(sK4,k3_xboole_0(sK4,k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK2))) = k1_xboole_0 ),
% 39.65/5.52      inference(superposition,[status(thm)],[c_1473,c_5974]) ).
% 39.65/5.52  
% 39.65/5.52  cnf(c_6062,plain,
% 39.65/5.52      ( k5_xboole_0(sK4,sK4) = k1_xboole_0 ),
% 39.65/5.52      inference(light_normalisation,[status(thm)],[c_6061,c_6055]) ).
% 39.65/5.52  
% 39.65/5.52  cnf(c_91874,plain,
% 39.65/5.52      ( k3_tarski(k4_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0)) = k1_xboole_0 ),
% 39.65/5.52      inference(light_normalisation,
% 39.65/5.52                [status(thm)],
% 39.65/5.52                [c_91851,c_6055,c_6062]) ).
% 39.65/5.52  
% 39.65/5.52  cnf(c_182573,plain,
% 39.65/5.52      ( k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK2) = k1_xboole_0 ),
% 39.65/5.52      inference(light_normalisation,[status(thm)],[c_182411,c_91874]) ).
% 39.65/5.52  
% 39.65/5.52  cnf(c_1782,plain,
% 39.65/5.52      ( k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK2) = sK3
% 39.65/5.52      | k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK2) != k1_xboole_0
% 39.65/5.52      | sK3 != k1_xboole_0 ),
% 39.65/5.52      inference(instantiation,[status(thm)],[c_1127]) ).
% 39.65/5.52  
% 39.65/5.52  cnf(contradiction,plain,
% 39.65/5.52      ( $false ),
% 39.65/5.52      inference(minisat,
% 39.65/5.52                [status(thm)],
% 39.65/5.52                [c_182573,c_180257,c_180155,c_92074,c_81241,c_81240,
% 39.65/5.52                 c_80193,c_28728,c_8612,c_5972,c_2029,c_1805,c_1782,
% 39.65/5.52                 c_1476,c_1230,c_638,c_635,c_62,c_23]) ).
% 39.65/5.52  
% 39.65/5.52  
% 39.65/5.52  % SZS output end CNFRefutation for theBenchmark.p
% 39.65/5.52  
% 39.65/5.52  ------                               Statistics
% 39.65/5.52  
% 39.65/5.52  ------ General
% 39.65/5.52  
% 39.65/5.52  abstr_ref_over_cycles:                  0
% 39.65/5.52  abstr_ref_under_cycles:                 0
% 39.65/5.52  gc_basic_clause_elim:                   0
% 39.65/5.52  forced_gc_time:                         0
% 39.65/5.52  parsing_time:                           0.01
% 39.65/5.52  unif_index_cands_time:                  0.
% 39.65/5.52  unif_index_add_time:                    0.
% 39.65/5.52  orderings_time:                         0.
% 39.65/5.52  out_proof_time:                         0.023
% 39.65/5.52  total_time:                             4.602
% 39.65/5.52  num_of_symbols:                         45
% 39.65/5.52  num_of_terms:                           163897
% 39.65/5.52  
% 39.65/5.52  ------ Preprocessing
% 39.65/5.52  
% 39.65/5.52  num_of_splits:                          0
% 39.65/5.52  num_of_split_atoms:                     0
% 39.65/5.52  num_of_reused_defs:                     0
% 39.65/5.52  num_eq_ax_congr_red:                    19
% 39.65/5.52  num_of_sem_filtered_clauses:            1
% 39.65/5.52  num_of_subtypes:                        0
% 39.65/5.52  monotx_restored_types:                  0
% 39.65/5.52  sat_num_of_epr_types:                   0
% 39.65/5.52  sat_num_of_non_cyclic_types:            0
% 39.65/5.52  sat_guarded_non_collapsed_types:        0
% 39.65/5.52  num_pure_diseq_elim:                    0
% 39.65/5.52  simp_replaced_by:                       0
% 39.65/5.52  res_preprocessed:                       124
% 39.65/5.52  prep_upred:                             0
% 39.65/5.52  prep_unflattend:                        8
% 39.65/5.52  smt_new_axioms:                         0
% 39.65/5.52  pred_elim_cands:                        3
% 39.65/5.52  pred_elim:                              1
% 39.65/5.52  pred_elim_cl:                           1
% 39.65/5.52  pred_elim_cycles:                       3
% 39.65/5.52  merged_defs:                            16
% 39.65/5.52  merged_defs_ncl:                        0
% 39.65/5.52  bin_hyper_res:                          16
% 39.65/5.52  prep_cycles:                            4
% 39.65/5.52  pred_elim_time:                         0.002
% 39.65/5.52  splitting_time:                         0.
% 39.65/5.52  sem_filter_time:                        0.
% 39.65/5.52  monotx_time:                            0.
% 39.65/5.52  subtype_inf_time:                       0.
% 39.65/5.52  
% 39.65/5.52  ------ Problem properties
% 39.65/5.52  
% 39.65/5.52  clauses:                                26
% 39.65/5.52  conjectures:                            4
% 39.65/5.52  epr:                                    0
% 39.65/5.52  horn:                                   20
% 39.65/5.52  ground:                                 4
% 39.65/5.52  unary:                                  6
% 39.65/5.52  binary:                                 16
% 39.65/5.52  lits:                                   50
% 39.65/5.52  lits_eq:                                18
% 39.65/5.52  fd_pure:                                0
% 39.65/5.52  fd_pseudo:                              0
% 39.65/5.52  fd_cond:                                1
% 39.65/5.52  fd_pseudo_cond:                         0
% 39.65/5.52  ac_symbols:                             0
% 39.65/5.52  
% 39.65/5.52  ------ Propositional Solver
% 39.65/5.52  
% 39.65/5.52  prop_solver_calls:                      46
% 39.65/5.52  prop_fast_solver_calls:                 1638
% 39.65/5.52  smt_solver_calls:                       0
% 39.65/5.52  smt_fast_solver_calls:                  0
% 39.65/5.52  prop_num_of_clauses:                    40486
% 39.65/5.52  prop_preprocess_simplified:             42699
% 39.65/5.52  prop_fo_subsumed:                       21
% 39.65/5.52  prop_solver_time:                       0.
% 39.65/5.52  smt_solver_time:                        0.
% 39.65/5.52  smt_fast_solver_time:                   0.
% 39.65/5.52  prop_fast_solver_time:                  0.
% 39.65/5.52  prop_unsat_core_time:                   0.002
% 39.65/5.52  
% 39.65/5.52  ------ QBF
% 39.65/5.52  
% 39.65/5.52  qbf_q_res:                              0
% 39.65/5.52  qbf_num_tautologies:                    0
% 39.65/5.52  qbf_prep_cycles:                        0
% 39.65/5.52  
% 39.65/5.52  ------ BMC1
% 39.65/5.52  
% 39.65/5.52  bmc1_current_bound:                     -1
% 39.65/5.52  bmc1_last_solved_bound:                 -1
% 39.65/5.52  bmc1_unsat_core_size:                   -1
% 39.65/5.52  bmc1_unsat_core_parents_size:           -1
% 39.65/5.52  bmc1_merge_next_fun:                    0
% 39.65/5.52  bmc1_unsat_core_clauses_time:           0.
% 39.65/5.52  
% 39.65/5.52  ------ Instantiation
% 39.65/5.52  
% 39.65/5.52  inst_num_of_clauses:                    803
% 39.65/5.52  inst_num_in_passive:                    137
% 39.65/5.52  inst_num_in_active:                     2480
% 39.65/5.52  inst_num_in_unprocessed:                366
% 39.65/5.52  inst_num_of_loops:                      3329
% 39.65/5.52  inst_num_of_learning_restarts:          1
% 39.65/5.52  inst_num_moves_active_passive:          841
% 39.65/5.52  inst_lit_activity:                      0
% 39.65/5.52  inst_lit_activity_moves:                0
% 39.65/5.52  inst_num_tautologies:                   0
% 39.65/5.52  inst_num_prop_implied:                  0
% 39.65/5.52  inst_num_existing_simplified:           0
% 39.65/5.52  inst_num_eq_res_simplified:             0
% 39.65/5.52  inst_num_child_elim:                    0
% 39.65/5.52  inst_num_of_dismatching_blockings:      39637
% 39.65/5.52  inst_num_of_non_proper_insts:           16208
% 39.65/5.52  inst_num_of_duplicates:                 0
% 39.65/5.52  inst_inst_num_from_inst_to_res:         0
% 39.65/5.52  inst_dismatching_checking_time:         0.
% 39.65/5.52  
% 39.65/5.52  ------ Resolution
% 39.65/5.52  
% 39.65/5.52  res_num_of_clauses:                     35
% 39.65/5.52  res_num_in_passive:                     35
% 39.65/5.52  res_num_in_active:                      0
% 39.65/5.52  res_num_of_loops:                       128
% 39.65/5.52  res_forward_subset_subsumed:            217
% 39.65/5.52  res_backward_subset_subsumed:           0
% 39.65/5.52  res_forward_subsumed:                   0
% 39.65/5.52  res_backward_subsumed:                  0
% 39.65/5.52  res_forward_subsumption_resolution:     0
% 39.65/5.52  res_backward_subsumption_resolution:    0
% 39.65/5.52  res_clause_to_clause_subsumption:       126046
% 39.65/5.52  res_orphan_elimination:                 0
% 39.65/5.52  res_tautology_del:                      774
% 39.65/5.52  res_num_eq_res_simplified:              0
% 39.65/5.52  res_num_sel_changes:                    0
% 39.65/5.52  res_moves_from_active_to_pass:          0
% 39.65/5.52  
% 39.65/5.52  ------ Superposition
% 39.65/5.52  
% 39.65/5.52  sup_time_total:                         0.
% 39.65/5.52  sup_time_generating:                    0.
% 39.65/5.52  sup_time_sim_full:                      0.
% 39.65/5.52  sup_time_sim_immed:                     0.
% 39.65/5.52  
% 39.65/5.52  sup_num_of_clauses:                     5435
% 39.65/5.52  sup_num_in_active:                      79
% 39.65/5.52  sup_num_in_passive:                     5356
% 39.65/5.52  sup_num_of_loops:                       664
% 39.65/5.52  sup_fw_superposition:                   32966
% 39.65/5.52  sup_bw_superposition:                   25681
% 39.65/5.52  sup_immediate_simplified:               16748
% 39.65/5.52  sup_given_eliminated:                   1
% 39.65/5.52  comparisons_done:                       0
% 39.65/5.52  comparisons_avoided:                    53
% 39.65/5.52  
% 39.65/5.52  ------ Simplifications
% 39.65/5.52  
% 39.65/5.52  
% 39.65/5.52  sim_fw_subset_subsumed:                 211
% 39.65/5.52  sim_bw_subset_subsumed:                 209
% 39.65/5.52  sim_fw_subsumed:                        4049
% 39.65/5.52  sim_bw_subsumed:                        200
% 39.65/5.52  sim_fw_subsumption_res:                 0
% 39.65/5.52  sim_bw_subsumption_res:                 0
% 39.65/5.52  sim_tautology_del:                      410
% 39.65/5.52  sim_eq_tautology_del:                   1487
% 39.65/5.52  sim_eq_res_simp:                        112
% 39.65/5.52  sim_fw_demodulated:                     8707
% 39.65/5.52  sim_bw_demodulated:                     621
% 39.65/5.52  sim_light_normalised:                   6635
% 39.65/5.52  sim_joinable_taut:                      0
% 39.65/5.52  sim_joinable_simp:                      0
% 39.65/5.52  sim_ac_normalised:                      0
% 39.65/5.52  sim_smt_subsumption:                    0
% 39.65/5.52  
%------------------------------------------------------------------------------
