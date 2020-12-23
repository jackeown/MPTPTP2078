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
% DateTime   : Thu Dec  3 11:35:49 EST 2020

% Result     : Theorem 7.68s
% Output     : CNFRefutation 7.68s
% Verified   : 
% Statistics : Number of formulae       :  144 ( 606 expanded)
%              Number of clauses        :   55 (  81 expanded)
%              Number of leaves         :   29 ( 183 expanded)
%              Depth                    :   25
%              Number of atoms          :  304 ( 928 expanded)
%              Number of equality atoms :  175 ( 735 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal clause size      :   10 (   2 average)
%              Maximal term depth       :    8 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f11,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ? [X2] :
            ( ( X0 != X2
              | ~ r2_hidden(X2,X1) )
            & ( X0 = X2
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | X0 != X2 )
            & ( X0 = X2
              | ~ r2_hidden(X2,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f11])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ? [X2] :
            ( ( X0 != X2
              | ~ r2_hidden(X2,X1) )
            & ( X0 = X2
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(rectify,[],[f36])).

fof(f38,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( X0 != X2
            | ~ r2_hidden(X2,X1) )
          & ( X0 = X2
            | r2_hidden(X2,X1) ) )
     => ( ( sK2(X0,X1) != X0
          | ~ r2_hidden(sK2(X0,X1),X1) )
        & ( sK2(X0,X1) = X0
          | r2_hidden(sK2(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ( ( sK2(X0,X1) != X0
            | ~ r2_hidden(sK2(X0,X1),X1) )
          & ( sK2(X0,X1) = X0
            | r2_hidden(sK2(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f37,f38])).

fof(f57,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f39])).

fof(f12,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f61,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f12])).

fof(f13,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f62,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f13])).

fof(f14,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f63,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f14])).

fof(f15,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f64,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f15])).

fof(f16,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f65,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f16])).

fof(f17,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f66,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f17])).

fof(f18,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f67,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f18])).

fof(f75,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f66,f67])).

fof(f76,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f65,f75])).

fof(f77,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f64,f76])).

fof(f78,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f63,f77])).

fof(f79,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f62,f78])).

fof(f83,plain,(
    ! [X0] : k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f61,f79])).

fof(f89,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) != X1 ) ),
    inference(definition_unfolding,[],[f57,f83])).

fof(f99,plain,(
    ! [X0,X3] :
      ( X0 = X3
      | ~ r2_hidden(X3,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) ) ),
    inference(equality_resolution,[],[f89])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f25])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f28])).

fof(f30,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK0(X0,X1),X1)
          & r2_hidden(sK0(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f29,f30])).

fof(f43,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f9,axiom,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f55,plain,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    inference(cnf_transformation,[],[f9])).

fof(f8,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f54,plain,(
    ! [X2,X0,X1] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f8])).

fof(f22,conjecture,(
    ! [X0,X1] :
      ~ ( k1_tarski(X1) != X0
        & k1_xboole_0 != X0
        & k1_xboole_0 = k4_xboole_0(X0,k1_tarski(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,negated_conjecture,(
    ~ ! [X0,X1] :
        ~ ( k1_tarski(X1) != X0
          & k1_xboole_0 != X0
          & k1_xboole_0 = k4_xboole_0(X0,k1_tarski(X1)) ) ),
    inference(negated_conjecture,[],[f22])).

fof(f27,plain,(
    ? [X0,X1] :
      ( k1_tarski(X1) != X0
      & k1_xboole_0 != X0
      & k1_xboole_0 = k4_xboole_0(X0,k1_tarski(X1)) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f41,plain,
    ( ? [X0,X1] :
        ( k1_tarski(X1) != X0
        & k1_xboole_0 != X0
        & k1_xboole_0 = k4_xboole_0(X0,k1_tarski(X1)) )
   => ( k1_tarski(sK4) != sK3
      & k1_xboole_0 != sK3
      & k1_xboole_0 = k4_xboole_0(sK3,k1_tarski(sK4)) ) ),
    introduced(choice_axiom,[])).

fof(f42,plain,
    ( k1_tarski(sK4) != sK3
    & k1_xboole_0 != sK3
    & k1_xboole_0 = k4_xboole_0(sK3,k1_tarski(sK4)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f27,f41])).

fof(f72,plain,(
    k1_xboole_0 = k4_xboole_0(sK3,k1_tarski(sK4)) ),
    inference(cnf_transformation,[],[f42])).

fof(f5,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f51,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f10,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f56,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f10])).

fof(f20,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f70,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f20])).

fof(f80,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f70,f79])).

fof(f81,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) ),
    inference(definition_unfolding,[],[f56,f80])).

fof(f82,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) ),
    inference(definition_unfolding,[],[f51,f81])).

fof(f94,plain,(
    k1_xboole_0 = k5_xboole_0(sK3,k5_xboole_0(k5_xboole_0(sK3,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)),k3_tarski(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))))) ),
    inference(definition_unfolding,[],[f72,f82,f83])).

fof(f2,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f2])).

fof(f46,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f24])).

fof(f84,plain,(
    ! [X0] : k5_xboole_0(k5_xboole_0(X0,X0),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))) = X0 ),
    inference(definition_unfolding,[],[f46,f81])).

fof(f21,axiom,(
    ! [X0] : k3_tarski(k1_tarski(X0)) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f71,plain,(
    ! [X0] : k3_tarski(k1_tarski(X0)) = X0 ),
    inference(cnf_transformation,[],[f21])).

fof(f92,plain,(
    ! [X0] : k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) = X0 ),
    inference(definition_unfolding,[],[f71,f83])).

fof(f6,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f52,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f6])).

fof(f7,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f53,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f85,plain,(
    ! [X0,X1] : r1_tarski(X0,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) ),
    inference(definition_unfolding,[],[f53,f80])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f34])).

fof(f48,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f35])).

fof(f96,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f48])).

fof(f50,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f19,axiom,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
    <=> r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(k1_tarski(X0),X1)
        | ~ r2_hidden(X0,X1) )
      & ( r2_hidden(X0,X1)
        | ~ r1_tarski(k1_tarski(X0),X1) ) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f69,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f90,plain,(
    ! [X0,X1] :
      ( r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f69,f83])).

fof(f3,axiom,(
    ! [X0] :
      ~ ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f3])).

fof(f32,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK1(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,(
    ! [X0] :
      ( r2_hidden(sK1(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f26,f32])).

fof(f47,plain,(
    ! [X0] :
      ( r2_hidden(sK1(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f33])).

fof(f58,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | X0 != X3
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f39])).

fof(f88,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | X0 != X3
      | k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) != X1 ) ),
    inference(definition_unfolding,[],[f58,f83])).

fof(f97,plain,(
    ! [X3,X1] :
      ( r2_hidden(X3,X1)
      | k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X3) != X1 ) ),
    inference(equality_resolution,[],[f88])).

fof(f98,plain,(
    ! [X3] : r2_hidden(X3,k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X3)) ),
    inference(equality_resolution,[],[f97])).

fof(f74,plain,(
    k1_tarski(sK4) != sK3 ),
    inference(cnf_transformation,[],[f42])).

fof(f93,plain,(
    k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) != sK3 ),
    inference(definition_unfolding,[],[f74,f83])).

fof(f73,plain,(
    k1_xboole_0 != sK3 ),
    inference(cnf_transformation,[],[f42])).

cnf(c_15,plain,
    ( ~ r2_hidden(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))
    | X0 = X1 ),
    inference(cnf_transformation,[],[f99])).

cnf(c_36343,plain,
    ( ~ r2_hidden(sK1(sK3),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))
    | sK1(sK3) = X0 ),
    inference(instantiation,[status(thm)],[c_15])).

cnf(c_36345,plain,
    ( ~ r2_hidden(sK1(sK3),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))
    | sK1(sK3) = sK4 ),
    inference(instantiation,[status(thm)],[c_36343])).

cnf(c_339,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_30101,plain,
    ( sK1(sK3) != X0
    | sK4 != X0
    | sK4 = sK1(sK3) ),
    inference(instantiation,[status(thm)],[c_339])).

cnf(c_30102,plain,
    ( sK1(sK3) != sK4
    | sK4 = sK1(sK3)
    | sK4 != sK4 ),
    inference(instantiation,[status(thm)],[c_30101])).

cnf(c_341,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_2341,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(sK1(sK3),sK3)
    | X0 != sK1(sK3)
    | X1 != sK3 ),
    inference(instantiation,[status(thm)],[c_341])).

cnf(c_9293,plain,
    ( ~ r2_hidden(sK1(sK3),sK3)
    | r2_hidden(sK4,sK3)
    | sK3 != sK3
    | sK4 != sK1(sK3) ),
    inference(instantiation,[status(thm)],[c_2341])).

cnf(c_2,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | ~ r1_tarski(X1,X2) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_1886,plain,
    ( r2_hidden(sK1(sK3),X0)
    | ~ r2_hidden(sK1(sK3),sK3)
    | ~ r1_tarski(sK3,X0) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_9030,plain,
    ( r2_hidden(sK1(sK3),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))
    | ~ r2_hidden(sK1(sK3),sK3)
    | ~ r1_tarski(sK3,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)) ),
    inference(instantiation,[status(thm)],[c_1886])).

cnf(c_11,plain,
    ( k5_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f55])).

cnf(c_10,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_21,negated_conjecture,
    ( k1_xboole_0 = k5_xboole_0(sK3,k5_xboole_0(k5_xboole_0(sK3,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)),k3_tarski(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))))) ),
    inference(cnf_transformation,[],[f94])).

cnf(c_1080,plain,
    ( k5_xboole_0(sK3,k5_xboole_0(sK3,k5_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k3_tarski(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)))))) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_10,c_21])).

cnf(c_1334,plain,
    ( k5_xboole_0(sK3,k5_xboole_0(k5_xboole_0(sK3,k5_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k3_tarski(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))))),X0)) = k5_xboole_0(k1_xboole_0,X0) ),
    inference(superposition,[status(thm)],[c_1080,c_10])).

cnf(c_3,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X0),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))) = X0 ),
    inference(cnf_transformation,[],[f84])).

cnf(c_18,plain,
    ( k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) = X0 ),
    inference(cnf_transformation,[],[f92])).

cnf(c_683,plain,
    ( k5_xboole_0(k1_xboole_0,X0) = X0 ),
    inference(light_normalisation,[status(thm)],[c_3,c_11,c_18])).

cnf(c_1335,plain,
    ( k5_xboole_0(sK3,k5_xboole_0(k5_xboole_0(sK3,k5_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k3_tarski(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))))),X0)) = X0 ),
    inference(light_normalisation,[status(thm)],[c_1334,c_683])).

cnf(c_1429,plain,
    ( k5_xboole_0(sK3,k5_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k3_tarski(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))))) = k5_xboole_0(sK3,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_11,c_1335])).

cnf(c_8,plain,
    ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f52])).

cnf(c_1438,plain,
    ( k5_xboole_0(sK3,k5_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k3_tarski(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))))) = sK3 ),
    inference(demodulation,[status(thm)],[c_1429,c_8])).

cnf(c_1443,plain,
    ( k5_xboole_0(sK3,k5_xboole_0(sK3,X0)) = X0 ),
    inference(demodulation,[status(thm)],[c_1438,c_1335])).

cnf(c_1453,plain,
    ( k5_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k3_tarski(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1443,c_1080])).

cnf(c_1585,plain,
    ( k5_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k5_xboole_0(k3_tarski(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))),X0)) = k5_xboole_0(k1_xboole_0,X0) ),
    inference(superposition,[status(thm)],[c_1453,c_10])).

cnf(c_1586,plain,
    ( k5_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k5_xboole_0(k3_tarski(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))),X0)) = X0 ),
    inference(light_normalisation,[status(thm)],[c_1585,c_683])).

cnf(c_1589,plain,
    ( k3_tarski(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))) = k5_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_11,c_1586])).

cnf(c_1597,plain,
    ( k3_tarski(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))) = k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) ),
    inference(demodulation,[status(thm)],[c_1589,c_8])).

cnf(c_9,plain,
    ( r1_tarski(X0,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_676,plain,
    ( r1_tarski(X0,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_5614,plain,
    ( r1_tarski(sK3,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1597,c_676])).

cnf(c_5615,plain,
    ( r1_tarski(sK3,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_5614])).

cnf(c_710,plain,
    ( k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) != X0
    | k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) = sK3
    | sK3 != X0 ),
    inference(instantiation,[status(thm)],[c_339])).

cnf(c_2153,plain,
    ( k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) != k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)
    | k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) = sK3
    | sK3 != k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) ),
    inference(instantiation,[status(thm)],[c_710])).

cnf(c_7,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f96])).

cnf(c_1204,plain,
    ( r1_tarski(sK3,sK3) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_5,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f50])).

cnf(c_806,plain,
    ( ~ r1_tarski(X0,sK3)
    | ~ r1_tarski(sK3,X0)
    | sK3 = X0 ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_933,plain,
    ( ~ r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),sK3)
    | ~ r1_tarski(sK3,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))
    | sK3 = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
    inference(instantiation,[status(thm)],[c_806])).

cnf(c_935,plain,
    ( ~ r1_tarski(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),sK3)
    | ~ r1_tarski(sK3,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))
    | sK3 = k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) ),
    inference(instantiation,[status(thm)],[c_933])).

cnf(c_930,plain,
    ( ~ r1_tarski(sK3,sK3)
    | sK3 = sK3 ),
    inference(instantiation,[status(thm)],[c_806])).

cnf(c_16,plain,
    ( ~ r2_hidden(X0,X1)
    | r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_746,plain,
    ( ~ r2_hidden(sK4,sK3)
    | r1_tarski(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),sK3) ),
    inference(instantiation,[status(thm)],[c_16])).

cnf(c_4,plain,
    ( r2_hidden(sK1(X0),X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f47])).

cnf(c_716,plain,
    ( r2_hidden(sK1(sK3),sK3)
    | k1_xboole_0 = sK3 ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_343,plain,
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

cnf(c_348,plain,
    ( k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) = k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)
    | sK4 != sK4 ),
    inference(instantiation,[status(thm)],[c_343])).

cnf(c_14,plain,
    ( r2_hidden(X0,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) ),
    inference(cnf_transformation,[],[f98])).

cnf(c_33,plain,
    ( r2_hidden(sK4,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)) ),
    inference(instantiation,[status(thm)],[c_14])).

cnf(c_30,plain,
    ( ~ r2_hidden(sK4,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))
    | sK4 = sK4 ),
    inference(instantiation,[status(thm)],[c_15])).

cnf(c_19,negated_conjecture,
    ( k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) != sK3 ),
    inference(cnf_transformation,[],[f93])).

cnf(c_20,negated_conjecture,
    ( k1_xboole_0 != sK3 ),
    inference(cnf_transformation,[],[f73])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_36345,c_30102,c_9293,c_9030,c_5615,c_2153,c_1204,c_935,c_930,c_746,c_716,c_348,c_33,c_30,c_19,c_20])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 13:25:12 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 7.68/1.53  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.68/1.53  
% 7.68/1.53  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.68/1.53  
% 7.68/1.53  ------  iProver source info
% 7.68/1.53  
% 7.68/1.53  git: date: 2020-06-30 10:37:57 +0100
% 7.68/1.53  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.68/1.53  git: non_committed_changes: false
% 7.68/1.53  git: last_make_outside_of_git: false
% 7.68/1.53  
% 7.68/1.53  ------ 
% 7.68/1.53  
% 7.68/1.53  ------ Input Options
% 7.68/1.53  
% 7.68/1.53  --out_options                           all
% 7.68/1.53  --tptp_safe_out                         true
% 7.68/1.53  --problem_path                          ""
% 7.68/1.53  --include_path                          ""
% 7.68/1.53  --clausifier                            res/vclausify_rel
% 7.68/1.53  --clausifier_options                    ""
% 7.68/1.53  --stdin                                 false
% 7.68/1.53  --stats_out                             all
% 7.68/1.53  
% 7.68/1.53  ------ General Options
% 7.68/1.53  
% 7.68/1.53  --fof                                   false
% 7.68/1.53  --time_out_real                         305.
% 7.68/1.53  --time_out_virtual                      -1.
% 7.68/1.53  --symbol_type_check                     false
% 7.68/1.53  --clausify_out                          false
% 7.68/1.53  --sig_cnt_out                           false
% 7.68/1.53  --trig_cnt_out                          false
% 7.68/1.53  --trig_cnt_out_tolerance                1.
% 7.68/1.53  --trig_cnt_out_sk_spl                   false
% 7.68/1.53  --abstr_cl_out                          false
% 7.68/1.53  
% 7.68/1.53  ------ Global Options
% 7.68/1.53  
% 7.68/1.53  --schedule                              default
% 7.68/1.53  --add_important_lit                     false
% 7.68/1.53  --prop_solver_per_cl                    1000
% 7.68/1.53  --min_unsat_core                        false
% 7.68/1.53  --soft_assumptions                      false
% 7.68/1.53  --soft_lemma_size                       3
% 7.68/1.53  --prop_impl_unit_size                   0
% 7.68/1.53  --prop_impl_unit                        []
% 7.68/1.53  --share_sel_clauses                     true
% 7.68/1.53  --reset_solvers                         false
% 7.68/1.53  --bc_imp_inh                            [conj_cone]
% 7.68/1.53  --conj_cone_tolerance                   3.
% 7.68/1.53  --extra_neg_conj                        none
% 7.68/1.53  --large_theory_mode                     true
% 7.68/1.53  --prolific_symb_bound                   200
% 7.68/1.53  --lt_threshold                          2000
% 7.68/1.53  --clause_weak_htbl                      true
% 7.68/1.53  --gc_record_bc_elim                     false
% 7.68/1.53  
% 7.68/1.53  ------ Preprocessing Options
% 7.68/1.53  
% 7.68/1.53  --preprocessing_flag                    true
% 7.68/1.53  --time_out_prep_mult                    0.1
% 7.68/1.53  --splitting_mode                        input
% 7.68/1.53  --splitting_grd                         true
% 7.68/1.53  --splitting_cvd                         false
% 7.68/1.53  --splitting_cvd_svl                     false
% 7.68/1.53  --splitting_nvd                         32
% 7.68/1.53  --sub_typing                            true
% 7.68/1.53  --prep_gs_sim                           true
% 7.68/1.53  --prep_unflatten                        true
% 7.68/1.53  --prep_res_sim                          true
% 7.68/1.53  --prep_upred                            true
% 7.68/1.53  --prep_sem_filter                       exhaustive
% 7.68/1.53  --prep_sem_filter_out                   false
% 7.68/1.53  --pred_elim                             true
% 7.68/1.53  --res_sim_input                         true
% 7.68/1.53  --eq_ax_congr_red                       true
% 7.68/1.53  --pure_diseq_elim                       true
% 7.68/1.53  --brand_transform                       false
% 7.68/1.53  --non_eq_to_eq                          false
% 7.68/1.53  --prep_def_merge                        true
% 7.68/1.53  --prep_def_merge_prop_impl              false
% 7.68/1.53  --prep_def_merge_mbd                    true
% 7.68/1.53  --prep_def_merge_tr_red                 false
% 7.68/1.53  --prep_def_merge_tr_cl                  false
% 7.68/1.53  --smt_preprocessing                     true
% 7.68/1.53  --smt_ac_axioms                         fast
% 7.68/1.53  --preprocessed_out                      false
% 7.68/1.53  --preprocessed_stats                    false
% 7.68/1.53  
% 7.68/1.53  ------ Abstraction refinement Options
% 7.68/1.53  
% 7.68/1.53  --abstr_ref                             []
% 7.68/1.53  --abstr_ref_prep                        false
% 7.68/1.53  --abstr_ref_until_sat                   false
% 7.68/1.53  --abstr_ref_sig_restrict                funpre
% 7.68/1.53  --abstr_ref_af_restrict_to_split_sk     false
% 7.68/1.53  --abstr_ref_under                       []
% 7.68/1.53  
% 7.68/1.53  ------ SAT Options
% 7.68/1.53  
% 7.68/1.53  --sat_mode                              false
% 7.68/1.53  --sat_fm_restart_options                ""
% 7.68/1.53  --sat_gr_def                            false
% 7.68/1.53  --sat_epr_types                         true
% 7.68/1.53  --sat_non_cyclic_types                  false
% 7.68/1.53  --sat_finite_models                     false
% 7.68/1.53  --sat_fm_lemmas                         false
% 7.68/1.53  --sat_fm_prep                           false
% 7.68/1.53  --sat_fm_uc_incr                        true
% 7.68/1.53  --sat_out_model                         small
% 7.68/1.53  --sat_out_clauses                       false
% 7.68/1.53  
% 7.68/1.53  ------ QBF Options
% 7.68/1.53  
% 7.68/1.53  --qbf_mode                              false
% 7.68/1.53  --qbf_elim_univ                         false
% 7.68/1.53  --qbf_dom_inst                          none
% 7.68/1.53  --qbf_dom_pre_inst                      false
% 7.68/1.53  --qbf_sk_in                             false
% 7.68/1.53  --qbf_pred_elim                         true
% 7.68/1.53  --qbf_split                             512
% 7.68/1.53  
% 7.68/1.53  ------ BMC1 Options
% 7.68/1.53  
% 7.68/1.53  --bmc1_incremental                      false
% 7.68/1.53  --bmc1_axioms                           reachable_all
% 7.68/1.53  --bmc1_min_bound                        0
% 7.68/1.53  --bmc1_max_bound                        -1
% 7.68/1.53  --bmc1_max_bound_default                -1
% 7.68/1.53  --bmc1_symbol_reachability              true
% 7.68/1.53  --bmc1_property_lemmas                  false
% 7.68/1.53  --bmc1_k_induction                      false
% 7.68/1.53  --bmc1_non_equiv_states                 false
% 7.68/1.53  --bmc1_deadlock                         false
% 7.68/1.53  --bmc1_ucm                              false
% 7.68/1.53  --bmc1_add_unsat_core                   none
% 7.68/1.53  --bmc1_unsat_core_children              false
% 7.68/1.53  --bmc1_unsat_core_extrapolate_axioms    false
% 7.68/1.53  --bmc1_out_stat                         full
% 7.68/1.53  --bmc1_ground_init                      false
% 7.68/1.53  --bmc1_pre_inst_next_state              false
% 7.68/1.53  --bmc1_pre_inst_state                   false
% 7.68/1.53  --bmc1_pre_inst_reach_state             false
% 7.68/1.53  --bmc1_out_unsat_core                   false
% 7.68/1.53  --bmc1_aig_witness_out                  false
% 7.68/1.53  --bmc1_verbose                          false
% 7.68/1.53  --bmc1_dump_clauses_tptp                false
% 7.68/1.53  --bmc1_dump_unsat_core_tptp             false
% 7.68/1.53  --bmc1_dump_file                        -
% 7.68/1.53  --bmc1_ucm_expand_uc_limit              128
% 7.68/1.53  --bmc1_ucm_n_expand_iterations          6
% 7.68/1.53  --bmc1_ucm_extend_mode                  1
% 7.68/1.53  --bmc1_ucm_init_mode                    2
% 7.68/1.53  --bmc1_ucm_cone_mode                    none
% 7.68/1.53  --bmc1_ucm_reduced_relation_type        0
% 7.68/1.53  --bmc1_ucm_relax_model                  4
% 7.68/1.53  --bmc1_ucm_full_tr_after_sat            true
% 7.68/1.53  --bmc1_ucm_expand_neg_assumptions       false
% 7.68/1.53  --bmc1_ucm_layered_model                none
% 7.68/1.53  --bmc1_ucm_max_lemma_size               10
% 7.68/1.53  
% 7.68/1.53  ------ AIG Options
% 7.68/1.53  
% 7.68/1.53  --aig_mode                              false
% 7.68/1.53  
% 7.68/1.53  ------ Instantiation Options
% 7.68/1.53  
% 7.68/1.53  --instantiation_flag                    true
% 7.68/1.53  --inst_sos_flag                         true
% 7.68/1.53  --inst_sos_phase                        true
% 7.68/1.53  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.68/1.53  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.68/1.53  --inst_lit_sel_side                     num_symb
% 7.68/1.53  --inst_solver_per_active                1400
% 7.68/1.53  --inst_solver_calls_frac                1.
% 7.68/1.53  --inst_passive_queue_type               priority_queues
% 7.68/1.53  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.68/1.53  --inst_passive_queues_freq              [25;2]
% 7.68/1.53  --inst_dismatching                      true
% 7.68/1.53  --inst_eager_unprocessed_to_passive     true
% 7.68/1.53  --inst_prop_sim_given                   true
% 7.68/1.53  --inst_prop_sim_new                     false
% 7.68/1.53  --inst_subs_new                         false
% 7.68/1.53  --inst_eq_res_simp                      false
% 7.68/1.53  --inst_subs_given                       false
% 7.68/1.53  --inst_orphan_elimination               true
% 7.68/1.53  --inst_learning_loop_flag               true
% 7.68/1.53  --inst_learning_start                   3000
% 7.68/1.53  --inst_learning_factor                  2
% 7.68/1.53  --inst_start_prop_sim_after_learn       3
% 7.68/1.53  --inst_sel_renew                        solver
% 7.68/1.53  --inst_lit_activity_flag                true
% 7.68/1.53  --inst_restr_to_given                   false
% 7.68/1.53  --inst_activity_threshold               500
% 7.68/1.53  --inst_out_proof                        true
% 7.68/1.53  
% 7.68/1.53  ------ Resolution Options
% 7.68/1.53  
% 7.68/1.53  --resolution_flag                       true
% 7.68/1.53  --res_lit_sel                           adaptive
% 7.68/1.53  --res_lit_sel_side                      none
% 7.68/1.53  --res_ordering                          kbo
% 7.68/1.53  --res_to_prop_solver                    active
% 7.68/1.53  --res_prop_simpl_new                    false
% 7.68/1.53  --res_prop_simpl_given                  true
% 7.68/1.53  --res_passive_queue_type                priority_queues
% 7.68/1.53  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.68/1.53  --res_passive_queues_freq               [15;5]
% 7.68/1.53  --res_forward_subs                      full
% 7.68/1.53  --res_backward_subs                     full
% 7.68/1.53  --res_forward_subs_resolution           true
% 7.68/1.53  --res_backward_subs_resolution          true
% 7.68/1.53  --res_orphan_elimination                true
% 7.68/1.53  --res_time_limit                        2.
% 7.68/1.53  --res_out_proof                         true
% 7.68/1.53  
% 7.68/1.53  ------ Superposition Options
% 7.68/1.53  
% 7.68/1.53  --superposition_flag                    true
% 7.68/1.53  --sup_passive_queue_type                priority_queues
% 7.68/1.53  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.68/1.53  --sup_passive_queues_freq               [8;1;4]
% 7.68/1.53  --demod_completeness_check              fast
% 7.68/1.53  --demod_use_ground                      true
% 7.68/1.53  --sup_to_prop_solver                    passive
% 7.68/1.53  --sup_prop_simpl_new                    true
% 7.68/1.53  --sup_prop_simpl_given                  true
% 7.68/1.53  --sup_fun_splitting                     true
% 7.68/1.53  --sup_smt_interval                      50000
% 7.68/1.53  
% 7.68/1.53  ------ Superposition Simplification Setup
% 7.68/1.53  
% 7.68/1.53  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 7.68/1.53  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 7.68/1.53  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 7.68/1.53  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 7.68/1.53  --sup_full_triv                         [TrivRules;PropSubs]
% 7.68/1.53  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 7.68/1.53  --sup_full_bw                           [BwDemod;BwSubsumption]
% 7.68/1.53  --sup_immed_triv                        [TrivRules]
% 7.68/1.53  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.68/1.53  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.68/1.53  --sup_immed_bw_main                     []
% 7.68/1.53  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 7.68/1.53  --sup_input_triv                        [Unflattening;TrivRules]
% 7.68/1.53  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.68/1.53  --sup_input_bw                          []
% 7.68/1.53  
% 7.68/1.53  ------ Combination Options
% 7.68/1.53  
% 7.68/1.53  --comb_res_mult                         3
% 7.68/1.53  --comb_sup_mult                         2
% 7.68/1.53  --comb_inst_mult                        10
% 7.68/1.53  
% 7.68/1.53  ------ Debug Options
% 7.68/1.53  
% 7.68/1.53  --dbg_backtrace                         false
% 7.68/1.53  --dbg_dump_prop_clauses                 false
% 7.68/1.53  --dbg_dump_prop_clauses_file            -
% 7.68/1.53  --dbg_out_stat                          false
% 7.68/1.53  ------ Parsing...
% 7.68/1.53  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.68/1.53  
% 7.68/1.53  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e  sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 7.68/1.53  
% 7.68/1.53  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.68/1.53  
% 7.68/1.53  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.68/1.53  ------ Proving...
% 7.68/1.53  ------ Problem Properties 
% 7.68/1.53  
% 7.68/1.53  
% 7.68/1.53  clauses                                 21
% 7.68/1.53  conjectures                             3
% 7.68/1.53  EPR                                     4
% 7.68/1.53  Horn                                    18
% 7.68/1.53  unary                                   11
% 7.68/1.53  binary                                  6
% 7.68/1.53  lits                                    35
% 7.68/1.53  lits eq                                 15
% 7.68/1.53  fd_pure                                 0
% 7.68/1.53  fd_pseudo                               0
% 7.68/1.53  fd_cond                                 1
% 7.68/1.53  fd_pseudo_cond                          3
% 7.68/1.53  AC symbols                              0
% 7.68/1.53  
% 7.68/1.53  ------ Schedule dynamic 5 is on 
% 7.68/1.53  
% 7.68/1.53  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 7.68/1.53  
% 7.68/1.53  
% 7.68/1.53  ------ 
% 7.68/1.53  Current options:
% 7.68/1.53  ------ 
% 7.68/1.53  
% 7.68/1.53  ------ Input Options
% 7.68/1.53  
% 7.68/1.53  --out_options                           all
% 7.68/1.53  --tptp_safe_out                         true
% 7.68/1.53  --problem_path                          ""
% 7.68/1.53  --include_path                          ""
% 7.68/1.53  --clausifier                            res/vclausify_rel
% 7.68/1.53  --clausifier_options                    ""
% 7.68/1.53  --stdin                                 false
% 7.68/1.53  --stats_out                             all
% 7.68/1.53  
% 7.68/1.53  ------ General Options
% 7.68/1.53  
% 7.68/1.53  --fof                                   false
% 7.68/1.53  --time_out_real                         305.
% 7.68/1.53  --time_out_virtual                      -1.
% 7.68/1.53  --symbol_type_check                     false
% 7.68/1.53  --clausify_out                          false
% 7.68/1.53  --sig_cnt_out                           false
% 7.68/1.53  --trig_cnt_out                          false
% 7.68/1.53  --trig_cnt_out_tolerance                1.
% 7.68/1.53  --trig_cnt_out_sk_spl                   false
% 7.68/1.53  --abstr_cl_out                          false
% 7.68/1.53  
% 7.68/1.53  ------ Global Options
% 7.68/1.53  
% 7.68/1.53  --schedule                              default
% 7.68/1.53  --add_important_lit                     false
% 7.68/1.53  --prop_solver_per_cl                    1000
% 7.68/1.53  --min_unsat_core                        false
% 7.68/1.53  --soft_assumptions                      false
% 7.68/1.53  --soft_lemma_size                       3
% 7.68/1.53  --prop_impl_unit_size                   0
% 7.68/1.53  --prop_impl_unit                        []
% 7.68/1.53  --share_sel_clauses                     true
% 7.68/1.53  --reset_solvers                         false
% 7.68/1.53  --bc_imp_inh                            [conj_cone]
% 7.68/1.53  --conj_cone_tolerance                   3.
% 7.68/1.53  --extra_neg_conj                        none
% 7.68/1.53  --large_theory_mode                     true
% 7.68/1.53  --prolific_symb_bound                   200
% 7.68/1.53  --lt_threshold                          2000
% 7.68/1.53  --clause_weak_htbl                      true
% 7.68/1.53  --gc_record_bc_elim                     false
% 7.68/1.53  
% 7.68/1.53  ------ Preprocessing Options
% 7.68/1.53  
% 7.68/1.53  --preprocessing_flag                    true
% 7.68/1.53  --time_out_prep_mult                    0.1
% 7.68/1.53  --splitting_mode                        input
% 7.68/1.53  --splitting_grd                         true
% 7.68/1.53  --splitting_cvd                         false
% 7.68/1.53  --splitting_cvd_svl                     false
% 7.68/1.53  --splitting_nvd                         32
% 7.68/1.53  --sub_typing                            true
% 7.68/1.53  --prep_gs_sim                           true
% 7.68/1.53  --prep_unflatten                        true
% 7.68/1.53  --prep_res_sim                          true
% 7.68/1.53  --prep_upred                            true
% 7.68/1.53  --prep_sem_filter                       exhaustive
% 7.68/1.53  --prep_sem_filter_out                   false
% 7.68/1.53  --pred_elim                             true
% 7.68/1.53  --res_sim_input                         true
% 7.68/1.53  --eq_ax_congr_red                       true
% 7.68/1.53  --pure_diseq_elim                       true
% 7.68/1.53  --brand_transform                       false
% 7.68/1.53  --non_eq_to_eq                          false
% 7.68/1.53  --prep_def_merge                        true
% 7.68/1.53  --prep_def_merge_prop_impl              false
% 7.68/1.53  --prep_def_merge_mbd                    true
% 7.68/1.53  --prep_def_merge_tr_red                 false
% 7.68/1.53  --prep_def_merge_tr_cl                  false
% 7.68/1.53  --smt_preprocessing                     true
% 7.68/1.53  --smt_ac_axioms                         fast
% 7.68/1.53  --preprocessed_out                      false
% 7.68/1.53  --preprocessed_stats                    false
% 7.68/1.53  
% 7.68/1.53  ------ Abstraction refinement Options
% 7.68/1.53  
% 7.68/1.53  --abstr_ref                             []
% 7.68/1.53  --abstr_ref_prep                        false
% 7.68/1.53  --abstr_ref_until_sat                   false
% 7.68/1.53  --abstr_ref_sig_restrict                funpre
% 7.68/1.53  --abstr_ref_af_restrict_to_split_sk     false
% 7.68/1.53  --abstr_ref_under                       []
% 7.68/1.53  
% 7.68/1.53  ------ SAT Options
% 7.68/1.53  
% 7.68/1.53  --sat_mode                              false
% 7.68/1.53  --sat_fm_restart_options                ""
% 7.68/1.53  --sat_gr_def                            false
% 7.68/1.53  --sat_epr_types                         true
% 7.68/1.53  --sat_non_cyclic_types                  false
% 7.68/1.53  --sat_finite_models                     false
% 7.68/1.53  --sat_fm_lemmas                         false
% 7.68/1.53  --sat_fm_prep                           false
% 7.68/1.53  --sat_fm_uc_incr                        true
% 7.68/1.53  --sat_out_model                         small
% 7.68/1.53  --sat_out_clauses                       false
% 7.68/1.53  
% 7.68/1.53  ------ QBF Options
% 7.68/1.53  
% 7.68/1.53  --qbf_mode                              false
% 7.68/1.53  --qbf_elim_univ                         false
% 7.68/1.53  --qbf_dom_inst                          none
% 7.68/1.53  --qbf_dom_pre_inst                      false
% 7.68/1.53  --qbf_sk_in                             false
% 7.68/1.53  --qbf_pred_elim                         true
% 7.68/1.53  --qbf_split                             512
% 7.68/1.53  
% 7.68/1.53  ------ BMC1 Options
% 7.68/1.53  
% 7.68/1.53  --bmc1_incremental                      false
% 7.68/1.53  --bmc1_axioms                           reachable_all
% 7.68/1.53  --bmc1_min_bound                        0
% 7.68/1.53  --bmc1_max_bound                        -1
% 7.68/1.53  --bmc1_max_bound_default                -1
% 7.68/1.53  --bmc1_symbol_reachability              true
% 7.68/1.53  --bmc1_property_lemmas                  false
% 7.68/1.53  --bmc1_k_induction                      false
% 7.68/1.53  --bmc1_non_equiv_states                 false
% 7.68/1.53  --bmc1_deadlock                         false
% 7.68/1.53  --bmc1_ucm                              false
% 7.68/1.53  --bmc1_add_unsat_core                   none
% 7.68/1.53  --bmc1_unsat_core_children              false
% 7.68/1.53  --bmc1_unsat_core_extrapolate_axioms    false
% 7.68/1.53  --bmc1_out_stat                         full
% 7.68/1.53  --bmc1_ground_init                      false
% 7.68/1.53  --bmc1_pre_inst_next_state              false
% 7.68/1.53  --bmc1_pre_inst_state                   false
% 7.68/1.53  --bmc1_pre_inst_reach_state             false
% 7.68/1.53  --bmc1_out_unsat_core                   false
% 7.68/1.53  --bmc1_aig_witness_out                  false
% 7.68/1.53  --bmc1_verbose                          false
% 7.68/1.53  --bmc1_dump_clauses_tptp                false
% 7.68/1.53  --bmc1_dump_unsat_core_tptp             false
% 7.68/1.53  --bmc1_dump_file                        -
% 7.68/1.53  --bmc1_ucm_expand_uc_limit              128
% 7.68/1.53  --bmc1_ucm_n_expand_iterations          6
% 7.68/1.53  --bmc1_ucm_extend_mode                  1
% 7.68/1.53  --bmc1_ucm_init_mode                    2
% 7.68/1.53  --bmc1_ucm_cone_mode                    none
% 7.68/1.53  --bmc1_ucm_reduced_relation_type        0
% 7.68/1.53  --bmc1_ucm_relax_model                  4
% 7.68/1.53  --bmc1_ucm_full_tr_after_sat            true
% 7.68/1.53  --bmc1_ucm_expand_neg_assumptions       false
% 7.68/1.53  --bmc1_ucm_layered_model                none
% 7.68/1.53  --bmc1_ucm_max_lemma_size               10
% 7.68/1.53  
% 7.68/1.53  ------ AIG Options
% 7.68/1.53  
% 7.68/1.53  --aig_mode                              false
% 7.68/1.53  
% 7.68/1.53  ------ Instantiation Options
% 7.68/1.53  
% 7.68/1.53  --instantiation_flag                    true
% 7.68/1.53  --inst_sos_flag                         true
% 7.68/1.53  --inst_sos_phase                        true
% 7.68/1.53  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.68/1.53  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.68/1.53  --inst_lit_sel_side                     none
% 7.68/1.53  --inst_solver_per_active                1400
% 7.68/1.53  --inst_solver_calls_frac                1.
% 7.68/1.53  --inst_passive_queue_type               priority_queues
% 7.68/1.53  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.68/1.53  --inst_passive_queues_freq              [25;2]
% 7.68/1.53  --inst_dismatching                      true
% 7.68/1.53  --inst_eager_unprocessed_to_passive     true
% 7.68/1.53  --inst_prop_sim_given                   true
% 7.68/1.53  --inst_prop_sim_new                     false
% 7.68/1.53  --inst_subs_new                         false
% 7.68/1.53  --inst_eq_res_simp                      false
% 7.68/1.53  --inst_subs_given                       false
% 7.68/1.53  --inst_orphan_elimination               true
% 7.68/1.53  --inst_learning_loop_flag               true
% 7.68/1.53  --inst_learning_start                   3000
% 7.68/1.53  --inst_learning_factor                  2
% 7.68/1.53  --inst_start_prop_sim_after_learn       3
% 7.68/1.53  --inst_sel_renew                        solver
% 7.68/1.53  --inst_lit_activity_flag                true
% 7.68/1.53  --inst_restr_to_given                   false
% 7.68/1.53  --inst_activity_threshold               500
% 7.68/1.53  --inst_out_proof                        true
% 7.68/1.53  
% 7.68/1.53  ------ Resolution Options
% 7.68/1.53  
% 7.68/1.53  --resolution_flag                       false
% 7.68/1.53  --res_lit_sel                           adaptive
% 7.68/1.53  --res_lit_sel_side                      none
% 7.68/1.53  --res_ordering                          kbo
% 7.68/1.53  --res_to_prop_solver                    active
% 7.68/1.53  --res_prop_simpl_new                    false
% 7.68/1.53  --res_prop_simpl_given                  true
% 7.68/1.53  --res_passive_queue_type                priority_queues
% 7.68/1.53  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.68/1.53  --res_passive_queues_freq               [15;5]
% 7.68/1.53  --res_forward_subs                      full
% 7.68/1.53  --res_backward_subs                     full
% 7.68/1.53  --res_forward_subs_resolution           true
% 7.68/1.53  --res_backward_subs_resolution          true
% 7.68/1.53  --res_orphan_elimination                true
% 7.68/1.53  --res_time_limit                        2.
% 7.68/1.53  --res_out_proof                         true
% 7.68/1.53  
% 7.68/1.53  ------ Superposition Options
% 7.68/1.53  
% 7.68/1.53  --superposition_flag                    true
% 7.68/1.53  --sup_passive_queue_type                priority_queues
% 7.68/1.53  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.68/1.53  --sup_passive_queues_freq               [8;1;4]
% 7.68/1.53  --demod_completeness_check              fast
% 7.68/1.53  --demod_use_ground                      true
% 7.68/1.53  --sup_to_prop_solver                    passive
% 7.68/1.53  --sup_prop_simpl_new                    true
% 7.68/1.53  --sup_prop_simpl_given                  true
% 7.68/1.53  --sup_fun_splitting                     true
% 7.68/1.53  --sup_smt_interval                      50000
% 7.68/1.53  
% 7.68/1.53  ------ Superposition Simplification Setup
% 7.68/1.53  
% 7.68/1.53  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 7.68/1.53  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 7.68/1.53  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 7.68/1.53  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 7.68/1.53  --sup_full_triv                         [TrivRules;PropSubs]
% 7.68/1.53  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 7.68/1.53  --sup_full_bw                           [BwDemod;BwSubsumption]
% 7.68/1.53  --sup_immed_triv                        [TrivRules]
% 7.68/1.53  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.68/1.53  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.68/1.53  --sup_immed_bw_main                     []
% 7.68/1.53  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 7.68/1.53  --sup_input_triv                        [Unflattening;TrivRules]
% 7.68/1.53  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.68/1.53  --sup_input_bw                          []
% 7.68/1.53  
% 7.68/1.53  ------ Combination Options
% 7.68/1.53  
% 7.68/1.53  --comb_res_mult                         3
% 7.68/1.53  --comb_sup_mult                         2
% 7.68/1.53  --comb_inst_mult                        10
% 7.68/1.53  
% 7.68/1.53  ------ Debug Options
% 7.68/1.53  
% 7.68/1.53  --dbg_backtrace                         false
% 7.68/1.53  --dbg_dump_prop_clauses                 false
% 7.68/1.53  --dbg_dump_prop_clauses_file            -
% 7.68/1.53  --dbg_out_stat                          false
% 7.68/1.53  
% 7.68/1.53  
% 7.68/1.53  
% 7.68/1.53  
% 7.68/1.53  ------ Proving...
% 7.68/1.53  
% 7.68/1.53  
% 7.68/1.53  % SZS status Theorem for theBenchmark.p
% 7.68/1.53  
% 7.68/1.53  % SZS output start CNFRefutation for theBenchmark.p
% 7.68/1.53  
% 7.68/1.53  fof(f11,axiom,(
% 7.68/1.53    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 7.68/1.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.68/1.53  
% 7.68/1.53  fof(f36,plain,(
% 7.68/1.53    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | X0 != X2) & (X0 = X2 | ~r2_hidden(X2,X1))) | k1_tarski(X0) != X1))),
% 7.68/1.53    inference(nnf_transformation,[],[f11])).
% 7.68/1.53  
% 7.68/1.53  fof(f37,plain,(
% 7.68/1.53    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 7.68/1.53    inference(rectify,[],[f36])).
% 7.68/1.53  
% 7.68/1.53  fof(f38,plain,(
% 7.68/1.53    ! [X1,X0] : (? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1))) => ((sK2(X0,X1) != X0 | ~r2_hidden(sK2(X0,X1),X1)) & (sK2(X0,X1) = X0 | r2_hidden(sK2(X0,X1),X1))))),
% 7.68/1.53    introduced(choice_axiom,[])).
% 7.68/1.53  
% 7.68/1.53  fof(f39,plain,(
% 7.68/1.53    ! [X0,X1] : ((k1_tarski(X0) = X1 | ((sK2(X0,X1) != X0 | ~r2_hidden(sK2(X0,X1),X1)) & (sK2(X0,X1) = X0 | r2_hidden(sK2(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 7.68/1.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f37,f38])).
% 7.68/1.53  
% 7.68/1.53  fof(f57,plain,(
% 7.68/1.53    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k1_tarski(X0) != X1) )),
% 7.68/1.53    inference(cnf_transformation,[],[f39])).
% 7.68/1.53  
% 7.68/1.53  fof(f12,axiom,(
% 7.68/1.53    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)),
% 7.68/1.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.68/1.53  
% 7.68/1.53  fof(f61,plain,(
% 7.68/1.53    ( ! [X0] : (k1_tarski(X0) = k2_tarski(X0,X0)) )),
% 7.68/1.53    inference(cnf_transformation,[],[f12])).
% 7.68/1.53  
% 7.68/1.53  fof(f13,axiom,(
% 7.68/1.53    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 7.68/1.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.68/1.53  
% 7.68/1.53  fof(f62,plain,(
% 7.68/1.53    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 7.68/1.53    inference(cnf_transformation,[],[f13])).
% 7.68/1.53  
% 7.68/1.53  fof(f14,axiom,(
% 7.68/1.53    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 7.68/1.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.68/1.53  
% 7.68/1.53  fof(f63,plain,(
% 7.68/1.53    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 7.68/1.53    inference(cnf_transformation,[],[f14])).
% 7.68/1.53  
% 7.68/1.53  fof(f15,axiom,(
% 7.68/1.53    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 7.68/1.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.68/1.53  
% 7.68/1.53  fof(f64,plain,(
% 7.68/1.53    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 7.68/1.53    inference(cnf_transformation,[],[f15])).
% 7.68/1.53  
% 7.68/1.53  fof(f16,axiom,(
% 7.68/1.53    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)),
% 7.68/1.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.68/1.53  
% 7.68/1.53  fof(f65,plain,(
% 7.68/1.53    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)) )),
% 7.68/1.53    inference(cnf_transformation,[],[f16])).
% 7.68/1.53  
% 7.68/1.53  fof(f17,axiom,(
% 7.68/1.53    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)),
% 7.68/1.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.68/1.53  
% 7.68/1.53  fof(f66,plain,(
% 7.68/1.53    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)) )),
% 7.68/1.53    inference(cnf_transformation,[],[f17])).
% 7.68/1.53  
% 7.68/1.53  fof(f18,axiom,(
% 7.68/1.53    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)),
% 7.68/1.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.68/1.53  
% 7.68/1.53  fof(f67,plain,(
% 7.68/1.53    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)) )),
% 7.68/1.53    inference(cnf_transformation,[],[f18])).
% 7.68/1.53  
% 7.68/1.53  fof(f75,plain,(
% 7.68/1.53    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 7.68/1.53    inference(definition_unfolding,[],[f66,f67])).
% 7.68/1.53  
% 7.68/1.53  fof(f76,plain,(
% 7.68/1.53    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 7.68/1.53    inference(definition_unfolding,[],[f65,f75])).
% 7.68/1.53  
% 7.68/1.53  fof(f77,plain,(
% 7.68/1.53    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 7.68/1.53    inference(definition_unfolding,[],[f64,f76])).
% 7.68/1.53  
% 7.68/1.53  fof(f78,plain,(
% 7.68/1.53    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 7.68/1.53    inference(definition_unfolding,[],[f63,f77])).
% 7.68/1.53  
% 7.68/1.53  fof(f79,plain,(
% 7.68/1.53    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 7.68/1.53    inference(definition_unfolding,[],[f62,f78])).
% 7.68/1.53  
% 7.68/1.53  fof(f83,plain,(
% 7.68/1.53    ( ! [X0] : (k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) )),
% 7.68/1.53    inference(definition_unfolding,[],[f61,f79])).
% 7.68/1.53  
% 7.68/1.53  fof(f89,plain,(
% 7.68/1.53    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) != X1) )),
% 7.68/1.53    inference(definition_unfolding,[],[f57,f83])).
% 7.68/1.53  
% 7.68/1.53  fof(f99,plain,(
% 7.68/1.53    ( ! [X0,X3] : (X0 = X3 | ~r2_hidden(X3,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))) )),
% 7.68/1.53    inference(equality_resolution,[],[f89])).
% 7.68/1.53  
% 7.68/1.53  fof(f1,axiom,(
% 7.68/1.53    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 7.68/1.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.68/1.53  
% 7.68/1.53  fof(f25,plain,(
% 7.68/1.53    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 7.68/1.53    inference(ennf_transformation,[],[f1])).
% 7.68/1.53  
% 7.68/1.53  fof(f28,plain,(
% 7.68/1.53    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 7.68/1.53    inference(nnf_transformation,[],[f25])).
% 7.68/1.53  
% 7.68/1.53  fof(f29,plain,(
% 7.68/1.53    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 7.68/1.53    inference(rectify,[],[f28])).
% 7.68/1.53  
% 7.68/1.53  fof(f30,plain,(
% 7.68/1.53    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 7.68/1.53    introduced(choice_axiom,[])).
% 7.68/1.53  
% 7.68/1.53  fof(f31,plain,(
% 7.68/1.53    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 7.68/1.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f29,f30])).
% 7.68/1.53  
% 7.68/1.53  fof(f43,plain,(
% 7.68/1.53    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,X1)) )),
% 7.68/1.53    inference(cnf_transformation,[],[f31])).
% 7.68/1.53  
% 7.68/1.53  fof(f9,axiom,(
% 7.68/1.53    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0)),
% 7.68/1.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.68/1.53  
% 7.68/1.53  fof(f55,plain,(
% 7.68/1.53    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(X0,X0)) )),
% 7.68/1.53    inference(cnf_transformation,[],[f9])).
% 7.68/1.53  
% 7.68/1.53  fof(f8,axiom,(
% 7.68/1.53    ! [X0,X1,X2] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2)),
% 7.68/1.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.68/1.53  
% 7.68/1.53  fof(f54,plain,(
% 7.68/1.53    ( ! [X2,X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2)) )),
% 7.68/1.53    inference(cnf_transformation,[],[f8])).
% 7.68/1.53  
% 7.68/1.53  fof(f22,conjecture,(
% 7.68/1.53    ! [X0,X1] : ~(k1_tarski(X1) != X0 & k1_xboole_0 != X0 & k1_xboole_0 = k4_xboole_0(X0,k1_tarski(X1)))),
% 7.68/1.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.68/1.53  
% 7.68/1.53  fof(f23,negated_conjecture,(
% 7.68/1.53    ~! [X0,X1] : ~(k1_tarski(X1) != X0 & k1_xboole_0 != X0 & k1_xboole_0 = k4_xboole_0(X0,k1_tarski(X1)))),
% 7.68/1.53    inference(negated_conjecture,[],[f22])).
% 7.68/1.53  
% 7.68/1.53  fof(f27,plain,(
% 7.68/1.53    ? [X0,X1] : (k1_tarski(X1) != X0 & k1_xboole_0 != X0 & k1_xboole_0 = k4_xboole_0(X0,k1_tarski(X1)))),
% 7.68/1.53    inference(ennf_transformation,[],[f23])).
% 7.68/1.53  
% 7.68/1.53  fof(f41,plain,(
% 7.68/1.53    ? [X0,X1] : (k1_tarski(X1) != X0 & k1_xboole_0 != X0 & k1_xboole_0 = k4_xboole_0(X0,k1_tarski(X1))) => (k1_tarski(sK4) != sK3 & k1_xboole_0 != sK3 & k1_xboole_0 = k4_xboole_0(sK3,k1_tarski(sK4)))),
% 7.68/1.53    introduced(choice_axiom,[])).
% 7.68/1.53  
% 7.68/1.53  fof(f42,plain,(
% 7.68/1.53    k1_tarski(sK4) != sK3 & k1_xboole_0 != sK3 & k1_xboole_0 = k4_xboole_0(sK3,k1_tarski(sK4))),
% 7.68/1.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f27,f41])).
% 7.68/1.53  
% 7.68/1.53  fof(f72,plain,(
% 7.68/1.53    k1_xboole_0 = k4_xboole_0(sK3,k1_tarski(sK4))),
% 7.68/1.53    inference(cnf_transformation,[],[f42])).
% 7.68/1.53  
% 7.68/1.53  fof(f5,axiom,(
% 7.68/1.53    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 7.68/1.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.68/1.53  
% 7.68/1.53  fof(f51,plain,(
% 7.68/1.53    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 7.68/1.53    inference(cnf_transformation,[],[f5])).
% 7.68/1.53  
% 7.68/1.53  fof(f10,axiom,(
% 7.68/1.53    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))),
% 7.68/1.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.68/1.53  
% 7.68/1.53  fof(f56,plain,(
% 7.68/1.53    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))) )),
% 7.68/1.53    inference(cnf_transformation,[],[f10])).
% 7.68/1.53  
% 7.68/1.53  fof(f20,axiom,(
% 7.68/1.53    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 7.68/1.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.68/1.53  
% 7.68/1.53  fof(f70,plain,(
% 7.68/1.53    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 7.68/1.53    inference(cnf_transformation,[],[f20])).
% 7.68/1.53  
% 7.68/1.53  fof(f80,plain,(
% 7.68/1.53    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) )),
% 7.68/1.53    inference(definition_unfolding,[],[f70,f79])).
% 7.68/1.53  
% 7.68/1.53  fof(f81,plain,(
% 7.68/1.53    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) )),
% 7.68/1.53    inference(definition_unfolding,[],[f56,f80])).
% 7.68/1.53  
% 7.68/1.53  fof(f82,plain,(
% 7.68/1.53    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))))) )),
% 7.68/1.53    inference(definition_unfolding,[],[f51,f81])).
% 7.68/1.53  
% 7.68/1.53  fof(f94,plain,(
% 7.68/1.53    k1_xboole_0 = k5_xboole_0(sK3,k5_xboole_0(k5_xboole_0(sK3,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)),k3_tarski(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)))))),
% 7.68/1.53    inference(definition_unfolding,[],[f72,f82,f83])).
% 7.68/1.53  
% 7.68/1.53  fof(f2,axiom,(
% 7.68/1.53    ! [X0,X1] : k3_xboole_0(X0,X0) = X0),
% 7.68/1.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.68/1.53  
% 7.68/1.53  fof(f24,plain,(
% 7.68/1.53    ! [X0] : k3_xboole_0(X0,X0) = X0),
% 7.68/1.53    inference(rectify,[],[f2])).
% 7.68/1.53  
% 7.68/1.53  fof(f46,plain,(
% 7.68/1.53    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 7.68/1.53    inference(cnf_transformation,[],[f24])).
% 7.68/1.53  
% 7.68/1.53  fof(f84,plain,(
% 7.68/1.53    ( ! [X0] : (k5_xboole_0(k5_xboole_0(X0,X0),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))) = X0) )),
% 7.68/1.53    inference(definition_unfolding,[],[f46,f81])).
% 7.68/1.53  
% 7.68/1.53  fof(f21,axiom,(
% 7.68/1.53    ! [X0] : k3_tarski(k1_tarski(X0)) = X0),
% 7.68/1.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.68/1.53  
% 7.68/1.53  fof(f71,plain,(
% 7.68/1.53    ( ! [X0] : (k3_tarski(k1_tarski(X0)) = X0) )),
% 7.68/1.53    inference(cnf_transformation,[],[f21])).
% 7.68/1.53  
% 7.68/1.53  fof(f92,plain,(
% 7.68/1.53    ( ! [X0] : (k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) = X0) )),
% 7.68/1.53    inference(definition_unfolding,[],[f71,f83])).
% 7.68/1.53  
% 7.68/1.53  fof(f6,axiom,(
% 7.68/1.53    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 7.68/1.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.68/1.53  
% 7.68/1.53  fof(f52,plain,(
% 7.68/1.53    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 7.68/1.53    inference(cnf_transformation,[],[f6])).
% 7.68/1.53  
% 7.68/1.53  fof(f7,axiom,(
% 7.68/1.53    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 7.68/1.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.68/1.53  
% 7.68/1.53  fof(f53,plain,(
% 7.68/1.53    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 7.68/1.53    inference(cnf_transformation,[],[f7])).
% 7.68/1.53  
% 7.68/1.53  fof(f85,plain,(
% 7.68/1.53    ( ! [X0,X1] : (r1_tarski(X0,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) )),
% 7.68/1.53    inference(definition_unfolding,[],[f53,f80])).
% 7.68/1.53  
% 7.68/1.53  fof(f4,axiom,(
% 7.68/1.53    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 7.68/1.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.68/1.53  
% 7.68/1.53  fof(f34,plain,(
% 7.68/1.53    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 7.68/1.53    inference(nnf_transformation,[],[f4])).
% 7.68/1.53  
% 7.68/1.53  fof(f35,plain,(
% 7.68/1.53    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 7.68/1.53    inference(flattening,[],[f34])).
% 7.68/1.53  
% 7.68/1.53  fof(f48,plain,(
% 7.68/1.53    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 7.68/1.53    inference(cnf_transformation,[],[f35])).
% 7.68/1.53  
% 7.68/1.53  fof(f96,plain,(
% 7.68/1.53    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 7.68/1.53    inference(equality_resolution,[],[f48])).
% 7.68/1.53  
% 7.68/1.53  fof(f50,plain,(
% 7.68/1.53    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 7.68/1.53    inference(cnf_transformation,[],[f35])).
% 7.68/1.53  
% 7.68/1.53  fof(f19,axiom,(
% 7.68/1.53    ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) <=> r2_hidden(X0,X1))),
% 7.68/1.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.68/1.53  
% 7.68/1.53  fof(f40,plain,(
% 7.68/1.53    ! [X0,X1] : ((r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) & (r2_hidden(X0,X1) | ~r1_tarski(k1_tarski(X0),X1)))),
% 7.68/1.53    inference(nnf_transformation,[],[f19])).
% 7.68/1.53  
% 7.68/1.53  fof(f69,plain,(
% 7.68/1.53    ( ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) )),
% 7.68/1.53    inference(cnf_transformation,[],[f40])).
% 7.68/1.53  
% 7.68/1.53  fof(f90,plain,(
% 7.68/1.53    ( ! [X0,X1] : (r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1) | ~r2_hidden(X0,X1)) )),
% 7.68/1.53    inference(definition_unfolding,[],[f69,f83])).
% 7.68/1.53  
% 7.68/1.53  fof(f3,axiom,(
% 7.68/1.53    ! [X0] : ~(! [X1] : ~r2_hidden(X1,X0) & k1_xboole_0 != X0)),
% 7.68/1.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.68/1.53  
% 7.68/1.53  fof(f26,plain,(
% 7.68/1.53    ! [X0] : (? [X1] : r2_hidden(X1,X0) | k1_xboole_0 = X0)),
% 7.68/1.53    inference(ennf_transformation,[],[f3])).
% 7.68/1.53  
% 7.68/1.53  fof(f32,plain,(
% 7.68/1.53    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK1(X0),X0))),
% 7.68/1.53    introduced(choice_axiom,[])).
% 7.68/1.53  
% 7.68/1.53  fof(f33,plain,(
% 7.68/1.53    ! [X0] : (r2_hidden(sK1(X0),X0) | k1_xboole_0 = X0)),
% 7.68/1.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f26,f32])).
% 7.68/1.53  
% 7.68/1.53  fof(f47,plain,(
% 7.68/1.53    ( ! [X0] : (r2_hidden(sK1(X0),X0) | k1_xboole_0 = X0) )),
% 7.68/1.53    inference(cnf_transformation,[],[f33])).
% 7.68/1.53  
% 7.68/1.53  fof(f58,plain,(
% 7.68/1.53    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | X0 != X3 | k1_tarski(X0) != X1) )),
% 7.68/1.53    inference(cnf_transformation,[],[f39])).
% 7.68/1.53  
% 7.68/1.53  fof(f88,plain,(
% 7.68/1.53    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | X0 != X3 | k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) != X1) )),
% 7.68/1.53    inference(definition_unfolding,[],[f58,f83])).
% 7.68/1.53  
% 7.68/1.53  fof(f97,plain,(
% 7.68/1.53    ( ! [X3,X1] : (r2_hidden(X3,X1) | k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X3) != X1) )),
% 7.68/1.53    inference(equality_resolution,[],[f88])).
% 7.68/1.53  
% 7.68/1.53  fof(f98,plain,(
% 7.68/1.53    ( ! [X3] : (r2_hidden(X3,k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X3))) )),
% 7.68/1.53    inference(equality_resolution,[],[f97])).
% 7.68/1.53  
% 7.68/1.53  fof(f74,plain,(
% 7.68/1.53    k1_tarski(sK4) != sK3),
% 7.68/1.53    inference(cnf_transformation,[],[f42])).
% 7.68/1.53  
% 7.68/1.53  fof(f93,plain,(
% 7.68/1.53    k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) != sK3),
% 7.68/1.53    inference(definition_unfolding,[],[f74,f83])).
% 7.68/1.53  
% 7.68/1.53  fof(f73,plain,(
% 7.68/1.53    k1_xboole_0 != sK3),
% 7.68/1.53    inference(cnf_transformation,[],[f42])).
% 7.68/1.53  
% 7.68/1.53  cnf(c_15,plain,
% 7.68/1.53      ( ~ r2_hidden(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)) | X0 = X1 ),
% 7.68/1.53      inference(cnf_transformation,[],[f99]) ).
% 7.68/1.53  
% 7.68/1.53  cnf(c_36343,plain,
% 7.68/1.53      ( ~ r2_hidden(sK1(sK3),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))
% 7.68/1.53      | sK1(sK3) = X0 ),
% 7.68/1.53      inference(instantiation,[status(thm)],[c_15]) ).
% 7.68/1.53  
% 7.68/1.53  cnf(c_36345,plain,
% 7.68/1.53      ( ~ r2_hidden(sK1(sK3),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))
% 7.68/1.53      | sK1(sK3) = sK4 ),
% 7.68/1.53      inference(instantiation,[status(thm)],[c_36343]) ).
% 7.68/1.53  
% 7.68/1.53  cnf(c_339,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 7.68/1.53  
% 7.68/1.53  cnf(c_30101,plain,
% 7.68/1.53      ( sK1(sK3) != X0 | sK4 != X0 | sK4 = sK1(sK3) ),
% 7.68/1.53      inference(instantiation,[status(thm)],[c_339]) ).
% 7.68/1.53  
% 7.68/1.53  cnf(c_30102,plain,
% 7.68/1.53      ( sK1(sK3) != sK4 | sK4 = sK1(sK3) | sK4 != sK4 ),
% 7.68/1.53      inference(instantiation,[status(thm)],[c_30101]) ).
% 7.68/1.53  
% 7.68/1.53  cnf(c_341,plain,
% 7.68/1.53      ( ~ r2_hidden(X0,X1) | r2_hidden(X2,X3) | X2 != X0 | X3 != X1 ),
% 7.68/1.53      theory(equality) ).
% 7.68/1.53  
% 7.68/1.53  cnf(c_2341,plain,
% 7.68/1.53      ( r2_hidden(X0,X1)
% 7.68/1.53      | ~ r2_hidden(sK1(sK3),sK3)
% 7.68/1.53      | X0 != sK1(sK3)
% 7.68/1.53      | X1 != sK3 ),
% 7.68/1.53      inference(instantiation,[status(thm)],[c_341]) ).
% 7.68/1.53  
% 7.68/1.53  cnf(c_9293,plain,
% 7.68/1.53      ( ~ r2_hidden(sK1(sK3),sK3)
% 7.68/1.53      | r2_hidden(sK4,sK3)
% 7.68/1.53      | sK3 != sK3
% 7.68/1.53      | sK4 != sK1(sK3) ),
% 7.68/1.53      inference(instantiation,[status(thm)],[c_2341]) ).
% 7.68/1.53  
% 7.68/1.53  cnf(c_2,plain,
% 7.68/1.53      ( ~ r2_hidden(X0,X1) | r2_hidden(X0,X2) | ~ r1_tarski(X1,X2) ),
% 7.68/1.53      inference(cnf_transformation,[],[f43]) ).
% 7.68/1.53  
% 7.68/1.53  cnf(c_1886,plain,
% 7.68/1.53      ( r2_hidden(sK1(sK3),X0)
% 7.68/1.53      | ~ r2_hidden(sK1(sK3),sK3)
% 7.68/1.53      | ~ r1_tarski(sK3,X0) ),
% 7.68/1.53      inference(instantiation,[status(thm)],[c_2]) ).
% 7.68/1.53  
% 7.68/1.53  cnf(c_9030,plain,
% 7.68/1.53      ( r2_hidden(sK1(sK3),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))
% 7.68/1.53      | ~ r2_hidden(sK1(sK3),sK3)
% 7.68/1.53      | ~ r1_tarski(sK3,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)) ),
% 7.68/1.53      inference(instantiation,[status(thm)],[c_1886]) ).
% 7.68/1.53  
% 7.68/1.53  cnf(c_11,plain,
% 7.68/1.53      ( k5_xboole_0(X0,X0) = k1_xboole_0 ),
% 7.68/1.53      inference(cnf_transformation,[],[f55]) ).
% 7.68/1.53  
% 7.68/1.53  cnf(c_10,plain,
% 7.68/1.53      ( k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
% 7.68/1.53      inference(cnf_transformation,[],[f54]) ).
% 7.68/1.53  
% 7.68/1.53  cnf(c_21,negated_conjecture,
% 7.68/1.53      ( k1_xboole_0 = k5_xboole_0(sK3,k5_xboole_0(k5_xboole_0(sK3,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)),k3_tarski(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))))) ),
% 7.68/1.53      inference(cnf_transformation,[],[f94]) ).
% 7.68/1.53  
% 7.68/1.53  cnf(c_1080,plain,
% 7.68/1.53      ( k5_xboole_0(sK3,k5_xboole_0(sK3,k5_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k3_tarski(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)))))) = k1_xboole_0 ),
% 7.68/1.53      inference(demodulation,[status(thm)],[c_10,c_21]) ).
% 7.68/1.53  
% 7.68/1.53  cnf(c_1334,plain,
% 7.68/1.53      ( k5_xboole_0(sK3,k5_xboole_0(k5_xboole_0(sK3,k5_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k3_tarski(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))))),X0)) = k5_xboole_0(k1_xboole_0,X0) ),
% 7.68/1.53      inference(superposition,[status(thm)],[c_1080,c_10]) ).
% 7.68/1.53  
% 7.68/1.53  cnf(c_3,plain,
% 7.68/1.53      ( k5_xboole_0(k5_xboole_0(X0,X0),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))) = X0 ),
% 7.68/1.53      inference(cnf_transformation,[],[f84]) ).
% 7.68/1.53  
% 7.68/1.53  cnf(c_18,plain,
% 7.68/1.53      ( k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) = X0 ),
% 7.68/1.53      inference(cnf_transformation,[],[f92]) ).
% 7.68/1.53  
% 7.68/1.53  cnf(c_683,plain,
% 7.68/1.53      ( k5_xboole_0(k1_xboole_0,X0) = X0 ),
% 7.68/1.53      inference(light_normalisation,[status(thm)],[c_3,c_11,c_18]) ).
% 7.68/1.53  
% 7.68/1.53  cnf(c_1335,plain,
% 7.68/1.53      ( k5_xboole_0(sK3,k5_xboole_0(k5_xboole_0(sK3,k5_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k3_tarski(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))))),X0)) = X0 ),
% 7.68/1.53      inference(light_normalisation,[status(thm)],[c_1334,c_683]) ).
% 7.68/1.53  
% 7.68/1.53  cnf(c_1429,plain,
% 7.68/1.53      ( k5_xboole_0(sK3,k5_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k3_tarski(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))))) = k5_xboole_0(sK3,k1_xboole_0) ),
% 7.68/1.53      inference(superposition,[status(thm)],[c_11,c_1335]) ).
% 7.68/1.53  
% 7.68/1.53  cnf(c_8,plain,
% 7.68/1.53      ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
% 7.68/1.53      inference(cnf_transformation,[],[f52]) ).
% 7.68/1.53  
% 7.68/1.53  cnf(c_1438,plain,
% 7.68/1.53      ( k5_xboole_0(sK3,k5_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k3_tarski(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))))) = sK3 ),
% 7.68/1.53      inference(demodulation,[status(thm)],[c_1429,c_8]) ).
% 7.68/1.53  
% 7.68/1.53  cnf(c_1443,plain,
% 7.68/1.53      ( k5_xboole_0(sK3,k5_xboole_0(sK3,X0)) = X0 ),
% 7.68/1.53      inference(demodulation,[status(thm)],[c_1438,c_1335]) ).
% 7.68/1.53  
% 7.68/1.53  cnf(c_1453,plain,
% 7.68/1.53      ( k5_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k3_tarski(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)))) = k1_xboole_0 ),
% 7.68/1.53      inference(superposition,[status(thm)],[c_1443,c_1080]) ).
% 7.68/1.53  
% 7.68/1.53  cnf(c_1585,plain,
% 7.68/1.53      ( k5_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k5_xboole_0(k3_tarski(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))),X0)) = k5_xboole_0(k1_xboole_0,X0) ),
% 7.68/1.53      inference(superposition,[status(thm)],[c_1453,c_10]) ).
% 7.68/1.53  
% 7.68/1.53  cnf(c_1586,plain,
% 7.68/1.53      ( k5_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k5_xboole_0(k3_tarski(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))),X0)) = X0 ),
% 7.68/1.53      inference(light_normalisation,[status(thm)],[c_1585,c_683]) ).
% 7.68/1.53  
% 7.68/1.53  cnf(c_1589,plain,
% 7.68/1.53      ( k3_tarski(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))) = k5_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k1_xboole_0) ),
% 7.68/1.53      inference(superposition,[status(thm)],[c_11,c_1586]) ).
% 7.68/1.53  
% 7.68/1.53  cnf(c_1597,plain,
% 7.68/1.53      ( k3_tarski(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))) = k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) ),
% 7.68/1.53      inference(demodulation,[status(thm)],[c_1589,c_8]) ).
% 7.68/1.53  
% 7.68/1.53  cnf(c_9,plain,
% 7.68/1.53      ( r1_tarski(X0,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) ),
% 7.68/1.53      inference(cnf_transformation,[],[f85]) ).
% 7.68/1.53  
% 7.68/1.53  cnf(c_676,plain,
% 7.68/1.53      ( r1_tarski(X0,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) = iProver_top ),
% 7.68/1.53      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 7.68/1.53  
% 7.68/1.53  cnf(c_5614,plain,
% 7.68/1.53      ( r1_tarski(sK3,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)) = iProver_top ),
% 7.68/1.53      inference(superposition,[status(thm)],[c_1597,c_676]) ).
% 7.68/1.53  
% 7.68/1.53  cnf(c_5615,plain,
% 7.68/1.53      ( r1_tarski(sK3,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)) ),
% 7.68/1.53      inference(predicate_to_equality_rev,[status(thm)],[c_5614]) ).
% 7.68/1.53  
% 7.68/1.53  cnf(c_710,plain,
% 7.68/1.53      ( k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) != X0
% 7.68/1.53      | k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) = sK3
% 7.68/1.53      | sK3 != X0 ),
% 7.68/1.53      inference(instantiation,[status(thm)],[c_339]) ).
% 7.68/1.53  
% 7.68/1.53  cnf(c_2153,plain,
% 7.68/1.53      ( k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) != k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)
% 7.68/1.53      | k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) = sK3
% 7.68/1.53      | sK3 != k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) ),
% 7.68/1.53      inference(instantiation,[status(thm)],[c_710]) ).
% 7.68/1.53  
% 7.68/1.53  cnf(c_7,plain,
% 7.68/1.53      ( r1_tarski(X0,X0) ),
% 7.68/1.53      inference(cnf_transformation,[],[f96]) ).
% 7.68/1.53  
% 7.68/1.53  cnf(c_1204,plain,
% 7.68/1.53      ( r1_tarski(sK3,sK3) ),
% 7.68/1.53      inference(instantiation,[status(thm)],[c_7]) ).
% 7.68/1.53  
% 7.68/1.53  cnf(c_5,plain,
% 7.68/1.53      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X1 = X0 ),
% 7.68/1.53      inference(cnf_transformation,[],[f50]) ).
% 7.68/1.53  
% 7.68/1.53  cnf(c_806,plain,
% 7.68/1.53      ( ~ r1_tarski(X0,sK3) | ~ r1_tarski(sK3,X0) | sK3 = X0 ),
% 7.68/1.53      inference(instantiation,[status(thm)],[c_5]) ).
% 7.68/1.53  
% 7.68/1.53  cnf(c_933,plain,
% 7.68/1.53      ( ~ r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),sK3)
% 7.68/1.53      | ~ r1_tarski(sK3,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))
% 7.68/1.53      | sK3 = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
% 7.68/1.53      inference(instantiation,[status(thm)],[c_806]) ).
% 7.68/1.53  
% 7.68/1.53  cnf(c_935,plain,
% 7.68/1.53      ( ~ r1_tarski(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),sK3)
% 7.68/1.53      | ~ r1_tarski(sK3,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))
% 7.68/1.53      | sK3 = k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) ),
% 7.68/1.53      inference(instantiation,[status(thm)],[c_933]) ).
% 7.68/1.53  
% 7.68/1.53  cnf(c_930,plain,
% 7.68/1.53      ( ~ r1_tarski(sK3,sK3) | sK3 = sK3 ),
% 7.68/1.53      inference(instantiation,[status(thm)],[c_806]) ).
% 7.68/1.53  
% 7.68/1.53  cnf(c_16,plain,
% 7.68/1.53      ( ~ r2_hidden(X0,X1)
% 7.68/1.53      | r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1) ),
% 7.68/1.53      inference(cnf_transformation,[],[f90]) ).
% 7.68/1.53  
% 7.68/1.53  cnf(c_746,plain,
% 7.68/1.53      ( ~ r2_hidden(sK4,sK3)
% 7.68/1.53      | r1_tarski(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),sK3) ),
% 7.68/1.53      inference(instantiation,[status(thm)],[c_16]) ).
% 7.68/1.53  
% 7.68/1.53  cnf(c_4,plain,
% 7.68/1.53      ( r2_hidden(sK1(X0),X0) | k1_xboole_0 = X0 ),
% 7.68/1.53      inference(cnf_transformation,[],[f47]) ).
% 7.68/1.53  
% 7.68/1.53  cnf(c_716,plain,
% 7.68/1.53      ( r2_hidden(sK1(sK3),sK3) | k1_xboole_0 = sK3 ),
% 7.68/1.53      inference(instantiation,[status(thm)],[c_4]) ).
% 7.68/1.53  
% 7.68/1.53  cnf(c_343,plain,
% 7.68/1.53      ( X0 != X1
% 7.68/1.53      | X2 != X3
% 7.68/1.53      | X4 != X5
% 7.68/1.53      | X6 != X7
% 7.68/1.53      | X8 != X9
% 7.68/1.53      | X10 != X11
% 7.68/1.53      | X12 != X13
% 7.68/1.53      | X14 != X15
% 7.68/1.53      | k6_enumset1(X0,X2,X4,X6,X8,X10,X12,X14) = k6_enumset1(X1,X3,X5,X7,X9,X11,X13,X15) ),
% 7.68/1.53      theory(equality) ).
% 7.68/1.53  
% 7.68/1.53  cnf(c_348,plain,
% 7.68/1.53      ( k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) = k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)
% 7.68/1.53      | sK4 != sK4 ),
% 7.68/1.53      inference(instantiation,[status(thm)],[c_343]) ).
% 7.68/1.53  
% 7.68/1.53  cnf(c_14,plain,
% 7.68/1.53      ( r2_hidden(X0,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) ),
% 7.68/1.53      inference(cnf_transformation,[],[f98]) ).
% 7.68/1.53  
% 7.68/1.53  cnf(c_33,plain,
% 7.68/1.53      ( r2_hidden(sK4,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)) ),
% 7.68/1.53      inference(instantiation,[status(thm)],[c_14]) ).
% 7.68/1.53  
% 7.68/1.53  cnf(c_30,plain,
% 7.68/1.53      ( ~ r2_hidden(sK4,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))
% 7.68/1.53      | sK4 = sK4 ),
% 7.68/1.53      inference(instantiation,[status(thm)],[c_15]) ).
% 7.68/1.53  
% 7.68/1.53  cnf(c_19,negated_conjecture,
% 7.68/1.53      ( k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) != sK3 ),
% 7.68/1.53      inference(cnf_transformation,[],[f93]) ).
% 7.68/1.53  
% 7.68/1.53  cnf(c_20,negated_conjecture,
% 7.68/1.53      ( k1_xboole_0 != sK3 ),
% 7.68/1.53      inference(cnf_transformation,[],[f73]) ).
% 7.68/1.53  
% 7.68/1.53  cnf(contradiction,plain,
% 7.68/1.53      ( $false ),
% 7.68/1.53      inference(minisat,
% 7.68/1.53                [status(thm)],
% 7.68/1.53                [c_36345,c_30102,c_9293,c_9030,c_5615,c_2153,c_1204,
% 7.68/1.53                 c_935,c_930,c_746,c_716,c_348,c_33,c_30,c_19,c_20]) ).
% 7.68/1.53  
% 7.68/1.53  
% 7.68/1.53  % SZS output end CNFRefutation for theBenchmark.p
% 7.68/1.53  
% 7.68/1.53  ------                               Statistics
% 7.68/1.53  
% 7.68/1.53  ------ General
% 7.68/1.53  
% 7.68/1.53  abstr_ref_over_cycles:                  0
% 7.68/1.53  abstr_ref_under_cycles:                 0
% 7.68/1.53  gc_basic_clause_elim:                   0
% 7.68/1.53  forced_gc_time:                         0
% 7.68/1.53  parsing_time:                           0.009
% 7.68/1.53  unif_index_cands_time:                  0.
% 7.68/1.53  unif_index_add_time:                    0.
% 7.68/1.53  orderings_time:                         0.
% 7.68/1.53  out_proof_time:                         0.007
% 7.68/1.53  total_time:                             0.937
% 7.68/1.53  num_of_symbols:                         43
% 7.68/1.53  num_of_terms:                           38366
% 7.68/1.53  
% 7.68/1.53  ------ Preprocessing
% 7.68/1.53  
% 7.68/1.53  num_of_splits:                          0
% 7.68/1.53  num_of_split_atoms:                     1
% 7.68/1.53  num_of_reused_defs:                     0
% 7.68/1.53  num_eq_ax_congr_red:                    15
% 7.68/1.53  num_of_sem_filtered_clauses:            1
% 7.68/1.53  num_of_subtypes:                        0
% 7.68/1.53  monotx_restored_types:                  0
% 7.68/1.53  sat_num_of_epr_types:                   0
% 7.68/1.53  sat_num_of_non_cyclic_types:            0
% 7.68/1.53  sat_guarded_non_collapsed_types:        0
% 7.68/1.53  num_pure_diseq_elim:                    0
% 7.68/1.53  simp_replaced_by:                       0
% 7.68/1.53  res_preprocessed:                       99
% 7.68/1.53  prep_upred:                             0
% 7.68/1.53  prep_unflattend:                        0
% 7.68/1.53  smt_new_axioms:                         0
% 7.68/1.53  pred_elim_cands:                        2
% 7.68/1.53  pred_elim:                              0
% 7.68/1.53  pred_elim_cl:                           0
% 7.68/1.53  pred_elim_cycles:                       2
% 7.68/1.53  merged_defs:                            8
% 7.68/1.53  merged_defs_ncl:                        0
% 7.68/1.53  bin_hyper_res:                          8
% 7.68/1.53  prep_cycles:                            4
% 7.68/1.53  pred_elim_time:                         0.
% 7.68/1.53  splitting_time:                         0.
% 7.68/1.53  sem_filter_time:                        0.
% 7.68/1.53  monotx_time:                            0.
% 7.68/1.53  subtype_inf_time:                       0.
% 7.68/1.53  
% 7.68/1.53  ------ Problem properties
% 7.68/1.53  
% 7.68/1.53  clauses:                                21
% 7.68/1.53  conjectures:                            3
% 7.68/1.53  epr:                                    4
% 7.68/1.53  horn:                                   18
% 7.68/1.53  ground:                                 3
% 7.68/1.53  unary:                                  11
% 7.68/1.53  binary:                                 6
% 7.68/1.53  lits:                                   35
% 7.68/1.53  lits_eq:                                15
% 7.68/1.53  fd_pure:                                0
% 7.68/1.53  fd_pseudo:                              0
% 7.68/1.53  fd_cond:                                1
% 7.68/1.53  fd_pseudo_cond:                         3
% 7.68/1.53  ac_symbols:                             1
% 7.68/1.53  
% 7.68/1.53  ------ Propositional Solver
% 7.68/1.53  
% 7.68/1.53  prop_solver_calls:                      30
% 7.68/1.53  prop_fast_solver_calls:                 672
% 7.68/1.53  smt_solver_calls:                       0
% 7.68/1.53  smt_fast_solver_calls:                  0
% 7.68/1.53  prop_num_of_clauses:                    6851
% 7.68/1.53  prop_preprocess_simplified:             13560
% 7.68/1.53  prop_fo_subsumed:                       0
% 7.68/1.53  prop_solver_time:                       0.
% 7.68/1.53  smt_solver_time:                        0.
% 7.68/1.53  smt_fast_solver_time:                   0.
% 7.68/1.53  prop_fast_solver_time:                  0.
% 7.68/1.53  prop_unsat_core_time:                   0.
% 7.68/1.53  
% 7.68/1.53  ------ QBF
% 7.68/1.53  
% 7.68/1.53  qbf_q_res:                              0
% 7.68/1.53  qbf_num_tautologies:                    0
% 7.68/1.53  qbf_prep_cycles:                        0
% 7.68/1.53  
% 7.68/1.53  ------ BMC1
% 7.68/1.53  
% 7.68/1.53  bmc1_current_bound:                     -1
% 7.68/1.53  bmc1_last_solved_bound:                 -1
% 7.68/1.53  bmc1_unsat_core_size:                   -1
% 7.68/1.53  bmc1_unsat_core_parents_size:           -1
% 7.68/1.53  bmc1_merge_next_fun:                    0
% 7.68/1.53  bmc1_unsat_core_clauses_time:           0.
% 7.68/1.53  
% 7.68/1.53  ------ Instantiation
% 7.68/1.53  
% 7.68/1.53  inst_num_of_clauses:                    1601
% 7.68/1.53  inst_num_in_passive:                    821
% 7.68/1.53  inst_num_in_active:                     613
% 7.68/1.53  inst_num_in_unprocessed:                169
% 7.68/1.53  inst_num_of_loops:                      926
% 7.68/1.53  inst_num_of_learning_restarts:          0
% 7.68/1.53  inst_num_moves_active_passive:          312
% 7.68/1.53  inst_lit_activity:                      0
% 7.68/1.53  inst_lit_activity_moves:                0
% 7.68/1.53  inst_num_tautologies:                   0
% 7.68/1.53  inst_num_prop_implied:                  0
% 7.68/1.53  inst_num_existing_simplified:           0
% 7.68/1.53  inst_num_eq_res_simplified:             0
% 7.68/1.53  inst_num_child_elim:                    0
% 7.68/1.53  inst_num_of_dismatching_blockings:      1352
% 7.68/1.53  inst_num_of_non_proper_insts:           2466
% 7.68/1.53  inst_num_of_duplicates:                 0
% 7.68/1.53  inst_inst_num_from_inst_to_res:         0
% 7.68/1.53  inst_dismatching_checking_time:         0.
% 7.68/1.53  
% 7.68/1.53  ------ Resolution
% 7.68/1.53  
% 7.68/1.53  res_num_of_clauses:                     0
% 7.68/1.53  res_num_in_passive:                     0
% 7.68/1.53  res_num_in_active:                      0
% 7.68/1.53  res_num_of_loops:                       103
% 7.68/1.53  res_forward_subset_subsumed:            319
% 7.68/1.53  res_backward_subset_subsumed:           6
% 7.68/1.53  res_forward_subsumed:                   0
% 7.68/1.53  res_backward_subsumed:                  0
% 7.68/1.53  res_forward_subsumption_resolution:     0
% 7.68/1.53  res_backward_subsumption_resolution:    0
% 7.68/1.53  res_clause_to_clause_subsumption:       37194
% 7.68/1.53  res_orphan_elimination:                 0
% 7.68/1.53  res_tautology_del:                      217
% 7.68/1.53  res_num_eq_res_simplified:              0
% 7.68/1.53  res_num_sel_changes:                    0
% 7.68/1.53  res_moves_from_active_to_pass:          0
% 7.68/1.53  
% 7.68/1.53  ------ Superposition
% 7.68/1.53  
% 7.68/1.53  sup_time_total:                         0.
% 7.68/1.53  sup_time_generating:                    0.
% 7.68/1.53  sup_time_sim_full:                      0.
% 7.68/1.53  sup_time_sim_immed:                     0.
% 7.68/1.53  
% 7.68/1.53  sup_num_of_clauses:                     1581
% 7.68/1.53  sup_num_in_active:                      135
% 7.68/1.53  sup_num_in_passive:                     1446
% 7.68/1.53  sup_num_of_loops:                       184
% 7.68/1.53  sup_fw_superposition:                   8590
% 7.68/1.53  sup_bw_superposition:                   5624
% 7.68/1.53  sup_immediate_simplified:               7361
% 7.68/1.53  sup_given_eliminated:                   10
% 7.68/1.53  comparisons_done:                       0
% 7.68/1.53  comparisons_avoided:                    5
% 7.68/1.53  
% 7.68/1.53  ------ Simplifications
% 7.68/1.53  
% 7.68/1.53  
% 7.68/1.53  sim_fw_subset_subsumed:                 1
% 7.68/1.53  sim_bw_subset_subsumed:                 0
% 7.68/1.53  sim_fw_subsumed:                        424
% 7.68/1.53  sim_bw_subsumed:                        38
% 7.68/1.53  sim_fw_subsumption_res:                 0
% 7.68/1.53  sim_bw_subsumption_res:                 0
% 7.68/1.53  sim_tautology_del:                      0
% 7.68/1.53  sim_eq_tautology_del:                   2110
% 7.68/1.53  sim_eq_res_simp:                        0
% 7.68/1.53  sim_fw_demodulated:                     4544
% 7.68/1.53  sim_bw_demodulated:                     74
% 7.68/1.53  sim_light_normalised:                   3535
% 7.68/1.53  sim_joinable_taut:                      446
% 7.68/1.53  sim_joinable_simp:                      0
% 7.68/1.53  sim_ac_normalised:                      0
% 7.68/1.53  sim_smt_subsumption:                    0
% 7.68/1.53  
%------------------------------------------------------------------------------
