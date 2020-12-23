%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:35:50 EST 2020

% Result     : Theorem 12.01s
% Output     : CNFRefutation 12.01s
% Verified   : 
% Statistics : Number of formulae       :  162 ( 644 expanded)
%              Number of clauses        :   71 (  97 expanded)
%              Number of leaves         :   32 ( 194 expanded)
%              Depth                    :   24
%              Number of atoms          :  357 ( 971 expanded)
%              Number of equality atoms :  217 ( 793 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal clause size      :   10 (   2 average)
%              Maximal term depth       :    8 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f10,axiom,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f57,plain,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    inference(cnf_transformation,[],[f10])).

fof(f9,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f56,plain,(
    ! [X2,X0,X1] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f9])).

fof(f23,conjecture,(
    ! [X0,X1] :
      ~ ( k1_tarski(X1) != X0
        & k1_xboole_0 != X0
        & k1_xboole_0 = k4_xboole_0(X0,k1_tarski(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,negated_conjecture,(
    ~ ! [X0,X1] :
        ~ ( k1_tarski(X1) != X0
          & k1_xboole_0 != X0
          & k1_xboole_0 = k4_xboole_0(X0,k1_tarski(X1)) ) ),
    inference(negated_conjecture,[],[f23])).

fof(f32,plain,(
    ? [X0,X1] :
      ( k1_tarski(X1) != X0
      & k1_xboole_0 != X0
      & k1_xboole_0 = k4_xboole_0(X0,k1_tarski(X1)) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f44,plain,
    ( ? [X0,X1] :
        ( k1_tarski(X1) != X0
        & k1_xboole_0 != X0
        & k1_xboole_0 = k4_xboole_0(X0,k1_tarski(X1)) )
   => ( k1_tarski(sK4) != sK3
      & k1_xboole_0 != sK3
      & k1_xboole_0 = k4_xboole_0(sK3,k1_tarski(sK4)) ) ),
    introduced(choice_axiom,[])).

fof(f45,plain,
    ( k1_tarski(sK4) != sK3
    & k1_xboole_0 != sK3
    & k1_xboole_0 = k4_xboole_0(sK3,k1_tarski(sK4)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f32,f44])).

fof(f74,plain,(
    k1_xboole_0 = k4_xboole_0(sK3,k1_tarski(sK4)) ),
    inference(cnf_transformation,[],[f45])).

fof(f5,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f52,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f11,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f58,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f11])).

fof(f21,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f72,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f21])).

fof(f82,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f72,f81])).

fof(f83,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) ),
    inference(definition_unfolding,[],[f58,f82])).

fof(f84,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) ),
    inference(definition_unfolding,[],[f52,f83])).

fof(f13,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f63,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f13])).

fof(f14,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f64,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f14])).

fof(f15,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f65,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f15])).

fof(f16,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f66,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f16])).

fof(f17,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f67,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f17])).

fof(f18,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f68,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f18])).

fof(f19,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f69,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f19])).

fof(f77,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f68,f69])).

fof(f78,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f67,f77])).

fof(f79,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f66,f78])).

fof(f80,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f65,f79])).

fof(f81,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f64,f80])).

fof(f85,plain,(
    ! [X0] : k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f63,f81])).

fof(f96,plain,(
    k1_xboole_0 = k5_xboole_0(sK3,k5_xboole_0(k5_xboole_0(sK3,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)),k3_tarski(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))))) ),
    inference(definition_unfolding,[],[f74,f84,f85])).

fof(f3,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f3])).

fof(f50,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f25])).

fof(f86,plain,(
    ! [X0] : k5_xboole_0(k5_xboole_0(X0,X0),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))) = X0 ),
    inference(definition_unfolding,[],[f50,f83])).

fof(f22,axiom,(
    ! [X0] : k3_tarski(k1_tarski(X0)) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f73,plain,(
    ! [X0] : k3_tarski(k1_tarski(X0)) = X0 ),
    inference(cnf_transformation,[],[f22])).

fof(f94,plain,(
    ! [X0] : k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) = X0 ),
    inference(definition_unfolding,[],[f73,f85])).

fof(f6,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f53,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f6])).

fof(f8,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f55,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f87,plain,(
    ! [X0,X1] : r1_tarski(X0,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) ),
    inference(definition_unfolding,[],[f55,f82])).

fof(f20,axiom,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
    <=> r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(k1_tarski(X0),X1)
        | ~ r2_hidden(X0,X1) )
      & ( r2_hidden(X0,X1)
        | ~ r1_tarski(k1_tarski(X0),X1) ) ) ),
    inference(nnf_transformation,[],[f20])).

fof(f71,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f92,plain,(
    ! [X0,X1] :
      ( r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f71,f85])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r2_xboole_0(X0,X1)
    <=> ( X0 != X1
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( X0 != X1
        & r1_tarski(X0,X1) )
     => r2_xboole_0(X0,X1) ) ),
    inference(unused_predicate_definition_removal,[],[f2])).

fof(f28,plain,(
    ! [X0,X1] :
      ( r2_xboole_0(X0,X1)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f26])).

fof(f29,plain,(
    ! [X0,X1] :
      ( r2_xboole_0(X0,X1)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f28])).

fof(f49,plain,(
    ! [X0,X1] :
      ( r2_xboole_0(X0,X1)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f76,plain,(
    k1_tarski(sK4) != sK3 ),
    inference(cnf_transformation,[],[f45])).

fof(f95,plain,(
    k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) != sK3 ),
    inference(definition_unfolding,[],[f76,f85])).

fof(f7,axiom,(
    ! [X0,X1] :
      ~ ( r2_xboole_0(X1,X0)
        & r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1] :
      ( ~ r2_xboole_0(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ~ r2_xboole_0(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
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
    inference(nnf_transformation,[],[f12])).

fof(f40,plain,(
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
    inference(rectify,[],[f39])).

fof(f41,plain,(
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

fof(f42,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f40,f41])).

fof(f59,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f42])).

fof(f91,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) != X1 ) ),
    inference(definition_unfolding,[],[f59,f85])).

fof(f99,plain,(
    ! [X0,X3] :
      ( X0 = X3
      | ~ r2_hidden(X3,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) ) ),
    inference(equality_resolution,[],[f91])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f27])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f33])).

fof(f35,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK0(X0,X1),X1)
          & r2_hidden(sK0(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f34,f35])).

fof(f46,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f4,axiom,(
    ! [X0] :
      ~ ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f4])).

fof(f37,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK1(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,(
    ! [X0] :
      ( r2_hidden(sK1(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f30,f37])).

fof(f51,plain,(
    ! [X0] :
      ( r2_hidden(sK1(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f38])).

fof(f60,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | X0 != X3
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f42])).

fof(f90,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | X0 != X3
      | k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) != X1 ) ),
    inference(definition_unfolding,[],[f60,f85])).

fof(f97,plain,(
    ! [X3,X1] :
      ( r2_hidden(X3,X1)
      | k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X3) != X1 ) ),
    inference(equality_resolution,[],[f90])).

fof(f98,plain,(
    ! [X3] : r2_hidden(X3,k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X3)) ),
    inference(equality_resolution,[],[f97])).

fof(f75,plain,(
    k1_xboole_0 != sK3 ),
    inference(cnf_transformation,[],[f45])).

cnf(c_10,plain,
    ( k5_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f57])).

cnf(c_9,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_20,negated_conjecture,
    ( k1_xboole_0 = k5_xboole_0(sK3,k5_xboole_0(k5_xboole_0(sK3,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)),k3_tarski(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))))) ),
    inference(cnf_transformation,[],[f96])).

cnf(c_822,plain,
    ( k5_xboole_0(sK3,k5_xboole_0(sK3,k5_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k3_tarski(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)))))) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_9,c_20])).

cnf(c_843,plain,
    ( k5_xboole_0(sK3,k5_xboole_0(k5_xboole_0(sK3,k5_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k3_tarski(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))))),X0)) = k5_xboole_0(k1_xboole_0,X0) ),
    inference(superposition,[status(thm)],[c_822,c_9])).

cnf(c_4,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X0),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))) = X0 ),
    inference(cnf_transformation,[],[f86])).

cnf(c_17,plain,
    ( k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) = X0 ),
    inference(cnf_transformation,[],[f94])).

cnf(c_564,plain,
    ( k5_xboole_0(k1_xboole_0,X0) = X0 ),
    inference(light_normalisation,[status(thm)],[c_4,c_10,c_17])).

cnf(c_844,plain,
    ( k5_xboole_0(sK3,k5_xboole_0(k5_xboole_0(sK3,k5_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k3_tarski(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))))),X0)) = X0 ),
    inference(light_normalisation,[status(thm)],[c_843,c_564])).

cnf(c_1297,plain,
    ( k5_xboole_0(sK3,k5_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k3_tarski(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))))) = k5_xboole_0(sK3,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_10,c_844])).

cnf(c_6,plain,
    ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f53])).

cnf(c_1317,plain,
    ( k5_xboole_0(sK3,k5_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k3_tarski(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))))) = sK3 ),
    inference(demodulation,[status(thm)],[c_1297,c_6])).

cnf(c_1322,plain,
    ( k5_xboole_0(sK3,k5_xboole_0(sK3,X0)) = X0 ),
    inference(demodulation,[status(thm)],[c_1317,c_844])).

cnf(c_1427,plain,
    ( k5_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k3_tarski(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1322,c_822])).

cnf(c_1464,plain,
    ( k5_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k5_xboole_0(k3_tarski(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))),X0)) = k5_xboole_0(k1_xboole_0,X0) ),
    inference(superposition,[status(thm)],[c_1427,c_9])).

cnf(c_1466,plain,
    ( k5_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k5_xboole_0(k3_tarski(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))),X0)) = X0 ),
    inference(light_normalisation,[status(thm)],[c_1464,c_564])).

cnf(c_1553,plain,
    ( k3_tarski(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))) = k5_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_10,c_1466])).

cnf(c_1570,plain,
    ( k3_tarski(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))) = k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) ),
    inference(demodulation,[status(thm)],[c_1553,c_6])).

cnf(c_8,plain,
    ( r1_tarski(X0,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_525,plain,
    ( r1_tarski(X0,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_43651,plain,
    ( r1_tarski(sK3,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1570,c_525])).

cnf(c_15,plain,
    ( ~ r2_hidden(X0,X1)
    | r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_1495,plain,
    ( ~ r2_hidden(sK1(sK3),X0)
    | r1_tarski(k6_enumset1(sK1(sK3),sK1(sK3),sK1(sK3),sK1(sK3),sK1(sK3),sK1(sK3),sK1(sK3),sK1(sK3)),X0) ),
    inference(instantiation,[status(thm)],[c_15])).

cnf(c_42832,plain,
    ( ~ r2_hidden(sK1(sK3),k5_xboole_0(k5_xboole_0(sK3,sK3),k3_tarski(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3))))
    | r1_tarski(k6_enumset1(sK1(sK3),sK1(sK3),sK1(sK3),sK1(sK3),sK1(sK3),sK1(sK3),sK1(sK3),sK1(sK3)),k5_xboole_0(k5_xboole_0(sK3,sK3),k3_tarski(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3)))) ),
    inference(instantiation,[status(thm)],[c_1495])).

cnf(c_42835,plain,
    ( r2_hidden(sK1(sK3),k5_xboole_0(k5_xboole_0(sK3,sK3),k3_tarski(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3)))) != iProver_top
    | r1_tarski(k6_enumset1(sK1(sK3),sK1(sK3),sK1(sK3),sK1(sK3),sK1(sK3),sK1(sK3),sK1(sK3),sK1(sK3)),k5_xboole_0(k5_xboole_0(sK3,sK3),k3_tarski(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_42832])).

cnf(c_185,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_701,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2),X3)
    | X3 != X1
    | k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2) != X0 ),
    inference(instantiation,[status(thm)],[c_185])).

cnf(c_1130,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),sK3)
    | k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) != X0
    | sK3 != X1 ),
    inference(instantiation,[status(thm)],[c_701])).

cnf(c_4798,plain,
    ( ~ r1_tarski(X0,k5_xboole_0(k5_xboole_0(sK3,sK3),k3_tarski(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3))))
    | r1_tarski(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),sK3)
    | k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) != X0
    | sK3 != k5_xboole_0(k5_xboole_0(sK3,sK3),k3_tarski(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3))) ),
    inference(instantiation,[status(thm)],[c_1130])).

cnf(c_42831,plain,
    ( ~ r1_tarski(k6_enumset1(sK1(sK3),sK1(sK3),sK1(sK3),sK1(sK3),sK1(sK3),sK1(sK3),sK1(sK3),sK1(sK3)),k5_xboole_0(k5_xboole_0(sK3,sK3),k3_tarski(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3))))
    | r1_tarski(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),sK3)
    | k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) != k6_enumset1(sK1(sK3),sK1(sK3),sK1(sK3),sK1(sK3),sK1(sK3),sK1(sK3),sK1(sK3),sK1(sK3))
    | sK3 != k5_xboole_0(k5_xboole_0(sK3,sK3),k3_tarski(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3))) ),
    inference(instantiation,[status(thm)],[c_4798])).

cnf(c_42833,plain,
    ( k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) != k6_enumset1(sK1(sK3),sK1(sK3),sK1(sK3),sK1(sK3),sK1(sK3),sK1(sK3),sK1(sK3),sK1(sK3))
    | sK3 != k5_xboole_0(k5_xboole_0(sK3,sK3),k3_tarski(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3)))
    | r1_tarski(k6_enumset1(sK1(sK3),sK1(sK3),sK1(sK3),sK1(sK3),sK1(sK3),sK1(sK3),sK1(sK3),sK1(sK3)),k5_xboole_0(k5_xboole_0(sK3,sK3),k3_tarski(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3)))) != iProver_top
    | r1_tarski(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_42831])).

cnf(c_3,plain,
    ( r2_xboole_0(X0,X1)
    | ~ r1_tarski(X0,X1)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f49])).

cnf(c_18,negated_conjecture,
    ( k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) != sK3 ),
    inference(cnf_transformation,[],[f95])).

cnf(c_861,plain,
    ( r2_xboole_0(sK3,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))
    | ~ r1_tarski(sK3,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)) ),
    inference(resolution,[status(thm)],[c_3,c_18])).

cnf(c_7,plain,
    ( ~ r2_xboole_0(X0,X1)
    | ~ r1_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_7749,plain,
    ( ~ r1_tarski(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),sK3)
    | ~ r1_tarski(sK3,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)) ),
    inference(resolution,[status(thm)],[c_861,c_7])).

cnf(c_7750,plain,
    ( r1_tarski(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),sK3) != iProver_top
    | r1_tarski(sK3,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7749])).

cnf(c_186,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_719,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(sK1(sK3),sK3)
    | X0 != sK1(sK3)
    | X1 != sK3 ),
    inference(instantiation,[status(thm)],[c_186])).

cnf(c_1538,plain,
    ( r2_hidden(sK1(sK3),X0)
    | ~ r2_hidden(sK1(sK3),sK3)
    | X0 != sK3
    | sK1(sK3) != sK1(sK3) ),
    inference(instantiation,[status(thm)],[c_719])).

cnf(c_4841,plain,
    ( r2_hidden(sK1(sK3),k5_xboole_0(k5_xboole_0(sK3,sK3),k3_tarski(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3))))
    | ~ r2_hidden(sK1(sK3),sK3)
    | k5_xboole_0(k5_xboole_0(sK3,sK3),k3_tarski(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3))) != sK3
    | sK1(sK3) != sK1(sK3) ),
    inference(instantiation,[status(thm)],[c_1538])).

cnf(c_4855,plain,
    ( k5_xboole_0(k5_xboole_0(sK3,sK3),k3_tarski(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3))) != sK3
    | sK1(sK3) != sK1(sK3)
    | r2_hidden(sK1(sK3),k5_xboole_0(k5_xboole_0(sK3,sK3),k3_tarski(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3)))) = iProver_top
    | r2_hidden(sK1(sK3),sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4841])).

cnf(c_14,plain,
    ( ~ r2_hidden(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))
    | X0 = X1 ),
    inference(cnf_transformation,[],[f99])).

cnf(c_4283,plain,
    ( ~ r2_hidden(sK1(sK3),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))
    | sK1(sK3) = X0 ),
    inference(instantiation,[status(thm)],[c_14])).

cnf(c_4284,plain,
    ( sK1(sK3) = X0
    | r2_hidden(sK1(sK3),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4283])).

cnf(c_4286,plain,
    ( sK1(sK3) = sK4
    | r2_hidden(sK1(sK3),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_4284])).

cnf(c_188,plain,
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

cnf(c_3336,plain,
    ( X0 != sK1(sK3)
    | X1 != sK1(sK3)
    | X2 != sK1(sK3)
    | X3 != sK1(sK3)
    | X4 != sK1(sK3)
    | X5 != sK1(sK3)
    | X6 != sK1(sK3)
    | X7 != sK1(sK3)
    | k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k6_enumset1(sK1(sK3),sK1(sK3),sK1(sK3),sK1(sK3),sK1(sK3),sK1(sK3),sK1(sK3),sK1(sK3)) ),
    inference(instantiation,[status(thm)],[c_188])).

cnf(c_3338,plain,
    ( k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) = k6_enumset1(sK1(sK3),sK1(sK3),sK1(sK3),sK1(sK3),sK1(sK3),sK1(sK3),sK1(sK3),sK1(sK3))
    | sK4 != sK1(sK3) ),
    inference(instantiation,[status(thm)],[c_3336])).

cnf(c_2,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | ~ r1_tarski(X1,X2) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_717,plain,
    ( r2_hidden(sK1(sK3),X0)
    | ~ r2_hidden(sK1(sK3),sK3)
    | ~ r1_tarski(sK3,X0) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_2963,plain,
    ( r2_hidden(sK1(sK3),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))
    | ~ r2_hidden(sK1(sK3),sK3)
    | ~ r1_tarski(sK3,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)) ),
    inference(instantiation,[status(thm)],[c_717])).

cnf(c_2964,plain,
    ( r2_hidden(sK1(sK3),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)) = iProver_top
    | r2_hidden(sK1(sK3),sK3) != iProver_top
    | r1_tarski(sK3,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2963])).

cnf(c_1665,plain,
    ( k5_xboole_0(k5_xboole_0(sK3,sK3),k3_tarski(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3))) = sK3 ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_184,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_764,plain,
    ( X0 != X1
    | sK3 != X1
    | sK3 = X0 ),
    inference(instantiation,[status(thm)],[c_184])).

cnf(c_931,plain,
    ( X0 != sK3
    | sK3 = X0
    | sK3 != sK3 ),
    inference(instantiation,[status(thm)],[c_764])).

cnf(c_1664,plain,
    ( k5_xboole_0(k5_xboole_0(sK3,sK3),k3_tarski(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3))) != sK3
    | sK3 = k5_xboole_0(k5_xboole_0(sK3,sK3),k3_tarski(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3)))
    | sK3 != sK3 ),
    inference(instantiation,[status(thm)],[c_931])).

cnf(c_183,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_1539,plain,
    ( sK1(sK3) = sK1(sK3) ),
    inference(instantiation,[status(thm)],[c_183])).

cnf(c_1530,plain,
    ( X0 != X1
    | X0 = sK1(sK3)
    | sK1(sK3) != X1 ),
    inference(instantiation,[status(thm)],[c_184])).

cnf(c_1531,plain,
    ( sK1(sK3) != sK4
    | sK4 = sK1(sK3)
    | sK4 != sK4 ),
    inference(instantiation,[status(thm)],[c_1530])).

cnf(c_932,plain,
    ( sK3 = sK3 ),
    inference(instantiation,[status(thm)],[c_183])).

cnf(c_5,plain,
    ( r2_hidden(sK1(X0),X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f51])).

cnf(c_640,plain,
    ( r2_hidden(sK1(sK3),sK3)
    | k1_xboole_0 = sK3 ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_641,plain,
    ( k1_xboole_0 = sK3
    | r2_hidden(sK1(sK3),sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_640])).

cnf(c_13,plain,
    ( r2_hidden(X0,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) ),
    inference(cnf_transformation,[],[f98])).

cnf(c_32,plain,
    ( r2_hidden(sK4,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)) ),
    inference(instantiation,[status(thm)],[c_13])).

cnf(c_29,plain,
    ( ~ r2_hidden(sK4,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))
    | sK4 = sK4 ),
    inference(instantiation,[status(thm)],[c_14])).

cnf(c_19,negated_conjecture,
    ( k1_xboole_0 != sK3 ),
    inference(cnf_transformation,[],[f75])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_43651,c_42835,c_42833,c_7750,c_4855,c_4286,c_3338,c_2964,c_1665,c_1664,c_1539,c_1531,c_932,c_641,c_32,c_29,c_19])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n004.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 13:43:08 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 12.01/1.98  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 12.01/1.98  
% 12.01/1.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 12.01/1.98  
% 12.01/1.98  ------  iProver source info
% 12.01/1.98  
% 12.01/1.98  git: date: 2020-06-30 10:37:57 +0100
% 12.01/1.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 12.01/1.98  git: non_committed_changes: false
% 12.01/1.98  git: last_make_outside_of_git: false
% 12.01/1.98  
% 12.01/1.98  ------ 
% 12.01/1.98  ------ Parsing...
% 12.01/1.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 12.01/1.98  
% 12.01/1.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e 
% 12.01/1.98  
% 12.01/1.98  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 12.01/1.98  
% 12.01/1.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 12.01/1.98  ------ Proving...
% 12.01/1.98  ------ Problem Properties 
% 12.01/1.98  
% 12.01/1.98  
% 12.01/1.98  clauses                                 21
% 12.01/1.98  conjectures                             3
% 12.01/1.98  EPR                                     4
% 12.01/1.98  Horn                                    17
% 12.01/1.98  unary                                   10
% 12.01/1.98  binary                                  7
% 12.01/1.98  lits                                    36
% 12.01/1.98  lits eq                                 15
% 12.01/1.98  fd_pure                                 0
% 12.01/1.98  fd_pseudo                               0
% 12.01/1.98  fd_cond                                 1
% 12.01/1.98  fd_pseudo_cond                          3
% 12.01/1.98  AC symbols                              0
% 12.01/1.98  
% 12.01/1.98  ------ Input Options Time Limit: Unbounded
% 12.01/1.98  
% 12.01/1.98  
% 12.01/1.98  ------ 
% 12.01/1.98  Current options:
% 12.01/1.98  ------ 
% 12.01/1.98  
% 12.01/1.98  
% 12.01/1.98  
% 12.01/1.98  
% 12.01/1.98  ------ Proving...
% 12.01/1.98  
% 12.01/1.98  
% 12.01/1.98  % SZS status Theorem for theBenchmark.p
% 12.01/1.98  
% 12.01/1.98  % SZS output start CNFRefutation for theBenchmark.p
% 12.01/1.98  
% 12.01/1.98  fof(f10,axiom,(
% 12.01/1.98    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0)),
% 12.01/1.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 12.01/1.98  
% 12.01/1.98  fof(f57,plain,(
% 12.01/1.98    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(X0,X0)) )),
% 12.01/1.98    inference(cnf_transformation,[],[f10])).
% 12.01/1.98  
% 12.01/1.98  fof(f9,axiom,(
% 12.01/1.98    ! [X0,X1,X2] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2)),
% 12.01/1.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 12.01/1.98  
% 12.01/1.98  fof(f56,plain,(
% 12.01/1.98    ( ! [X2,X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2)) )),
% 12.01/1.98    inference(cnf_transformation,[],[f9])).
% 12.01/1.98  
% 12.01/1.98  fof(f23,conjecture,(
% 12.01/1.98    ! [X0,X1] : ~(k1_tarski(X1) != X0 & k1_xboole_0 != X0 & k1_xboole_0 = k4_xboole_0(X0,k1_tarski(X1)))),
% 12.01/1.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 12.01/1.98  
% 12.01/1.98  fof(f24,negated_conjecture,(
% 12.01/1.98    ~! [X0,X1] : ~(k1_tarski(X1) != X0 & k1_xboole_0 != X0 & k1_xboole_0 = k4_xboole_0(X0,k1_tarski(X1)))),
% 12.01/1.98    inference(negated_conjecture,[],[f23])).
% 12.01/1.98  
% 12.01/1.98  fof(f32,plain,(
% 12.01/1.98    ? [X0,X1] : (k1_tarski(X1) != X0 & k1_xboole_0 != X0 & k1_xboole_0 = k4_xboole_0(X0,k1_tarski(X1)))),
% 12.01/1.98    inference(ennf_transformation,[],[f24])).
% 12.01/1.98  
% 12.01/1.98  fof(f44,plain,(
% 12.01/1.98    ? [X0,X1] : (k1_tarski(X1) != X0 & k1_xboole_0 != X0 & k1_xboole_0 = k4_xboole_0(X0,k1_tarski(X1))) => (k1_tarski(sK4) != sK3 & k1_xboole_0 != sK3 & k1_xboole_0 = k4_xboole_0(sK3,k1_tarski(sK4)))),
% 12.01/1.98    introduced(choice_axiom,[])).
% 12.01/1.98  
% 12.01/1.98  fof(f45,plain,(
% 12.01/1.98    k1_tarski(sK4) != sK3 & k1_xboole_0 != sK3 & k1_xboole_0 = k4_xboole_0(sK3,k1_tarski(sK4))),
% 12.01/1.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f32,f44])).
% 12.01/1.98  
% 12.01/1.98  fof(f74,plain,(
% 12.01/1.98    k1_xboole_0 = k4_xboole_0(sK3,k1_tarski(sK4))),
% 12.01/1.98    inference(cnf_transformation,[],[f45])).
% 12.01/1.98  
% 12.01/1.98  fof(f5,axiom,(
% 12.01/1.98    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 12.01/1.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 12.01/1.98  
% 12.01/1.98  fof(f52,plain,(
% 12.01/1.98    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 12.01/1.98    inference(cnf_transformation,[],[f5])).
% 12.01/1.98  
% 12.01/1.98  fof(f11,axiom,(
% 12.01/1.98    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))),
% 12.01/1.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 12.01/1.98  
% 12.01/1.98  fof(f58,plain,(
% 12.01/1.98    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))) )),
% 12.01/1.98    inference(cnf_transformation,[],[f11])).
% 12.01/1.98  
% 12.01/1.98  fof(f21,axiom,(
% 12.01/1.98    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 12.01/1.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 12.01/1.98  
% 12.01/1.98  fof(f72,plain,(
% 12.01/1.98    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 12.01/1.98    inference(cnf_transformation,[],[f21])).
% 12.01/1.98  
% 12.01/1.98  fof(f82,plain,(
% 12.01/1.98    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) )),
% 12.01/1.98    inference(definition_unfolding,[],[f72,f81])).
% 12.01/1.98  
% 12.01/1.98  fof(f83,plain,(
% 12.01/1.98    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) )),
% 12.01/1.98    inference(definition_unfolding,[],[f58,f82])).
% 12.01/1.98  
% 12.01/1.98  fof(f84,plain,(
% 12.01/1.98    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))))) )),
% 12.01/1.98    inference(definition_unfolding,[],[f52,f83])).
% 12.01/1.98  
% 12.01/1.98  fof(f13,axiom,(
% 12.01/1.98    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)),
% 12.01/1.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 12.01/1.98  
% 12.01/1.98  fof(f63,plain,(
% 12.01/1.98    ( ! [X0] : (k1_tarski(X0) = k2_tarski(X0,X0)) )),
% 12.01/1.98    inference(cnf_transformation,[],[f13])).
% 12.01/1.98  
% 12.01/1.98  fof(f14,axiom,(
% 12.01/1.98    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 12.01/1.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 12.01/1.98  
% 12.01/1.98  fof(f64,plain,(
% 12.01/1.98    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 12.01/1.98    inference(cnf_transformation,[],[f14])).
% 12.01/1.98  
% 12.01/1.98  fof(f15,axiom,(
% 12.01/1.98    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 12.01/1.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 12.01/1.98  
% 12.01/1.98  fof(f65,plain,(
% 12.01/1.98    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 12.01/1.98    inference(cnf_transformation,[],[f15])).
% 12.01/1.98  
% 12.01/1.98  fof(f16,axiom,(
% 12.01/1.98    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 12.01/1.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 12.01/1.98  
% 12.01/1.98  fof(f66,plain,(
% 12.01/1.98    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 12.01/1.98    inference(cnf_transformation,[],[f16])).
% 12.01/1.98  
% 12.01/1.98  fof(f17,axiom,(
% 12.01/1.98    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)),
% 12.01/1.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 12.01/1.98  
% 12.01/1.98  fof(f67,plain,(
% 12.01/1.98    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)) )),
% 12.01/1.98    inference(cnf_transformation,[],[f17])).
% 12.01/1.98  
% 12.01/1.98  fof(f18,axiom,(
% 12.01/1.98    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)),
% 12.01/1.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 12.01/1.98  
% 12.01/1.98  fof(f68,plain,(
% 12.01/1.98    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)) )),
% 12.01/1.98    inference(cnf_transformation,[],[f18])).
% 12.01/1.98  
% 12.01/1.98  fof(f19,axiom,(
% 12.01/1.98    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)),
% 12.01/1.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 12.01/1.98  
% 12.01/1.98  fof(f69,plain,(
% 12.01/1.98    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)) )),
% 12.01/1.98    inference(cnf_transformation,[],[f19])).
% 12.01/1.98  
% 12.01/1.98  fof(f77,plain,(
% 12.01/1.98    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 12.01/1.98    inference(definition_unfolding,[],[f68,f69])).
% 12.01/1.98  
% 12.01/1.98  fof(f78,plain,(
% 12.01/1.98    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 12.01/1.98    inference(definition_unfolding,[],[f67,f77])).
% 12.01/1.98  
% 12.01/1.98  fof(f79,plain,(
% 12.01/1.98    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 12.01/1.98    inference(definition_unfolding,[],[f66,f78])).
% 12.01/1.98  
% 12.01/1.98  fof(f80,plain,(
% 12.01/1.98    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 12.01/1.98    inference(definition_unfolding,[],[f65,f79])).
% 12.01/1.98  
% 12.01/1.98  fof(f81,plain,(
% 12.01/1.98    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 12.01/1.98    inference(definition_unfolding,[],[f64,f80])).
% 12.01/1.98  
% 12.01/1.98  fof(f85,plain,(
% 12.01/1.98    ( ! [X0] : (k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) )),
% 12.01/1.98    inference(definition_unfolding,[],[f63,f81])).
% 12.01/1.98  
% 12.01/1.98  fof(f96,plain,(
% 12.01/1.98    k1_xboole_0 = k5_xboole_0(sK3,k5_xboole_0(k5_xboole_0(sK3,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)),k3_tarski(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)))))),
% 12.01/1.98    inference(definition_unfolding,[],[f74,f84,f85])).
% 12.01/1.98  
% 12.01/1.98  fof(f3,axiom,(
% 12.01/1.98    ! [X0,X1] : k3_xboole_0(X0,X0) = X0),
% 12.01/1.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 12.01/1.98  
% 12.01/1.98  fof(f25,plain,(
% 12.01/1.98    ! [X0] : k3_xboole_0(X0,X0) = X0),
% 12.01/1.98    inference(rectify,[],[f3])).
% 12.01/1.98  
% 12.01/1.98  fof(f50,plain,(
% 12.01/1.98    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 12.01/1.98    inference(cnf_transformation,[],[f25])).
% 12.01/1.98  
% 12.01/1.98  fof(f86,plain,(
% 12.01/1.98    ( ! [X0] : (k5_xboole_0(k5_xboole_0(X0,X0),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))) = X0) )),
% 12.01/1.98    inference(definition_unfolding,[],[f50,f83])).
% 12.01/1.98  
% 12.01/1.98  fof(f22,axiom,(
% 12.01/1.98    ! [X0] : k3_tarski(k1_tarski(X0)) = X0),
% 12.01/1.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 12.01/1.98  
% 12.01/1.98  fof(f73,plain,(
% 12.01/1.98    ( ! [X0] : (k3_tarski(k1_tarski(X0)) = X0) )),
% 12.01/1.98    inference(cnf_transformation,[],[f22])).
% 12.01/1.98  
% 12.01/1.98  fof(f94,plain,(
% 12.01/1.98    ( ! [X0] : (k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) = X0) )),
% 12.01/1.98    inference(definition_unfolding,[],[f73,f85])).
% 12.01/1.98  
% 12.01/1.98  fof(f6,axiom,(
% 12.01/1.98    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 12.01/1.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 12.01/1.98  
% 12.01/1.98  fof(f53,plain,(
% 12.01/1.98    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 12.01/1.98    inference(cnf_transformation,[],[f6])).
% 12.01/1.98  
% 12.01/1.98  fof(f8,axiom,(
% 12.01/1.98    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 12.01/1.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 12.01/1.98  
% 12.01/1.98  fof(f55,plain,(
% 12.01/1.98    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 12.01/1.98    inference(cnf_transformation,[],[f8])).
% 12.01/1.98  
% 12.01/1.98  fof(f87,plain,(
% 12.01/1.98    ( ! [X0,X1] : (r1_tarski(X0,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) )),
% 12.01/1.98    inference(definition_unfolding,[],[f55,f82])).
% 12.01/1.98  
% 12.01/1.98  fof(f20,axiom,(
% 12.01/1.98    ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) <=> r2_hidden(X0,X1))),
% 12.01/1.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 12.01/1.98  
% 12.01/1.98  fof(f43,plain,(
% 12.01/1.98    ! [X0,X1] : ((r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) & (r2_hidden(X0,X1) | ~r1_tarski(k1_tarski(X0),X1)))),
% 12.01/1.98    inference(nnf_transformation,[],[f20])).
% 12.01/1.98  
% 12.01/1.98  fof(f71,plain,(
% 12.01/1.98    ( ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) )),
% 12.01/1.98    inference(cnf_transformation,[],[f43])).
% 12.01/1.98  
% 12.01/1.98  fof(f92,plain,(
% 12.01/1.98    ( ! [X0,X1] : (r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1) | ~r2_hidden(X0,X1)) )),
% 12.01/1.98    inference(definition_unfolding,[],[f71,f85])).
% 12.01/1.98  
% 12.01/1.98  fof(f2,axiom,(
% 12.01/1.98    ! [X0,X1] : (r2_xboole_0(X0,X1) <=> (X0 != X1 & r1_tarski(X0,X1)))),
% 12.01/1.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 12.01/1.98  
% 12.01/1.98  fof(f26,plain,(
% 12.01/1.98    ! [X0,X1] : ((X0 != X1 & r1_tarski(X0,X1)) => r2_xboole_0(X0,X1))),
% 12.01/1.98    inference(unused_predicate_definition_removal,[],[f2])).
% 12.01/1.98  
% 12.01/1.98  fof(f28,plain,(
% 12.01/1.98    ! [X0,X1] : (r2_xboole_0(X0,X1) | (X0 = X1 | ~r1_tarski(X0,X1)))),
% 12.01/1.98    inference(ennf_transformation,[],[f26])).
% 12.01/1.98  
% 12.01/1.98  fof(f29,plain,(
% 12.01/1.98    ! [X0,X1] : (r2_xboole_0(X0,X1) | X0 = X1 | ~r1_tarski(X0,X1))),
% 12.01/1.98    inference(flattening,[],[f28])).
% 12.01/1.98  
% 12.01/1.98  fof(f49,plain,(
% 12.01/1.98    ( ! [X0,X1] : (r2_xboole_0(X0,X1) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 12.01/1.98    inference(cnf_transformation,[],[f29])).
% 12.01/1.98  
% 12.01/1.98  fof(f76,plain,(
% 12.01/1.98    k1_tarski(sK4) != sK3),
% 12.01/1.98    inference(cnf_transformation,[],[f45])).
% 12.01/1.98  
% 12.01/1.98  fof(f95,plain,(
% 12.01/1.98    k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) != sK3),
% 12.01/1.98    inference(definition_unfolding,[],[f76,f85])).
% 12.01/1.98  
% 12.01/1.98  fof(f7,axiom,(
% 12.01/1.98    ! [X0,X1] : ~(r2_xboole_0(X1,X0) & r1_tarski(X0,X1))),
% 12.01/1.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 12.01/1.98  
% 12.01/1.98  fof(f31,plain,(
% 12.01/1.98    ! [X0,X1] : (~r2_xboole_0(X1,X0) | ~r1_tarski(X0,X1))),
% 12.01/1.98    inference(ennf_transformation,[],[f7])).
% 12.01/1.98  
% 12.01/1.98  fof(f54,plain,(
% 12.01/1.98    ( ! [X0,X1] : (~r2_xboole_0(X1,X0) | ~r1_tarski(X0,X1)) )),
% 12.01/1.98    inference(cnf_transformation,[],[f31])).
% 12.01/1.98  
% 12.01/1.98  fof(f12,axiom,(
% 12.01/1.98    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 12.01/1.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 12.01/1.98  
% 12.01/1.98  fof(f39,plain,(
% 12.01/1.98    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | X0 != X2) & (X0 = X2 | ~r2_hidden(X2,X1))) | k1_tarski(X0) != X1))),
% 12.01/1.98    inference(nnf_transformation,[],[f12])).
% 12.01/1.98  
% 12.01/1.98  fof(f40,plain,(
% 12.01/1.98    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 12.01/1.98    inference(rectify,[],[f39])).
% 12.01/1.98  
% 12.01/1.98  fof(f41,plain,(
% 12.01/1.98    ! [X1,X0] : (? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1))) => ((sK2(X0,X1) != X0 | ~r2_hidden(sK2(X0,X1),X1)) & (sK2(X0,X1) = X0 | r2_hidden(sK2(X0,X1),X1))))),
% 12.01/1.98    introduced(choice_axiom,[])).
% 12.01/1.98  
% 12.01/1.98  fof(f42,plain,(
% 12.01/1.98    ! [X0,X1] : ((k1_tarski(X0) = X1 | ((sK2(X0,X1) != X0 | ~r2_hidden(sK2(X0,X1),X1)) & (sK2(X0,X1) = X0 | r2_hidden(sK2(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 12.01/1.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f40,f41])).
% 12.01/1.98  
% 12.01/1.98  fof(f59,plain,(
% 12.01/1.98    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k1_tarski(X0) != X1) )),
% 12.01/1.98    inference(cnf_transformation,[],[f42])).
% 12.01/1.98  
% 12.01/1.98  fof(f91,plain,(
% 12.01/1.98    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) != X1) )),
% 12.01/1.98    inference(definition_unfolding,[],[f59,f85])).
% 12.01/1.98  
% 12.01/1.98  fof(f99,plain,(
% 12.01/1.98    ( ! [X0,X3] : (X0 = X3 | ~r2_hidden(X3,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))) )),
% 12.01/1.98    inference(equality_resolution,[],[f91])).
% 12.01/1.98  
% 12.01/1.98  fof(f1,axiom,(
% 12.01/1.98    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 12.01/1.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 12.01/1.98  
% 12.01/1.98  fof(f27,plain,(
% 12.01/1.98    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 12.01/1.98    inference(ennf_transformation,[],[f1])).
% 12.01/1.98  
% 12.01/1.98  fof(f33,plain,(
% 12.01/1.98    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 12.01/1.98    inference(nnf_transformation,[],[f27])).
% 12.01/1.98  
% 12.01/1.98  fof(f34,plain,(
% 12.01/1.98    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 12.01/1.98    inference(rectify,[],[f33])).
% 12.01/1.98  
% 12.01/1.98  fof(f35,plain,(
% 12.01/1.98    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 12.01/1.98    introduced(choice_axiom,[])).
% 12.01/1.98  
% 12.01/1.98  fof(f36,plain,(
% 12.01/1.98    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 12.01/1.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f34,f35])).
% 12.01/1.98  
% 12.01/1.98  fof(f46,plain,(
% 12.01/1.98    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,X1)) )),
% 12.01/1.98    inference(cnf_transformation,[],[f36])).
% 12.01/1.98  
% 12.01/1.98  fof(f4,axiom,(
% 12.01/1.98    ! [X0] : ~(! [X1] : ~r2_hidden(X1,X0) & k1_xboole_0 != X0)),
% 12.01/1.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 12.01/1.98  
% 12.01/1.98  fof(f30,plain,(
% 12.01/1.98    ! [X0] : (? [X1] : r2_hidden(X1,X0) | k1_xboole_0 = X0)),
% 12.01/1.98    inference(ennf_transformation,[],[f4])).
% 12.01/1.98  
% 12.01/1.98  fof(f37,plain,(
% 12.01/1.98    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK1(X0),X0))),
% 12.01/1.98    introduced(choice_axiom,[])).
% 12.01/1.98  
% 12.01/1.98  fof(f38,plain,(
% 12.01/1.98    ! [X0] : (r2_hidden(sK1(X0),X0) | k1_xboole_0 = X0)),
% 12.01/1.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f30,f37])).
% 12.01/1.98  
% 12.01/1.98  fof(f51,plain,(
% 12.01/1.98    ( ! [X0] : (r2_hidden(sK1(X0),X0) | k1_xboole_0 = X0) )),
% 12.01/1.98    inference(cnf_transformation,[],[f38])).
% 12.01/1.98  
% 12.01/1.98  fof(f60,plain,(
% 12.01/1.98    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | X0 != X3 | k1_tarski(X0) != X1) )),
% 12.01/1.98    inference(cnf_transformation,[],[f42])).
% 12.01/1.98  
% 12.01/1.98  fof(f90,plain,(
% 12.01/1.98    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | X0 != X3 | k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) != X1) )),
% 12.01/1.98    inference(definition_unfolding,[],[f60,f85])).
% 12.01/1.98  
% 12.01/1.98  fof(f97,plain,(
% 12.01/1.98    ( ! [X3,X1] : (r2_hidden(X3,X1) | k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X3) != X1) )),
% 12.01/1.98    inference(equality_resolution,[],[f90])).
% 12.01/1.98  
% 12.01/1.98  fof(f98,plain,(
% 12.01/1.98    ( ! [X3] : (r2_hidden(X3,k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X3))) )),
% 12.01/1.98    inference(equality_resolution,[],[f97])).
% 12.01/1.98  
% 12.01/1.98  fof(f75,plain,(
% 12.01/1.98    k1_xboole_0 != sK3),
% 12.01/1.98    inference(cnf_transformation,[],[f45])).
% 12.01/1.98  
% 12.01/1.98  cnf(c_10,plain,
% 12.01/1.98      ( k5_xboole_0(X0,X0) = k1_xboole_0 ),
% 12.01/1.98      inference(cnf_transformation,[],[f57]) ).
% 12.01/1.98  
% 12.01/1.98  cnf(c_9,plain,
% 12.01/1.98      ( k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
% 12.01/1.98      inference(cnf_transformation,[],[f56]) ).
% 12.01/1.98  
% 12.01/1.98  cnf(c_20,negated_conjecture,
% 12.01/1.98      ( k1_xboole_0 = k5_xboole_0(sK3,k5_xboole_0(k5_xboole_0(sK3,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)),k3_tarski(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))))) ),
% 12.01/1.98      inference(cnf_transformation,[],[f96]) ).
% 12.01/1.98  
% 12.01/1.98  cnf(c_822,plain,
% 12.01/1.98      ( k5_xboole_0(sK3,k5_xboole_0(sK3,k5_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k3_tarski(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)))))) = k1_xboole_0 ),
% 12.01/1.98      inference(demodulation,[status(thm)],[c_9,c_20]) ).
% 12.01/1.98  
% 12.01/1.98  cnf(c_843,plain,
% 12.01/1.98      ( k5_xboole_0(sK3,k5_xboole_0(k5_xboole_0(sK3,k5_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k3_tarski(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))))),X0)) = k5_xboole_0(k1_xboole_0,X0) ),
% 12.01/1.98      inference(superposition,[status(thm)],[c_822,c_9]) ).
% 12.01/1.98  
% 12.01/1.98  cnf(c_4,plain,
% 12.01/1.98      ( k5_xboole_0(k5_xboole_0(X0,X0),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))) = X0 ),
% 12.01/1.98      inference(cnf_transformation,[],[f86]) ).
% 12.01/1.98  
% 12.01/1.98  cnf(c_17,plain,
% 12.01/1.98      ( k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) = X0 ),
% 12.01/1.98      inference(cnf_transformation,[],[f94]) ).
% 12.01/1.98  
% 12.01/1.98  cnf(c_564,plain,
% 12.01/1.98      ( k5_xboole_0(k1_xboole_0,X0) = X0 ),
% 12.01/1.98      inference(light_normalisation,[status(thm)],[c_4,c_10,c_17]) ).
% 12.01/1.98  
% 12.01/1.98  cnf(c_844,plain,
% 12.01/1.98      ( k5_xboole_0(sK3,k5_xboole_0(k5_xboole_0(sK3,k5_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k3_tarski(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))))),X0)) = X0 ),
% 12.01/1.98      inference(light_normalisation,[status(thm)],[c_843,c_564]) ).
% 12.01/1.98  
% 12.01/1.98  cnf(c_1297,plain,
% 12.01/1.98      ( k5_xboole_0(sK3,k5_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k3_tarski(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))))) = k5_xboole_0(sK3,k1_xboole_0) ),
% 12.01/1.98      inference(superposition,[status(thm)],[c_10,c_844]) ).
% 12.01/1.98  
% 12.01/1.98  cnf(c_6,plain,
% 12.01/1.98      ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
% 12.01/1.98      inference(cnf_transformation,[],[f53]) ).
% 12.01/1.98  
% 12.01/1.98  cnf(c_1317,plain,
% 12.01/1.98      ( k5_xboole_0(sK3,k5_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k3_tarski(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))))) = sK3 ),
% 12.01/1.98      inference(demodulation,[status(thm)],[c_1297,c_6]) ).
% 12.01/1.98  
% 12.01/1.98  cnf(c_1322,plain,
% 12.01/1.98      ( k5_xboole_0(sK3,k5_xboole_0(sK3,X0)) = X0 ),
% 12.01/1.98      inference(demodulation,[status(thm)],[c_1317,c_844]) ).
% 12.01/1.98  
% 12.01/1.98  cnf(c_1427,plain,
% 12.01/1.98      ( k5_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k3_tarski(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)))) = k1_xboole_0 ),
% 12.01/1.98      inference(superposition,[status(thm)],[c_1322,c_822]) ).
% 12.01/1.98  
% 12.01/1.98  cnf(c_1464,plain,
% 12.01/1.98      ( k5_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k5_xboole_0(k3_tarski(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))),X0)) = k5_xboole_0(k1_xboole_0,X0) ),
% 12.01/1.98      inference(superposition,[status(thm)],[c_1427,c_9]) ).
% 12.01/1.98  
% 12.01/1.98  cnf(c_1466,plain,
% 12.01/1.98      ( k5_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k5_xboole_0(k3_tarski(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))),X0)) = X0 ),
% 12.01/1.98      inference(light_normalisation,[status(thm)],[c_1464,c_564]) ).
% 12.01/1.98  
% 12.01/1.98  cnf(c_1553,plain,
% 12.01/1.98      ( k3_tarski(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))) = k5_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k1_xboole_0) ),
% 12.01/1.98      inference(superposition,[status(thm)],[c_10,c_1466]) ).
% 12.01/1.98  
% 12.01/1.98  cnf(c_1570,plain,
% 12.01/1.98      ( k3_tarski(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))) = k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) ),
% 12.01/1.98      inference(demodulation,[status(thm)],[c_1553,c_6]) ).
% 12.01/1.98  
% 12.01/1.98  cnf(c_8,plain,
% 12.01/1.98      ( r1_tarski(X0,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) ),
% 12.01/1.98      inference(cnf_transformation,[],[f87]) ).
% 12.01/1.98  
% 12.01/1.98  cnf(c_525,plain,
% 12.01/1.98      ( r1_tarski(X0,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) = iProver_top ),
% 12.01/1.98      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 12.01/1.98  
% 12.01/1.98  cnf(c_43651,plain,
% 12.01/1.98      ( r1_tarski(sK3,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)) = iProver_top ),
% 12.01/1.98      inference(superposition,[status(thm)],[c_1570,c_525]) ).
% 12.01/1.98  
% 12.01/1.98  cnf(c_15,plain,
% 12.01/1.98      ( ~ r2_hidden(X0,X1)
% 12.01/1.98      | r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1) ),
% 12.01/1.98      inference(cnf_transformation,[],[f92]) ).
% 12.01/1.98  
% 12.01/1.98  cnf(c_1495,plain,
% 12.01/1.98      ( ~ r2_hidden(sK1(sK3),X0)
% 12.01/1.98      | r1_tarski(k6_enumset1(sK1(sK3),sK1(sK3),sK1(sK3),sK1(sK3),sK1(sK3),sK1(sK3),sK1(sK3),sK1(sK3)),X0) ),
% 12.01/1.98      inference(instantiation,[status(thm)],[c_15]) ).
% 12.01/1.98  
% 12.01/1.98  cnf(c_42832,plain,
% 12.01/1.98      ( ~ r2_hidden(sK1(sK3),k5_xboole_0(k5_xboole_0(sK3,sK3),k3_tarski(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3))))
% 12.01/1.98      | r1_tarski(k6_enumset1(sK1(sK3),sK1(sK3),sK1(sK3),sK1(sK3),sK1(sK3),sK1(sK3),sK1(sK3),sK1(sK3)),k5_xboole_0(k5_xboole_0(sK3,sK3),k3_tarski(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3)))) ),
% 12.01/1.98      inference(instantiation,[status(thm)],[c_1495]) ).
% 12.01/1.98  
% 12.01/1.98  cnf(c_42835,plain,
% 12.01/1.98      ( r2_hidden(sK1(sK3),k5_xboole_0(k5_xboole_0(sK3,sK3),k3_tarski(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3)))) != iProver_top
% 12.01/1.98      | r1_tarski(k6_enumset1(sK1(sK3),sK1(sK3),sK1(sK3),sK1(sK3),sK1(sK3),sK1(sK3),sK1(sK3),sK1(sK3)),k5_xboole_0(k5_xboole_0(sK3,sK3),k3_tarski(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3)))) = iProver_top ),
% 12.01/1.98      inference(predicate_to_equality,[status(thm)],[c_42832]) ).
% 12.01/1.98  
% 12.01/1.98  cnf(c_185,plain,
% 12.01/1.98      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,X3) | X2 != X0 | X3 != X1 ),
% 12.01/1.98      theory(equality) ).
% 12.01/1.98  
% 12.01/1.98  cnf(c_701,plain,
% 12.01/1.98      ( ~ r1_tarski(X0,X1)
% 12.01/1.98      | r1_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2),X3)
% 12.01/1.98      | X3 != X1
% 12.01/1.98      | k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2) != X0 ),
% 12.01/1.98      inference(instantiation,[status(thm)],[c_185]) ).
% 12.01/1.98  
% 12.01/1.98  cnf(c_1130,plain,
% 12.01/1.98      ( ~ r1_tarski(X0,X1)
% 12.01/1.98      | r1_tarski(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),sK3)
% 12.01/1.98      | k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) != X0
% 12.01/1.98      | sK3 != X1 ),
% 12.01/1.98      inference(instantiation,[status(thm)],[c_701]) ).
% 12.01/1.98  
% 12.01/1.98  cnf(c_4798,plain,
% 12.01/1.98      ( ~ r1_tarski(X0,k5_xboole_0(k5_xboole_0(sK3,sK3),k3_tarski(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3))))
% 12.01/1.98      | r1_tarski(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),sK3)
% 12.01/1.98      | k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) != X0
% 12.01/1.98      | sK3 != k5_xboole_0(k5_xboole_0(sK3,sK3),k3_tarski(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3))) ),
% 12.01/1.98      inference(instantiation,[status(thm)],[c_1130]) ).
% 12.01/1.98  
% 12.01/1.98  cnf(c_42831,plain,
% 12.01/1.98      ( ~ r1_tarski(k6_enumset1(sK1(sK3),sK1(sK3),sK1(sK3),sK1(sK3),sK1(sK3),sK1(sK3),sK1(sK3),sK1(sK3)),k5_xboole_0(k5_xboole_0(sK3,sK3),k3_tarski(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3))))
% 12.01/1.98      | r1_tarski(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),sK3)
% 12.01/1.98      | k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) != k6_enumset1(sK1(sK3),sK1(sK3),sK1(sK3),sK1(sK3),sK1(sK3),sK1(sK3),sK1(sK3),sK1(sK3))
% 12.01/1.98      | sK3 != k5_xboole_0(k5_xboole_0(sK3,sK3),k3_tarski(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3))) ),
% 12.01/1.98      inference(instantiation,[status(thm)],[c_4798]) ).
% 12.01/1.98  
% 12.01/1.98  cnf(c_42833,plain,
% 12.01/1.98      ( k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) != k6_enumset1(sK1(sK3),sK1(sK3),sK1(sK3),sK1(sK3),sK1(sK3),sK1(sK3),sK1(sK3),sK1(sK3))
% 12.01/1.98      | sK3 != k5_xboole_0(k5_xboole_0(sK3,sK3),k3_tarski(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3)))
% 12.01/1.98      | r1_tarski(k6_enumset1(sK1(sK3),sK1(sK3),sK1(sK3),sK1(sK3),sK1(sK3),sK1(sK3),sK1(sK3),sK1(sK3)),k5_xboole_0(k5_xboole_0(sK3,sK3),k3_tarski(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3)))) != iProver_top
% 12.01/1.98      | r1_tarski(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),sK3) = iProver_top ),
% 12.01/1.98      inference(predicate_to_equality,[status(thm)],[c_42831]) ).
% 12.01/1.98  
% 12.01/1.98  cnf(c_3,plain,
% 12.01/1.98      ( r2_xboole_0(X0,X1) | ~ r1_tarski(X0,X1) | X1 = X0 ),
% 12.01/1.98      inference(cnf_transformation,[],[f49]) ).
% 12.01/1.98  
% 12.01/1.98  cnf(c_18,negated_conjecture,
% 12.01/1.98      ( k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) != sK3 ),
% 12.01/1.98      inference(cnf_transformation,[],[f95]) ).
% 12.01/1.98  
% 12.01/1.98  cnf(c_861,plain,
% 12.01/1.98      ( r2_xboole_0(sK3,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))
% 12.01/1.98      | ~ r1_tarski(sK3,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)) ),
% 12.01/1.98      inference(resolution,[status(thm)],[c_3,c_18]) ).
% 12.01/1.98  
% 12.01/1.98  cnf(c_7,plain,
% 12.01/1.98      ( ~ r2_xboole_0(X0,X1) | ~ r1_tarski(X1,X0) ),
% 12.01/1.98      inference(cnf_transformation,[],[f54]) ).
% 12.01/1.98  
% 12.01/1.98  cnf(c_7749,plain,
% 12.01/1.98      ( ~ r1_tarski(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),sK3)
% 12.01/1.98      | ~ r1_tarski(sK3,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)) ),
% 12.01/1.98      inference(resolution,[status(thm)],[c_861,c_7]) ).
% 12.01/1.98  
% 12.01/1.98  cnf(c_7750,plain,
% 12.01/1.98      ( r1_tarski(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),sK3) != iProver_top
% 12.01/1.98      | r1_tarski(sK3,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)) != iProver_top ),
% 12.01/1.98      inference(predicate_to_equality,[status(thm)],[c_7749]) ).
% 12.01/1.98  
% 12.01/1.98  cnf(c_186,plain,
% 12.01/1.98      ( ~ r2_hidden(X0,X1) | r2_hidden(X2,X3) | X2 != X0 | X3 != X1 ),
% 12.01/1.98      theory(equality) ).
% 12.01/1.98  
% 12.01/1.98  cnf(c_719,plain,
% 12.01/1.98      ( r2_hidden(X0,X1)
% 12.01/1.98      | ~ r2_hidden(sK1(sK3),sK3)
% 12.01/1.98      | X0 != sK1(sK3)
% 12.01/1.98      | X1 != sK3 ),
% 12.01/1.98      inference(instantiation,[status(thm)],[c_186]) ).
% 12.01/1.98  
% 12.01/1.98  cnf(c_1538,plain,
% 12.01/1.98      ( r2_hidden(sK1(sK3),X0)
% 12.01/1.98      | ~ r2_hidden(sK1(sK3),sK3)
% 12.01/1.98      | X0 != sK3
% 12.01/1.98      | sK1(sK3) != sK1(sK3) ),
% 12.01/1.98      inference(instantiation,[status(thm)],[c_719]) ).
% 12.01/1.98  
% 12.01/1.98  cnf(c_4841,plain,
% 12.01/1.98      ( r2_hidden(sK1(sK3),k5_xboole_0(k5_xboole_0(sK3,sK3),k3_tarski(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3))))
% 12.01/1.98      | ~ r2_hidden(sK1(sK3),sK3)
% 12.01/1.98      | k5_xboole_0(k5_xboole_0(sK3,sK3),k3_tarski(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3))) != sK3
% 12.01/1.98      | sK1(sK3) != sK1(sK3) ),
% 12.01/1.98      inference(instantiation,[status(thm)],[c_1538]) ).
% 12.01/1.98  
% 12.01/1.98  cnf(c_4855,plain,
% 12.01/1.98      ( k5_xboole_0(k5_xboole_0(sK3,sK3),k3_tarski(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3))) != sK3
% 12.01/1.98      | sK1(sK3) != sK1(sK3)
% 12.01/1.98      | r2_hidden(sK1(sK3),k5_xboole_0(k5_xboole_0(sK3,sK3),k3_tarski(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3)))) = iProver_top
% 12.01/1.98      | r2_hidden(sK1(sK3),sK3) != iProver_top ),
% 12.01/1.98      inference(predicate_to_equality,[status(thm)],[c_4841]) ).
% 12.01/1.98  
% 12.01/1.98  cnf(c_14,plain,
% 12.01/1.98      ( ~ r2_hidden(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)) | X0 = X1 ),
% 12.01/1.98      inference(cnf_transformation,[],[f99]) ).
% 12.01/1.98  
% 12.01/1.98  cnf(c_4283,plain,
% 12.01/1.98      ( ~ r2_hidden(sK1(sK3),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))
% 12.01/1.98      | sK1(sK3) = X0 ),
% 12.01/1.98      inference(instantiation,[status(thm)],[c_14]) ).
% 12.01/1.98  
% 12.01/1.98  cnf(c_4284,plain,
% 12.01/1.98      ( sK1(sK3) = X0
% 12.01/1.98      | r2_hidden(sK1(sK3),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) != iProver_top ),
% 12.01/1.98      inference(predicate_to_equality,[status(thm)],[c_4283]) ).
% 12.01/1.98  
% 12.01/1.98  cnf(c_4286,plain,
% 12.01/1.98      ( sK1(sK3) = sK4
% 12.01/1.98      | r2_hidden(sK1(sK3),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)) != iProver_top ),
% 12.01/1.98      inference(instantiation,[status(thm)],[c_4284]) ).
% 12.01/1.98  
% 12.01/1.98  cnf(c_188,plain,
% 12.01/1.98      ( X0 != X1
% 12.01/1.98      | X2 != X3
% 12.01/1.98      | X4 != X5
% 12.01/1.98      | X6 != X7
% 12.01/1.98      | X8 != X9
% 12.01/1.98      | X10 != X11
% 12.01/1.98      | X12 != X13
% 12.01/1.98      | X14 != X15
% 12.01/1.98      | k6_enumset1(X0,X2,X4,X6,X8,X10,X12,X14) = k6_enumset1(X1,X3,X5,X7,X9,X11,X13,X15) ),
% 12.01/1.98      theory(equality) ).
% 12.01/1.98  
% 12.01/1.98  cnf(c_3336,plain,
% 12.01/1.98      ( X0 != sK1(sK3)
% 12.01/1.98      | X1 != sK1(sK3)
% 12.01/1.98      | X2 != sK1(sK3)
% 12.01/1.98      | X3 != sK1(sK3)
% 12.01/1.98      | X4 != sK1(sK3)
% 12.01/1.98      | X5 != sK1(sK3)
% 12.01/1.98      | X6 != sK1(sK3)
% 12.01/1.98      | X7 != sK1(sK3)
% 12.01/1.98      | k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k6_enumset1(sK1(sK3),sK1(sK3),sK1(sK3),sK1(sK3),sK1(sK3),sK1(sK3),sK1(sK3),sK1(sK3)) ),
% 12.01/1.98      inference(instantiation,[status(thm)],[c_188]) ).
% 12.01/1.98  
% 12.01/1.98  cnf(c_3338,plain,
% 12.01/1.98      ( k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) = k6_enumset1(sK1(sK3),sK1(sK3),sK1(sK3),sK1(sK3),sK1(sK3),sK1(sK3),sK1(sK3),sK1(sK3))
% 12.01/1.98      | sK4 != sK1(sK3) ),
% 12.01/1.98      inference(instantiation,[status(thm)],[c_3336]) ).
% 12.01/1.98  
% 12.01/1.98  cnf(c_2,plain,
% 12.01/1.98      ( ~ r2_hidden(X0,X1) | r2_hidden(X0,X2) | ~ r1_tarski(X1,X2) ),
% 12.01/1.98      inference(cnf_transformation,[],[f46]) ).
% 12.01/1.98  
% 12.01/1.98  cnf(c_717,plain,
% 12.01/1.98      ( r2_hidden(sK1(sK3),X0)
% 12.01/1.98      | ~ r2_hidden(sK1(sK3),sK3)
% 12.01/1.98      | ~ r1_tarski(sK3,X0) ),
% 12.01/1.98      inference(instantiation,[status(thm)],[c_2]) ).
% 12.01/1.98  
% 12.01/1.98  cnf(c_2963,plain,
% 12.01/1.98      ( r2_hidden(sK1(sK3),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))
% 12.01/1.98      | ~ r2_hidden(sK1(sK3),sK3)
% 12.01/1.98      | ~ r1_tarski(sK3,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)) ),
% 12.01/1.98      inference(instantiation,[status(thm)],[c_717]) ).
% 12.01/1.98  
% 12.01/1.98  cnf(c_2964,plain,
% 12.01/1.98      ( r2_hidden(sK1(sK3),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)) = iProver_top
% 12.01/1.98      | r2_hidden(sK1(sK3),sK3) != iProver_top
% 12.01/1.98      | r1_tarski(sK3,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)) != iProver_top ),
% 12.01/1.98      inference(predicate_to_equality,[status(thm)],[c_2963]) ).
% 12.01/1.98  
% 12.01/1.98  cnf(c_1665,plain,
% 12.01/1.98      ( k5_xboole_0(k5_xboole_0(sK3,sK3),k3_tarski(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3))) = sK3 ),
% 12.01/1.98      inference(instantiation,[status(thm)],[c_4]) ).
% 12.01/1.98  
% 12.01/1.98  cnf(c_184,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 12.01/1.98  
% 12.01/1.98  cnf(c_764,plain,
% 12.01/1.98      ( X0 != X1 | sK3 != X1 | sK3 = X0 ),
% 12.01/1.98      inference(instantiation,[status(thm)],[c_184]) ).
% 12.01/1.98  
% 12.01/1.98  cnf(c_931,plain,
% 12.01/1.98      ( X0 != sK3 | sK3 = X0 | sK3 != sK3 ),
% 12.01/1.98      inference(instantiation,[status(thm)],[c_764]) ).
% 12.01/1.98  
% 12.01/1.98  cnf(c_1664,plain,
% 12.01/1.98      ( k5_xboole_0(k5_xboole_0(sK3,sK3),k3_tarski(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3))) != sK3
% 12.01/1.98      | sK3 = k5_xboole_0(k5_xboole_0(sK3,sK3),k3_tarski(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3)))
% 12.01/1.98      | sK3 != sK3 ),
% 12.01/1.98      inference(instantiation,[status(thm)],[c_931]) ).
% 12.01/1.98  
% 12.01/1.98  cnf(c_183,plain,( X0 = X0 ),theory(equality) ).
% 12.01/1.98  
% 12.01/1.98  cnf(c_1539,plain,
% 12.01/1.98      ( sK1(sK3) = sK1(sK3) ),
% 12.01/1.98      inference(instantiation,[status(thm)],[c_183]) ).
% 12.01/1.98  
% 12.01/1.98  cnf(c_1530,plain,
% 12.01/1.98      ( X0 != X1 | X0 = sK1(sK3) | sK1(sK3) != X1 ),
% 12.01/1.98      inference(instantiation,[status(thm)],[c_184]) ).
% 12.01/1.98  
% 12.01/1.98  cnf(c_1531,plain,
% 12.01/1.98      ( sK1(sK3) != sK4 | sK4 = sK1(sK3) | sK4 != sK4 ),
% 12.01/1.98      inference(instantiation,[status(thm)],[c_1530]) ).
% 12.01/1.98  
% 12.01/1.98  cnf(c_932,plain,
% 12.01/1.98      ( sK3 = sK3 ),
% 12.01/1.98      inference(instantiation,[status(thm)],[c_183]) ).
% 12.01/1.98  
% 12.01/1.98  cnf(c_5,plain,
% 12.01/1.98      ( r2_hidden(sK1(X0),X0) | k1_xboole_0 = X0 ),
% 12.01/1.98      inference(cnf_transformation,[],[f51]) ).
% 12.01/1.98  
% 12.01/1.98  cnf(c_640,plain,
% 12.01/1.98      ( r2_hidden(sK1(sK3),sK3) | k1_xboole_0 = sK3 ),
% 12.01/1.98      inference(instantiation,[status(thm)],[c_5]) ).
% 12.01/1.98  
% 12.01/1.98  cnf(c_641,plain,
% 12.01/1.98      ( k1_xboole_0 = sK3 | r2_hidden(sK1(sK3),sK3) = iProver_top ),
% 12.01/1.98      inference(predicate_to_equality,[status(thm)],[c_640]) ).
% 12.01/1.98  
% 12.01/1.98  cnf(c_13,plain,
% 12.01/1.98      ( r2_hidden(X0,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) ),
% 12.01/1.98      inference(cnf_transformation,[],[f98]) ).
% 12.01/1.98  
% 12.01/1.98  cnf(c_32,plain,
% 12.01/1.98      ( r2_hidden(sK4,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)) ),
% 12.01/1.98      inference(instantiation,[status(thm)],[c_13]) ).
% 12.01/1.98  
% 12.01/1.98  cnf(c_29,plain,
% 12.01/1.98      ( ~ r2_hidden(sK4,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))
% 12.01/1.98      | sK4 = sK4 ),
% 12.01/1.98      inference(instantiation,[status(thm)],[c_14]) ).
% 12.01/1.98  
% 12.01/1.98  cnf(c_19,negated_conjecture,
% 12.01/1.98      ( k1_xboole_0 != sK3 ),
% 12.01/1.98      inference(cnf_transformation,[],[f75]) ).
% 12.01/1.98  
% 12.01/1.98  cnf(contradiction,plain,
% 12.01/1.98      ( $false ),
% 12.01/1.98      inference(minisat,
% 12.01/1.98                [status(thm)],
% 12.01/1.98                [c_43651,c_42835,c_42833,c_7750,c_4855,c_4286,c_3338,
% 12.01/1.98                 c_2964,c_1665,c_1664,c_1539,c_1531,c_932,c_641,c_32,
% 12.01/1.98                 c_29,c_19]) ).
% 12.01/1.98  
% 12.01/1.98  
% 12.01/1.98  % SZS output end CNFRefutation for theBenchmark.p
% 12.01/1.98  
% 12.01/1.98  ------                               Statistics
% 12.01/1.98  
% 12.01/1.98  ------ Selected
% 12.01/1.98  
% 12.01/1.98  total_time:                             1.444
% 12.01/1.98  
%------------------------------------------------------------------------------
