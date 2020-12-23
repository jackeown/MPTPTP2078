%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:32:20 EST 2020

% Result     : Theorem 7.59s
% Output     : CNFRefutation 7.59s
% Verified   : 
% Statistics : Number of formulae       :  151 (1555 expanded)
%              Number of clauses        :   60 ( 122 expanded)
%              Number of leaves         :   26 ( 488 expanded)
%              Depth                    :   25
%              Number of atoms          :  298 (2394 expanded)
%              Number of equality atoms :  202 (2219 expanded)
%              Maximal formula depth    :   11 (   3 average)
%              Maximal clause size      :   14 (   2 average)
%              Maximal term depth       :    5 (   2 average)

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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

fof(f35,plain,(
    ? [X0,X1,X2] :
      ( ( k1_xboole_0 != X2
        | k1_tarski(X0) != X1 )
      & ( k1_tarski(X0) != X2
        | k1_xboole_0 != X1 )
      & ( k1_tarski(X0) != X2
        | k1_tarski(X0) != X1 )
      & k2_xboole_0(X1,X2) = k1_tarski(X0) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f43,plain,
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

fof(f44,plain,
    ( ( k1_xboole_0 != sK3
      | k1_tarski(sK1) != sK2 )
    & ( k1_tarski(sK1) != sK3
      | k1_xboole_0 != sK2 )
    & ( k1_tarski(sK1) != sK3
      | k1_tarski(sK1) != sK2 )
    & k2_xboole_0(sK2,sK3) = k1_tarski(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f35,f43])).

fof(f73,plain,(
    k2_xboole_0(sK2,sK3) = k1_tarski(sK1) ),
    inference(cnf_transformation,[],[f44])).

fof(f23,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f72,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f23])).

fof(f82,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f72,f81])).

fof(f13,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f59,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f13])).

fof(f14,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f60,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f14])).

fof(f15,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f61,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f15])).

fof(f16,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f62,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f16])).

fof(f17,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f63,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f17])).

fof(f18,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f64,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f18])).

fof(f19,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f65,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f19])).

fof(f77,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f64,f65])).

fof(f78,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f63,f77])).

fof(f79,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f62,f78])).

fof(f80,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f61,f79])).

fof(f81,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f60,f80])).

fof(f84,plain,(
    ! [X0] : k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f59,f81])).

fof(f99,plain,(
    k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) = k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3)) ),
    inference(definition_unfolding,[],[f73,f82,f84])).

fof(f9,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f55,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f89,plain,(
    ! [X0,X1] : r1_tarski(X0,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) ),
    inference(definition_unfolding,[],[f55,f82])).

fof(f22,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,k1_tarski(X1))
    <=> ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,k1_tarski(X1))
        | ( k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k1_tarski(X1)) ) ) ),
    inference(nnf_transformation,[],[f22])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,k1_tarski(X1))
        | ( k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k1_tarski(X1)) ) ) ),
    inference(flattening,[],[f41])).

fof(f69,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = X0
      | k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_tarski(X1)) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f95,plain,(
    ! [X0,X1] :
      ( k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) = X0
      | k1_xboole_0 = X0
      | ~ r1_tarski(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)) ) ),
    inference(definition_unfolding,[],[f69,f84,f84])).

fof(f21,axiom,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
     => r1_xboole_0(k1_tarski(X0),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f68,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f92,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f68,f84])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    inference(unused_predicate_definition_removal,[],[f4])).

fof(f32,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f28])).

fof(f50,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f12,axiom,(
    ! [X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f58,plain,(
    ! [X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f12])).

fof(f83,plain,(
    ! [X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) = k3_xboole_0(X0,X1) ),
    inference(definition_unfolding,[],[f58,f82])).

fof(f85,plain,(
    ! [X0,X1] :
      ( k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(definition_unfolding,[],[f50,f83])).

fof(f10,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f56,plain,(
    ! [X2,X0,X1] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f10])).

fof(f1,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f20,axiom,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
    <=> r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(k1_tarski(X0),X1)
        | ~ r2_hidden(X0,X1) )
      & ( r2_hidden(X0,X1)
        | ~ r1_tarski(k1_tarski(X0),X1) ) ) ),
    inference(nnf_transformation,[],[f20])).

fof(f67,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f90,plain,(
    ! [X0,X1] :
      ( r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f67,f84])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f54,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f88,plain,(
    ! [X0,X1] :
      ( k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f54,f82])).

fof(f74,plain,
    ( k1_tarski(sK1) != sK3
    | k1_tarski(sK1) != sK2 ),
    inference(cnf_transformation,[],[f44])).

fof(f98,plain,
    ( k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) != sK3
    | k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) != sK2 ),
    inference(definition_unfolding,[],[f74,f84,f84])).

fof(f75,plain,
    ( k1_tarski(sK1) != sK3
    | k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f44])).

fof(f97,plain,
    ( k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) != sK3
    | k1_xboole_0 != sK2 ),
    inference(definition_unfolding,[],[f75,f84])).

fof(f11,axiom,(
    ! [X0] : k5_xboole_0(X0,X0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f57,plain,(
    ! [X0] : k5_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f11])).

fof(f7,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f7])).

fof(f53,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f27])).

fof(f87,plain,(
    ! [X0] : k5_xboole_0(k5_xboole_0(X0,X0),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))) = X0 ),
    inference(definition_unfolding,[],[f53,f83])).

fof(f6,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f6])).

fof(f52,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f26])).

fof(f86,plain,(
    ! [X0] : k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) = X0 ),
    inference(definition_unfolding,[],[f52,f82])).

fof(f76,plain,
    ( k1_xboole_0 != sK3
    | k1_tarski(sK1) != sK2 ),
    inference(cnf_transformation,[],[f44])).

fof(f96,plain,
    ( k1_xboole_0 != sK3
    | k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) != sK2 ),
    inference(definition_unfolding,[],[f76,f84])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f31])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f36])).

fof(f38,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK0(X0,X1),X1)
          & r2_hidden(sK0(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f37,f38])).

fof(f48,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK0(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => ! [X1] : ~ r2_hidden(X1,X0) ) ),
    inference(unused_predicate_definition_removal,[],[f2])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] : ~ r2_hidden(X1,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f29])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f5,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f51,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f5])).

cnf(c_22,negated_conjecture,
    ( k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) = k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3)) ),
    inference(cnf_transformation,[],[f99])).

cnf(c_10,plain,
    ( r1_tarski(X0,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_1238,plain,
    ( r1_tarski(X0,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_8328,plain,
    ( r1_tarski(sK2,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_22,c_1238])).

cnf(c_18,plain,
    ( ~ r1_tarski(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))
    | k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) = X0
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f95])).

cnf(c_1232,plain,
    ( k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) = X1
    | k1_xboole_0 = X1
    | r1_tarski(X1,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_8368,plain,
    ( k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) = sK2
    | sK2 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_8328,c_1232])).

cnf(c_15,plain,
    ( r1_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1)
    | r2_hidden(X0,X1) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_1235,plain,
    ( r1_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1) = iProver_top
    | r2_hidden(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_8396,plain,
    ( sK2 = k1_xboole_0
    | r1_xboole_0(sK2,X0) = iProver_top
    | r2_hidden(sK1,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_8368,c_1235])).

cnf(c_5,plain,
    ( ~ r1_xboole_0(X0,X1)
    | k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f85])).

cnf(c_11,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_0,plain,
    ( k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_879,plain,
    ( ~ r1_xboole_0(X0,X1)
    | k5_xboole_0(X0,k5_xboole_0(X1,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) = k1_xboole_0 ),
    inference(theory_normalisation,[status(thm)],[c_5,c_11,c_0])).

cnf(c_1240,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) = k1_xboole_0
    | r1_xboole_0(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_879])).

cnf(c_13720,plain,
    ( k5_xboole_0(sK2,k5_xboole_0(X0,k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,X0)))) = k1_xboole_0
    | sK2 = k1_xboole_0
    | r2_hidden(sK1,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_8396,c_1240])).

cnf(c_13,plain,
    ( r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1)
    | ~ r2_hidden(X0,X1) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_1237,plain,
    ( r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1) = iProver_top
    | r2_hidden(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_8826,plain,
    ( sK2 = k1_xboole_0
    | r1_tarski(sK2,X0) = iProver_top
    | r2_hidden(sK1,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_8368,c_1237])).

cnf(c_18167,plain,
    ( k5_xboole_0(sK2,k5_xboole_0(X0,k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,X0)))) = k1_xboole_0
    | sK2 = k1_xboole_0
    | r1_tarski(sK2,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_13720,c_8826])).

cnf(c_9,plain,
    ( ~ r1_tarski(X0,X1)
    | k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = X1 ),
    inference(cnf_transformation,[],[f88])).

cnf(c_1239,plain,
    ( k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = X1
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_18220,plain,
    ( k5_xboole_0(sK2,k5_xboole_0(X0,k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,X0)))) = k1_xboole_0
    | k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,X0)) = X0
    | sK2 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_18167,c_1239])).

cnf(c_18251,plain,
    ( k5_xboole_0(sK2,k5_xboole_0(sK3,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))) = k1_xboole_0
    | k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3)) = sK3
    | sK2 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_22,c_18220])).

cnf(c_18480,plain,
    ( k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) = sK3
    | k5_xboole_0(sK2,k5_xboole_0(sK3,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))) = k1_xboole_0
    | sK2 = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_18251,c_22])).

cnf(c_21,negated_conjecture,
    ( k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) != sK2
    | k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) != sK3 ),
    inference(cnf_transformation,[],[f98])).

cnf(c_8400,plain,
    ( k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) != sK3
    | sK2 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_8368,c_21])).

cnf(c_20,negated_conjecture,
    ( k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) != sK3
    | k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f97])).

cnf(c_1267,plain,
    ( ~ r1_tarski(sK2,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))
    | k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) = sK2
    | k1_xboole_0 = sK2 ),
    inference(instantiation,[status(thm)],[c_18])).

cnf(c_8334,plain,
    ( r1_tarski(sK2,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_8328])).

cnf(c_8534,plain,
    ( k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) != sK3 ),
    inference(global_propositional_subsumption,[status(thm)],[c_8400,c_21,c_20,c_1267,c_8334])).

cnf(c_18513,plain,
    ( k5_xboole_0(sK2,k5_xboole_0(sK3,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))) = k1_xboole_0
    | sK2 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_18480,c_21,c_20,c_1267,c_8334])).

cnf(c_18518,plain,
    ( k5_xboole_0(sK2,k5_xboole_0(sK3,sK2)) = k1_xboole_0
    | sK2 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_8368,c_18513])).

cnf(c_12,plain,
    ( k5_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f57])).

cnf(c_1451,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X0,X1))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_11,c_12])).

cnf(c_1449,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X0,X1)) = k5_xboole_0(k1_xboole_0,X1) ),
    inference(superposition,[status(thm)],[c_12,c_11])).

cnf(c_8,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X0),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))) = X0 ),
    inference(cnf_transformation,[],[f87])).

cnf(c_878,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X0,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)))) = X0 ),
    inference(theory_normalisation,[status(thm)],[c_8,c_11,c_0])).

cnf(c_7,plain,
    ( k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) = X0 ),
    inference(cnf_transformation,[],[f86])).

cnf(c_1244,plain,
    ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(light_normalisation,[status(thm)],[c_878,c_7,c_12])).

cnf(c_1409,plain,
    ( k5_xboole_0(k1_xboole_0,X0) = X0 ),
    inference(superposition,[status(thm)],[c_1244,c_0])).

cnf(c_1455,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1 ),
    inference(demodulation,[status(thm)],[c_1449,c_1409])).

cnf(c_1556,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,X0)) = k5_xboole_0(X1,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_1451,c_1455])).

cnf(c_1565,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,X0)) = X1 ),
    inference(demodulation,[status(thm)],[c_1556,c_1244])).

cnf(c_18767,plain,
    ( sK2 = k1_xboole_0
    | sK3 = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_18518,c_1565])).

cnf(c_19,negated_conjecture,
    ( k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) != sK2
    | k1_xboole_0 != sK3 ),
    inference(cnf_transformation,[],[f96])).

cnf(c_8402,plain,
    ( sK2 = k1_xboole_0
    | sK3 != k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_8368,c_19])).

cnf(c_18822,plain,
    ( sK2 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_18767,c_8402])).

cnf(c_18844,plain,
    ( k3_tarski(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,sK3)) = k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) ),
    inference(demodulation,[status(thm)],[c_18822,c_22])).

cnf(c_3,plain,
    ( r1_tarski(X0,X1)
    | r2_hidden(sK0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_1242,plain,
    ( r1_tarski(X0,X1) = iProver_top
    | r2_hidden(sK0(X0,X1),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_1,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_6,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_220,plain,
    ( ~ r2_hidden(X0,X1)
    | k1_xboole_0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_1,c_6])).

cnf(c_221,plain,
    ( ~ r2_hidden(X0,k1_xboole_0) ),
    inference(unflattening,[status(thm)],[c_220])).

cnf(c_1231,plain,
    ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_221])).

cnf(c_3511,plain,
    ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1242,c_1231])).

cnf(c_10852,plain,
    ( k3_tarski(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,X0)) = X0 ),
    inference(superposition,[status(thm)],[c_3511,c_1239])).

cnf(c_18846,plain,
    ( k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) = sK3 ),
    inference(demodulation,[status(thm)],[c_18844,c_10852])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_18846,c_8534])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n008.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 16:32:30 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 7.59/1.49  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.59/1.49  
% 7.59/1.49  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.59/1.49  
% 7.59/1.49  ------  iProver source info
% 7.59/1.49  
% 7.59/1.49  git: date: 2020-06-30 10:37:57 +0100
% 7.59/1.49  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.59/1.49  git: non_committed_changes: false
% 7.59/1.49  git: last_make_outside_of_git: false
% 7.59/1.49  
% 7.59/1.49  ------ 
% 7.59/1.49  
% 7.59/1.49  ------ Input Options
% 7.59/1.49  
% 7.59/1.49  --out_options                           all
% 7.59/1.49  --tptp_safe_out                         true
% 7.59/1.49  --problem_path                          ""
% 7.59/1.49  --include_path                          ""
% 7.59/1.49  --clausifier                            res/vclausify_rel
% 7.59/1.49  --clausifier_options                    ""
% 7.59/1.49  --stdin                                 false
% 7.59/1.49  --stats_out                             all
% 7.59/1.49  
% 7.59/1.49  ------ General Options
% 7.59/1.49  
% 7.59/1.49  --fof                                   false
% 7.59/1.49  --time_out_real                         305.
% 7.59/1.49  --time_out_virtual                      -1.
% 7.59/1.49  --symbol_type_check                     false
% 7.59/1.49  --clausify_out                          false
% 7.59/1.49  --sig_cnt_out                           false
% 7.59/1.49  --trig_cnt_out                          false
% 7.59/1.49  --trig_cnt_out_tolerance                1.
% 7.59/1.49  --trig_cnt_out_sk_spl                   false
% 7.59/1.49  --abstr_cl_out                          false
% 7.59/1.49  
% 7.59/1.49  ------ Global Options
% 7.59/1.49  
% 7.59/1.49  --schedule                              default
% 7.59/1.49  --add_important_lit                     false
% 7.59/1.49  --prop_solver_per_cl                    1000
% 7.59/1.49  --min_unsat_core                        false
% 7.59/1.49  --soft_assumptions                      false
% 7.59/1.49  --soft_lemma_size                       3
% 7.59/1.49  --prop_impl_unit_size                   0
% 7.59/1.49  --prop_impl_unit                        []
% 7.59/1.49  --share_sel_clauses                     true
% 7.59/1.49  --reset_solvers                         false
% 7.59/1.49  --bc_imp_inh                            [conj_cone]
% 7.59/1.49  --conj_cone_tolerance                   3.
% 7.59/1.49  --extra_neg_conj                        none
% 7.59/1.49  --large_theory_mode                     true
% 7.59/1.49  --prolific_symb_bound                   200
% 7.59/1.49  --lt_threshold                          2000
% 7.59/1.49  --clause_weak_htbl                      true
% 7.59/1.49  --gc_record_bc_elim                     false
% 7.59/1.49  
% 7.59/1.49  ------ Preprocessing Options
% 7.59/1.49  
% 7.59/1.49  --preprocessing_flag                    true
% 7.59/1.49  --time_out_prep_mult                    0.1
% 7.59/1.49  --splitting_mode                        input
% 7.59/1.49  --splitting_grd                         true
% 7.59/1.49  --splitting_cvd                         false
% 7.59/1.49  --splitting_cvd_svl                     false
% 7.59/1.49  --splitting_nvd                         32
% 7.59/1.49  --sub_typing                            true
% 7.59/1.49  --prep_gs_sim                           true
% 7.59/1.49  --prep_unflatten                        true
% 7.59/1.49  --prep_res_sim                          true
% 7.59/1.49  --prep_upred                            true
% 7.59/1.49  --prep_sem_filter                       exhaustive
% 7.59/1.49  --prep_sem_filter_out                   false
% 7.59/1.49  --pred_elim                             true
% 7.59/1.49  --res_sim_input                         true
% 7.59/1.49  --eq_ax_congr_red                       true
% 7.59/1.49  --pure_diseq_elim                       true
% 7.59/1.49  --brand_transform                       false
% 7.59/1.49  --non_eq_to_eq                          false
% 7.59/1.49  --prep_def_merge                        true
% 7.59/1.49  --prep_def_merge_prop_impl              false
% 7.59/1.49  --prep_def_merge_mbd                    true
% 7.59/1.49  --prep_def_merge_tr_red                 false
% 7.59/1.49  --prep_def_merge_tr_cl                  false
% 7.59/1.49  --smt_preprocessing                     true
% 7.59/1.49  --smt_ac_axioms                         fast
% 7.59/1.49  --preprocessed_out                      false
% 7.59/1.49  --preprocessed_stats                    false
% 7.59/1.49  
% 7.59/1.49  ------ Abstraction refinement Options
% 7.59/1.49  
% 7.59/1.49  --abstr_ref                             []
% 7.59/1.49  --abstr_ref_prep                        false
% 7.59/1.49  --abstr_ref_until_sat                   false
% 7.59/1.49  --abstr_ref_sig_restrict                funpre
% 7.59/1.49  --abstr_ref_af_restrict_to_split_sk     false
% 7.59/1.49  --abstr_ref_under                       []
% 7.59/1.49  
% 7.59/1.49  ------ SAT Options
% 7.59/1.49  
% 7.59/1.49  --sat_mode                              false
% 7.59/1.49  --sat_fm_restart_options                ""
% 7.59/1.49  --sat_gr_def                            false
% 7.59/1.49  --sat_epr_types                         true
% 7.59/1.49  --sat_non_cyclic_types                  false
% 7.59/1.49  --sat_finite_models                     false
% 7.59/1.49  --sat_fm_lemmas                         false
% 7.59/1.49  --sat_fm_prep                           false
% 7.59/1.49  --sat_fm_uc_incr                        true
% 7.59/1.49  --sat_out_model                         small
% 7.59/1.49  --sat_out_clauses                       false
% 7.59/1.49  
% 7.59/1.49  ------ QBF Options
% 7.59/1.49  
% 7.59/1.49  --qbf_mode                              false
% 7.59/1.49  --qbf_elim_univ                         false
% 7.59/1.49  --qbf_dom_inst                          none
% 7.59/1.49  --qbf_dom_pre_inst                      false
% 7.59/1.49  --qbf_sk_in                             false
% 7.59/1.49  --qbf_pred_elim                         true
% 7.59/1.49  --qbf_split                             512
% 7.59/1.49  
% 7.59/1.49  ------ BMC1 Options
% 7.59/1.49  
% 7.59/1.49  --bmc1_incremental                      false
% 7.59/1.49  --bmc1_axioms                           reachable_all
% 7.59/1.49  --bmc1_min_bound                        0
% 7.59/1.49  --bmc1_max_bound                        -1
% 7.59/1.49  --bmc1_max_bound_default                -1
% 7.59/1.49  --bmc1_symbol_reachability              true
% 7.59/1.49  --bmc1_property_lemmas                  false
% 7.59/1.49  --bmc1_k_induction                      false
% 7.59/1.49  --bmc1_non_equiv_states                 false
% 7.59/1.49  --bmc1_deadlock                         false
% 7.59/1.49  --bmc1_ucm                              false
% 7.59/1.49  --bmc1_add_unsat_core                   none
% 7.59/1.49  --bmc1_unsat_core_children              false
% 7.59/1.49  --bmc1_unsat_core_extrapolate_axioms    false
% 7.59/1.49  --bmc1_out_stat                         full
% 7.59/1.49  --bmc1_ground_init                      false
% 7.59/1.49  --bmc1_pre_inst_next_state              false
% 7.59/1.49  --bmc1_pre_inst_state                   false
% 7.59/1.49  --bmc1_pre_inst_reach_state             false
% 7.59/1.49  --bmc1_out_unsat_core                   false
% 7.59/1.49  --bmc1_aig_witness_out                  false
% 7.59/1.49  --bmc1_verbose                          false
% 7.59/1.49  --bmc1_dump_clauses_tptp                false
% 7.59/1.49  --bmc1_dump_unsat_core_tptp             false
% 7.59/1.49  --bmc1_dump_file                        -
% 7.59/1.49  --bmc1_ucm_expand_uc_limit              128
% 7.59/1.49  --bmc1_ucm_n_expand_iterations          6
% 7.59/1.49  --bmc1_ucm_extend_mode                  1
% 7.59/1.49  --bmc1_ucm_init_mode                    2
% 7.59/1.49  --bmc1_ucm_cone_mode                    none
% 7.59/1.49  --bmc1_ucm_reduced_relation_type        0
% 7.59/1.49  --bmc1_ucm_relax_model                  4
% 7.59/1.49  --bmc1_ucm_full_tr_after_sat            true
% 7.59/1.49  --bmc1_ucm_expand_neg_assumptions       false
% 7.59/1.49  --bmc1_ucm_layered_model                none
% 7.59/1.49  --bmc1_ucm_max_lemma_size               10
% 7.59/1.49  
% 7.59/1.49  ------ AIG Options
% 7.59/1.49  
% 7.59/1.49  --aig_mode                              false
% 7.59/1.49  
% 7.59/1.49  ------ Instantiation Options
% 7.59/1.49  
% 7.59/1.49  --instantiation_flag                    true
% 7.59/1.49  --inst_sos_flag                         true
% 7.59/1.49  --inst_sos_phase                        true
% 7.59/1.49  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.59/1.49  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.59/1.49  --inst_lit_sel_side                     num_symb
% 7.59/1.49  --inst_solver_per_active                1400
% 7.59/1.49  --inst_solver_calls_frac                1.
% 7.59/1.49  --inst_passive_queue_type               priority_queues
% 7.59/1.49  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.59/1.49  --inst_passive_queues_freq              [25;2]
% 7.59/1.49  --inst_dismatching                      true
% 7.59/1.49  --inst_eager_unprocessed_to_passive     true
% 7.59/1.49  --inst_prop_sim_given                   true
% 7.59/1.49  --inst_prop_sim_new                     false
% 7.59/1.49  --inst_subs_new                         false
% 7.59/1.49  --inst_eq_res_simp                      false
% 7.59/1.49  --inst_subs_given                       false
% 7.59/1.49  --inst_orphan_elimination               true
% 7.59/1.49  --inst_learning_loop_flag               true
% 7.59/1.49  --inst_learning_start                   3000
% 7.59/1.49  --inst_learning_factor                  2
% 7.59/1.49  --inst_start_prop_sim_after_learn       3
% 7.59/1.49  --inst_sel_renew                        solver
% 7.59/1.49  --inst_lit_activity_flag                true
% 7.59/1.49  --inst_restr_to_given                   false
% 7.59/1.49  --inst_activity_threshold               500
% 7.59/1.49  --inst_out_proof                        true
% 7.59/1.49  
% 7.59/1.49  ------ Resolution Options
% 7.59/1.49  
% 7.59/1.49  --resolution_flag                       true
% 7.59/1.49  --res_lit_sel                           adaptive
% 7.59/1.49  --res_lit_sel_side                      none
% 7.59/1.49  --res_ordering                          kbo
% 7.59/1.49  --res_to_prop_solver                    active
% 7.59/1.49  --res_prop_simpl_new                    false
% 7.59/1.49  --res_prop_simpl_given                  true
% 7.59/1.49  --res_passive_queue_type                priority_queues
% 7.59/1.49  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.59/1.49  --res_passive_queues_freq               [15;5]
% 7.59/1.49  --res_forward_subs                      full
% 7.59/1.49  --res_backward_subs                     full
% 7.59/1.49  --res_forward_subs_resolution           true
% 7.59/1.49  --res_backward_subs_resolution          true
% 7.59/1.49  --res_orphan_elimination                true
% 7.59/1.49  --res_time_limit                        2.
% 7.59/1.49  --res_out_proof                         true
% 7.59/1.49  
% 7.59/1.49  ------ Superposition Options
% 7.59/1.49  
% 7.59/1.49  --superposition_flag                    true
% 7.59/1.49  --sup_passive_queue_type                priority_queues
% 7.59/1.49  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.59/1.49  --sup_passive_queues_freq               [8;1;4]
% 7.59/1.49  --demod_completeness_check              fast
% 7.59/1.49  --demod_use_ground                      true
% 7.59/1.49  --sup_to_prop_solver                    passive
% 7.59/1.49  --sup_prop_simpl_new                    true
% 7.59/1.49  --sup_prop_simpl_given                  true
% 7.59/1.49  --sup_fun_splitting                     true
% 7.59/1.49  --sup_smt_interval                      50000
% 7.59/1.49  
% 7.59/1.49  ------ Superposition Simplification Setup
% 7.59/1.49  
% 7.59/1.49  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 7.59/1.49  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 7.59/1.49  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 7.59/1.49  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 7.59/1.49  --sup_full_triv                         [TrivRules;PropSubs]
% 7.59/1.49  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 7.59/1.49  --sup_full_bw                           [BwDemod;BwSubsumption]
% 7.59/1.49  --sup_immed_triv                        [TrivRules]
% 7.59/1.49  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.59/1.49  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.59/1.49  --sup_immed_bw_main                     []
% 7.59/1.49  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 7.59/1.49  --sup_input_triv                        [Unflattening;TrivRules]
% 7.59/1.49  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.59/1.49  --sup_input_bw                          []
% 7.59/1.49  
% 7.59/1.49  ------ Combination Options
% 7.59/1.49  
% 7.59/1.49  --comb_res_mult                         3
% 7.59/1.49  --comb_sup_mult                         2
% 7.59/1.49  --comb_inst_mult                        10
% 7.59/1.49  
% 7.59/1.49  ------ Debug Options
% 7.59/1.49  
% 7.59/1.49  --dbg_backtrace                         false
% 7.59/1.49  --dbg_dump_prop_clauses                 false
% 7.59/1.49  --dbg_dump_prop_clauses_file            -
% 7.59/1.49  --dbg_out_stat                          false
% 7.59/1.49  ------ Parsing...
% 7.59/1.49  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.59/1.49  
% 7.59/1.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 7.59/1.49  
% 7.59/1.49  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.59/1.49  
% 7.59/1.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.59/1.49  ------ Proving...
% 7.59/1.49  ------ Problem Properties 
% 7.59/1.49  
% 7.59/1.49  
% 7.59/1.49  clauses                                 22
% 7.59/1.49  conjectures                             4
% 7.59/1.49  EPR                                     2
% 7.59/1.49  Horn                                    19
% 7.59/1.49  unary                                   10
% 7.59/1.49  binary                                  10
% 7.59/1.49  lits                                    36
% 7.59/1.49  lits eq                                 16
% 7.59/1.49  fd_pure                                 0
% 7.59/1.49  fd_pseudo                               0
% 7.59/1.49  fd_cond                                 0
% 7.59/1.49  fd_pseudo_cond                          1
% 7.59/1.49  AC symbols                              1
% 7.59/1.49  
% 7.59/1.49  ------ Schedule dynamic 5 is on 
% 7.59/1.49  
% 7.59/1.49  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 7.59/1.49  
% 7.59/1.49  
% 7.59/1.49  ------ 
% 7.59/1.49  Current options:
% 7.59/1.49  ------ 
% 7.59/1.49  
% 7.59/1.49  ------ Input Options
% 7.59/1.49  
% 7.59/1.49  --out_options                           all
% 7.59/1.49  --tptp_safe_out                         true
% 7.59/1.49  --problem_path                          ""
% 7.59/1.49  --include_path                          ""
% 7.59/1.49  --clausifier                            res/vclausify_rel
% 7.59/1.49  --clausifier_options                    ""
% 7.59/1.49  --stdin                                 false
% 7.59/1.49  --stats_out                             all
% 7.59/1.49  
% 7.59/1.49  ------ General Options
% 7.59/1.49  
% 7.59/1.49  --fof                                   false
% 7.59/1.49  --time_out_real                         305.
% 7.59/1.49  --time_out_virtual                      -1.
% 7.59/1.49  --symbol_type_check                     false
% 7.59/1.49  --clausify_out                          false
% 7.59/1.49  --sig_cnt_out                           false
% 7.59/1.49  --trig_cnt_out                          false
% 7.59/1.49  --trig_cnt_out_tolerance                1.
% 7.59/1.49  --trig_cnt_out_sk_spl                   false
% 7.59/1.49  --abstr_cl_out                          false
% 7.59/1.49  
% 7.59/1.49  ------ Global Options
% 7.59/1.49  
% 7.59/1.49  --schedule                              default
% 7.59/1.49  --add_important_lit                     false
% 7.59/1.49  --prop_solver_per_cl                    1000
% 7.59/1.49  --min_unsat_core                        false
% 7.59/1.49  --soft_assumptions                      false
% 7.59/1.49  --soft_lemma_size                       3
% 7.59/1.49  --prop_impl_unit_size                   0
% 7.59/1.49  --prop_impl_unit                        []
% 7.59/1.49  --share_sel_clauses                     true
% 7.59/1.49  --reset_solvers                         false
% 7.59/1.49  --bc_imp_inh                            [conj_cone]
% 7.59/1.49  --conj_cone_tolerance                   3.
% 7.59/1.49  --extra_neg_conj                        none
% 7.59/1.49  --large_theory_mode                     true
% 7.59/1.49  --prolific_symb_bound                   200
% 7.59/1.49  --lt_threshold                          2000
% 7.59/1.49  --clause_weak_htbl                      true
% 7.59/1.49  --gc_record_bc_elim                     false
% 7.59/1.49  
% 7.59/1.49  ------ Preprocessing Options
% 7.59/1.49  
% 7.59/1.49  --preprocessing_flag                    true
% 7.59/1.49  --time_out_prep_mult                    0.1
% 7.59/1.49  --splitting_mode                        input
% 7.59/1.49  --splitting_grd                         true
% 7.59/1.49  --splitting_cvd                         false
% 7.59/1.49  --splitting_cvd_svl                     false
% 7.59/1.49  --splitting_nvd                         32
% 7.59/1.49  --sub_typing                            true
% 7.59/1.49  --prep_gs_sim                           true
% 7.59/1.49  --prep_unflatten                        true
% 7.59/1.49  --prep_res_sim                          true
% 7.59/1.49  --prep_upred                            true
% 7.59/1.49  --prep_sem_filter                       exhaustive
% 7.59/1.49  --prep_sem_filter_out                   false
% 7.59/1.49  --pred_elim                             true
% 7.59/1.49  --res_sim_input                         true
% 7.59/1.49  --eq_ax_congr_red                       true
% 7.59/1.49  --pure_diseq_elim                       true
% 7.59/1.49  --brand_transform                       false
% 7.59/1.49  --non_eq_to_eq                          false
% 7.59/1.49  --prep_def_merge                        true
% 7.59/1.49  --prep_def_merge_prop_impl              false
% 7.59/1.49  --prep_def_merge_mbd                    true
% 7.59/1.49  --prep_def_merge_tr_red                 false
% 7.59/1.49  --prep_def_merge_tr_cl                  false
% 7.59/1.49  --smt_preprocessing                     true
% 7.59/1.49  --smt_ac_axioms                         fast
% 7.59/1.49  --preprocessed_out                      false
% 7.59/1.49  --preprocessed_stats                    false
% 7.59/1.49  
% 7.59/1.49  ------ Abstraction refinement Options
% 7.59/1.49  
% 7.59/1.49  --abstr_ref                             []
% 7.59/1.49  --abstr_ref_prep                        false
% 7.59/1.49  --abstr_ref_until_sat                   false
% 7.59/1.49  --abstr_ref_sig_restrict                funpre
% 7.59/1.49  --abstr_ref_af_restrict_to_split_sk     false
% 7.59/1.49  --abstr_ref_under                       []
% 7.59/1.49  
% 7.59/1.49  ------ SAT Options
% 7.59/1.49  
% 7.59/1.49  --sat_mode                              false
% 7.59/1.49  --sat_fm_restart_options                ""
% 7.59/1.49  --sat_gr_def                            false
% 7.59/1.49  --sat_epr_types                         true
% 7.59/1.49  --sat_non_cyclic_types                  false
% 7.59/1.49  --sat_finite_models                     false
% 7.59/1.49  --sat_fm_lemmas                         false
% 7.59/1.49  --sat_fm_prep                           false
% 7.59/1.49  --sat_fm_uc_incr                        true
% 7.59/1.49  --sat_out_model                         small
% 7.59/1.49  --sat_out_clauses                       false
% 7.59/1.49  
% 7.59/1.49  ------ QBF Options
% 7.59/1.49  
% 7.59/1.49  --qbf_mode                              false
% 7.59/1.49  --qbf_elim_univ                         false
% 7.59/1.49  --qbf_dom_inst                          none
% 7.59/1.49  --qbf_dom_pre_inst                      false
% 7.59/1.49  --qbf_sk_in                             false
% 7.59/1.49  --qbf_pred_elim                         true
% 7.59/1.49  --qbf_split                             512
% 7.59/1.49  
% 7.59/1.49  ------ BMC1 Options
% 7.59/1.49  
% 7.59/1.49  --bmc1_incremental                      false
% 7.59/1.49  --bmc1_axioms                           reachable_all
% 7.59/1.49  --bmc1_min_bound                        0
% 7.59/1.49  --bmc1_max_bound                        -1
% 7.59/1.49  --bmc1_max_bound_default                -1
% 7.59/1.49  --bmc1_symbol_reachability              true
% 7.59/1.49  --bmc1_property_lemmas                  false
% 7.59/1.49  --bmc1_k_induction                      false
% 7.59/1.49  --bmc1_non_equiv_states                 false
% 7.59/1.49  --bmc1_deadlock                         false
% 7.59/1.49  --bmc1_ucm                              false
% 7.59/1.49  --bmc1_add_unsat_core                   none
% 7.59/1.49  --bmc1_unsat_core_children              false
% 7.59/1.49  --bmc1_unsat_core_extrapolate_axioms    false
% 7.59/1.49  --bmc1_out_stat                         full
% 7.59/1.49  --bmc1_ground_init                      false
% 7.59/1.49  --bmc1_pre_inst_next_state              false
% 7.59/1.49  --bmc1_pre_inst_state                   false
% 7.59/1.49  --bmc1_pre_inst_reach_state             false
% 7.59/1.49  --bmc1_out_unsat_core                   false
% 7.59/1.49  --bmc1_aig_witness_out                  false
% 7.59/1.49  --bmc1_verbose                          false
% 7.59/1.49  --bmc1_dump_clauses_tptp                false
% 7.59/1.49  --bmc1_dump_unsat_core_tptp             false
% 7.59/1.49  --bmc1_dump_file                        -
% 7.59/1.49  --bmc1_ucm_expand_uc_limit              128
% 7.59/1.49  --bmc1_ucm_n_expand_iterations          6
% 7.59/1.49  --bmc1_ucm_extend_mode                  1
% 7.59/1.49  --bmc1_ucm_init_mode                    2
% 7.59/1.49  --bmc1_ucm_cone_mode                    none
% 7.59/1.49  --bmc1_ucm_reduced_relation_type        0
% 7.59/1.49  --bmc1_ucm_relax_model                  4
% 7.59/1.49  --bmc1_ucm_full_tr_after_sat            true
% 7.59/1.49  --bmc1_ucm_expand_neg_assumptions       false
% 7.59/1.49  --bmc1_ucm_layered_model                none
% 7.59/1.49  --bmc1_ucm_max_lemma_size               10
% 7.59/1.49  
% 7.59/1.49  ------ AIG Options
% 7.59/1.49  
% 7.59/1.49  --aig_mode                              false
% 7.59/1.49  
% 7.59/1.49  ------ Instantiation Options
% 7.59/1.49  
% 7.59/1.49  --instantiation_flag                    true
% 7.59/1.49  --inst_sos_flag                         true
% 7.59/1.49  --inst_sos_phase                        true
% 7.59/1.49  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.59/1.49  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.59/1.49  --inst_lit_sel_side                     none
% 7.59/1.49  --inst_solver_per_active                1400
% 7.59/1.49  --inst_solver_calls_frac                1.
% 7.59/1.49  --inst_passive_queue_type               priority_queues
% 7.59/1.49  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.59/1.49  --inst_passive_queues_freq              [25;2]
% 7.59/1.49  --inst_dismatching                      true
% 7.59/1.49  --inst_eager_unprocessed_to_passive     true
% 7.59/1.49  --inst_prop_sim_given                   true
% 7.59/1.49  --inst_prop_sim_new                     false
% 7.59/1.49  --inst_subs_new                         false
% 7.59/1.49  --inst_eq_res_simp                      false
% 7.59/1.49  --inst_subs_given                       false
% 7.59/1.49  --inst_orphan_elimination               true
% 7.59/1.49  --inst_learning_loop_flag               true
% 7.59/1.49  --inst_learning_start                   3000
% 7.59/1.49  --inst_learning_factor                  2
% 7.59/1.49  --inst_start_prop_sim_after_learn       3
% 7.59/1.49  --inst_sel_renew                        solver
% 7.59/1.49  --inst_lit_activity_flag                true
% 7.59/1.49  --inst_restr_to_given                   false
% 7.59/1.49  --inst_activity_threshold               500
% 7.59/1.49  --inst_out_proof                        true
% 7.59/1.49  
% 7.59/1.49  ------ Resolution Options
% 7.59/1.49  
% 7.59/1.49  --resolution_flag                       false
% 7.59/1.49  --res_lit_sel                           adaptive
% 7.59/1.49  --res_lit_sel_side                      none
% 7.59/1.49  --res_ordering                          kbo
% 7.59/1.49  --res_to_prop_solver                    active
% 7.59/1.49  --res_prop_simpl_new                    false
% 7.59/1.49  --res_prop_simpl_given                  true
% 7.59/1.49  --res_passive_queue_type                priority_queues
% 7.59/1.49  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.59/1.49  --res_passive_queues_freq               [15;5]
% 7.59/1.49  --res_forward_subs                      full
% 7.59/1.49  --res_backward_subs                     full
% 7.59/1.49  --res_forward_subs_resolution           true
% 7.59/1.49  --res_backward_subs_resolution          true
% 7.59/1.49  --res_orphan_elimination                true
% 7.59/1.49  --res_time_limit                        2.
% 7.59/1.49  --res_out_proof                         true
% 7.59/1.49  
% 7.59/1.49  ------ Superposition Options
% 7.59/1.49  
% 7.59/1.49  --superposition_flag                    true
% 7.59/1.49  --sup_passive_queue_type                priority_queues
% 7.59/1.49  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.59/1.49  --sup_passive_queues_freq               [8;1;4]
% 7.59/1.49  --demod_completeness_check              fast
% 7.59/1.49  --demod_use_ground                      true
% 7.59/1.49  --sup_to_prop_solver                    passive
% 7.59/1.49  --sup_prop_simpl_new                    true
% 7.59/1.49  --sup_prop_simpl_given                  true
% 7.59/1.49  --sup_fun_splitting                     true
% 7.59/1.49  --sup_smt_interval                      50000
% 7.59/1.49  
% 7.59/1.49  ------ Superposition Simplification Setup
% 7.59/1.49  
% 7.59/1.49  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 7.59/1.49  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 7.59/1.49  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 7.59/1.49  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 7.59/1.49  --sup_full_triv                         [TrivRules;PropSubs]
% 7.59/1.49  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 7.59/1.49  --sup_full_bw                           [BwDemod;BwSubsumption]
% 7.59/1.49  --sup_immed_triv                        [TrivRules]
% 7.59/1.49  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.59/1.49  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.59/1.49  --sup_immed_bw_main                     []
% 7.59/1.49  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 7.59/1.49  --sup_input_triv                        [Unflattening;TrivRules]
% 7.59/1.49  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.59/1.49  --sup_input_bw                          []
% 7.59/1.49  
% 7.59/1.49  ------ Combination Options
% 7.59/1.49  
% 7.59/1.49  --comb_res_mult                         3
% 7.59/1.49  --comb_sup_mult                         2
% 7.59/1.49  --comb_inst_mult                        10
% 7.59/1.49  
% 7.59/1.49  ------ Debug Options
% 7.59/1.49  
% 7.59/1.49  --dbg_backtrace                         false
% 7.59/1.49  --dbg_dump_prop_clauses                 false
% 7.59/1.49  --dbg_dump_prop_clauses_file            -
% 7.59/1.49  --dbg_out_stat                          false
% 7.59/1.49  
% 7.59/1.49  
% 7.59/1.49  
% 7.59/1.49  
% 7.59/1.49  ------ Proving...
% 7.59/1.49  
% 7.59/1.49  
% 7.59/1.49  % SZS status Theorem for theBenchmark.p
% 7.59/1.49  
% 7.59/1.49  % SZS output start CNFRefutation for theBenchmark.p
% 7.59/1.49  
% 7.59/1.49  fof(f24,conjecture,(
% 7.59/1.49    ! [X0,X1,X2] : ~(~(k1_xboole_0 = X2 & k1_tarski(X0) = X1) & ~(k1_tarski(X0) = X2 & k1_xboole_0 = X1) & ~(k1_tarski(X0) = X2 & k1_tarski(X0) = X1) & k2_xboole_0(X1,X2) = k1_tarski(X0))),
% 7.59/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.59/1.49  
% 7.59/1.49  fof(f25,negated_conjecture,(
% 7.59/1.49    ~! [X0,X1,X2] : ~(~(k1_xboole_0 = X2 & k1_tarski(X0) = X1) & ~(k1_tarski(X0) = X2 & k1_xboole_0 = X1) & ~(k1_tarski(X0) = X2 & k1_tarski(X0) = X1) & k2_xboole_0(X1,X2) = k1_tarski(X0))),
% 7.59/1.49    inference(negated_conjecture,[],[f24])).
% 7.59/1.49  
% 7.59/1.49  fof(f35,plain,(
% 7.59/1.49    ? [X0,X1,X2] : ((k1_xboole_0 != X2 | k1_tarski(X0) != X1) & (k1_tarski(X0) != X2 | k1_xboole_0 != X1) & (k1_tarski(X0) != X2 | k1_tarski(X0) != X1) & k2_xboole_0(X1,X2) = k1_tarski(X0))),
% 7.59/1.49    inference(ennf_transformation,[],[f25])).
% 7.59/1.49  
% 7.59/1.49  fof(f43,plain,(
% 7.59/1.49    ? [X0,X1,X2] : ((k1_xboole_0 != X2 | k1_tarski(X0) != X1) & (k1_tarski(X0) != X2 | k1_xboole_0 != X1) & (k1_tarski(X0) != X2 | k1_tarski(X0) != X1) & k2_xboole_0(X1,X2) = k1_tarski(X0)) => ((k1_xboole_0 != sK3 | k1_tarski(sK1) != sK2) & (k1_tarski(sK1) != sK3 | k1_xboole_0 != sK2) & (k1_tarski(sK1) != sK3 | k1_tarski(sK1) != sK2) & k2_xboole_0(sK2,sK3) = k1_tarski(sK1))),
% 7.59/1.49    introduced(choice_axiom,[])).
% 7.59/1.49  
% 7.59/1.49  fof(f44,plain,(
% 7.59/1.49    (k1_xboole_0 != sK3 | k1_tarski(sK1) != sK2) & (k1_tarski(sK1) != sK3 | k1_xboole_0 != sK2) & (k1_tarski(sK1) != sK3 | k1_tarski(sK1) != sK2) & k2_xboole_0(sK2,sK3) = k1_tarski(sK1)),
% 7.59/1.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f35,f43])).
% 7.59/1.49  
% 7.59/1.49  fof(f73,plain,(
% 7.59/1.49    k2_xboole_0(sK2,sK3) = k1_tarski(sK1)),
% 7.59/1.49    inference(cnf_transformation,[],[f44])).
% 7.59/1.49  
% 7.59/1.49  fof(f23,axiom,(
% 7.59/1.49    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 7.59/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.59/1.49  
% 7.59/1.49  fof(f72,plain,(
% 7.59/1.49    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 7.59/1.49    inference(cnf_transformation,[],[f23])).
% 7.59/1.49  
% 7.59/1.49  fof(f82,plain,(
% 7.59/1.49    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) )),
% 7.59/1.49    inference(definition_unfolding,[],[f72,f81])).
% 7.59/1.49  
% 7.59/1.49  fof(f13,axiom,(
% 7.59/1.49    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 7.59/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.59/1.49  
% 7.59/1.49  fof(f59,plain,(
% 7.59/1.49    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 7.59/1.49    inference(cnf_transformation,[],[f13])).
% 7.59/1.49  
% 7.59/1.49  fof(f14,axiom,(
% 7.59/1.49    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 7.59/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.59/1.49  
% 7.59/1.49  fof(f60,plain,(
% 7.59/1.49    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 7.59/1.49    inference(cnf_transformation,[],[f14])).
% 7.59/1.49  
% 7.59/1.49  fof(f15,axiom,(
% 7.59/1.49    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 7.59/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.59/1.49  
% 7.59/1.49  fof(f61,plain,(
% 7.59/1.49    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 7.59/1.49    inference(cnf_transformation,[],[f15])).
% 7.59/1.49  
% 7.59/1.49  fof(f16,axiom,(
% 7.59/1.49    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 7.59/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.59/1.49  
% 7.59/1.49  fof(f62,plain,(
% 7.59/1.49    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 7.59/1.49    inference(cnf_transformation,[],[f16])).
% 7.59/1.49  
% 7.59/1.49  fof(f17,axiom,(
% 7.59/1.49    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)),
% 7.59/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.59/1.49  
% 7.59/1.49  fof(f63,plain,(
% 7.59/1.49    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)) )),
% 7.59/1.49    inference(cnf_transformation,[],[f17])).
% 7.59/1.49  
% 7.59/1.49  fof(f18,axiom,(
% 7.59/1.49    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)),
% 7.59/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.59/1.49  
% 7.59/1.49  fof(f64,plain,(
% 7.59/1.49    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)) )),
% 7.59/1.49    inference(cnf_transformation,[],[f18])).
% 7.59/1.49  
% 7.59/1.49  fof(f19,axiom,(
% 7.59/1.49    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)),
% 7.59/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.59/1.49  
% 7.59/1.49  fof(f65,plain,(
% 7.59/1.49    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)) )),
% 7.59/1.49    inference(cnf_transformation,[],[f19])).
% 7.59/1.49  
% 7.59/1.49  fof(f77,plain,(
% 7.59/1.49    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 7.59/1.49    inference(definition_unfolding,[],[f64,f65])).
% 7.59/1.49  
% 7.59/1.49  fof(f78,plain,(
% 7.59/1.49    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 7.59/1.49    inference(definition_unfolding,[],[f63,f77])).
% 7.59/1.49  
% 7.59/1.49  fof(f79,plain,(
% 7.59/1.49    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 7.59/1.49    inference(definition_unfolding,[],[f62,f78])).
% 7.59/1.49  
% 7.59/1.49  fof(f80,plain,(
% 7.59/1.49    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 7.59/1.49    inference(definition_unfolding,[],[f61,f79])).
% 7.59/1.49  
% 7.59/1.49  fof(f81,plain,(
% 7.59/1.49    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 7.59/1.49    inference(definition_unfolding,[],[f60,f80])).
% 7.59/1.49  
% 7.59/1.49  fof(f84,plain,(
% 7.59/1.49    ( ! [X0] : (k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) )),
% 7.59/1.49    inference(definition_unfolding,[],[f59,f81])).
% 7.59/1.49  
% 7.59/1.49  fof(f99,plain,(
% 7.59/1.49    k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) = k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3))),
% 7.59/1.49    inference(definition_unfolding,[],[f73,f82,f84])).
% 7.59/1.49  
% 7.59/1.49  fof(f9,axiom,(
% 7.59/1.49    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 7.59/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.59/1.49  
% 7.59/1.49  fof(f55,plain,(
% 7.59/1.49    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 7.59/1.49    inference(cnf_transformation,[],[f9])).
% 7.59/1.49  
% 7.59/1.49  fof(f89,plain,(
% 7.59/1.49    ( ! [X0,X1] : (r1_tarski(X0,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) )),
% 7.59/1.49    inference(definition_unfolding,[],[f55,f82])).
% 7.59/1.49  
% 7.59/1.49  fof(f22,axiom,(
% 7.59/1.49    ! [X0,X1] : (r1_tarski(X0,k1_tarski(X1)) <=> (k1_tarski(X1) = X0 | k1_xboole_0 = X0))),
% 7.59/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.59/1.49  
% 7.59/1.49  fof(f41,plain,(
% 7.59/1.49    ! [X0,X1] : ((r1_tarski(X0,k1_tarski(X1)) | (k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & ((k1_tarski(X1) = X0 | k1_xboole_0 = X0) | ~r1_tarski(X0,k1_tarski(X1))))),
% 7.59/1.49    inference(nnf_transformation,[],[f22])).
% 7.59/1.49  
% 7.59/1.49  fof(f42,plain,(
% 7.59/1.49    ! [X0,X1] : ((r1_tarski(X0,k1_tarski(X1)) | (k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & (k1_tarski(X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k1_tarski(X1))))),
% 7.59/1.49    inference(flattening,[],[f41])).
% 7.59/1.49  
% 7.59/1.49  fof(f69,plain,(
% 7.59/1.49    ( ! [X0,X1] : (k1_tarski(X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k1_tarski(X1))) )),
% 7.59/1.49    inference(cnf_transformation,[],[f42])).
% 7.59/1.49  
% 7.59/1.49  fof(f95,plain,(
% 7.59/1.49    ( ! [X0,X1] : (k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))) )),
% 7.59/1.49    inference(definition_unfolding,[],[f69,f84,f84])).
% 7.59/1.49  
% 7.59/1.49  fof(f21,axiom,(
% 7.59/1.49    ! [X0,X1] : (~r2_hidden(X0,X1) => r1_xboole_0(k1_tarski(X0),X1))),
% 7.59/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.59/1.49  
% 7.59/1.49  fof(f34,plain,(
% 7.59/1.49    ! [X0,X1] : (r1_xboole_0(k1_tarski(X0),X1) | r2_hidden(X0,X1))),
% 7.59/1.49    inference(ennf_transformation,[],[f21])).
% 7.59/1.49  
% 7.59/1.49  fof(f68,plain,(
% 7.59/1.49    ( ! [X0,X1] : (r1_xboole_0(k1_tarski(X0),X1) | r2_hidden(X0,X1)) )),
% 7.59/1.49    inference(cnf_transformation,[],[f34])).
% 7.59/1.49  
% 7.59/1.49  fof(f92,plain,(
% 7.59/1.49    ( ! [X0,X1] : (r1_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1) | r2_hidden(X0,X1)) )),
% 7.59/1.49    inference(definition_unfolding,[],[f68,f84])).
% 7.59/1.49  
% 7.59/1.49  fof(f4,axiom,(
% 7.59/1.49    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 7.59/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.59/1.49  
% 7.59/1.49  fof(f28,plain,(
% 7.59/1.49    ! [X0,X1] : (r1_xboole_0(X0,X1) => k3_xboole_0(X0,X1) = k1_xboole_0)),
% 7.59/1.49    inference(unused_predicate_definition_removal,[],[f4])).
% 7.59/1.49  
% 7.59/1.49  fof(f32,plain,(
% 7.59/1.49    ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1))),
% 7.59/1.49    inference(ennf_transformation,[],[f28])).
% 7.59/1.49  
% 7.59/1.49  fof(f50,plain,(
% 7.59/1.49    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)) )),
% 7.59/1.49    inference(cnf_transformation,[],[f32])).
% 7.59/1.49  
% 7.59/1.49  fof(f12,axiom,(
% 7.59/1.49    ! [X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)),
% 7.59/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.59/1.49  
% 7.59/1.49  fof(f58,plain,(
% 7.59/1.49    ( ! [X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)) )),
% 7.59/1.49    inference(cnf_transformation,[],[f12])).
% 7.59/1.49  
% 7.59/1.49  fof(f83,plain,(
% 7.59/1.49    ( ! [X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) = k3_xboole_0(X0,X1)) )),
% 7.59/1.49    inference(definition_unfolding,[],[f58,f82])).
% 7.59/1.49  
% 7.59/1.49  fof(f85,plain,(
% 7.59/1.49    ( ! [X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) = k1_xboole_0 | ~r1_xboole_0(X0,X1)) )),
% 7.59/1.49    inference(definition_unfolding,[],[f50,f83])).
% 7.59/1.49  
% 7.59/1.49  fof(f10,axiom,(
% 7.59/1.49    ! [X0,X1,X2] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2)),
% 7.59/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.59/1.49  
% 7.59/1.49  fof(f56,plain,(
% 7.59/1.49    ( ! [X2,X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2)) )),
% 7.59/1.49    inference(cnf_transformation,[],[f10])).
% 7.59/1.49  
% 7.59/1.49  fof(f1,axiom,(
% 7.59/1.49    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)),
% 7.59/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.59/1.49  
% 7.59/1.49  fof(f45,plain,(
% 7.59/1.49    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)) )),
% 7.59/1.49    inference(cnf_transformation,[],[f1])).
% 7.59/1.49  
% 7.59/1.49  fof(f20,axiom,(
% 7.59/1.49    ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) <=> r2_hidden(X0,X1))),
% 7.59/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.59/1.49  
% 7.59/1.49  fof(f40,plain,(
% 7.59/1.49    ! [X0,X1] : ((r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) & (r2_hidden(X0,X1) | ~r1_tarski(k1_tarski(X0),X1)))),
% 7.59/1.49    inference(nnf_transformation,[],[f20])).
% 7.59/1.49  
% 7.59/1.49  fof(f67,plain,(
% 7.59/1.49    ( ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) )),
% 7.59/1.49    inference(cnf_transformation,[],[f40])).
% 7.59/1.49  
% 7.59/1.49  fof(f90,plain,(
% 7.59/1.49    ( ! [X0,X1] : (r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1) | ~r2_hidden(X0,X1)) )),
% 7.59/1.49    inference(definition_unfolding,[],[f67,f84])).
% 7.59/1.49  
% 7.59/1.49  fof(f8,axiom,(
% 7.59/1.49    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 7.59/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.59/1.49  
% 7.59/1.49  fof(f33,plain,(
% 7.59/1.49    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 7.59/1.49    inference(ennf_transformation,[],[f8])).
% 7.59/1.49  
% 7.59/1.49  fof(f54,plain,(
% 7.59/1.49    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1)) )),
% 7.59/1.49    inference(cnf_transformation,[],[f33])).
% 7.59/1.49  
% 7.59/1.49  fof(f88,plain,(
% 7.59/1.49    ( ! [X0,X1] : (k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = X1 | ~r1_tarski(X0,X1)) )),
% 7.59/1.49    inference(definition_unfolding,[],[f54,f82])).
% 7.59/1.49  
% 7.59/1.49  fof(f74,plain,(
% 7.59/1.49    k1_tarski(sK1) != sK3 | k1_tarski(sK1) != sK2),
% 7.59/1.49    inference(cnf_transformation,[],[f44])).
% 7.59/1.49  
% 7.59/1.49  fof(f98,plain,(
% 7.59/1.49    k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) != sK3 | k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) != sK2),
% 7.59/1.49    inference(definition_unfolding,[],[f74,f84,f84])).
% 7.59/1.49  
% 7.59/1.49  fof(f75,plain,(
% 7.59/1.49    k1_tarski(sK1) != sK3 | k1_xboole_0 != sK2),
% 7.59/1.49    inference(cnf_transformation,[],[f44])).
% 7.59/1.49  
% 7.59/1.49  fof(f97,plain,(
% 7.59/1.49    k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) != sK3 | k1_xboole_0 != sK2),
% 7.59/1.49    inference(definition_unfolding,[],[f75,f84])).
% 7.59/1.49  
% 7.59/1.49  fof(f11,axiom,(
% 7.59/1.49    ! [X0] : k5_xboole_0(X0,X0) = k1_xboole_0),
% 7.59/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.59/1.49  
% 7.59/1.49  fof(f57,plain,(
% 7.59/1.49    ( ! [X0] : (k5_xboole_0(X0,X0) = k1_xboole_0) )),
% 7.59/1.49    inference(cnf_transformation,[],[f11])).
% 7.59/1.49  
% 7.59/1.49  fof(f7,axiom,(
% 7.59/1.49    ! [X0,X1] : k3_xboole_0(X0,X0) = X0),
% 7.59/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.59/1.49  
% 7.59/1.49  fof(f27,plain,(
% 7.59/1.49    ! [X0] : k3_xboole_0(X0,X0) = X0),
% 7.59/1.49    inference(rectify,[],[f7])).
% 7.59/1.49  
% 7.59/1.49  fof(f53,plain,(
% 7.59/1.49    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 7.59/1.49    inference(cnf_transformation,[],[f27])).
% 7.59/1.49  
% 7.59/1.49  fof(f87,plain,(
% 7.59/1.49    ( ! [X0] : (k5_xboole_0(k5_xboole_0(X0,X0),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))) = X0) )),
% 7.59/1.49    inference(definition_unfolding,[],[f53,f83])).
% 7.59/1.49  
% 7.59/1.49  fof(f6,axiom,(
% 7.59/1.49    ! [X0,X1] : k2_xboole_0(X0,X0) = X0),
% 7.59/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.59/1.49  
% 7.59/1.49  fof(f26,plain,(
% 7.59/1.49    ! [X0] : k2_xboole_0(X0,X0) = X0),
% 7.59/1.49    inference(rectify,[],[f6])).
% 7.59/1.49  
% 7.59/1.49  fof(f52,plain,(
% 7.59/1.49    ( ! [X0] : (k2_xboole_0(X0,X0) = X0) )),
% 7.59/1.49    inference(cnf_transformation,[],[f26])).
% 7.59/1.49  
% 7.59/1.49  fof(f86,plain,(
% 7.59/1.49    ( ! [X0] : (k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) = X0) )),
% 7.59/1.49    inference(definition_unfolding,[],[f52,f82])).
% 7.59/1.49  
% 7.59/1.49  fof(f76,plain,(
% 7.59/1.49    k1_xboole_0 != sK3 | k1_tarski(sK1) != sK2),
% 7.59/1.49    inference(cnf_transformation,[],[f44])).
% 7.59/1.49  
% 7.59/1.49  fof(f96,plain,(
% 7.59/1.49    k1_xboole_0 != sK3 | k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) != sK2),
% 7.59/1.49    inference(definition_unfolding,[],[f76,f84])).
% 7.59/1.49  
% 7.59/1.49  fof(f3,axiom,(
% 7.59/1.49    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 7.59/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.59/1.49  
% 7.59/1.49  fof(f31,plain,(
% 7.59/1.49    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 7.59/1.49    inference(ennf_transformation,[],[f3])).
% 7.59/1.49  
% 7.59/1.49  fof(f36,plain,(
% 7.59/1.49    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 7.59/1.49    inference(nnf_transformation,[],[f31])).
% 7.59/1.49  
% 7.59/1.49  fof(f37,plain,(
% 7.59/1.49    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 7.59/1.49    inference(rectify,[],[f36])).
% 7.59/1.49  
% 7.59/1.49  fof(f38,plain,(
% 7.59/1.49    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 7.59/1.49    introduced(choice_axiom,[])).
% 7.59/1.49  
% 7.59/1.49  fof(f39,plain,(
% 7.59/1.49    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 7.59/1.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f37,f38])).
% 7.59/1.49  
% 7.59/1.49  fof(f48,plain,(
% 7.59/1.49    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK0(X0,X1),X0)) )),
% 7.59/1.49    inference(cnf_transformation,[],[f39])).
% 7.59/1.49  
% 7.59/1.49  fof(f2,axiom,(
% 7.59/1.49    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 7.59/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.59/1.49  
% 7.59/1.49  fof(f29,plain,(
% 7.59/1.49    ! [X0] : (v1_xboole_0(X0) => ! [X1] : ~r2_hidden(X1,X0))),
% 7.59/1.49    inference(unused_predicate_definition_removal,[],[f2])).
% 7.59/1.49  
% 7.59/1.49  fof(f30,plain,(
% 7.59/1.49    ! [X0] : (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0))),
% 7.59/1.49    inference(ennf_transformation,[],[f29])).
% 7.59/1.49  
% 7.59/1.49  fof(f46,plain,(
% 7.59/1.49    ( ! [X0,X1] : (~r2_hidden(X1,X0) | ~v1_xboole_0(X0)) )),
% 7.59/1.49    inference(cnf_transformation,[],[f30])).
% 7.59/1.49  
% 7.59/1.49  fof(f5,axiom,(
% 7.59/1.49    v1_xboole_0(k1_xboole_0)),
% 7.59/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.59/1.49  
% 7.59/1.49  fof(f51,plain,(
% 7.59/1.49    v1_xboole_0(k1_xboole_0)),
% 7.59/1.49    inference(cnf_transformation,[],[f5])).
% 7.59/1.49  
% 7.59/1.49  cnf(c_22,negated_conjecture,
% 7.59/1.49      ( k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) = k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3)) ),
% 7.59/1.49      inference(cnf_transformation,[],[f99]) ).
% 7.59/1.49  
% 7.59/1.49  cnf(c_10,plain,
% 7.59/1.49      ( r1_tarski(X0,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) ),
% 7.59/1.49      inference(cnf_transformation,[],[f89]) ).
% 7.59/1.49  
% 7.59/1.49  cnf(c_1238,plain,
% 7.59/1.49      ( r1_tarski(X0,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) = iProver_top ),
% 7.59/1.49      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 7.59/1.49  
% 7.59/1.49  cnf(c_8328,plain,
% 7.59/1.49      ( r1_tarski(sK2,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)) = iProver_top ),
% 7.59/1.49      inference(superposition,[status(thm)],[c_22,c_1238]) ).
% 7.59/1.49  
% 7.59/1.49  cnf(c_18,plain,
% 7.59/1.49      ( ~ r1_tarski(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))
% 7.59/1.49      | k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) = X0
% 7.59/1.49      | k1_xboole_0 = X0 ),
% 7.59/1.49      inference(cnf_transformation,[],[f95]) ).
% 7.59/1.49  
% 7.59/1.49  cnf(c_1232,plain,
% 7.59/1.49      ( k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) = X1
% 7.59/1.49      | k1_xboole_0 = X1
% 7.59/1.49      | r1_tarski(X1,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) != iProver_top ),
% 7.59/1.49      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 7.59/1.49  
% 7.59/1.49  cnf(c_8368,plain,
% 7.59/1.49      ( k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) = sK2
% 7.59/1.49      | sK2 = k1_xboole_0 ),
% 7.59/1.49      inference(superposition,[status(thm)],[c_8328,c_1232]) ).
% 7.59/1.49  
% 7.59/1.49  cnf(c_15,plain,
% 7.59/1.49      ( r1_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1)
% 7.59/1.49      | r2_hidden(X0,X1) ),
% 7.59/1.49      inference(cnf_transformation,[],[f92]) ).
% 7.59/1.49  
% 7.59/1.49  cnf(c_1235,plain,
% 7.59/1.49      ( r1_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1) = iProver_top
% 7.59/1.49      | r2_hidden(X0,X1) = iProver_top ),
% 7.59/1.49      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 7.59/1.49  
% 7.59/1.49  cnf(c_8396,plain,
% 7.59/1.49      ( sK2 = k1_xboole_0
% 7.59/1.49      | r1_xboole_0(sK2,X0) = iProver_top
% 7.59/1.49      | r2_hidden(sK1,X0) = iProver_top ),
% 7.59/1.49      inference(superposition,[status(thm)],[c_8368,c_1235]) ).
% 7.59/1.49  
% 7.59/1.49  cnf(c_5,plain,
% 7.59/1.49      ( ~ r1_xboole_0(X0,X1)
% 7.59/1.49      | k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) = k1_xboole_0 ),
% 7.59/1.49      inference(cnf_transformation,[],[f85]) ).
% 7.59/1.49  
% 7.59/1.49  cnf(c_11,plain,
% 7.59/1.49      ( k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
% 7.59/1.49      inference(cnf_transformation,[],[f56]) ).
% 7.59/1.49  
% 7.59/1.49  cnf(c_0,plain,
% 7.59/1.49      ( k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
% 7.59/1.49      inference(cnf_transformation,[],[f45]) ).
% 7.59/1.49  
% 7.59/1.49  cnf(c_879,plain,
% 7.59/1.49      ( ~ r1_xboole_0(X0,X1)
% 7.59/1.49      | k5_xboole_0(X0,k5_xboole_0(X1,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) = k1_xboole_0 ),
% 7.59/1.49      inference(theory_normalisation,[status(thm)],[c_5,c_11,c_0]) ).
% 7.59/1.49  
% 7.59/1.49  cnf(c_1240,plain,
% 7.59/1.49      ( k5_xboole_0(X0,k5_xboole_0(X1,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) = k1_xboole_0
% 7.59/1.49      | r1_xboole_0(X0,X1) != iProver_top ),
% 7.59/1.49      inference(predicate_to_equality,[status(thm)],[c_879]) ).
% 7.59/1.49  
% 7.59/1.49  cnf(c_13720,plain,
% 7.59/1.49      ( k5_xboole_0(sK2,k5_xboole_0(X0,k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,X0)))) = k1_xboole_0
% 7.59/1.49      | sK2 = k1_xboole_0
% 7.59/1.49      | r2_hidden(sK1,X0) = iProver_top ),
% 7.59/1.49      inference(superposition,[status(thm)],[c_8396,c_1240]) ).
% 7.59/1.49  
% 7.59/1.49  cnf(c_13,plain,
% 7.59/1.49      ( r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1)
% 7.59/1.49      | ~ r2_hidden(X0,X1) ),
% 7.59/1.49      inference(cnf_transformation,[],[f90]) ).
% 7.59/1.49  
% 7.59/1.49  cnf(c_1237,plain,
% 7.59/1.49      ( r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1) = iProver_top
% 7.59/1.49      | r2_hidden(X0,X1) != iProver_top ),
% 7.59/1.49      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 7.59/1.49  
% 7.59/1.49  cnf(c_8826,plain,
% 7.59/1.49      ( sK2 = k1_xboole_0
% 7.59/1.49      | r1_tarski(sK2,X0) = iProver_top
% 7.59/1.49      | r2_hidden(sK1,X0) != iProver_top ),
% 7.59/1.49      inference(superposition,[status(thm)],[c_8368,c_1237]) ).
% 7.59/1.49  
% 7.59/1.49  cnf(c_18167,plain,
% 7.59/1.49      ( k5_xboole_0(sK2,k5_xboole_0(X0,k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,X0)))) = k1_xboole_0
% 7.59/1.49      | sK2 = k1_xboole_0
% 7.59/1.49      | r1_tarski(sK2,X0) = iProver_top ),
% 7.59/1.49      inference(superposition,[status(thm)],[c_13720,c_8826]) ).
% 7.59/1.49  
% 7.59/1.49  cnf(c_9,plain,
% 7.59/1.49      ( ~ r1_tarski(X0,X1)
% 7.59/1.49      | k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = X1 ),
% 7.59/1.49      inference(cnf_transformation,[],[f88]) ).
% 7.59/1.49  
% 7.59/1.49  cnf(c_1239,plain,
% 7.59/1.49      ( k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = X1
% 7.59/1.49      | r1_tarski(X0,X1) != iProver_top ),
% 7.59/1.49      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 7.59/1.49  
% 7.59/1.49  cnf(c_18220,plain,
% 7.59/1.49      ( k5_xboole_0(sK2,k5_xboole_0(X0,k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,X0)))) = k1_xboole_0
% 7.59/1.49      | k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,X0)) = X0
% 7.59/1.49      | sK2 = k1_xboole_0 ),
% 7.59/1.49      inference(superposition,[status(thm)],[c_18167,c_1239]) ).
% 7.59/1.49  
% 7.59/1.49  cnf(c_18251,plain,
% 7.59/1.49      ( k5_xboole_0(sK2,k5_xboole_0(sK3,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))) = k1_xboole_0
% 7.59/1.49      | k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3)) = sK3
% 7.59/1.49      | sK2 = k1_xboole_0 ),
% 7.59/1.49      inference(superposition,[status(thm)],[c_22,c_18220]) ).
% 7.59/1.49  
% 7.59/1.49  cnf(c_18480,plain,
% 7.59/1.49      ( k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) = sK3
% 7.59/1.49      | k5_xboole_0(sK2,k5_xboole_0(sK3,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))) = k1_xboole_0
% 7.59/1.49      | sK2 = k1_xboole_0 ),
% 7.59/1.49      inference(demodulation,[status(thm)],[c_18251,c_22]) ).
% 7.59/1.49  
% 7.59/1.49  cnf(c_21,negated_conjecture,
% 7.59/1.49      ( k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) != sK2
% 7.59/1.49      | k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) != sK3 ),
% 7.59/1.49      inference(cnf_transformation,[],[f98]) ).
% 7.59/1.49  
% 7.59/1.49  cnf(c_8400,plain,
% 7.59/1.49      ( k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) != sK3
% 7.59/1.49      | sK2 = k1_xboole_0 ),
% 7.59/1.49      inference(superposition,[status(thm)],[c_8368,c_21]) ).
% 7.59/1.49  
% 7.59/1.49  cnf(c_20,negated_conjecture,
% 7.59/1.49      ( k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) != sK3
% 7.59/1.49      | k1_xboole_0 != sK2 ),
% 7.59/1.49      inference(cnf_transformation,[],[f97]) ).
% 7.59/1.49  
% 7.59/1.49  cnf(c_1267,plain,
% 7.59/1.49      ( ~ r1_tarski(sK2,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))
% 7.59/1.49      | k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) = sK2
% 7.59/1.49      | k1_xboole_0 = sK2 ),
% 7.59/1.49      inference(instantiation,[status(thm)],[c_18]) ).
% 7.59/1.49  
% 7.59/1.49  cnf(c_8334,plain,
% 7.59/1.49      ( r1_tarski(sK2,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)) ),
% 7.59/1.49      inference(predicate_to_equality_rev,[status(thm)],[c_8328]) ).
% 7.59/1.49  
% 7.59/1.49  cnf(c_8534,plain,
% 7.59/1.49      ( k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) != sK3 ),
% 7.59/1.49      inference(global_propositional_subsumption,
% 7.59/1.49                [status(thm)],
% 7.59/1.49                [c_8400,c_21,c_20,c_1267,c_8334]) ).
% 7.59/1.49  
% 7.59/1.49  cnf(c_18513,plain,
% 7.59/1.49      ( k5_xboole_0(sK2,k5_xboole_0(sK3,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))) = k1_xboole_0
% 7.59/1.49      | sK2 = k1_xboole_0 ),
% 7.59/1.49      inference(global_propositional_subsumption,
% 7.59/1.49                [status(thm)],
% 7.59/1.49                [c_18480,c_21,c_20,c_1267,c_8334]) ).
% 7.59/1.49  
% 7.59/1.49  cnf(c_18518,plain,
% 7.59/1.49      ( k5_xboole_0(sK2,k5_xboole_0(sK3,sK2)) = k1_xboole_0
% 7.59/1.49      | sK2 = k1_xboole_0 ),
% 7.59/1.49      inference(superposition,[status(thm)],[c_8368,c_18513]) ).
% 7.59/1.49  
% 7.59/1.49  cnf(c_12,plain,
% 7.59/1.49      ( k5_xboole_0(X0,X0) = k1_xboole_0 ),
% 7.59/1.49      inference(cnf_transformation,[],[f57]) ).
% 7.59/1.49  
% 7.59/1.49  cnf(c_1451,plain,
% 7.59/1.49      ( k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X0,X1))) = k1_xboole_0 ),
% 7.59/1.49      inference(superposition,[status(thm)],[c_11,c_12]) ).
% 7.59/1.49  
% 7.59/1.49  cnf(c_1449,plain,
% 7.59/1.49      ( k5_xboole_0(X0,k5_xboole_0(X0,X1)) = k5_xboole_0(k1_xboole_0,X1) ),
% 7.59/1.49      inference(superposition,[status(thm)],[c_12,c_11]) ).
% 7.59/1.49  
% 7.59/1.49  cnf(c_8,plain,
% 7.59/1.49      ( k5_xboole_0(k5_xboole_0(X0,X0),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))) = X0 ),
% 7.59/1.49      inference(cnf_transformation,[],[f87]) ).
% 7.59/1.49  
% 7.59/1.49  cnf(c_878,plain,
% 7.59/1.49      ( k5_xboole_0(X0,k5_xboole_0(X0,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)))) = X0 ),
% 7.59/1.49      inference(theory_normalisation,[status(thm)],[c_8,c_11,c_0]) ).
% 7.59/1.49  
% 7.59/1.49  cnf(c_7,plain,
% 7.59/1.49      ( k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) = X0 ),
% 7.59/1.49      inference(cnf_transformation,[],[f86]) ).
% 7.59/1.49  
% 7.59/1.49  cnf(c_1244,plain,
% 7.59/1.49      ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
% 7.59/1.49      inference(light_normalisation,[status(thm)],[c_878,c_7,c_12]) ).
% 7.59/1.49  
% 7.59/1.49  cnf(c_1409,plain,
% 7.59/1.49      ( k5_xboole_0(k1_xboole_0,X0) = X0 ),
% 7.59/1.49      inference(superposition,[status(thm)],[c_1244,c_0]) ).
% 7.59/1.49  
% 7.59/1.49  cnf(c_1455,plain,
% 7.59/1.49      ( k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1 ),
% 7.59/1.49      inference(demodulation,[status(thm)],[c_1449,c_1409]) ).
% 7.59/1.49  
% 7.59/1.49  cnf(c_1556,plain,
% 7.59/1.49      ( k5_xboole_0(X0,k5_xboole_0(X1,X0)) = k5_xboole_0(X1,k1_xboole_0) ),
% 7.59/1.49      inference(superposition,[status(thm)],[c_1451,c_1455]) ).
% 7.59/1.49  
% 7.59/1.49  cnf(c_1565,plain,
% 7.59/1.49      ( k5_xboole_0(X0,k5_xboole_0(X1,X0)) = X1 ),
% 7.59/1.49      inference(demodulation,[status(thm)],[c_1556,c_1244]) ).
% 7.59/1.49  
% 7.59/1.49  cnf(c_18767,plain,
% 7.59/1.49      ( sK2 = k1_xboole_0 | sK3 = k1_xboole_0 ),
% 7.59/1.49      inference(demodulation,[status(thm)],[c_18518,c_1565]) ).
% 7.59/1.49  
% 7.59/1.49  cnf(c_19,negated_conjecture,
% 7.59/1.49      ( k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) != sK2
% 7.59/1.49      | k1_xboole_0 != sK3 ),
% 7.59/1.49      inference(cnf_transformation,[],[f96]) ).
% 7.59/1.49  
% 7.59/1.49  cnf(c_8402,plain,
% 7.59/1.49      ( sK2 = k1_xboole_0 | sK3 != k1_xboole_0 ),
% 7.59/1.49      inference(superposition,[status(thm)],[c_8368,c_19]) ).
% 7.59/1.49  
% 7.59/1.49  cnf(c_18822,plain,
% 7.59/1.49      ( sK2 = k1_xboole_0 ),
% 7.59/1.49      inference(global_propositional_subsumption,
% 7.59/1.49                [status(thm)],
% 7.59/1.49                [c_18767,c_8402]) ).
% 7.59/1.49  
% 7.59/1.49  cnf(c_18844,plain,
% 7.59/1.49      ( k3_tarski(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,sK3)) = k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) ),
% 7.59/1.49      inference(demodulation,[status(thm)],[c_18822,c_22]) ).
% 7.59/1.49  
% 7.59/1.49  cnf(c_3,plain,
% 7.59/1.49      ( r1_tarski(X0,X1) | r2_hidden(sK0(X0,X1),X0) ),
% 7.59/1.49      inference(cnf_transformation,[],[f48]) ).
% 7.59/1.49  
% 7.59/1.49  cnf(c_1242,plain,
% 7.59/1.49      ( r1_tarski(X0,X1) = iProver_top
% 7.59/1.49      | r2_hidden(sK0(X0,X1),X0) = iProver_top ),
% 7.59/1.49      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 7.59/1.49  
% 7.59/1.49  cnf(c_1,plain,
% 7.59/1.49      ( ~ r2_hidden(X0,X1) | ~ v1_xboole_0(X1) ),
% 7.59/1.49      inference(cnf_transformation,[],[f46]) ).
% 7.59/1.49  
% 7.59/1.49  cnf(c_6,plain,
% 7.59/1.49      ( v1_xboole_0(k1_xboole_0) ),
% 7.59/1.49      inference(cnf_transformation,[],[f51]) ).
% 7.59/1.49  
% 7.59/1.49  cnf(c_220,plain,
% 7.59/1.49      ( ~ r2_hidden(X0,X1) | k1_xboole_0 != X1 ),
% 7.59/1.49      inference(resolution_lifted,[status(thm)],[c_1,c_6]) ).
% 7.59/1.49  
% 7.59/1.49  cnf(c_221,plain,
% 7.59/1.49      ( ~ r2_hidden(X0,k1_xboole_0) ),
% 7.59/1.49      inference(unflattening,[status(thm)],[c_220]) ).
% 7.59/1.49  
% 7.59/1.49  cnf(c_1231,plain,
% 7.59/1.49      ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
% 7.59/1.49      inference(predicate_to_equality,[status(thm)],[c_221]) ).
% 7.59/1.49  
% 7.59/1.49  cnf(c_3511,plain,
% 7.59/1.49      ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
% 7.59/1.49      inference(superposition,[status(thm)],[c_1242,c_1231]) ).
% 7.59/1.49  
% 7.59/1.49  cnf(c_10852,plain,
% 7.59/1.49      ( k3_tarski(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,X0)) = X0 ),
% 7.59/1.49      inference(superposition,[status(thm)],[c_3511,c_1239]) ).
% 7.59/1.49  
% 7.59/1.49  cnf(c_18846,plain,
% 7.59/1.49      ( k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) = sK3 ),
% 7.59/1.49      inference(demodulation,[status(thm)],[c_18844,c_10852]) ).
% 7.59/1.49  
% 7.59/1.49  cnf(contradiction,plain,
% 7.59/1.49      ( $false ),
% 7.59/1.49      inference(minisat,[status(thm)],[c_18846,c_8534]) ).
% 7.59/1.49  
% 7.59/1.49  
% 7.59/1.49  % SZS output end CNFRefutation for theBenchmark.p
% 7.59/1.49  
% 7.59/1.49  ------                               Statistics
% 7.59/1.49  
% 7.59/1.49  ------ General
% 7.59/1.49  
% 7.59/1.49  abstr_ref_over_cycles:                  0
% 7.59/1.49  abstr_ref_under_cycles:                 0
% 7.59/1.49  gc_basic_clause_elim:                   0
% 7.59/1.49  forced_gc_time:                         0
% 7.59/1.49  parsing_time:                           0.007
% 7.59/1.49  unif_index_cands_time:                  0.
% 7.59/1.49  unif_index_add_time:                    0.
% 7.59/1.49  orderings_time:                         0.
% 7.59/1.49  out_proof_time:                         0.008
% 7.59/1.49  total_time:                             0.529
% 7.59/1.49  num_of_symbols:                         43
% 7.59/1.49  num_of_terms:                           44619
% 7.59/1.49  
% 7.59/1.49  ------ Preprocessing
% 7.59/1.49  
% 7.59/1.49  num_of_splits:                          0
% 7.59/1.49  num_of_split_atoms:                     0
% 7.59/1.49  num_of_reused_defs:                     0
% 7.59/1.49  num_eq_ax_congr_red:                    10
% 7.59/1.49  num_of_sem_filtered_clauses:            1
% 7.59/1.49  num_of_subtypes:                        0
% 7.59/1.49  monotx_restored_types:                  0
% 7.59/1.49  sat_num_of_epr_types:                   0
% 7.59/1.49  sat_num_of_non_cyclic_types:            0
% 7.59/1.49  sat_guarded_non_collapsed_types:        0
% 7.59/1.49  num_pure_diseq_elim:                    0
% 7.59/1.49  simp_replaced_by:                       0
% 7.59/1.49  res_preprocessed:                       106
% 7.59/1.49  prep_upred:                             0
% 7.59/1.49  prep_unflattend:                        71
% 7.59/1.49  smt_new_axioms:                         0
% 7.59/1.49  pred_elim_cands:                        3
% 7.59/1.49  pred_elim:                              1
% 7.59/1.49  pred_elim_cl:                           1
% 7.59/1.49  pred_elim_cycles:                       5
% 7.59/1.49  merged_defs:                            8
% 7.59/1.49  merged_defs_ncl:                        0
% 7.59/1.49  bin_hyper_res:                          8
% 7.59/1.49  prep_cycles:                            4
% 7.59/1.49  pred_elim_time:                         0.005
% 7.59/1.49  splitting_time:                         0.
% 7.59/1.49  sem_filter_time:                        0.
% 7.59/1.49  monotx_time:                            0.
% 7.59/1.49  subtype_inf_time:                       0.
% 7.59/1.49  
% 7.59/1.49  ------ Problem properties
% 7.59/1.49  
% 7.59/1.49  clauses:                                22
% 7.59/1.49  conjectures:                            4
% 7.59/1.49  epr:                                    2
% 7.59/1.49  horn:                                   19
% 7.59/1.49  ground:                                 4
% 7.59/1.49  unary:                                  10
% 7.59/1.49  binary:                                 10
% 7.59/1.49  lits:                                   36
% 7.59/1.49  lits_eq:                                16
% 7.59/1.49  fd_pure:                                0
% 7.59/1.49  fd_pseudo:                              0
% 7.59/1.49  fd_cond:                                0
% 7.59/1.49  fd_pseudo_cond:                         1
% 7.59/1.49  ac_symbols:                             1
% 7.59/1.49  
% 7.59/1.49  ------ Propositional Solver
% 7.59/1.49  
% 7.59/1.49  prop_solver_calls:                      34
% 7.59/1.49  prop_fast_solver_calls:                 684
% 7.59/1.49  smt_solver_calls:                       0
% 7.59/1.49  smt_fast_solver_calls:                  0
% 7.59/1.49  prop_num_of_clauses:                    2938
% 7.59/1.49  prop_preprocess_simplified:             6138
% 7.59/1.49  prop_fo_subsumed:                       5
% 7.59/1.49  prop_solver_time:                       0.
% 7.59/1.49  smt_solver_time:                        0.
% 7.59/1.49  smt_fast_solver_time:                   0.
% 7.59/1.49  prop_fast_solver_time:                  0.
% 7.59/1.49  prop_unsat_core_time:                   0.
% 7.59/1.49  
% 7.59/1.49  ------ QBF
% 7.59/1.49  
% 7.59/1.49  qbf_q_res:                              0
% 7.59/1.49  qbf_num_tautologies:                    0
% 7.59/1.49  qbf_prep_cycles:                        0
% 7.59/1.49  
% 7.59/1.49  ------ BMC1
% 7.59/1.49  
% 7.59/1.49  bmc1_current_bound:                     -1
% 7.59/1.49  bmc1_last_solved_bound:                 -1
% 7.59/1.49  bmc1_unsat_core_size:                   -1
% 7.59/1.49  bmc1_unsat_core_parents_size:           -1
% 7.59/1.49  bmc1_merge_next_fun:                    0
% 7.59/1.49  bmc1_unsat_core_clauses_time:           0.
% 7.59/1.49  
% 7.59/1.49  ------ Instantiation
% 7.59/1.49  
% 7.59/1.49  inst_num_of_clauses:                    793
% 7.59/1.49  inst_num_in_passive:                    44
% 7.59/1.49  inst_num_in_active:                     370
% 7.59/1.49  inst_num_in_unprocessed:                380
% 7.59/1.49  inst_num_of_loops:                      510
% 7.59/1.49  inst_num_of_learning_restarts:          0
% 7.59/1.49  inst_num_moves_active_passive:          134
% 7.59/1.49  inst_lit_activity:                      0
% 7.59/1.49  inst_lit_activity_moves:                0
% 7.59/1.49  inst_num_tautologies:                   0
% 7.59/1.49  inst_num_prop_implied:                  0
% 7.59/1.49  inst_num_existing_simplified:           0
% 7.59/1.49  inst_num_eq_res_simplified:             0
% 7.59/1.49  inst_num_child_elim:                    0
% 7.59/1.49  inst_num_of_dismatching_blockings:      217
% 7.59/1.49  inst_num_of_non_proper_insts:           831
% 7.59/1.49  inst_num_of_duplicates:                 0
% 7.59/1.49  inst_inst_num_from_inst_to_res:         0
% 7.59/1.49  inst_dismatching_checking_time:         0.
% 7.59/1.49  
% 7.59/1.49  ------ Resolution
% 7.59/1.49  
% 7.59/1.49  res_num_of_clauses:                     0
% 7.59/1.49  res_num_in_passive:                     0
% 7.59/1.49  res_num_in_active:                      0
% 7.59/1.49  res_num_of_loops:                       110
% 7.59/1.49  res_forward_subset_subsumed:            122
% 7.59/1.49  res_backward_subset_subsumed:           6
% 7.59/1.49  res_forward_subsumed:                   2
% 7.59/1.49  res_backward_subsumed:                  0
% 7.59/1.49  res_forward_subsumption_resolution:     0
% 7.59/1.49  res_backward_subsumption_resolution:    0
% 7.59/1.49  res_clause_to_clause_subsumption:       31009
% 7.59/1.49  res_orphan_elimination:                 0
% 7.59/1.49  res_tautology_del:                      76
% 7.59/1.49  res_num_eq_res_simplified:              0
% 7.59/1.49  res_num_sel_changes:                    0
% 7.59/1.49  res_moves_from_active_to_pass:          0
% 7.59/1.49  
% 7.59/1.49  ------ Superposition
% 7.59/1.49  
% 7.59/1.49  sup_time_total:                         0.
% 7.59/1.49  sup_time_generating:                    0.
% 7.59/1.49  sup_time_sim_full:                      0.
% 7.59/1.49  sup_time_sim_immed:                     0.
% 7.59/1.49  
% 7.59/1.49  sup_num_of_clauses:                     767
% 7.59/1.49  sup_num_in_active:                      65
% 7.59/1.49  sup_num_in_passive:                     702
% 7.59/1.49  sup_num_of_loops:                       100
% 7.59/1.49  sup_fw_superposition:                   4631
% 7.59/1.49  sup_bw_superposition:                   2946
% 7.59/1.49  sup_immediate_simplified:               4356
% 7.59/1.49  sup_given_eliminated:                   0
% 7.59/1.49  comparisons_done:                       0
% 7.59/1.49  comparisons_avoided:                    24
% 7.59/1.49  
% 7.59/1.49  ------ Simplifications
% 7.59/1.49  
% 7.59/1.49  
% 7.59/1.49  sim_fw_subset_subsumed:                 5
% 7.59/1.49  sim_bw_subset_subsumed:                 9
% 7.59/1.49  sim_fw_subsumed:                        135
% 7.59/1.49  sim_bw_subsumed:                        3
% 7.59/1.49  sim_fw_subsumption_res:                 0
% 7.59/1.49  sim_bw_subsumption_res:                 0
% 7.59/1.49  sim_tautology_del:                      2
% 7.59/1.49  sim_eq_tautology_del:                   916
% 7.59/1.49  sim_eq_res_simp:                        0
% 7.59/1.49  sim_fw_demodulated:                     4927
% 7.59/1.49  sim_bw_demodulated:                     28
% 7.59/1.49  sim_light_normalised:                   1038
% 7.59/1.49  sim_joinable_taut:                      235
% 7.59/1.49  sim_joinable_simp:                      0
% 7.59/1.49  sim_ac_normalised:                      0
% 7.59/1.49  sim_smt_subsumption:                    0
% 7.59/1.49  
%------------------------------------------------------------------------------
