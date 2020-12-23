%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:32:20 EST 2020

% Result     : Theorem 12.09s
% Output     : CNFRefutation 12.09s
% Verified   : 
% Statistics : Number of formulae       :  160 (1733 expanded)
%              Number of clauses        :   77 ( 194 expanded)
%              Number of leaves         :   27 ( 539 expanded)
%              Depth                    :   25
%              Number of atoms          :  317 (2636 expanded)
%              Number of equality atoms :  223 (2430 expanded)
%              Maximal formula depth    :   11 (   3 average)
%              Maximal clause size      :   14 (   2 average)
%              Maximal term depth       :    6 (   2 average)

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

fof(f34,plain,(
    ? [X0,X1,X2] :
      ( ( k1_xboole_0 != X2
        | k1_tarski(X0) != X1 )
      & ( k1_tarski(X0) != X2
        | k1_xboole_0 != X1 )
      & ( k1_tarski(X0) != X2
        | k1_tarski(X0) != X1 )
      & k2_xboole_0(X1,X2) = k1_tarski(X0) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f42,plain,
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

fof(f43,plain,
    ( ( k1_xboole_0 != sK4
      | k1_tarski(sK2) != sK3 )
    & ( k1_tarski(sK2) != sK4
      | k1_xboole_0 != sK3 )
    & ( k1_tarski(sK2) != sK4
      | k1_tarski(sK2) != sK3 )
    & k2_xboole_0(sK3,sK4) = k1_tarski(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f34,f42])).

fof(f71,plain,(
    k2_xboole_0(sK3,sK4) = k1_tarski(sK2) ),
    inference(cnf_transformation,[],[f43])).

fof(f23,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f70,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f23])).

fof(f80,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f70,f79])).

fof(f15,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f60,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f15])).

fof(f16,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f61,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f16])).

fof(f17,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f62,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f17])).

fof(f18,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f63,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f18])).

fof(f19,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f64,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f19])).

fof(f20,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f65,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f20])).

fof(f21,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f66,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f21])).

fof(f75,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f65,f66])).

fof(f76,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f64,f75])).

fof(f77,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f63,f76])).

fof(f78,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f62,f77])).

fof(f79,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f61,f78])).

fof(f82,plain,(
    ! [X0] : k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f60,f79])).

fof(f97,plain,(
    k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) = k3_tarski(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4)) ),
    inference(definition_unfolding,[],[f71,f80,f82])).

fof(f9,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f54,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f9])).

fof(f14,axiom,(
    ! [X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f59,plain,(
    ! [X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f14])).

fof(f81,plain,(
    ! [X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) = k3_xboole_0(X0,X1) ),
    inference(definition_unfolding,[],[f59,f80])).

fof(f89,plain,(
    ! [X0,X1] : r1_tarski(k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))),X0) ),
    inference(definition_unfolding,[],[f54,f81])).

fof(f12,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f57,plain,(
    ! [X2,X0,X1] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f12])).

fof(f1,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f11,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f56,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f11])).

fof(f90,plain,(
    ! [X0,X1] : r1_tarski(X0,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) ),
    inference(definition_unfolding,[],[f56,f80])).

fof(f22,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,k1_tarski(X1))
    <=> ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,k1_tarski(X1))
        | ( k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k1_tarski(X1)) ) ) ),
    inference(nnf_transformation,[],[f22])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,k1_tarski(X1))
        | ( k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k1_tarski(X1)) ) ) ),
    inference(flattening,[],[f40])).

fof(f67,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = X0
      | k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_tarski(X1)) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f93,plain,(
    ! [X0,X1] :
      ( k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) = X0
      | k1_xboole_0 = X0
      | ~ r1_tarski(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)) ) ),
    inference(definition_unfolding,[],[f67,f82,f82])).

fof(f74,plain,
    ( k1_xboole_0 != sK4
    | k1_tarski(sK2) != sK3 ),
    inference(cnf_transformation,[],[f43])).

fof(f94,plain,
    ( k1_xboole_0 != sK4
    | k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) != sK3 ),
    inference(definition_unfolding,[],[f74,f82])).

fof(f72,plain,
    ( k1_tarski(sK2) != sK4
    | k1_tarski(sK2) != sK3 ),
    inference(cnf_transformation,[],[f43])).

fof(f96,plain,
    ( k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) != sK4
    | k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) != sK3 ),
    inference(definition_unfolding,[],[f72,f82,f82])).

fof(f73,plain,
    ( k1_tarski(sK2) != sK4
    | k1_xboole_0 != sK3 ),
    inference(cnf_transformation,[],[f43])).

fof(f95,plain,
    ( k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) != sK4
    | k1_xboole_0 != sK3 ),
    inference(definition_unfolding,[],[f73,f82])).

fof(f13,axiom,(
    ! [X0] : k5_xboole_0(X0,X0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f58,plain,(
    ! [X0] : k5_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f13])).

fof(f10,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f55,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f10])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r2_xboole_0(X0,X1)
    <=> ( X0 != X1
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( X0 != X1
        & r1_tarski(X0,X1) )
     => r2_xboole_0(X0,X1) ) ),
    inference(unused_predicate_definition_removal,[],[f4])).

fof(f30,plain,(
    ! [X0,X1] :
      ( r2_xboole_0(X0,X1)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f29])).

fof(f31,plain,(
    ! [X0,X1] :
      ( r2_xboole_0(X0,X1)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f30])).

fof(f47,plain,(
    ! [X0,X1] :
      ( r2_xboole_0(X0,X1)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f8,axiom,(
    ! [X0,X1] :
      ~ ( ! [X2] :
            ~ ( ~ r2_hidden(X2,X0)
              & r2_hidden(X2,X1) )
        & r2_xboole_0(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X0)
          & r2_hidden(X2,X1) )
      | ~ r2_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f38,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X0)
          & r2_hidden(X2,X1) )
     => ( ~ r2_hidden(sK1(X0,X1),X0)
        & r2_hidden(sK1(X0,X1),X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( ~ r2_hidden(sK1(X0,X1),X0)
        & r2_hidden(sK1(X0,X1),X1) )
      | ~ r2_xboole_0(X0,X1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f33,f38])).

fof(f52,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK1(X0,X1),X1)
      | ~ r2_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f5,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f5])).

fof(f48,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f26])).

fof(f85,plain,(
    ! [X0] : k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) = X0 ),
    inference(definition_unfolding,[],[f48,f80])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f7])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f28])).

fof(f36,plain,(
    ! [X1,X0] :
      ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
     => r2_hidden(sK0(X0,X1),k3_xboole_0(X0,X1)) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( r2_hidden(sK0(X0,X1),k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f32,f36])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,k3_xboole_0(X0,X1)) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f87,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) ) ),
    inference(definition_unfolding,[],[f51,f81])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k3_xboole_0(X0,X1) != k1_xboole_0 )
      & ( k3_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f46,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k3_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f35])).

fof(f83,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) != k1_xboole_0 ) ),
    inference(definition_unfolding,[],[f46,f81])).

cnf(c_21,negated_conjecture,
    ( k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) = k3_tarski(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4)) ),
    inference(cnf_transformation,[],[f97])).

cnf(c_10,plain,
    ( r1_tarski(k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))),X0) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_13,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_0,plain,
    ( k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_413,plain,
    ( r1_tarski(k5_xboole_0(X0,k5_xboole_0(X1,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))),X0) ),
    inference(theory_normalisation,[status(thm)],[c_10,c_13,c_0])).

cnf(c_753,plain,
    ( r1_tarski(k5_xboole_0(X0,k5_xboole_0(X1,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_413])).

cnf(c_6911,plain,
    ( r1_tarski(k5_xboole_0(sK3,k5_xboole_0(sK4,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))),sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_21,c_753])).

cnf(c_12,plain,
    ( r1_tarski(X0,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_752,plain,
    ( r1_tarski(X0,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_6184,plain,
    ( r1_tarski(sK3,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_21,c_752])).

cnf(c_17,plain,
    ( ~ r1_tarski(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))
    | k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) = X0
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f93])).

cnf(c_749,plain,
    ( k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) = X1
    | k1_xboole_0 = X1
    | r1_tarski(X1,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_6562,plain,
    ( k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) = sK3
    | sK3 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_6184,c_749])).

cnf(c_6655,plain,
    ( k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) = X0
    | sK3 = k1_xboole_0
    | k1_xboole_0 = X0
    | r1_tarski(X0,sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_6562,c_749])).

cnf(c_7839,plain,
    ( k5_xboole_0(sK3,k5_xboole_0(sK4,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))) = k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)
    | k5_xboole_0(sK3,k5_xboole_0(sK4,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))) = k1_xboole_0
    | sK3 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_6911,c_6655])).

cnf(c_18,negated_conjecture,
    ( k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) != sK3
    | k1_xboole_0 != sK4 ),
    inference(cnf_transformation,[],[f94])).

cnf(c_6659,plain,
    ( sK3 = k1_xboole_0
    | sK4 != k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_6562,c_18])).

cnf(c_20,negated_conjecture,
    ( k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) != sK3
    | k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) != sK4 ),
    inference(cnf_transformation,[],[f96])).

cnf(c_6657,plain,
    ( k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) != sK4
    | sK3 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_6562,c_20])).

cnf(c_19,negated_conjecture,
    ( k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) != sK4
    | k1_xboole_0 != sK3 ),
    inference(cnf_transformation,[],[f95])).

cnf(c_791,plain,
    ( ~ r1_tarski(sK3,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))
    | k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) = sK3
    | k1_xboole_0 = sK3 ),
    inference(instantiation,[status(thm)],[c_17])).

cnf(c_793,plain,
    ( ~ r1_tarski(sK3,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))
    | k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) = sK3
    | k1_xboole_0 = sK3 ),
    inference(instantiation,[status(thm)],[c_791])).

cnf(c_420,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_924,plain,
    ( sK3 = sK3 ),
    inference(instantiation,[status(thm)],[c_420])).

cnf(c_425,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_836,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(sK3,k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2))
    | k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2) != X1
    | sK3 != X0 ),
    inference(instantiation,[status(thm)],[c_425])).

cnf(c_895,plain,
    ( ~ r1_tarski(sK3,X0)
    | r1_tarski(sK3,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))
    | k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) != X0
    | sK3 != sK3 ),
    inference(instantiation,[status(thm)],[c_836])).

cnf(c_1022,plain,
    ( r1_tarski(sK3,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))
    | ~ r1_tarski(sK3,k3_tarski(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,X1)))
    | k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) != k3_tarski(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,X1))
    | sK3 != sK3 ),
    inference(instantiation,[status(thm)],[c_895])).

cnf(c_3663,plain,
    ( r1_tarski(sK3,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))
    | ~ r1_tarski(sK3,k3_tarski(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4)))
    | k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) != k3_tarski(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4))
    | sK3 != sK3 ),
    inference(instantiation,[status(thm)],[c_1022])).

cnf(c_1355,plain,
    ( r1_tarski(sK3,k3_tarski(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,X0))) ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_5650,plain,
    ( r1_tarski(sK3,k3_tarski(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4))) ),
    inference(instantiation,[status(thm)],[c_1355])).

cnf(c_6749,plain,
    ( k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) != sK4 ),
    inference(global_propositional_subsumption,[status(thm)],[c_6657,c_21,c_20,c_19,c_793,c_924,c_3663,c_5650])).

cnf(c_7573,plain,
    ( sK3 = k1_xboole_0
    | r1_tarski(k5_xboole_0(sK3,k5_xboole_0(sK4,sK3)),sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_6562,c_6911])).

cnf(c_14,plain,
    ( k5_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f58])).

cnf(c_774,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(X1,k5_xboole_0(X0,X2)) ),
    inference(superposition,[status(thm)],[c_13,c_0])).

cnf(c_1300,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,X0)) = k5_xboole_0(X1,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_14,c_774])).

cnf(c_11,plain,
    ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f55])).

cnf(c_1317,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,X0)) = X1 ),
    inference(demodulation,[status(thm)],[c_1300,c_11])).

cnf(c_7574,plain,
    ( sK3 = k1_xboole_0
    | r1_tarski(sK4,sK3) = iProver_top ),
    inference(demodulation,[status(thm)],[c_7573,c_1317])).

cnf(c_7842,plain,
    ( k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) = sK4
    | sK3 = k1_xboole_0
    | sK4 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_7574,c_6655])).

cnf(c_7844,plain,
    ( sK3 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_7839,c_21,c_20,c_19,c_793,c_924,c_3663,c_5650,c_6659,c_7842])).

cnf(c_7849,plain,
    ( r1_tarski(k5_xboole_0(k1_xboole_0,k5_xboole_0(sK4,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))),k1_xboole_0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_7844,c_6911])).

cnf(c_775,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(X2,k5_xboole_0(X1,X0)) ),
    inference(superposition,[status(thm)],[c_13,c_0])).

cnf(c_1602,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(X0,X1)) = k5_xboole_0(X1,X0) ),
    inference(superposition,[status(thm)],[c_11,c_775])).

cnf(c_7856,plain,
    ( r1_tarski(k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK4),k1_xboole_0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_7849,c_1602])).

cnf(c_3,plain,
    ( ~ r1_tarski(X0,X1)
    | r2_xboole_0(X0,X1)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f47])).

cnf(c_758,plain,
    ( X0 = X1
    | r1_tarski(X1,X0) != iProver_top
    | r2_xboole_0(X1,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_52966,plain,
    ( k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK4) = k1_xboole_0
    | r2_xboole_0(k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK4),k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_7856,c_758])).

cnf(c_9,plain,
    ( r2_hidden(sK1(X0,X1),X1)
    | ~ r2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_754,plain,
    ( r2_hidden(sK1(X0,X1),X1) = iProver_top
    | r2_xboole_0(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_4,plain,
    ( k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) = X0 ),
    inference(cnf_transformation,[],[f85])).

cnf(c_6,plain,
    ( ~ r2_hidden(X0,k5_xboole_0(k5_xboole_0(X1,X2),k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))))
    | ~ r1_xboole_0(X1,X2) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_415,plain,
    ( ~ r2_hidden(X0,k5_xboole_0(X1,k5_xboole_0(X2,k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)))))
    | ~ r1_xboole_0(X1,X2) ),
    inference(theory_normalisation,[status(thm)],[c_6,c_13,c_0])).

cnf(c_757,plain,
    ( r2_hidden(X0,k5_xboole_0(X1,k5_xboole_0(X2,k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))))) != iProver_top
    | r1_xboole_0(X1,X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_415])).

cnf(c_10454,plain,
    ( r2_hidden(X0,k5_xboole_0(X1,k5_xboole_0(X1,X1))) != iProver_top
    | r1_xboole_0(X1,X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_4,c_757])).

cnf(c_1063,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X0,X1)) = k5_xboole_0(k1_xboole_0,X1) ),
    inference(superposition,[status(thm)],[c_14,c_13])).

cnf(c_985,plain,
    ( k5_xboole_0(k1_xboole_0,X0) = X0 ),
    inference(superposition,[status(thm)],[c_11,c_0])).

cnf(c_1070,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1 ),
    inference(demodulation,[status(thm)],[c_1063,c_985])).

cnf(c_10457,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r1_xboole_0(X1,X1) != iProver_top ),
    inference(demodulation,[status(thm)],[c_10454,c_1070])).

cnf(c_31208,plain,
    ( r2_xboole_0(X0,X1) != iProver_top
    | r1_xboole_0(X1,X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_754,c_10457])).

cnf(c_57082,plain,
    ( k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK4) = k1_xboole_0
    | r1_xboole_0(k1_xboole_0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_52966,c_31208])).

cnf(c_1,plain,
    ( r1_xboole_0(X0,X1)
    | k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f83])).

cnf(c_418,plain,
    ( r1_xboole_0(X0,X1)
    | k5_xboole_0(X0,k5_xboole_0(X1,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) != k1_xboole_0 ),
    inference(theory_normalisation,[status(thm)],[c_1,c_13,c_0])).

cnf(c_760,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) != k1_xboole_0
    | r1_xboole_0(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_418])).

cnf(c_16657,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X0,X0)) != k1_xboole_0
    | r1_xboole_0(X0,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_4,c_760])).

cnf(c_16660,plain,
    ( k1_xboole_0 != X0
    | r1_xboole_0(X0,X0) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_16657,c_11,c_14])).

cnf(c_16694,plain,
    ( r1_xboole_0(k1_xboole_0,k1_xboole_0) = iProver_top ),
    inference(equality_resolution,[status(thm)],[c_16660])).

cnf(c_57086,plain,
    ( k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK4) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_57082,c_16694])).

cnf(c_776,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(X1,k5_xboole_0(X2,X0)) ),
    inference(superposition,[status(thm)],[c_13,c_0])).

cnf(c_1943,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X1,k5_xboole_0(X2,X0))) = X2 ),
    inference(superposition,[status(thm)],[c_776,c_1317])).

cnf(c_20257,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,X2)),k5_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(X3,X0)))) = X3 ),
    inference(superposition,[status(thm)],[c_13,c_1943])).

cnf(c_57257,plain,
    ( k5_xboole_0(k5_xboole_0(sK4,k5_xboole_0(X0,X1)),k5_xboole_0(X0,k5_xboole_0(X1,k1_xboole_0))) = k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) ),
    inference(superposition,[status(thm)],[c_57086,c_20257])).

cnf(c_1414,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),X1) = X0 ),
    inference(superposition,[status(thm)],[c_1070,c_1317])).

cnf(c_1457,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X2,X1)) = k5_xboole_0(X2,X0) ),
    inference(superposition,[status(thm)],[c_1414,c_774])).

cnf(c_4355,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,X2)),k5_xboole_0(X1,k5_xboole_0(X2,X3))) = k5_xboole_0(X3,X0) ),
    inference(superposition,[status(thm)],[c_776,c_1457])).

cnf(c_57258,plain,
    ( k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) = sK4 ),
    inference(demodulation,[status(thm)],[c_57257,c_985,c_4355])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_57258,c_6749])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n009.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 20:20:26 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 12.09/1.99  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 12.09/1.99  
% 12.09/1.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 12.09/1.99  
% 12.09/1.99  ------  iProver source info
% 12.09/1.99  
% 12.09/1.99  git: date: 2020-06-30 10:37:57 +0100
% 12.09/1.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 12.09/1.99  git: non_committed_changes: false
% 12.09/1.99  git: last_make_outside_of_git: false
% 12.09/1.99  
% 12.09/1.99  ------ 
% 12.09/1.99  
% 12.09/1.99  ------ Input Options
% 12.09/1.99  
% 12.09/1.99  --out_options                           all
% 12.09/1.99  --tptp_safe_out                         true
% 12.09/1.99  --problem_path                          ""
% 12.09/1.99  --include_path                          ""
% 12.09/1.99  --clausifier                            res/vclausify_rel
% 12.09/1.99  --clausifier_options                    ""
% 12.09/1.99  --stdin                                 false
% 12.09/1.99  --stats_out                             all
% 12.09/1.99  
% 12.09/1.99  ------ General Options
% 12.09/1.99  
% 12.09/1.99  --fof                                   false
% 12.09/1.99  --time_out_real                         305.
% 12.09/1.99  --time_out_virtual                      -1.
% 12.09/1.99  --symbol_type_check                     false
% 12.09/1.99  --clausify_out                          false
% 12.09/1.99  --sig_cnt_out                           false
% 12.09/1.99  --trig_cnt_out                          false
% 12.09/1.99  --trig_cnt_out_tolerance                1.
% 12.09/1.99  --trig_cnt_out_sk_spl                   false
% 12.09/1.99  --abstr_cl_out                          false
% 12.09/1.99  
% 12.09/1.99  ------ Global Options
% 12.09/1.99  
% 12.09/1.99  --schedule                              default
% 12.09/1.99  --add_important_lit                     false
% 12.09/1.99  --prop_solver_per_cl                    1000
% 12.09/1.99  --min_unsat_core                        false
% 12.09/1.99  --soft_assumptions                      false
% 12.09/1.99  --soft_lemma_size                       3
% 12.09/1.99  --prop_impl_unit_size                   0
% 12.09/1.99  --prop_impl_unit                        []
% 12.09/1.99  --share_sel_clauses                     true
% 12.09/1.99  --reset_solvers                         false
% 12.09/1.99  --bc_imp_inh                            [conj_cone]
% 12.09/1.99  --conj_cone_tolerance                   3.
% 12.09/1.99  --extra_neg_conj                        none
% 12.09/1.99  --large_theory_mode                     true
% 12.09/1.99  --prolific_symb_bound                   200
% 12.09/1.99  --lt_threshold                          2000
% 12.09/1.99  --clause_weak_htbl                      true
% 12.09/1.99  --gc_record_bc_elim                     false
% 12.09/1.99  
% 12.09/1.99  ------ Preprocessing Options
% 12.09/1.99  
% 12.09/1.99  --preprocessing_flag                    true
% 12.09/1.99  --time_out_prep_mult                    0.1
% 12.09/1.99  --splitting_mode                        input
% 12.09/1.99  --splitting_grd                         true
% 12.09/1.99  --splitting_cvd                         false
% 12.09/1.99  --splitting_cvd_svl                     false
% 12.09/1.99  --splitting_nvd                         32
% 12.09/1.99  --sub_typing                            true
% 12.09/1.99  --prep_gs_sim                           true
% 12.09/1.99  --prep_unflatten                        true
% 12.09/1.99  --prep_res_sim                          true
% 12.09/1.99  --prep_upred                            true
% 12.09/1.99  --prep_sem_filter                       exhaustive
% 12.09/1.99  --prep_sem_filter_out                   false
% 12.09/1.99  --pred_elim                             true
% 12.09/1.99  --res_sim_input                         true
% 12.09/1.99  --eq_ax_congr_red                       true
% 12.09/1.99  --pure_diseq_elim                       true
% 12.09/1.99  --brand_transform                       false
% 12.09/1.99  --non_eq_to_eq                          false
% 12.09/1.99  --prep_def_merge                        true
% 12.09/1.99  --prep_def_merge_prop_impl              false
% 12.09/1.99  --prep_def_merge_mbd                    true
% 12.09/1.99  --prep_def_merge_tr_red                 false
% 12.09/1.99  --prep_def_merge_tr_cl                  false
% 12.09/1.99  --smt_preprocessing                     true
% 12.09/1.99  --smt_ac_axioms                         fast
% 12.09/1.99  --preprocessed_out                      false
% 12.09/1.99  --preprocessed_stats                    false
% 12.09/1.99  
% 12.09/1.99  ------ Abstraction refinement Options
% 12.09/1.99  
% 12.09/1.99  --abstr_ref                             []
% 12.09/1.99  --abstr_ref_prep                        false
% 12.09/1.99  --abstr_ref_until_sat                   false
% 12.09/1.99  --abstr_ref_sig_restrict                funpre
% 12.09/1.99  --abstr_ref_af_restrict_to_split_sk     false
% 12.09/1.99  --abstr_ref_under                       []
% 12.09/1.99  
% 12.09/1.99  ------ SAT Options
% 12.09/1.99  
% 12.09/1.99  --sat_mode                              false
% 12.09/1.99  --sat_fm_restart_options                ""
% 12.09/1.99  --sat_gr_def                            false
% 12.09/1.99  --sat_epr_types                         true
% 12.09/1.99  --sat_non_cyclic_types                  false
% 12.09/1.99  --sat_finite_models                     false
% 12.09/1.99  --sat_fm_lemmas                         false
% 12.09/1.99  --sat_fm_prep                           false
% 12.09/1.99  --sat_fm_uc_incr                        true
% 12.09/1.99  --sat_out_model                         small
% 12.09/1.99  --sat_out_clauses                       false
% 12.09/1.99  
% 12.09/1.99  ------ QBF Options
% 12.09/1.99  
% 12.09/1.99  --qbf_mode                              false
% 12.09/1.99  --qbf_elim_univ                         false
% 12.09/1.99  --qbf_dom_inst                          none
% 12.09/1.99  --qbf_dom_pre_inst                      false
% 12.09/1.99  --qbf_sk_in                             false
% 12.09/1.99  --qbf_pred_elim                         true
% 12.09/1.99  --qbf_split                             512
% 12.09/1.99  
% 12.09/1.99  ------ BMC1 Options
% 12.09/1.99  
% 12.09/1.99  --bmc1_incremental                      false
% 12.09/1.99  --bmc1_axioms                           reachable_all
% 12.09/1.99  --bmc1_min_bound                        0
% 12.09/1.99  --bmc1_max_bound                        -1
% 12.09/1.99  --bmc1_max_bound_default                -1
% 12.09/1.99  --bmc1_symbol_reachability              true
% 12.09/1.99  --bmc1_property_lemmas                  false
% 12.09/1.99  --bmc1_k_induction                      false
% 12.09/1.99  --bmc1_non_equiv_states                 false
% 12.09/1.99  --bmc1_deadlock                         false
% 12.09/1.99  --bmc1_ucm                              false
% 12.09/1.99  --bmc1_add_unsat_core                   none
% 12.09/1.99  --bmc1_unsat_core_children              false
% 12.09/1.99  --bmc1_unsat_core_extrapolate_axioms    false
% 12.09/1.99  --bmc1_out_stat                         full
% 12.09/1.99  --bmc1_ground_init                      false
% 12.09/1.99  --bmc1_pre_inst_next_state              false
% 12.09/1.99  --bmc1_pre_inst_state                   false
% 12.09/1.99  --bmc1_pre_inst_reach_state             false
% 12.09/1.99  --bmc1_out_unsat_core                   false
% 12.09/1.99  --bmc1_aig_witness_out                  false
% 12.09/1.99  --bmc1_verbose                          false
% 12.09/1.99  --bmc1_dump_clauses_tptp                false
% 12.09/1.99  --bmc1_dump_unsat_core_tptp             false
% 12.09/1.99  --bmc1_dump_file                        -
% 12.09/1.99  --bmc1_ucm_expand_uc_limit              128
% 12.09/1.99  --bmc1_ucm_n_expand_iterations          6
% 12.09/1.99  --bmc1_ucm_extend_mode                  1
% 12.09/1.99  --bmc1_ucm_init_mode                    2
% 12.09/1.99  --bmc1_ucm_cone_mode                    none
% 12.09/1.99  --bmc1_ucm_reduced_relation_type        0
% 12.09/1.99  --bmc1_ucm_relax_model                  4
% 12.09/1.99  --bmc1_ucm_full_tr_after_sat            true
% 12.09/1.99  --bmc1_ucm_expand_neg_assumptions       false
% 12.09/1.99  --bmc1_ucm_layered_model                none
% 12.09/1.99  --bmc1_ucm_max_lemma_size               10
% 12.09/1.99  
% 12.09/1.99  ------ AIG Options
% 12.09/1.99  
% 12.09/1.99  --aig_mode                              false
% 12.09/1.99  
% 12.09/1.99  ------ Instantiation Options
% 12.09/1.99  
% 12.09/1.99  --instantiation_flag                    true
% 12.09/1.99  --inst_sos_flag                         true
% 12.09/1.99  --inst_sos_phase                        true
% 12.09/1.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 12.09/1.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 12.09/1.99  --inst_lit_sel_side                     num_symb
% 12.09/1.99  --inst_solver_per_active                1400
% 12.09/1.99  --inst_solver_calls_frac                1.
% 12.09/1.99  --inst_passive_queue_type               priority_queues
% 12.09/1.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 12.09/1.99  --inst_passive_queues_freq              [25;2]
% 12.09/1.99  --inst_dismatching                      true
% 12.09/1.99  --inst_eager_unprocessed_to_passive     true
% 12.09/1.99  --inst_prop_sim_given                   true
% 12.09/1.99  --inst_prop_sim_new                     false
% 12.09/1.99  --inst_subs_new                         false
% 12.09/1.99  --inst_eq_res_simp                      false
% 12.09/1.99  --inst_subs_given                       false
% 12.09/1.99  --inst_orphan_elimination               true
% 12.09/1.99  --inst_learning_loop_flag               true
% 12.09/1.99  --inst_learning_start                   3000
% 12.09/1.99  --inst_learning_factor                  2
% 12.09/1.99  --inst_start_prop_sim_after_learn       3
% 12.09/1.99  --inst_sel_renew                        solver
% 12.09/1.99  --inst_lit_activity_flag                true
% 12.09/1.99  --inst_restr_to_given                   false
% 12.09/1.99  --inst_activity_threshold               500
% 12.09/1.99  --inst_out_proof                        true
% 12.09/1.99  
% 12.09/1.99  ------ Resolution Options
% 12.09/1.99  
% 12.09/1.99  --resolution_flag                       true
% 12.09/1.99  --res_lit_sel                           adaptive
% 12.09/1.99  --res_lit_sel_side                      none
% 12.09/1.99  --res_ordering                          kbo
% 12.09/1.99  --res_to_prop_solver                    active
% 12.09/1.99  --res_prop_simpl_new                    false
% 12.09/1.99  --res_prop_simpl_given                  true
% 12.09/1.99  --res_passive_queue_type                priority_queues
% 12.09/1.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 12.09/1.99  --res_passive_queues_freq               [15;5]
% 12.09/1.99  --res_forward_subs                      full
% 12.09/1.99  --res_backward_subs                     full
% 12.09/1.99  --res_forward_subs_resolution           true
% 12.09/1.99  --res_backward_subs_resolution          true
% 12.09/1.99  --res_orphan_elimination                true
% 12.09/1.99  --res_time_limit                        2.
% 12.09/1.99  --res_out_proof                         true
% 12.09/1.99  
% 12.09/1.99  ------ Superposition Options
% 12.09/1.99  
% 12.09/1.99  --superposition_flag                    true
% 12.09/1.99  --sup_passive_queue_type                priority_queues
% 12.09/1.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 12.09/1.99  --sup_passive_queues_freq               [8;1;4]
% 12.09/1.99  --demod_completeness_check              fast
% 12.09/1.99  --demod_use_ground                      true
% 12.09/1.99  --sup_to_prop_solver                    passive
% 12.09/1.99  --sup_prop_simpl_new                    true
% 12.09/1.99  --sup_prop_simpl_given                  true
% 12.09/1.99  --sup_fun_splitting                     true
% 12.09/1.99  --sup_smt_interval                      50000
% 12.09/1.99  
% 12.09/1.99  ------ Superposition Simplification Setup
% 12.09/1.99  
% 12.09/1.99  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 12.09/1.99  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 12.09/1.99  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 12.09/1.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 12.09/1.99  --sup_full_triv                         [TrivRules;PropSubs]
% 12.09/1.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 12.09/1.99  --sup_full_bw                           [BwDemod;BwSubsumption]
% 12.09/1.99  --sup_immed_triv                        [TrivRules]
% 12.09/1.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 12.09/1.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 12.09/1.99  --sup_immed_bw_main                     []
% 12.09/1.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 12.09/1.99  --sup_input_triv                        [Unflattening;TrivRules]
% 12.09/1.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 12.09/1.99  --sup_input_bw                          []
% 12.09/1.99  
% 12.09/1.99  ------ Combination Options
% 12.09/1.99  
% 12.09/1.99  --comb_res_mult                         3
% 12.09/1.99  --comb_sup_mult                         2
% 12.09/1.99  --comb_inst_mult                        10
% 12.09/1.99  
% 12.09/1.99  ------ Debug Options
% 12.09/1.99  
% 12.09/1.99  --dbg_backtrace                         false
% 12.09/1.99  --dbg_dump_prop_clauses                 false
% 12.09/1.99  --dbg_dump_prop_clauses_file            -
% 12.09/1.99  --dbg_out_stat                          false
% 12.09/1.99  ------ Parsing...
% 12.09/1.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 12.09/1.99  
% 12.09/1.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 12.09/1.99  
% 12.09/1.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 12.09/1.99  
% 12.09/1.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 12.09/1.99  ------ Proving...
% 12.09/1.99  ------ Problem Properties 
% 12.09/1.99  
% 12.09/1.99  
% 12.09/1.99  clauses                                 22
% 12.09/1.99  conjectures                             4
% 12.09/1.99  EPR                                     1
% 12.09/1.99  Horn                                    19
% 12.09/1.99  unary                                   11
% 12.09/1.99  binary                                  9
% 12.09/1.99  lits                                    35
% 12.09/1.99  lits eq                                 18
% 12.09/1.99  fd_pure                                 0
% 12.09/1.99  fd_pseudo                               0
% 12.09/1.99  fd_cond                                 0
% 12.09/1.99  fd_pseudo_cond                          2
% 12.09/1.99  AC symbols                              1
% 12.09/1.99  
% 12.09/1.99  ------ Schedule dynamic 5 is on 
% 12.09/1.99  
% 12.09/1.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 12.09/1.99  
% 12.09/1.99  
% 12.09/1.99  ------ 
% 12.09/1.99  Current options:
% 12.09/1.99  ------ 
% 12.09/1.99  
% 12.09/1.99  ------ Input Options
% 12.09/1.99  
% 12.09/1.99  --out_options                           all
% 12.09/1.99  --tptp_safe_out                         true
% 12.09/1.99  --problem_path                          ""
% 12.09/1.99  --include_path                          ""
% 12.09/1.99  --clausifier                            res/vclausify_rel
% 12.09/1.99  --clausifier_options                    ""
% 12.09/1.99  --stdin                                 false
% 12.09/1.99  --stats_out                             all
% 12.09/1.99  
% 12.09/1.99  ------ General Options
% 12.09/1.99  
% 12.09/1.99  --fof                                   false
% 12.09/1.99  --time_out_real                         305.
% 12.09/1.99  --time_out_virtual                      -1.
% 12.09/1.99  --symbol_type_check                     false
% 12.09/1.99  --clausify_out                          false
% 12.09/1.99  --sig_cnt_out                           false
% 12.09/1.99  --trig_cnt_out                          false
% 12.09/1.99  --trig_cnt_out_tolerance                1.
% 12.09/1.99  --trig_cnt_out_sk_spl                   false
% 12.09/1.99  --abstr_cl_out                          false
% 12.09/1.99  
% 12.09/1.99  ------ Global Options
% 12.09/1.99  
% 12.09/1.99  --schedule                              default
% 12.09/1.99  --add_important_lit                     false
% 12.09/1.99  --prop_solver_per_cl                    1000
% 12.09/1.99  --min_unsat_core                        false
% 12.09/1.99  --soft_assumptions                      false
% 12.09/1.99  --soft_lemma_size                       3
% 12.09/1.99  --prop_impl_unit_size                   0
% 12.09/1.99  --prop_impl_unit                        []
% 12.09/1.99  --share_sel_clauses                     true
% 12.09/1.99  --reset_solvers                         false
% 12.09/1.99  --bc_imp_inh                            [conj_cone]
% 12.09/1.99  --conj_cone_tolerance                   3.
% 12.09/1.99  --extra_neg_conj                        none
% 12.09/1.99  --large_theory_mode                     true
% 12.09/1.99  --prolific_symb_bound                   200
% 12.09/1.99  --lt_threshold                          2000
% 12.09/1.99  --clause_weak_htbl                      true
% 12.09/1.99  --gc_record_bc_elim                     false
% 12.09/1.99  
% 12.09/1.99  ------ Preprocessing Options
% 12.09/1.99  
% 12.09/1.99  --preprocessing_flag                    true
% 12.09/1.99  --time_out_prep_mult                    0.1
% 12.09/1.99  --splitting_mode                        input
% 12.09/1.99  --splitting_grd                         true
% 12.09/1.99  --splitting_cvd                         false
% 12.09/1.99  --splitting_cvd_svl                     false
% 12.09/1.99  --splitting_nvd                         32
% 12.09/1.99  --sub_typing                            true
% 12.09/1.99  --prep_gs_sim                           true
% 12.09/1.99  --prep_unflatten                        true
% 12.09/1.99  --prep_res_sim                          true
% 12.09/1.99  --prep_upred                            true
% 12.09/1.99  --prep_sem_filter                       exhaustive
% 12.09/1.99  --prep_sem_filter_out                   false
% 12.09/1.99  --pred_elim                             true
% 12.09/1.99  --res_sim_input                         true
% 12.09/1.99  --eq_ax_congr_red                       true
% 12.09/1.99  --pure_diseq_elim                       true
% 12.09/1.99  --brand_transform                       false
% 12.09/1.99  --non_eq_to_eq                          false
% 12.09/1.99  --prep_def_merge                        true
% 12.09/1.99  --prep_def_merge_prop_impl              false
% 12.09/1.99  --prep_def_merge_mbd                    true
% 12.09/1.99  --prep_def_merge_tr_red                 false
% 12.09/1.99  --prep_def_merge_tr_cl                  false
% 12.09/1.99  --smt_preprocessing                     true
% 12.09/1.99  --smt_ac_axioms                         fast
% 12.09/1.99  --preprocessed_out                      false
% 12.09/1.99  --preprocessed_stats                    false
% 12.09/1.99  
% 12.09/1.99  ------ Abstraction refinement Options
% 12.09/1.99  
% 12.09/1.99  --abstr_ref                             []
% 12.09/1.99  --abstr_ref_prep                        false
% 12.09/1.99  --abstr_ref_until_sat                   false
% 12.09/1.99  --abstr_ref_sig_restrict                funpre
% 12.09/1.99  --abstr_ref_af_restrict_to_split_sk     false
% 12.09/1.99  --abstr_ref_under                       []
% 12.09/1.99  
% 12.09/1.99  ------ SAT Options
% 12.09/1.99  
% 12.09/1.99  --sat_mode                              false
% 12.09/1.99  --sat_fm_restart_options                ""
% 12.09/1.99  --sat_gr_def                            false
% 12.09/1.99  --sat_epr_types                         true
% 12.09/1.99  --sat_non_cyclic_types                  false
% 12.09/1.99  --sat_finite_models                     false
% 12.09/1.99  --sat_fm_lemmas                         false
% 12.09/1.99  --sat_fm_prep                           false
% 12.09/1.99  --sat_fm_uc_incr                        true
% 12.09/1.99  --sat_out_model                         small
% 12.09/1.99  --sat_out_clauses                       false
% 12.09/1.99  
% 12.09/1.99  ------ QBF Options
% 12.09/1.99  
% 12.09/1.99  --qbf_mode                              false
% 12.09/1.99  --qbf_elim_univ                         false
% 12.09/1.99  --qbf_dom_inst                          none
% 12.09/1.99  --qbf_dom_pre_inst                      false
% 12.09/1.99  --qbf_sk_in                             false
% 12.09/1.99  --qbf_pred_elim                         true
% 12.09/1.99  --qbf_split                             512
% 12.09/1.99  
% 12.09/1.99  ------ BMC1 Options
% 12.09/1.99  
% 12.09/1.99  --bmc1_incremental                      false
% 12.09/1.99  --bmc1_axioms                           reachable_all
% 12.09/1.99  --bmc1_min_bound                        0
% 12.09/1.99  --bmc1_max_bound                        -1
% 12.09/1.99  --bmc1_max_bound_default                -1
% 12.09/1.99  --bmc1_symbol_reachability              true
% 12.09/1.99  --bmc1_property_lemmas                  false
% 12.09/1.99  --bmc1_k_induction                      false
% 12.09/1.99  --bmc1_non_equiv_states                 false
% 12.09/1.99  --bmc1_deadlock                         false
% 12.09/1.99  --bmc1_ucm                              false
% 12.09/1.99  --bmc1_add_unsat_core                   none
% 12.09/1.99  --bmc1_unsat_core_children              false
% 12.09/1.99  --bmc1_unsat_core_extrapolate_axioms    false
% 12.09/1.99  --bmc1_out_stat                         full
% 12.09/1.99  --bmc1_ground_init                      false
% 12.09/1.99  --bmc1_pre_inst_next_state              false
% 12.09/1.99  --bmc1_pre_inst_state                   false
% 12.09/1.99  --bmc1_pre_inst_reach_state             false
% 12.09/1.99  --bmc1_out_unsat_core                   false
% 12.09/1.99  --bmc1_aig_witness_out                  false
% 12.09/1.99  --bmc1_verbose                          false
% 12.09/1.99  --bmc1_dump_clauses_tptp                false
% 12.09/1.99  --bmc1_dump_unsat_core_tptp             false
% 12.09/1.99  --bmc1_dump_file                        -
% 12.09/1.99  --bmc1_ucm_expand_uc_limit              128
% 12.09/1.99  --bmc1_ucm_n_expand_iterations          6
% 12.09/1.99  --bmc1_ucm_extend_mode                  1
% 12.09/1.99  --bmc1_ucm_init_mode                    2
% 12.09/1.99  --bmc1_ucm_cone_mode                    none
% 12.09/1.99  --bmc1_ucm_reduced_relation_type        0
% 12.09/1.99  --bmc1_ucm_relax_model                  4
% 12.09/1.99  --bmc1_ucm_full_tr_after_sat            true
% 12.09/1.99  --bmc1_ucm_expand_neg_assumptions       false
% 12.09/1.99  --bmc1_ucm_layered_model                none
% 12.09/1.99  --bmc1_ucm_max_lemma_size               10
% 12.09/1.99  
% 12.09/1.99  ------ AIG Options
% 12.09/1.99  
% 12.09/1.99  --aig_mode                              false
% 12.09/1.99  
% 12.09/1.99  ------ Instantiation Options
% 12.09/1.99  
% 12.09/1.99  --instantiation_flag                    true
% 12.09/1.99  --inst_sos_flag                         true
% 12.09/1.99  --inst_sos_phase                        true
% 12.09/1.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 12.09/1.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 12.09/1.99  --inst_lit_sel_side                     none
% 12.09/1.99  --inst_solver_per_active                1400
% 12.09/1.99  --inst_solver_calls_frac                1.
% 12.09/1.99  --inst_passive_queue_type               priority_queues
% 12.09/1.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 12.09/1.99  --inst_passive_queues_freq              [25;2]
% 12.09/1.99  --inst_dismatching                      true
% 12.09/1.99  --inst_eager_unprocessed_to_passive     true
% 12.09/1.99  --inst_prop_sim_given                   true
% 12.09/1.99  --inst_prop_sim_new                     false
% 12.09/1.99  --inst_subs_new                         false
% 12.09/1.99  --inst_eq_res_simp                      false
% 12.09/1.99  --inst_subs_given                       false
% 12.09/1.99  --inst_orphan_elimination               true
% 12.09/1.99  --inst_learning_loop_flag               true
% 12.09/1.99  --inst_learning_start                   3000
% 12.09/1.99  --inst_learning_factor                  2
% 12.09/1.99  --inst_start_prop_sim_after_learn       3
% 12.09/1.99  --inst_sel_renew                        solver
% 12.09/1.99  --inst_lit_activity_flag                true
% 12.09/1.99  --inst_restr_to_given                   false
% 12.09/1.99  --inst_activity_threshold               500
% 12.09/1.99  --inst_out_proof                        true
% 12.09/1.99  
% 12.09/1.99  ------ Resolution Options
% 12.09/1.99  
% 12.09/1.99  --resolution_flag                       false
% 12.09/1.99  --res_lit_sel                           adaptive
% 12.09/1.99  --res_lit_sel_side                      none
% 12.09/1.99  --res_ordering                          kbo
% 12.09/1.99  --res_to_prop_solver                    active
% 12.09/1.99  --res_prop_simpl_new                    false
% 12.09/1.99  --res_prop_simpl_given                  true
% 12.09/1.99  --res_passive_queue_type                priority_queues
% 12.09/1.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 12.09/1.99  --res_passive_queues_freq               [15;5]
% 12.09/1.99  --res_forward_subs                      full
% 12.09/1.99  --res_backward_subs                     full
% 12.09/1.99  --res_forward_subs_resolution           true
% 12.09/1.99  --res_backward_subs_resolution          true
% 12.09/1.99  --res_orphan_elimination                true
% 12.09/1.99  --res_time_limit                        2.
% 12.09/1.99  --res_out_proof                         true
% 12.09/1.99  
% 12.09/1.99  ------ Superposition Options
% 12.09/1.99  
% 12.09/1.99  --superposition_flag                    true
% 12.09/1.99  --sup_passive_queue_type                priority_queues
% 12.09/1.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 12.09/1.99  --sup_passive_queues_freq               [8;1;4]
% 12.09/1.99  --demod_completeness_check              fast
% 12.09/1.99  --demod_use_ground                      true
% 12.09/1.99  --sup_to_prop_solver                    passive
% 12.09/1.99  --sup_prop_simpl_new                    true
% 12.09/1.99  --sup_prop_simpl_given                  true
% 12.09/1.99  --sup_fun_splitting                     true
% 12.09/1.99  --sup_smt_interval                      50000
% 12.09/1.99  
% 12.09/1.99  ------ Superposition Simplification Setup
% 12.09/1.99  
% 12.09/1.99  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 12.09/1.99  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 12.09/1.99  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 12.09/1.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 12.09/1.99  --sup_full_triv                         [TrivRules;PropSubs]
% 12.09/1.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 12.09/1.99  --sup_full_bw                           [BwDemod;BwSubsumption]
% 12.09/1.99  --sup_immed_triv                        [TrivRules]
% 12.09/1.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 12.09/1.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 12.09/1.99  --sup_immed_bw_main                     []
% 12.09/1.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 12.09/1.99  --sup_input_triv                        [Unflattening;TrivRules]
% 12.09/1.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 12.09/1.99  --sup_input_bw                          []
% 12.09/1.99  
% 12.09/1.99  ------ Combination Options
% 12.09/1.99  
% 12.09/1.99  --comb_res_mult                         3
% 12.09/1.99  --comb_sup_mult                         2
% 12.09/1.99  --comb_inst_mult                        10
% 12.09/1.99  
% 12.09/1.99  ------ Debug Options
% 12.09/1.99  
% 12.09/1.99  --dbg_backtrace                         false
% 12.09/1.99  --dbg_dump_prop_clauses                 false
% 12.09/1.99  --dbg_dump_prop_clauses_file            -
% 12.09/1.99  --dbg_out_stat                          false
% 12.09/1.99  
% 12.09/1.99  
% 12.09/1.99  
% 12.09/1.99  
% 12.09/1.99  ------ Proving...
% 12.09/1.99  
% 12.09/1.99  
% 12.09/1.99  % SZS status Theorem for theBenchmark.p
% 12.09/1.99  
% 12.09/1.99  % SZS output start CNFRefutation for theBenchmark.p
% 12.09/1.99  
% 12.09/1.99  fof(f24,conjecture,(
% 12.09/1.99    ! [X0,X1,X2] : ~(~(k1_xboole_0 = X2 & k1_tarski(X0) = X1) & ~(k1_tarski(X0) = X2 & k1_xboole_0 = X1) & ~(k1_tarski(X0) = X2 & k1_tarski(X0) = X1) & k2_xboole_0(X1,X2) = k1_tarski(X0))),
% 12.09/1.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 12.09/1.99  
% 12.09/1.99  fof(f25,negated_conjecture,(
% 12.09/1.99    ~! [X0,X1,X2] : ~(~(k1_xboole_0 = X2 & k1_tarski(X0) = X1) & ~(k1_tarski(X0) = X2 & k1_xboole_0 = X1) & ~(k1_tarski(X0) = X2 & k1_tarski(X0) = X1) & k2_xboole_0(X1,X2) = k1_tarski(X0))),
% 12.09/1.99    inference(negated_conjecture,[],[f24])).
% 12.09/1.99  
% 12.09/1.99  fof(f34,plain,(
% 12.09/1.99    ? [X0,X1,X2] : ((k1_xboole_0 != X2 | k1_tarski(X0) != X1) & (k1_tarski(X0) != X2 | k1_xboole_0 != X1) & (k1_tarski(X0) != X2 | k1_tarski(X0) != X1) & k2_xboole_0(X1,X2) = k1_tarski(X0))),
% 12.09/1.99    inference(ennf_transformation,[],[f25])).
% 12.09/1.99  
% 12.09/1.99  fof(f42,plain,(
% 12.09/1.99    ? [X0,X1,X2] : ((k1_xboole_0 != X2 | k1_tarski(X0) != X1) & (k1_tarski(X0) != X2 | k1_xboole_0 != X1) & (k1_tarski(X0) != X2 | k1_tarski(X0) != X1) & k2_xboole_0(X1,X2) = k1_tarski(X0)) => ((k1_xboole_0 != sK4 | k1_tarski(sK2) != sK3) & (k1_tarski(sK2) != sK4 | k1_xboole_0 != sK3) & (k1_tarski(sK2) != sK4 | k1_tarski(sK2) != sK3) & k2_xboole_0(sK3,sK4) = k1_tarski(sK2))),
% 12.09/1.99    introduced(choice_axiom,[])).
% 12.09/1.99  
% 12.09/1.99  fof(f43,plain,(
% 12.09/1.99    (k1_xboole_0 != sK4 | k1_tarski(sK2) != sK3) & (k1_tarski(sK2) != sK4 | k1_xboole_0 != sK3) & (k1_tarski(sK2) != sK4 | k1_tarski(sK2) != sK3) & k2_xboole_0(sK3,sK4) = k1_tarski(sK2)),
% 12.09/1.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f34,f42])).
% 12.09/1.99  
% 12.09/1.99  fof(f71,plain,(
% 12.09/1.99    k2_xboole_0(sK3,sK4) = k1_tarski(sK2)),
% 12.09/1.99    inference(cnf_transformation,[],[f43])).
% 12.09/1.99  
% 12.09/1.99  fof(f23,axiom,(
% 12.09/1.99    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 12.09/1.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 12.09/1.99  
% 12.09/1.99  fof(f70,plain,(
% 12.09/1.99    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 12.09/1.99    inference(cnf_transformation,[],[f23])).
% 12.09/1.99  
% 12.09/1.99  fof(f80,plain,(
% 12.09/1.99    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) )),
% 12.09/1.99    inference(definition_unfolding,[],[f70,f79])).
% 12.09/1.99  
% 12.09/1.99  fof(f15,axiom,(
% 12.09/1.99    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 12.09/1.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 12.09/1.99  
% 12.09/1.99  fof(f60,plain,(
% 12.09/1.99    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 12.09/1.99    inference(cnf_transformation,[],[f15])).
% 12.09/1.99  
% 12.09/1.99  fof(f16,axiom,(
% 12.09/1.99    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 12.09/1.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 12.09/1.99  
% 12.09/1.99  fof(f61,plain,(
% 12.09/1.99    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 12.09/1.99    inference(cnf_transformation,[],[f16])).
% 12.09/1.99  
% 12.09/1.99  fof(f17,axiom,(
% 12.09/1.99    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 12.09/1.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 12.09/1.99  
% 12.09/1.99  fof(f62,plain,(
% 12.09/1.99    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 12.09/1.99    inference(cnf_transformation,[],[f17])).
% 12.09/1.99  
% 12.09/1.99  fof(f18,axiom,(
% 12.09/1.99    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 12.09/1.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 12.09/1.99  
% 12.09/1.99  fof(f63,plain,(
% 12.09/1.99    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 12.09/1.99    inference(cnf_transformation,[],[f18])).
% 12.09/1.99  
% 12.09/1.99  fof(f19,axiom,(
% 12.09/1.99    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)),
% 12.09/1.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 12.09/1.99  
% 12.09/1.99  fof(f64,plain,(
% 12.09/1.99    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)) )),
% 12.09/1.99    inference(cnf_transformation,[],[f19])).
% 12.09/1.99  
% 12.09/1.99  fof(f20,axiom,(
% 12.09/1.99    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)),
% 12.09/1.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 12.09/1.99  
% 12.09/1.99  fof(f65,plain,(
% 12.09/1.99    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)) )),
% 12.09/1.99    inference(cnf_transformation,[],[f20])).
% 12.09/1.99  
% 12.09/1.99  fof(f21,axiom,(
% 12.09/1.99    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)),
% 12.09/1.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 12.09/1.99  
% 12.09/1.99  fof(f66,plain,(
% 12.09/1.99    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)) )),
% 12.09/1.99    inference(cnf_transformation,[],[f21])).
% 12.09/1.99  
% 12.09/1.99  fof(f75,plain,(
% 12.09/1.99    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 12.09/1.99    inference(definition_unfolding,[],[f65,f66])).
% 12.09/1.99  
% 12.09/1.99  fof(f76,plain,(
% 12.09/1.99    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 12.09/1.99    inference(definition_unfolding,[],[f64,f75])).
% 12.09/1.99  
% 12.09/1.99  fof(f77,plain,(
% 12.09/1.99    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 12.09/1.99    inference(definition_unfolding,[],[f63,f76])).
% 12.09/1.99  
% 12.09/1.99  fof(f78,plain,(
% 12.09/1.99    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 12.09/1.99    inference(definition_unfolding,[],[f62,f77])).
% 12.09/1.99  
% 12.09/1.99  fof(f79,plain,(
% 12.09/1.99    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 12.09/1.99    inference(definition_unfolding,[],[f61,f78])).
% 12.09/1.99  
% 12.09/1.99  fof(f82,plain,(
% 12.09/1.99    ( ! [X0] : (k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) )),
% 12.09/1.99    inference(definition_unfolding,[],[f60,f79])).
% 12.09/1.99  
% 12.09/1.99  fof(f97,plain,(
% 12.09/1.99    k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) = k3_tarski(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4))),
% 12.09/1.99    inference(definition_unfolding,[],[f71,f80,f82])).
% 12.09/1.99  
% 12.09/1.99  fof(f9,axiom,(
% 12.09/1.99    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 12.09/1.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 12.09/1.99  
% 12.09/1.99  fof(f54,plain,(
% 12.09/1.99    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 12.09/2.00    inference(cnf_transformation,[],[f9])).
% 12.09/2.00  
% 12.09/2.00  fof(f14,axiom,(
% 12.09/2.00    ! [X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)),
% 12.09/2.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 12.09/2.00  
% 12.09/2.00  fof(f59,plain,(
% 12.09/2.00    ( ! [X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)) )),
% 12.09/2.00    inference(cnf_transformation,[],[f14])).
% 12.09/2.00  
% 12.09/2.00  fof(f81,plain,(
% 12.09/2.00    ( ! [X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) = k3_xboole_0(X0,X1)) )),
% 12.09/2.00    inference(definition_unfolding,[],[f59,f80])).
% 12.09/2.00  
% 12.09/2.00  fof(f89,plain,(
% 12.09/2.00    ( ! [X0,X1] : (r1_tarski(k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))),X0)) )),
% 12.09/2.00    inference(definition_unfolding,[],[f54,f81])).
% 12.09/2.00  
% 12.09/2.00  fof(f12,axiom,(
% 12.09/2.00    ! [X0,X1,X2] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2)),
% 12.09/2.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 12.09/2.00  
% 12.09/2.00  fof(f57,plain,(
% 12.09/2.00    ( ! [X2,X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2)) )),
% 12.09/2.00    inference(cnf_transformation,[],[f12])).
% 12.09/2.00  
% 12.09/2.00  fof(f1,axiom,(
% 12.09/2.00    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)),
% 12.09/2.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 12.09/2.00  
% 12.09/2.00  fof(f44,plain,(
% 12.09/2.00    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)) )),
% 12.09/2.00    inference(cnf_transformation,[],[f1])).
% 12.09/2.00  
% 12.09/2.00  fof(f11,axiom,(
% 12.09/2.00    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 12.09/2.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 12.09/2.00  
% 12.09/2.00  fof(f56,plain,(
% 12.09/2.00    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 12.09/2.00    inference(cnf_transformation,[],[f11])).
% 12.09/2.00  
% 12.09/2.00  fof(f90,plain,(
% 12.09/2.00    ( ! [X0,X1] : (r1_tarski(X0,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) )),
% 12.09/2.00    inference(definition_unfolding,[],[f56,f80])).
% 12.09/2.00  
% 12.09/2.00  fof(f22,axiom,(
% 12.09/2.00    ! [X0,X1] : (r1_tarski(X0,k1_tarski(X1)) <=> (k1_tarski(X1) = X0 | k1_xboole_0 = X0))),
% 12.09/2.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 12.09/2.00  
% 12.09/2.00  fof(f40,plain,(
% 12.09/2.00    ! [X0,X1] : ((r1_tarski(X0,k1_tarski(X1)) | (k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & ((k1_tarski(X1) = X0 | k1_xboole_0 = X0) | ~r1_tarski(X0,k1_tarski(X1))))),
% 12.09/2.00    inference(nnf_transformation,[],[f22])).
% 12.09/2.00  
% 12.09/2.00  fof(f41,plain,(
% 12.09/2.00    ! [X0,X1] : ((r1_tarski(X0,k1_tarski(X1)) | (k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & (k1_tarski(X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k1_tarski(X1))))),
% 12.09/2.00    inference(flattening,[],[f40])).
% 12.09/2.00  
% 12.09/2.00  fof(f67,plain,(
% 12.09/2.00    ( ! [X0,X1] : (k1_tarski(X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k1_tarski(X1))) )),
% 12.09/2.00    inference(cnf_transformation,[],[f41])).
% 12.09/2.00  
% 12.09/2.00  fof(f93,plain,(
% 12.09/2.00    ( ! [X0,X1] : (k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))) )),
% 12.09/2.00    inference(definition_unfolding,[],[f67,f82,f82])).
% 12.09/2.00  
% 12.09/2.00  fof(f74,plain,(
% 12.09/2.00    k1_xboole_0 != sK4 | k1_tarski(sK2) != sK3),
% 12.09/2.00    inference(cnf_transformation,[],[f43])).
% 12.09/2.00  
% 12.09/2.00  fof(f94,plain,(
% 12.09/2.00    k1_xboole_0 != sK4 | k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) != sK3),
% 12.09/2.00    inference(definition_unfolding,[],[f74,f82])).
% 12.09/2.00  
% 12.09/2.00  fof(f72,plain,(
% 12.09/2.00    k1_tarski(sK2) != sK4 | k1_tarski(sK2) != sK3),
% 12.09/2.00    inference(cnf_transformation,[],[f43])).
% 12.09/2.00  
% 12.09/2.00  fof(f96,plain,(
% 12.09/2.00    k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) != sK4 | k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) != sK3),
% 12.09/2.00    inference(definition_unfolding,[],[f72,f82,f82])).
% 12.09/2.00  
% 12.09/2.00  fof(f73,plain,(
% 12.09/2.00    k1_tarski(sK2) != sK4 | k1_xboole_0 != sK3),
% 12.09/2.00    inference(cnf_transformation,[],[f43])).
% 12.09/2.00  
% 12.09/2.00  fof(f95,plain,(
% 12.09/2.00    k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) != sK4 | k1_xboole_0 != sK3),
% 12.09/2.00    inference(definition_unfolding,[],[f73,f82])).
% 12.09/2.00  
% 12.09/2.00  fof(f13,axiom,(
% 12.09/2.00    ! [X0] : k5_xboole_0(X0,X0) = k1_xboole_0),
% 12.09/2.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 12.09/2.00  
% 12.09/2.00  fof(f58,plain,(
% 12.09/2.00    ( ! [X0] : (k5_xboole_0(X0,X0) = k1_xboole_0) )),
% 12.09/2.00    inference(cnf_transformation,[],[f13])).
% 12.09/2.00  
% 12.09/2.00  fof(f10,axiom,(
% 12.09/2.00    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 12.09/2.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 12.09/2.00  
% 12.09/2.00  fof(f55,plain,(
% 12.09/2.00    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 12.09/2.00    inference(cnf_transformation,[],[f10])).
% 12.09/2.00  
% 12.09/2.00  fof(f4,axiom,(
% 12.09/2.00    ! [X0,X1] : (r2_xboole_0(X0,X1) <=> (X0 != X1 & r1_tarski(X0,X1)))),
% 12.09/2.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 12.09/2.00  
% 12.09/2.00  fof(f29,plain,(
% 12.09/2.00    ! [X0,X1] : ((X0 != X1 & r1_tarski(X0,X1)) => r2_xboole_0(X0,X1))),
% 12.09/2.00    inference(unused_predicate_definition_removal,[],[f4])).
% 12.09/2.00  
% 12.09/2.00  fof(f30,plain,(
% 12.09/2.00    ! [X0,X1] : (r2_xboole_0(X0,X1) | (X0 = X1 | ~r1_tarski(X0,X1)))),
% 12.09/2.00    inference(ennf_transformation,[],[f29])).
% 12.09/2.00  
% 12.09/2.00  fof(f31,plain,(
% 12.09/2.00    ! [X0,X1] : (r2_xboole_0(X0,X1) | X0 = X1 | ~r1_tarski(X0,X1))),
% 12.09/2.00    inference(flattening,[],[f30])).
% 12.09/2.00  
% 12.09/2.00  fof(f47,plain,(
% 12.09/2.00    ( ! [X0,X1] : (r2_xboole_0(X0,X1) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 12.09/2.00    inference(cnf_transformation,[],[f31])).
% 12.09/2.00  
% 12.09/2.00  fof(f8,axiom,(
% 12.09/2.00    ! [X0,X1] : ~(! [X2] : ~(~r2_hidden(X2,X0) & r2_hidden(X2,X1)) & r2_xboole_0(X0,X1))),
% 12.09/2.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 12.09/2.00  
% 12.09/2.00  fof(f33,plain,(
% 12.09/2.00    ! [X0,X1] : (? [X2] : (~r2_hidden(X2,X0) & r2_hidden(X2,X1)) | ~r2_xboole_0(X0,X1))),
% 12.09/2.00    inference(ennf_transformation,[],[f8])).
% 12.09/2.00  
% 12.09/2.00  fof(f38,plain,(
% 12.09/2.00    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X0) & r2_hidden(X2,X1)) => (~r2_hidden(sK1(X0,X1),X0) & r2_hidden(sK1(X0,X1),X1)))),
% 12.09/2.00    introduced(choice_axiom,[])).
% 12.09/2.00  
% 12.09/2.00  fof(f39,plain,(
% 12.09/2.00    ! [X0,X1] : ((~r2_hidden(sK1(X0,X1),X0) & r2_hidden(sK1(X0,X1),X1)) | ~r2_xboole_0(X0,X1))),
% 12.09/2.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f33,f38])).
% 12.09/2.00  
% 12.09/2.00  fof(f52,plain,(
% 12.09/2.00    ( ! [X0,X1] : (r2_hidden(sK1(X0,X1),X1) | ~r2_xboole_0(X0,X1)) )),
% 12.09/2.00    inference(cnf_transformation,[],[f39])).
% 12.09/2.00  
% 12.09/2.00  fof(f5,axiom,(
% 12.09/2.00    ! [X0,X1] : k2_xboole_0(X0,X0) = X0),
% 12.09/2.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 12.09/2.00  
% 12.09/2.00  fof(f26,plain,(
% 12.09/2.00    ! [X0] : k2_xboole_0(X0,X0) = X0),
% 12.09/2.00    inference(rectify,[],[f5])).
% 12.09/2.00  
% 12.09/2.00  fof(f48,plain,(
% 12.09/2.00    ( ! [X0] : (k2_xboole_0(X0,X0) = X0) )),
% 12.09/2.00    inference(cnf_transformation,[],[f26])).
% 12.09/2.00  
% 12.09/2.00  fof(f85,plain,(
% 12.09/2.00    ( ! [X0] : (k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) = X0) )),
% 12.09/2.00    inference(definition_unfolding,[],[f48,f80])).
% 12.09/2.00  
% 12.09/2.00  fof(f7,axiom,(
% 12.09/2.00    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 12.09/2.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 12.09/2.00  
% 12.09/2.00  fof(f28,plain,(
% 12.09/2.00    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X3] : ~r2_hidden(X3,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 12.09/2.00    inference(rectify,[],[f7])).
% 12.09/2.00  
% 12.09/2.00  fof(f32,plain,(
% 12.09/2.00    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 12.09/2.00    inference(ennf_transformation,[],[f28])).
% 12.09/2.00  
% 12.09/2.00  fof(f36,plain,(
% 12.09/2.00    ! [X1,X0] : (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) => r2_hidden(sK0(X0,X1),k3_xboole_0(X0,X1)))),
% 12.09/2.00    introduced(choice_axiom,[])).
% 12.09/2.00  
% 12.09/2.00  fof(f37,plain,(
% 12.09/2.00    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (r2_hidden(sK0(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 12.09/2.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f32,f36])).
% 12.09/2.00  
% 12.09/2.00  fof(f51,plain,(
% 12.09/2.00    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,k3_xboole_0(X0,X1))) )),
% 12.09/2.00    inference(cnf_transformation,[],[f37])).
% 12.09/2.00  
% 12.09/2.00  fof(f87,plain,(
% 12.09/2.00    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))))) )),
% 12.09/2.00    inference(definition_unfolding,[],[f51,f81])).
% 12.09/2.00  
% 12.09/2.00  fof(f3,axiom,(
% 12.09/2.00    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 12.09/2.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 12.09/2.00  
% 12.09/2.00  fof(f35,plain,(
% 12.09/2.00    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) & (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)))),
% 12.09/2.00    inference(nnf_transformation,[],[f3])).
% 12.09/2.00  
% 12.09/2.00  fof(f46,plain,(
% 12.09/2.00    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) )),
% 12.09/2.00    inference(cnf_transformation,[],[f35])).
% 12.09/2.00  
% 12.09/2.00  fof(f83,plain,(
% 12.09/2.00    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) != k1_xboole_0) )),
% 12.09/2.00    inference(definition_unfolding,[],[f46,f81])).
% 12.09/2.00  
% 12.09/2.00  cnf(c_21,negated_conjecture,
% 12.09/2.00      ( k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) = k3_tarski(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4)) ),
% 12.09/2.00      inference(cnf_transformation,[],[f97]) ).
% 12.09/2.00  
% 12.09/2.00  cnf(c_10,plain,
% 12.09/2.00      ( r1_tarski(k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))),X0) ),
% 12.09/2.00      inference(cnf_transformation,[],[f89]) ).
% 12.09/2.00  
% 12.09/2.00  cnf(c_13,plain,
% 12.09/2.00      ( k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
% 12.09/2.00      inference(cnf_transformation,[],[f57]) ).
% 12.09/2.00  
% 12.09/2.00  cnf(c_0,plain,
% 12.09/2.00      ( k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
% 12.09/2.00      inference(cnf_transformation,[],[f44]) ).
% 12.09/2.00  
% 12.09/2.00  cnf(c_413,plain,
% 12.09/2.00      ( r1_tarski(k5_xboole_0(X0,k5_xboole_0(X1,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))),X0) ),
% 12.09/2.00      inference(theory_normalisation,[status(thm)],[c_10,c_13,c_0]) ).
% 12.09/2.00  
% 12.09/2.00  cnf(c_753,plain,
% 12.09/2.00      ( r1_tarski(k5_xboole_0(X0,k5_xboole_0(X1,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))),X0) = iProver_top ),
% 12.09/2.00      inference(predicate_to_equality,[status(thm)],[c_413]) ).
% 12.09/2.00  
% 12.09/2.00  cnf(c_6911,plain,
% 12.09/2.00      ( r1_tarski(k5_xboole_0(sK3,k5_xboole_0(sK4,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))),sK3) = iProver_top ),
% 12.09/2.00      inference(superposition,[status(thm)],[c_21,c_753]) ).
% 12.09/2.00  
% 12.09/2.00  cnf(c_12,plain,
% 12.09/2.00      ( r1_tarski(X0,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) ),
% 12.09/2.00      inference(cnf_transformation,[],[f90]) ).
% 12.09/2.00  
% 12.09/2.00  cnf(c_752,plain,
% 12.09/2.00      ( r1_tarski(X0,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) = iProver_top ),
% 12.09/2.00      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 12.09/2.00  
% 12.09/2.00  cnf(c_6184,plain,
% 12.09/2.00      ( r1_tarski(sK3,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)) = iProver_top ),
% 12.09/2.00      inference(superposition,[status(thm)],[c_21,c_752]) ).
% 12.09/2.00  
% 12.09/2.00  cnf(c_17,plain,
% 12.09/2.00      ( ~ r1_tarski(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))
% 12.09/2.00      | k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) = X0
% 12.09/2.00      | k1_xboole_0 = X0 ),
% 12.09/2.00      inference(cnf_transformation,[],[f93]) ).
% 12.09/2.00  
% 12.09/2.00  cnf(c_749,plain,
% 12.09/2.00      ( k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) = X1
% 12.09/2.00      | k1_xboole_0 = X1
% 12.09/2.00      | r1_tarski(X1,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) != iProver_top ),
% 12.09/2.00      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 12.09/2.00  
% 12.09/2.00  cnf(c_6562,plain,
% 12.09/2.00      ( k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) = sK3
% 12.09/2.00      | sK3 = k1_xboole_0 ),
% 12.09/2.00      inference(superposition,[status(thm)],[c_6184,c_749]) ).
% 12.09/2.00  
% 12.09/2.00  cnf(c_6655,plain,
% 12.09/2.00      ( k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) = X0
% 12.09/2.00      | sK3 = k1_xboole_0
% 12.09/2.00      | k1_xboole_0 = X0
% 12.09/2.00      | r1_tarski(X0,sK3) != iProver_top ),
% 12.09/2.00      inference(superposition,[status(thm)],[c_6562,c_749]) ).
% 12.09/2.00  
% 12.09/2.00  cnf(c_7839,plain,
% 12.09/2.00      ( k5_xboole_0(sK3,k5_xboole_0(sK4,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))) = k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)
% 12.09/2.00      | k5_xboole_0(sK3,k5_xboole_0(sK4,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))) = k1_xboole_0
% 12.09/2.00      | sK3 = k1_xboole_0 ),
% 12.09/2.00      inference(superposition,[status(thm)],[c_6911,c_6655]) ).
% 12.09/2.00  
% 12.09/2.00  cnf(c_18,negated_conjecture,
% 12.09/2.00      ( k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) != sK3
% 12.09/2.00      | k1_xboole_0 != sK4 ),
% 12.09/2.00      inference(cnf_transformation,[],[f94]) ).
% 12.09/2.00  
% 12.09/2.00  cnf(c_6659,plain,
% 12.09/2.00      ( sK3 = k1_xboole_0 | sK4 != k1_xboole_0 ),
% 12.09/2.00      inference(superposition,[status(thm)],[c_6562,c_18]) ).
% 12.09/2.00  
% 12.09/2.00  cnf(c_20,negated_conjecture,
% 12.09/2.00      ( k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) != sK3
% 12.09/2.00      | k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) != sK4 ),
% 12.09/2.00      inference(cnf_transformation,[],[f96]) ).
% 12.09/2.00  
% 12.09/2.00  cnf(c_6657,plain,
% 12.09/2.00      ( k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) != sK4
% 12.09/2.00      | sK3 = k1_xboole_0 ),
% 12.09/2.00      inference(superposition,[status(thm)],[c_6562,c_20]) ).
% 12.09/2.00  
% 12.09/2.00  cnf(c_19,negated_conjecture,
% 12.09/2.00      ( k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) != sK4
% 12.09/2.00      | k1_xboole_0 != sK3 ),
% 12.09/2.00      inference(cnf_transformation,[],[f95]) ).
% 12.09/2.00  
% 12.09/2.00  cnf(c_791,plain,
% 12.09/2.00      ( ~ r1_tarski(sK3,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))
% 12.09/2.00      | k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) = sK3
% 12.09/2.00      | k1_xboole_0 = sK3 ),
% 12.09/2.00      inference(instantiation,[status(thm)],[c_17]) ).
% 12.09/2.00  
% 12.09/2.00  cnf(c_793,plain,
% 12.09/2.00      ( ~ r1_tarski(sK3,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))
% 12.09/2.00      | k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) = sK3
% 12.09/2.00      | k1_xboole_0 = sK3 ),
% 12.09/2.00      inference(instantiation,[status(thm)],[c_791]) ).
% 12.09/2.00  
% 12.09/2.00  cnf(c_420,plain,( X0 = X0 ),theory(equality) ).
% 12.09/2.00  
% 12.09/2.00  cnf(c_924,plain,
% 12.09/2.00      ( sK3 = sK3 ),
% 12.09/2.00      inference(instantiation,[status(thm)],[c_420]) ).
% 12.09/2.00  
% 12.09/2.00  cnf(c_425,plain,
% 12.09/2.00      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,X3) | X2 != X0 | X3 != X1 ),
% 12.09/2.00      theory(equality) ).
% 12.09/2.00  
% 12.09/2.00  cnf(c_836,plain,
% 12.09/2.00      ( ~ r1_tarski(X0,X1)
% 12.09/2.00      | r1_tarski(sK3,k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2))
% 12.09/2.00      | k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2) != X1
% 12.09/2.00      | sK3 != X0 ),
% 12.09/2.00      inference(instantiation,[status(thm)],[c_425]) ).
% 12.09/2.00  
% 12.09/2.00  cnf(c_895,plain,
% 12.09/2.00      ( ~ r1_tarski(sK3,X0)
% 12.09/2.00      | r1_tarski(sK3,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))
% 12.09/2.00      | k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) != X0
% 12.09/2.00      | sK3 != sK3 ),
% 12.09/2.00      inference(instantiation,[status(thm)],[c_836]) ).
% 12.09/2.00  
% 12.09/2.00  cnf(c_1022,plain,
% 12.09/2.00      ( r1_tarski(sK3,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))
% 12.09/2.00      | ~ r1_tarski(sK3,k3_tarski(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,X1)))
% 12.09/2.00      | k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) != k3_tarski(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,X1))
% 12.09/2.00      | sK3 != sK3 ),
% 12.09/2.00      inference(instantiation,[status(thm)],[c_895]) ).
% 12.09/2.00  
% 12.09/2.00  cnf(c_3663,plain,
% 12.09/2.00      ( r1_tarski(sK3,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))
% 12.09/2.00      | ~ r1_tarski(sK3,k3_tarski(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4)))
% 12.09/2.00      | k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) != k3_tarski(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4))
% 12.09/2.00      | sK3 != sK3 ),
% 12.09/2.00      inference(instantiation,[status(thm)],[c_1022]) ).
% 12.09/2.00  
% 12.09/2.00  cnf(c_1355,plain,
% 12.09/2.00      ( r1_tarski(sK3,k3_tarski(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,X0))) ),
% 12.09/2.00      inference(instantiation,[status(thm)],[c_12]) ).
% 12.09/2.00  
% 12.09/2.00  cnf(c_5650,plain,
% 12.09/2.00      ( r1_tarski(sK3,k3_tarski(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4))) ),
% 12.09/2.00      inference(instantiation,[status(thm)],[c_1355]) ).
% 12.09/2.00  
% 12.09/2.00  cnf(c_6749,plain,
% 12.09/2.00      ( k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) != sK4 ),
% 12.09/2.00      inference(global_propositional_subsumption,
% 12.09/2.00                [status(thm)],
% 12.09/2.00                [c_6657,c_21,c_20,c_19,c_793,c_924,c_3663,c_5650]) ).
% 12.09/2.00  
% 12.09/2.00  cnf(c_7573,plain,
% 12.09/2.00      ( sK3 = k1_xboole_0
% 12.09/2.00      | r1_tarski(k5_xboole_0(sK3,k5_xboole_0(sK4,sK3)),sK3) = iProver_top ),
% 12.09/2.00      inference(superposition,[status(thm)],[c_6562,c_6911]) ).
% 12.09/2.00  
% 12.09/2.00  cnf(c_14,plain,
% 12.09/2.00      ( k5_xboole_0(X0,X0) = k1_xboole_0 ),
% 12.09/2.00      inference(cnf_transformation,[],[f58]) ).
% 12.09/2.00  
% 12.09/2.00  cnf(c_774,plain,
% 12.09/2.00      ( k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(X1,k5_xboole_0(X0,X2)) ),
% 12.09/2.00      inference(superposition,[status(thm)],[c_13,c_0]) ).
% 12.09/2.00  
% 12.09/2.00  cnf(c_1300,plain,
% 12.09/2.00      ( k5_xboole_0(X0,k5_xboole_0(X1,X0)) = k5_xboole_0(X1,k1_xboole_0) ),
% 12.09/2.00      inference(superposition,[status(thm)],[c_14,c_774]) ).
% 12.09/2.00  
% 12.09/2.00  cnf(c_11,plain,
% 12.09/2.00      ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
% 12.09/2.00      inference(cnf_transformation,[],[f55]) ).
% 12.09/2.00  
% 12.09/2.00  cnf(c_1317,plain,
% 12.09/2.00      ( k5_xboole_0(X0,k5_xboole_0(X1,X0)) = X1 ),
% 12.09/2.00      inference(demodulation,[status(thm)],[c_1300,c_11]) ).
% 12.09/2.00  
% 12.09/2.00  cnf(c_7574,plain,
% 12.09/2.00      ( sK3 = k1_xboole_0 | r1_tarski(sK4,sK3) = iProver_top ),
% 12.09/2.00      inference(demodulation,[status(thm)],[c_7573,c_1317]) ).
% 12.09/2.00  
% 12.09/2.00  cnf(c_7842,plain,
% 12.09/2.00      ( k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) = sK4
% 12.09/2.00      | sK3 = k1_xboole_0
% 12.09/2.00      | sK4 = k1_xboole_0 ),
% 12.09/2.00      inference(superposition,[status(thm)],[c_7574,c_6655]) ).
% 12.09/2.00  
% 12.09/2.00  cnf(c_7844,plain,
% 12.09/2.00      ( sK3 = k1_xboole_0 ),
% 12.09/2.00      inference(global_propositional_subsumption,
% 12.09/2.00                [status(thm)],
% 12.09/2.00                [c_7839,c_21,c_20,c_19,c_793,c_924,c_3663,c_5650,c_6659,
% 12.09/2.00                 c_7842]) ).
% 12.09/2.00  
% 12.09/2.00  cnf(c_7849,plain,
% 12.09/2.00      ( r1_tarski(k5_xboole_0(k1_xboole_0,k5_xboole_0(sK4,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))),k1_xboole_0) = iProver_top ),
% 12.09/2.00      inference(demodulation,[status(thm)],[c_7844,c_6911]) ).
% 12.09/2.00  
% 12.09/2.00  cnf(c_775,plain,
% 12.09/2.00      ( k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(X2,k5_xboole_0(X1,X0)) ),
% 12.09/2.00      inference(superposition,[status(thm)],[c_13,c_0]) ).
% 12.09/2.00  
% 12.09/2.00  cnf(c_1602,plain,
% 12.09/2.00      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(X0,X1)) = k5_xboole_0(X1,X0) ),
% 12.09/2.00      inference(superposition,[status(thm)],[c_11,c_775]) ).
% 12.09/2.00  
% 12.09/2.00  cnf(c_7856,plain,
% 12.09/2.00      ( r1_tarski(k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK4),k1_xboole_0) = iProver_top ),
% 12.09/2.00      inference(demodulation,[status(thm)],[c_7849,c_1602]) ).
% 12.09/2.00  
% 12.09/2.00  cnf(c_3,plain,
% 12.09/2.00      ( ~ r1_tarski(X0,X1) | r2_xboole_0(X0,X1) | X1 = X0 ),
% 12.09/2.00      inference(cnf_transformation,[],[f47]) ).
% 12.09/2.00  
% 12.09/2.00  cnf(c_758,plain,
% 12.09/2.00      ( X0 = X1
% 12.09/2.00      | r1_tarski(X1,X0) != iProver_top
% 12.09/2.00      | r2_xboole_0(X1,X0) = iProver_top ),
% 12.09/2.00      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 12.09/2.00  
% 12.09/2.00  cnf(c_52966,plain,
% 12.09/2.00      ( k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK4) = k1_xboole_0
% 12.09/2.00      | r2_xboole_0(k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK4),k1_xboole_0) = iProver_top ),
% 12.09/2.00      inference(superposition,[status(thm)],[c_7856,c_758]) ).
% 12.09/2.00  
% 12.09/2.00  cnf(c_9,plain,
% 12.09/2.00      ( r2_hidden(sK1(X0,X1),X1) | ~ r2_xboole_0(X0,X1) ),
% 12.09/2.00      inference(cnf_transformation,[],[f52]) ).
% 12.09/2.00  
% 12.09/2.00  cnf(c_754,plain,
% 12.09/2.00      ( r2_hidden(sK1(X0,X1),X1) = iProver_top
% 12.09/2.00      | r2_xboole_0(X0,X1) != iProver_top ),
% 12.09/2.00      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 12.09/2.00  
% 12.09/2.00  cnf(c_4,plain,
% 12.09/2.00      ( k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) = X0 ),
% 12.09/2.00      inference(cnf_transformation,[],[f85]) ).
% 12.09/2.00  
% 12.09/2.00  cnf(c_6,plain,
% 12.09/2.00      ( ~ r2_hidden(X0,k5_xboole_0(k5_xboole_0(X1,X2),k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))))
% 12.09/2.00      | ~ r1_xboole_0(X1,X2) ),
% 12.09/2.00      inference(cnf_transformation,[],[f87]) ).
% 12.09/2.00  
% 12.09/2.00  cnf(c_415,plain,
% 12.09/2.00      ( ~ r2_hidden(X0,k5_xboole_0(X1,k5_xboole_0(X2,k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)))))
% 12.09/2.00      | ~ r1_xboole_0(X1,X2) ),
% 12.09/2.00      inference(theory_normalisation,[status(thm)],[c_6,c_13,c_0]) ).
% 12.09/2.00  
% 12.09/2.00  cnf(c_757,plain,
% 12.09/2.00      ( r2_hidden(X0,k5_xboole_0(X1,k5_xboole_0(X2,k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))))) != iProver_top
% 12.09/2.00      | r1_xboole_0(X1,X2) != iProver_top ),
% 12.09/2.00      inference(predicate_to_equality,[status(thm)],[c_415]) ).
% 12.09/2.00  
% 12.09/2.00  cnf(c_10454,plain,
% 12.09/2.00      ( r2_hidden(X0,k5_xboole_0(X1,k5_xboole_0(X1,X1))) != iProver_top
% 12.09/2.00      | r1_xboole_0(X1,X1) != iProver_top ),
% 12.09/2.00      inference(superposition,[status(thm)],[c_4,c_757]) ).
% 12.09/2.00  
% 12.09/2.00  cnf(c_1063,plain,
% 12.09/2.00      ( k5_xboole_0(X0,k5_xboole_0(X0,X1)) = k5_xboole_0(k1_xboole_0,X1) ),
% 12.09/2.00      inference(superposition,[status(thm)],[c_14,c_13]) ).
% 12.09/2.00  
% 12.09/2.00  cnf(c_985,plain,
% 12.09/2.00      ( k5_xboole_0(k1_xboole_0,X0) = X0 ),
% 12.09/2.00      inference(superposition,[status(thm)],[c_11,c_0]) ).
% 12.09/2.00  
% 12.09/2.00  cnf(c_1070,plain,
% 12.09/2.00      ( k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1 ),
% 12.09/2.00      inference(demodulation,[status(thm)],[c_1063,c_985]) ).
% 12.09/2.00  
% 12.09/2.00  cnf(c_10457,plain,
% 12.09/2.00      ( r2_hidden(X0,X1) != iProver_top
% 12.09/2.00      | r1_xboole_0(X1,X1) != iProver_top ),
% 12.09/2.00      inference(demodulation,[status(thm)],[c_10454,c_1070]) ).
% 12.09/2.00  
% 12.09/2.00  cnf(c_31208,plain,
% 12.09/2.00      ( r2_xboole_0(X0,X1) != iProver_top
% 12.09/2.00      | r1_xboole_0(X1,X1) != iProver_top ),
% 12.09/2.00      inference(superposition,[status(thm)],[c_754,c_10457]) ).
% 12.09/2.00  
% 12.09/2.00  cnf(c_57082,plain,
% 12.09/2.00      ( k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK4) = k1_xboole_0
% 12.09/2.00      | r1_xboole_0(k1_xboole_0,k1_xboole_0) != iProver_top ),
% 12.09/2.00      inference(superposition,[status(thm)],[c_52966,c_31208]) ).
% 12.09/2.00  
% 12.09/2.00  cnf(c_1,plain,
% 12.09/2.00      ( r1_xboole_0(X0,X1)
% 12.09/2.00      | k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) != k1_xboole_0 ),
% 12.09/2.00      inference(cnf_transformation,[],[f83]) ).
% 12.09/2.00  
% 12.09/2.00  cnf(c_418,plain,
% 12.09/2.00      ( r1_xboole_0(X0,X1)
% 12.09/2.00      | k5_xboole_0(X0,k5_xboole_0(X1,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) != k1_xboole_0 ),
% 12.09/2.00      inference(theory_normalisation,[status(thm)],[c_1,c_13,c_0]) ).
% 12.09/2.00  
% 12.09/2.00  cnf(c_760,plain,
% 12.09/2.00      ( k5_xboole_0(X0,k5_xboole_0(X1,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) != k1_xboole_0
% 12.09/2.00      | r1_xboole_0(X0,X1) = iProver_top ),
% 12.09/2.00      inference(predicate_to_equality,[status(thm)],[c_418]) ).
% 12.09/2.00  
% 12.09/2.00  cnf(c_16657,plain,
% 12.09/2.00      ( k5_xboole_0(X0,k5_xboole_0(X0,X0)) != k1_xboole_0
% 12.09/2.00      | r1_xboole_0(X0,X0) = iProver_top ),
% 12.09/2.00      inference(superposition,[status(thm)],[c_4,c_760]) ).
% 12.09/2.00  
% 12.09/2.00  cnf(c_16660,plain,
% 12.09/2.00      ( k1_xboole_0 != X0 | r1_xboole_0(X0,X0) = iProver_top ),
% 12.09/2.00      inference(light_normalisation,[status(thm)],[c_16657,c_11,c_14]) ).
% 12.09/2.00  
% 12.09/2.00  cnf(c_16694,plain,
% 12.09/2.00      ( r1_xboole_0(k1_xboole_0,k1_xboole_0) = iProver_top ),
% 12.09/2.00      inference(equality_resolution,[status(thm)],[c_16660]) ).
% 12.09/2.00  
% 12.09/2.00  cnf(c_57086,plain,
% 12.09/2.00      ( k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK4) = k1_xboole_0 ),
% 12.09/2.00      inference(global_propositional_subsumption,
% 12.09/2.00                [status(thm)],
% 12.09/2.00                [c_57082,c_16694]) ).
% 12.09/2.00  
% 12.09/2.00  cnf(c_776,plain,
% 12.09/2.00      ( k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(X1,k5_xboole_0(X2,X0)) ),
% 12.09/2.00      inference(superposition,[status(thm)],[c_13,c_0]) ).
% 12.09/2.00  
% 12.09/2.00  cnf(c_1943,plain,
% 12.09/2.00      ( k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X1,k5_xboole_0(X2,X0))) = X2 ),
% 12.09/2.00      inference(superposition,[status(thm)],[c_776,c_1317]) ).
% 12.09/2.00  
% 12.09/2.00  cnf(c_20257,plain,
% 12.09/2.00      ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,X2)),k5_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(X3,X0)))) = X3 ),
% 12.09/2.00      inference(superposition,[status(thm)],[c_13,c_1943]) ).
% 12.09/2.00  
% 12.09/2.00  cnf(c_57257,plain,
% 12.09/2.00      ( k5_xboole_0(k5_xboole_0(sK4,k5_xboole_0(X0,X1)),k5_xboole_0(X0,k5_xboole_0(X1,k1_xboole_0))) = k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) ),
% 12.09/2.00      inference(superposition,[status(thm)],[c_57086,c_20257]) ).
% 12.09/2.00  
% 12.09/2.00  cnf(c_1414,plain,
% 12.09/2.00      ( k5_xboole_0(k5_xboole_0(X0,X1),X1) = X0 ),
% 12.09/2.00      inference(superposition,[status(thm)],[c_1070,c_1317]) ).
% 12.09/2.00  
% 12.09/2.00  cnf(c_1457,plain,
% 12.09/2.00      ( k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X2,X1)) = k5_xboole_0(X2,X0) ),
% 12.09/2.00      inference(superposition,[status(thm)],[c_1414,c_774]) ).
% 12.09/2.00  
% 12.09/2.00  cnf(c_4355,plain,
% 12.09/2.00      ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,X2)),k5_xboole_0(X1,k5_xboole_0(X2,X3))) = k5_xboole_0(X3,X0) ),
% 12.09/2.00      inference(superposition,[status(thm)],[c_776,c_1457]) ).
% 12.09/2.00  
% 12.09/2.00  cnf(c_57258,plain,
% 12.09/2.00      ( k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) = sK4 ),
% 12.09/2.00      inference(demodulation,[status(thm)],[c_57257,c_985,c_4355]) ).
% 12.09/2.00  
% 12.09/2.00  cnf(contradiction,plain,
% 12.09/2.00      ( $false ),
% 12.09/2.00      inference(minisat,[status(thm)],[c_57258,c_6749]) ).
% 12.09/2.00  
% 12.09/2.00  
% 12.09/2.00  % SZS output end CNFRefutation for theBenchmark.p
% 12.09/2.00  
% 12.09/2.00  ------                               Statistics
% 12.09/2.00  
% 12.09/2.00  ------ General
% 12.09/2.00  
% 12.09/2.00  abstr_ref_over_cycles:                  0
% 12.09/2.00  abstr_ref_under_cycles:                 0
% 12.09/2.00  gc_basic_clause_elim:                   0
% 12.09/2.00  forced_gc_time:                         0
% 12.09/2.00  parsing_time:                           0.009
% 12.09/2.00  unif_index_cands_time:                  0.
% 12.09/2.00  unif_index_add_time:                    0.
% 12.09/2.00  orderings_time:                         0.
% 12.09/2.00  out_proof_time:                         0.012
% 12.09/2.00  total_time:                             1.496
% 12.09/2.00  num_of_symbols:                         44
% 12.09/2.00  num_of_terms:                           126473
% 12.09/2.00  
% 12.09/2.00  ------ Preprocessing
% 12.09/2.00  
% 12.09/2.00  num_of_splits:                          0
% 12.09/2.00  num_of_split_atoms:                     0
% 12.09/2.00  num_of_reused_defs:                     0
% 12.09/2.00  num_eq_ax_congr_red:                    16
% 12.09/2.00  num_of_sem_filtered_clauses:            1
% 12.09/2.00  num_of_subtypes:                        0
% 12.09/2.00  monotx_restored_types:                  0
% 12.09/2.00  sat_num_of_epr_types:                   0
% 12.09/2.00  sat_num_of_non_cyclic_types:            0
% 12.09/2.00  sat_guarded_non_collapsed_types:        0
% 12.09/2.00  num_pure_diseq_elim:                    0
% 12.09/2.00  simp_replaced_by:                       0
% 12.09/2.00  res_preprocessed:                       81
% 12.09/2.00  prep_upred:                             0
% 12.09/2.00  prep_unflattend:                        22
% 12.09/2.00  smt_new_axioms:                         0
% 12.09/2.00  pred_elim_cands:                        4
% 12.09/2.00  pred_elim:                              0
% 12.09/2.00  pred_elim_cl:                           0
% 12.09/2.00  pred_elim_cycles:                       4
% 12.09/2.00  merged_defs:                            6
% 12.09/2.00  merged_defs_ncl:                        0
% 12.09/2.00  bin_hyper_res:                          6
% 12.09/2.00  prep_cycles:                            3
% 12.09/2.00  pred_elim_time:                         0.004
% 12.09/2.00  splitting_time:                         0.
% 12.09/2.00  sem_filter_time:                        0.
% 12.09/2.00  monotx_time:                            0.003
% 12.09/2.00  subtype_inf_time:                       0.
% 12.09/2.00  
% 12.09/2.00  ------ Problem properties
% 12.09/2.00  
% 12.09/2.00  clauses:                                22
% 12.09/2.00  conjectures:                            4
% 12.09/2.00  epr:                                    1
% 12.09/2.00  horn:                                   19
% 12.09/2.00  ground:                                 4
% 12.09/2.00  unary:                                  11
% 12.09/2.00  binary:                                 9
% 12.09/2.00  lits:                                   35
% 12.09/2.00  lits_eq:                                18
% 12.09/2.00  fd_pure:                                0
% 12.09/2.00  fd_pseudo:                              0
% 12.09/2.00  fd_cond:                                0
% 12.09/2.00  fd_pseudo_cond:                         2
% 12.09/2.00  ac_symbols:                             1
% 12.09/2.00  
% 12.09/2.00  ------ Propositional Solver
% 12.09/2.00  
% 12.09/2.00  prop_solver_calls:                      30
% 12.09/2.00  prop_fast_solver_calls:                 594
% 12.09/2.00  smt_solver_calls:                       0
% 12.09/2.00  smt_fast_solver_calls:                  0
% 12.09/2.00  prop_num_of_clauses:                    7435
% 12.09/2.00  prop_preprocess_simplified:             13538
% 12.09/2.00  prop_fo_subsumed:                       12
% 12.09/2.00  prop_solver_time:                       0.
% 12.09/2.00  smt_solver_time:                        0.
% 12.09/2.00  smt_fast_solver_time:                   0.
% 12.09/2.00  prop_fast_solver_time:                  0.
% 12.09/2.00  prop_unsat_core_time:                   0.001
% 12.09/2.00  
% 12.09/2.00  ------ QBF
% 12.09/2.00  
% 12.09/2.00  qbf_q_res:                              0
% 12.09/2.00  qbf_num_tautologies:                    0
% 12.09/2.00  qbf_prep_cycles:                        0
% 12.09/2.00  
% 12.09/2.00  ------ BMC1
% 12.09/2.00  
% 12.09/2.00  bmc1_current_bound:                     -1
% 12.09/2.00  bmc1_last_solved_bound:                 -1
% 12.09/2.00  bmc1_unsat_core_size:                   -1
% 12.09/2.00  bmc1_unsat_core_parents_size:           -1
% 12.09/2.00  bmc1_merge_next_fun:                    0
% 12.09/2.00  bmc1_unsat_core_clauses_time:           0.
% 12.09/2.00  
% 12.09/2.00  ------ Instantiation
% 12.09/2.00  
% 12.09/2.00  inst_num_of_clauses:                    1996
% 12.09/2.00  inst_num_in_passive:                    998
% 12.09/2.00  inst_num_in_active:                     675
% 12.09/2.00  inst_num_in_unprocessed:                323
% 12.09/2.00  inst_num_of_loops:                      770
% 12.09/2.00  inst_num_of_learning_restarts:          0
% 12.09/2.00  inst_num_moves_active_passive:          90
% 12.09/2.00  inst_lit_activity:                      0
% 12.09/2.00  inst_lit_activity_moves:                0
% 12.09/2.00  inst_num_tautologies:                   0
% 12.09/2.00  inst_num_prop_implied:                  0
% 12.09/2.00  inst_num_existing_simplified:           0
% 12.09/2.00  inst_num_eq_res_simplified:             0
% 12.09/2.00  inst_num_child_elim:                    0
% 12.09/2.00  inst_num_of_dismatching_blockings:      866
% 12.09/2.00  inst_num_of_non_proper_insts:           2336
% 12.09/2.00  inst_num_of_duplicates:                 0
% 12.09/2.00  inst_inst_num_from_inst_to_res:         0
% 12.09/2.00  inst_dismatching_checking_time:         0.
% 12.09/2.00  
% 12.09/2.00  ------ Resolution
% 12.09/2.00  
% 12.09/2.00  res_num_of_clauses:                     0
% 12.09/2.00  res_num_in_passive:                     0
% 12.09/2.00  res_num_in_active:                      0
% 12.09/2.00  res_num_of_loops:                       84
% 12.09/2.00  res_forward_subset_subsumed:            340
% 12.09/2.00  res_backward_subset_subsumed:           0
% 12.09/2.00  res_forward_subsumed:                   0
% 12.09/2.00  res_backward_subsumed:                  0
% 12.09/2.00  res_forward_subsumption_resolution:     0
% 12.09/2.00  res_backward_subsumption_resolution:    0
% 12.09/2.00  res_clause_to_clause_subsumption:       90878
% 12.09/2.00  res_orphan_elimination:                 0
% 12.09/2.00  res_tautology_del:                      129
% 12.09/2.00  res_num_eq_res_simplified:              0
% 12.09/2.00  res_num_sel_changes:                    0
% 12.09/2.00  res_moves_from_active_to_pass:          0
% 12.09/2.00  
% 12.09/2.00  ------ Superposition
% 12.09/2.00  
% 12.09/2.00  sup_time_total:                         0.
% 12.09/2.00  sup_time_generating:                    0.
% 12.09/2.00  sup_time_sim_full:                      0.
% 12.09/2.00  sup_time_sim_immed:                     0.
% 12.09/2.00  
% 12.09/2.00  sup_num_of_clauses:                     1485
% 12.09/2.00  sup_num_in_active:                      127
% 12.09/2.00  sup_num_in_passive:                     1358
% 12.09/2.00  sup_num_of_loops:                       153
% 12.09/2.00  sup_fw_superposition:                   16225
% 12.09/2.00  sup_bw_superposition:                   9841
% 12.09/2.00  sup_immediate_simplified:               14105
% 12.09/2.00  sup_given_eliminated:                   1
% 12.09/2.00  comparisons_done:                       0
% 12.09/2.00  comparisons_avoided:                    6
% 12.09/2.00  
% 12.09/2.00  ------ Simplifications
% 12.09/2.00  
% 12.09/2.00  
% 12.09/2.00  sim_fw_subset_subsumed:                 7
% 12.09/2.00  sim_bw_subset_subsumed:                 9
% 12.09/2.00  sim_fw_subsumed:                        370
% 12.09/2.00  sim_bw_subsumed:                        3
% 12.09/2.00  sim_fw_subsumption_res:                 0
% 12.09/2.00  sim_bw_subsumption_res:                 0
% 12.09/2.00  sim_tautology_del:                      7
% 12.09/2.00  sim_eq_tautology_del:                   2923
% 12.09/2.00  sim_eq_res_simp:                        1
% 12.09/2.00  sim_fw_demodulated:                     16329
% 12.09/2.00  sim_bw_demodulated:                     27
% 12.09/2.00  sim_light_normalised:                   3186
% 12.09/2.00  sim_joinable_taut:                      620
% 12.09/2.00  sim_joinable_simp:                      0
% 12.09/2.00  sim_ac_normalised:                      0
% 12.09/2.00  sim_smt_subsumption:                    0
% 12.09/2.00  
%------------------------------------------------------------------------------
