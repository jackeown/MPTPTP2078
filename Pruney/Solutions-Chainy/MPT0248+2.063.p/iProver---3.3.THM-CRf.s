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
% DateTime   : Thu Dec  3 11:32:17 EST 2020

% Result     : Theorem 22.95s
% Output     : CNFRefutation 22.95s
% Verified   : 
% Statistics : Number of formulae       :  250 (21027 expanded)
%              Number of clauses        :  175 (7879 expanded)
%              Number of leaves         :   23 (5656 expanded)
%              Depth                    :   36
%              Number of atoms          :  416 (26275 expanded)
%              Number of equality atoms :  368 (25614 expanded)
%              Maximal formula depth    :   11 (   3 average)
%              Maximal clause size      :   14 (   1 average)
%              Maximal term depth       :    8 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f8,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f52,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f80,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(definition_unfolding,[],[f41,f52,f52])).

fof(f12,axiom,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f56,plain,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    inference(cnf_transformation,[],[f12])).

fof(f5,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f49,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f79,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f49,f52])).

fof(f11,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f55,plain,(
    ! [X2,X0,X1] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f11])).

fof(f9,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f53,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f9])).

fof(f10,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f54,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f10])).

fof(f13,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f57,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f13])).

fof(f87,plain,(
    ! [X0,X1] : r1_tarski(X0,k5_xboole_0(X0,k4_xboole_0(X1,X0))) ),
    inference(definition_unfolding,[],[f54,f57])).

fof(f23,conjecture,(
    ! [X0,X1,X2] :
      ~ ( ~ ( k1_xboole_0 = X2
            & k1_tarski(X0) = X1 )
        & ~ ( k1_tarski(X0) = X2
            & k1_xboole_0 = X1 )
        & ~ ( k1_tarski(X0) = X2
            & k1_tarski(X0) = X1 )
        & k2_xboole_0(X1,X2) = k1_tarski(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ~ ( ~ ( k1_xboole_0 = X2
              & k1_tarski(X0) = X1 )
          & ~ ( k1_tarski(X0) = X2
              & k1_xboole_0 = X1 )
          & ~ ( k1_tarski(X0) = X2
              & k1_tarski(X0) = X1 )
          & k2_xboole_0(X1,X2) = k1_tarski(X0) ) ),
    inference(negated_conjecture,[],[f23])).

fof(f29,plain,(
    ? [X0,X1,X2] :
      ( ( k1_xboole_0 != X2
        | k1_tarski(X0) != X1 )
      & ( k1_tarski(X0) != X2
        | k1_xboole_0 != X1 )
      & ( k1_tarski(X0) != X2
        | k1_tarski(X0) != X1 )
      & k2_xboole_0(X1,X2) = k1_tarski(X0) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f39,plain,
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

fof(f40,plain,
    ( ( k1_xboole_0 != sK4
      | k1_tarski(sK2) != sK3 )
    & ( k1_tarski(sK2) != sK4
      | k1_xboole_0 != sK3 )
    & ( k1_tarski(sK2) != sK4
      | k1_tarski(sK2) != sK3 )
    & k2_xboole_0(sK3,sK4) = k1_tarski(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f29,f39])).

fof(f69,plain,(
    k2_xboole_0(sK3,sK4) = k1_tarski(sK2) ),
    inference(cnf_transformation,[],[f40])).

fof(f14,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f58,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f14])).

fof(f15,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f59,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f15])).

fof(f16,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f60,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f16])).

fof(f17,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f61,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f17])).

fof(f18,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f62,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f18])).

fof(f19,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f63,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f19])).

fof(f20,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f64,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f20])).

fof(f73,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f63,f64])).

fof(f74,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f62,f73])).

fof(f75,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f61,f74])).

fof(f76,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f60,f75])).

fof(f77,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f59,f76])).

fof(f78,plain,(
    ! [X0] : k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f58,f77])).

fof(f95,plain,(
    k5_xboole_0(sK3,k4_xboole_0(sK4,sK3)) = k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) ),
    inference(definition_unfolding,[],[f69,f57,f78])).

fof(f21,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,k1_tarski(X1))
    <=> ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,k1_tarski(X1))
        | ( k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k1_tarski(X1)) ) ) ),
    inference(nnf_transformation,[],[f21])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,k1_tarski(X1))
        | ( k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k1_tarski(X1)) ) ) ),
    inference(flattening,[],[f37])).

fof(f65,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = X0
      | k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_tarski(X1)) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f90,plain,(
    ! [X0,X1] :
      ( k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) = X0
      | k1_xboole_0 = X0
      | ~ r1_tarski(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)) ) ),
    inference(definition_unfolding,[],[f65,f78,f78])).

fof(f7,axiom,(
    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f51,plain,(
    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f7])).

fof(f86,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) ),
    inference(definition_unfolding,[],[f51,f52])).

fof(f72,plain,
    ( k1_xboole_0 != sK4
    | k1_tarski(sK2) != sK3 ),
    inference(cnf_transformation,[],[f40])).

fof(f92,plain,
    ( k1_xboole_0 != sK4
    | k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) != sK3 ),
    inference(definition_unfolding,[],[f72,f78])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f50,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f85,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f50,f52])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f4])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f35,plain,(
    ! [X1,X0] :
      ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
     => r2_hidden(sK1(X0,X1),k3_xboole_0(X0,X1)) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( r2_hidden(sK1(X0,X1),k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f27,f35])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,k3_xboole_0(X0,X1)) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f83,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ) ),
    inference(definition_unfolding,[],[f48,f52])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
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
    inference(cnf_transformation,[],[f34])).

fof(f81,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k1_xboole_0 != k4_xboole_0(X0,k4_xboole_0(X0,X1)) ) ),
    inference(definition_unfolding,[],[f46,f52])).

fof(f70,plain,
    ( k1_tarski(sK2) != sK4
    | k1_tarski(sK2) != sK3 ),
    inference(cnf_transformation,[],[f40])).

fof(f94,plain,
    ( k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) != sK4
    | k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) != sK3 ),
    inference(definition_unfolding,[],[f70,f78,f78])).

fof(f71,plain,
    ( k1_tarski(sK2) != sK4
    | k1_xboole_0 != sK3 ),
    inference(cnf_transformation,[],[f40])).

fof(f93,plain,
    ( k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) != sK4
    | k1_xboole_0 != sK3 ),
    inference(definition_unfolding,[],[f71,f78])).

cnf(c_1,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_14,plain,
    ( k5_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f56])).

cnf(c_0,plain,
    ( k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_13,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_973,plain,
    ( k5_xboole_0(X0,k5_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2)) = k5_xboole_0(k4_xboole_0(X0,X1),X2) ),
    inference(superposition,[status(thm)],[c_0,c_13])).

cnf(c_16070,plain,
    ( k5_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k5_xboole_0(X0,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_14,c_973])).

cnf(c_11,plain,
    ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f53])).

cnf(c_16222,plain,
    ( k5_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) = X0 ),
    inference(light_normalisation,[status(thm)],[c_16070,c_11])).

cnf(c_16535,plain,
    ( k5_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,k4_xboole_0(X1,X0))) = X0 ),
    inference(superposition,[status(thm)],[c_1,c_16222])).

cnf(c_12,plain,
    ( r1_tarski(X0,k5_xboole_0(X0,k4_xboole_0(X1,X0))) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_735,plain,
    ( r1_tarski(X0,k5_xboole_0(X0,k4_xboole_0(X1,X0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_22,negated_conjecture,
    ( k5_xboole_0(sK3,k4_xboole_0(sK4,sK3)) = k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) ),
    inference(cnf_transformation,[],[f95])).

cnf(c_17,plain,
    ( ~ r1_tarski(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))
    | k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) = X0
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f90])).

cnf(c_732,plain,
    ( k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) = X1
    | k1_xboole_0 = X1
    | r1_tarski(X1,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_918,plain,
    ( k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) = X0
    | k1_xboole_0 = X0
    | r1_tarski(X0,k5_xboole_0(sK3,k4_xboole_0(sK4,sK3))) != iProver_top ),
    inference(superposition,[status(thm)],[c_22,c_732])).

cnf(c_919,plain,
    ( k5_xboole_0(sK3,k4_xboole_0(sK4,sK3)) = X0
    | k1_xboole_0 = X0
    | r1_tarski(X0,k5_xboole_0(sK3,k4_xboole_0(sK4,sK3))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_918,c_22])).

cnf(c_1078,plain,
    ( k5_xboole_0(sK3,k4_xboole_0(sK4,sK3)) = sK3
    | sK3 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_735,c_919])).

cnf(c_976,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,k4_xboole_0(k5_xboole_0(X0,X1),k4_xboole_0(k5_xboole_0(X0,X1),X2)))) = k4_xboole_0(k5_xboole_0(X0,X1),X2) ),
    inference(superposition,[status(thm)],[c_13,c_0])).

cnf(c_18437,plain,
    ( k5_xboole_0(sK3,k5_xboole_0(k4_xboole_0(sK4,sK3),k4_xboole_0(sK3,k4_xboole_0(sK3,X0)))) = k4_xboole_0(k5_xboole_0(sK3,k4_xboole_0(sK4,sK3)),X0)
    | sK3 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1078,c_976])).

cnf(c_19500,plain,
    ( k4_xboole_0(k5_xboole_0(sK3,k4_xboole_0(sK4,sK3)),sK4) = k5_xboole_0(sK3,sK4)
    | sK3 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_16535,c_18437])).

cnf(c_19787,plain,
    ( sK3 = k1_xboole_0
    | r1_tarski(sK4,k5_xboole_0(sK4,k5_xboole_0(sK3,sK4))) = iProver_top ),
    inference(superposition,[status(thm)],[c_19500,c_735])).

cnf(c_10,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f86])).

cnf(c_923,plain,
    ( k5_xboole_0(X0,k1_xboole_0) = k4_xboole_0(X0,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_10,c_0])).

cnf(c_926,plain,
    ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(light_normalisation,[status(thm)],[c_923,c_11])).

cnf(c_1410,plain,
    ( k4_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_926,c_10])).

cnf(c_979,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X0,X1))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_13,c_14])).

cnf(c_16073,plain,
    ( k5_xboole_0(k4_xboole_0(X0,X1),k5_xboole_0(X2,k5_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2))) = k5_xboole_0(X0,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_979,c_973])).

cnf(c_16221,plain,
    ( k5_xboole_0(k4_xboole_0(X0,X1),k5_xboole_0(X2,k5_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2))) = X0 ),
    inference(light_normalisation,[status(thm)],[c_16073,c_11])).

cnf(c_34128,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(X0,k5_xboole_0(k4_xboole_0(X1,k1_xboole_0),X0))) = X1 ),
    inference(superposition,[status(thm)],[c_1410,c_16221])).

cnf(c_975,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X0,X1)) = k5_xboole_0(k1_xboole_0,X1) ),
    inference(superposition,[status(thm)],[c_14,c_13])).

cnf(c_2405,plain,
    ( k5_xboole_0(k1_xboole_0,X0) = k5_xboole_0(X0,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_14,c_975])).

cnf(c_2434,plain,
    ( k5_xboole_0(k1_xboole_0,X0) = X0 ),
    inference(light_normalisation,[status(thm)],[c_2405,c_11])).

cnf(c_34270,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,X0)) = X1 ),
    inference(demodulation,[status(thm)],[c_34128,c_926,c_2434])).

cnf(c_69451,plain,
    ( sK3 = k1_xboole_0
    | r1_tarski(sK4,sK3) = iProver_top ),
    inference(demodulation,[status(thm)],[c_19787,c_34270])).

cnf(c_1081,plain,
    ( k5_xboole_0(sK3,k4_xboole_0(sK4,sK3)) = X0
    | sK3 = k1_xboole_0
    | k1_xboole_0 = X0
    | r1_tarski(X0,sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1078,c_919])).

cnf(c_69454,plain,
    ( k5_xboole_0(sK3,k4_xboole_0(sK4,sK3)) = sK4
    | sK3 = k1_xboole_0
    | sK4 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_69451,c_1081])).

cnf(c_2419,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(k5_xboole_0(X0,X1),X2))) = k5_xboole_0(k1_xboole_0,X2) ),
    inference(superposition,[status(thm)],[c_975,c_13])).

cnf(c_974,plain,
    ( k5_xboole_0(X0,k5_xboole_0(k1_xboole_0,X1)) = k5_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_11,c_13])).

cnf(c_1947,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(k1_xboole_0,X2))) = k5_xboole_0(k5_xboole_0(X0,X1),X2) ),
    inference(superposition,[status(thm)],[c_974,c_13])).

cnf(c_1953,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2) ),
    inference(demodulation,[status(thm)],[c_1947,c_974])).

cnf(c_2500,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X0,k5_xboole_0(X1,X2)))) = k5_xboole_0(k1_xboole_0,X2) ),
    inference(light_normalisation,[status(thm)],[c_2419,c_1953])).

cnf(c_2501,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X0,k5_xboole_0(X1,X2)))) = X2 ),
    inference(demodulation,[status(thm)],[c_2500,c_2434])).

cnf(c_2435,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1 ),
    inference(demodulation,[status(thm)],[c_2434,c_975])).

cnf(c_58003,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X0,X2))) = k5_xboole_0(X1,X2) ),
    inference(superposition,[status(thm)],[c_2501,c_2435])).

cnf(c_58018,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X0,X2))) = k5_xboole_0(X3,k5_xboole_0(X1,k5_xboole_0(X3,X2))) ),
    inference(superposition,[status(thm)],[c_2501,c_2501])).

cnf(c_58228,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X0,X2))) = sP0_iProver_split(X1,X2) ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP0_iProver_split])],[c_58018])).

cnf(c_58408,plain,
    ( sP0_iProver_split(X0,X1) = k5_xboole_0(X0,X1) ),
    inference(light_normalisation,[status(thm)],[c_58003,c_58228])).

cnf(c_69455,plain,
    ( sP0_iProver_split(sK3,k4_xboole_0(sK4,sK3)) = sK4
    | sK3 = k1_xboole_0
    | sK4 = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_69454,c_58408])).

cnf(c_19,negated_conjecture,
    ( k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) != sK3
    | k1_xboole_0 != sK4 ),
    inference(cnf_transformation,[],[f92])).

cnf(c_745,plain,
    ( k5_xboole_0(sK3,k4_xboole_0(sK4,sK3)) != sK3
    | sK4 != k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_19,c_22])).

cnf(c_1084,plain,
    ( sK3 = k1_xboole_0
    | sK4 != k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1078,c_745])).

cnf(c_69456,plain,
    ( sK3 = k1_xboole_0
    | sP0_iProver_split(sK3,k4_xboole_0(sK4,sK3)) = sK4 ),
    inference(global_propositional_subsumption,[status(thm)],[c_69455,c_1084])).

cnf(c_69457,plain,
    ( sP0_iProver_split(sK3,k4_xboole_0(sK4,sK3)) = sK4
    | sK3 = k1_xboole_0 ),
    inference(renaming,[status(thm)],[c_69456])).

cnf(c_16569,plain,
    ( k5_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) = k5_xboole_0(X0,X0) ),
    inference(superposition,[status(thm)],[c_16222,c_973])).

cnf(c_16579,plain,
    ( k5_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_16569,c_14])).

cnf(c_53725,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k5_xboole_0(k4_xboole_0(X0,X1),k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_16579,c_2435])).

cnf(c_53992,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,X1) ),
    inference(demodulation,[status(thm)],[c_53725,c_11])).

cnf(c_54704,plain,
    ( k5_xboole_0(sK3,k5_xboole_0(k4_xboole_0(sK4,sK3),k4_xboole_0(sK3,X0))) = k4_xboole_0(k5_xboole_0(sK3,k4_xboole_0(sK4,sK3)),k4_xboole_0(sK3,X0))
    | sK3 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_53992,c_18437])).

cnf(c_1080,plain,
    ( k5_xboole_0(sK3,k5_xboole_0(k4_xboole_0(sK4,sK3),X0)) = k5_xboole_0(sK3,X0)
    | sK3 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1078,c_13])).

cnf(c_978,plain,
    ( r1_tarski(k5_xboole_0(X0,X1),k5_xboole_0(X0,k5_xboole_0(X1,k4_xboole_0(X2,k5_xboole_0(X0,X1))))) = iProver_top ),
    inference(superposition,[status(thm)],[c_13,c_735])).

cnf(c_20825,plain,
    ( sK3 = k1_xboole_0
    | r1_tarski(sK3,k5_xboole_0(sK3,k5_xboole_0(k4_xboole_0(sK4,sK3),k4_xboole_0(X0,sK3)))) = iProver_top ),
    inference(superposition,[status(thm)],[c_1078,c_978])).

cnf(c_9,plain,
    ( ~ r1_tarski(X0,X1)
    | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f85])).

cnf(c_736,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_22225,plain,
    ( k4_xboole_0(sK3,k4_xboole_0(sK3,k5_xboole_0(sK3,k5_xboole_0(k4_xboole_0(sK4,sK3),k4_xboole_0(X0,sK3))))) = sK3
    | sK3 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_20825,c_736])).

cnf(c_22298,plain,
    ( k4_xboole_0(k5_xboole_0(sK3,k4_xboole_0(sK4,sK3)),k5_xboole_0(sK3,k5_xboole_0(k4_xboole_0(sK4,sK3),k4_xboole_0(X0,sK3)))) = k5_xboole_0(sK3,k5_xboole_0(k4_xboole_0(sK4,sK3),sK3))
    | sK3 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_22225,c_18437])).

cnf(c_23510,plain,
    ( k4_xboole_0(sK3,k5_xboole_0(sK3,k5_xboole_0(k4_xboole_0(sK4,sK3),k4_xboole_0(X0,sK3)))) = k5_xboole_0(sK3,k5_xboole_0(k4_xboole_0(sK4,sK3),sK3))
    | sK3 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1078,c_22298])).

cnf(c_23668,plain,
    ( k4_xboole_0(k5_xboole_0(sK3,k4_xboole_0(sK4,sK3)),k5_xboole_0(sK3,k5_xboole_0(k4_xboole_0(sK4,sK3),k4_xboole_0(X0,sK3)))) = k5_xboole_0(sK3,k5_xboole_0(k4_xboole_0(sK4,sK3),k4_xboole_0(sK3,k5_xboole_0(sK3,k5_xboole_0(k4_xboole_0(sK4,sK3),sK3)))))
    | sK3 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_23510,c_18437])).

cnf(c_27706,plain,
    ( k5_xboole_0(sK3,k5_xboole_0(k4_xboole_0(sK4,sK3),k4_xboole_0(sK3,k5_xboole_0(sK3,k5_xboole_0(k4_xboole_0(sK4,sK3),sK3))))) = k4_xboole_0(k5_xboole_0(sK3,k4_xboole_0(sK4,sK3)),k5_xboole_0(sK3,k4_xboole_0(X0,sK3)))
    | sK3 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1080,c_23668])).

cnf(c_27704,plain,
    ( k5_xboole_0(sK3,k5_xboole_0(k4_xboole_0(sK4,sK3),k4_xboole_0(sK3,k5_xboole_0(sK3,k5_xboole_0(k4_xboole_0(sK4,sK3),sK3))))) = k4_xboole_0(sK3,k5_xboole_0(sK3,k5_xboole_0(k4_xboole_0(sK4,sK3),k4_xboole_0(X0,sK3))))
    | sK3 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1078,c_23668])).

cnf(c_30130,plain,
    ( k4_xboole_0(k5_xboole_0(sK3,k4_xboole_0(sK4,sK3)),k5_xboole_0(sK3,k4_xboole_0(X0,sK3))) = k4_xboole_0(sK3,k5_xboole_0(sK3,k5_xboole_0(k4_xboole_0(sK4,sK3),k4_xboole_0(X1,sK3))))
    | sK3 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_27706,c_27704])).

cnf(c_30391,plain,
    ( k5_xboole_0(sK3,k5_xboole_0(k4_xboole_0(sK4,sK3),k4_xboole_0(sK3,k4_xboole_0(k5_xboole_0(sK3,k4_xboole_0(sK4,sK3)),k5_xboole_0(sK3,k4_xboole_0(X0,sK3)))))) = k4_xboole_0(k5_xboole_0(sK3,k4_xboole_0(sK4,sK3)),k5_xboole_0(sK3,k5_xboole_0(k4_xboole_0(sK4,sK3),k4_xboole_0(X1,sK3))))
    | sK3 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_30130,c_18437])).

cnf(c_27947,plain,
    ( k4_xboole_0(k5_xboole_0(sK3,k4_xboole_0(sK4,sK3)),k5_xboole_0(sK3,k5_xboole_0(k4_xboole_0(sK4,sK3),k4_xboole_0(X0,sK3)))) = k4_xboole_0(sK3,k5_xboole_0(sK3,k5_xboole_0(k4_xboole_0(sK4,sK3),k4_xboole_0(X1,sK3))))
    | sK3 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_27704,c_23668])).

cnf(c_962,plain,
    ( k5_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0))) = k4_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_1,c_0])).

cnf(c_19499,plain,
    ( k4_xboole_0(k5_xboole_0(sK3,k4_xboole_0(sK4,sK3)),k4_xboole_0(sK4,sK3)) = k5_xboole_0(sK3,k4_xboole_0(k4_xboole_0(sK4,sK3),sK3))
    | sK3 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_962,c_18437])).

cnf(c_7,plain,
    ( ~ r1_xboole_0(X0,X1)
    | ~ r2_hidden(X2,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_738,plain,
    ( r1_xboole_0(X0,X1) != iProver_top
    | r2_hidden(X2,k4_xboole_0(X0,k4_xboole_0(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_20072,plain,
    ( sK3 = k1_xboole_0
    | r1_xboole_0(k5_xboole_0(sK3,k4_xboole_0(sK4,sK3)),k4_xboole_0(sK4,sK3)) != iProver_top
    | r2_hidden(X0,k4_xboole_0(k5_xboole_0(sK3,k4_xboole_0(sK4,sK3)),k5_xboole_0(sK3,k4_xboole_0(k4_xboole_0(sK4,sK3),sK3)))) != iProver_top ),
    inference(superposition,[status(thm)],[c_19499,c_738])).

cnf(c_2548,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X2,k5_xboole_0(X0,k5_xboole_0(X1,X2)))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_13,c_979])).

cnf(c_4888,plain,
    ( k5_xboole_0(sK3,k5_xboole_0(X0,k5_xboole_0(sK3,k5_xboole_0(k4_xboole_0(sK4,sK3),X0)))) = k1_xboole_0
    | sK3 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1078,c_2548])).

cnf(c_16146,plain,
    ( k5_xboole_0(k4_xboole_0(sK3,X0),k5_xboole_0(sK3,k5_xboole_0(k4_xboole_0(sK4,sK3),k4_xboole_0(sK3,k4_xboole_0(sK3,X0))))) = k1_xboole_0
    | sK3 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_973,c_4888])).

cnf(c_16979,plain,
    ( k5_xboole_0(k4_xboole_0(sK3,X0),k5_xboole_0(sK3,k5_xboole_0(k4_xboole_0(sK4,sK3),k4_xboole_0(X0,k4_xboole_0(X0,sK3))))) = k1_xboole_0
    | sK3 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1,c_16146])).

cnf(c_19539,plain,
    ( k5_xboole_0(k4_xboole_0(sK3,sK3),k4_xboole_0(k5_xboole_0(sK3,k4_xboole_0(sK4,sK3)),sK3)) = k1_xboole_0
    | sK3 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_18437,c_16979])).

cnf(c_19540,plain,
    ( k4_xboole_0(k5_xboole_0(sK3,k4_xboole_0(sK4,sK3)),sK3) = k1_xboole_0
    | sK3 = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_19539,c_1410,c_2434])).

cnf(c_2406,plain,
    ( k5_xboole_0(k1_xboole_0,k4_xboole_0(sK4,sK3)) = k5_xboole_0(sK3,sK3)
    | sK3 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1078,c_975])).

cnf(c_2515,plain,
    ( k4_xboole_0(sK4,sK3) = k1_xboole_0
    | sK3 = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_2406,c_14,c_2434])).

cnf(c_1743,plain,
    ( k5_xboole_0(sK3,k4_xboole_0(k4_xboole_0(sK4,sK3),k4_xboole_0(k4_xboole_0(sK4,sK3),X0))) = k5_xboole_0(sK3,k4_xboole_0(k4_xboole_0(sK4,sK3),X0))
    | sK3 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_0,c_1080])).

cnf(c_2656,plain,
    ( k5_xboole_0(sK3,k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0))) = k5_xboole_0(sK3,k4_xboole_0(k4_xboole_0(sK4,sK3),X0))
    | sK3 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2515,c_1743])).

cnf(c_964,plain,
    ( k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1,c_10])).

cnf(c_1504,plain,
    ( k4_xboole_0(k1_xboole_0,X0) = k5_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_964,c_0])).

cnf(c_1509,plain,
    ( k4_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_1504,c_11])).

cnf(c_2672,plain,
    ( k5_xboole_0(sK3,k4_xboole_0(k4_xboole_0(sK4,sK3),X0)) = k5_xboole_0(sK3,k4_xboole_0(k1_xboole_0,k1_xboole_0))
    | sK3 = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_2656,c_1509])).

cnf(c_2673,plain,
    ( k5_xboole_0(sK3,k4_xboole_0(k4_xboole_0(sK4,sK3),X0)) = sK3
    | sK3 = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_2672,c_11,c_1509])).

cnf(c_4964,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X1,k5_xboole_0(X0,k1_xboole_0))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_14,c_2548])).

cnf(c_5101,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X1,X0)) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_4964,c_11])).

cnf(c_5546,plain,
    ( k5_xboole_0(k5_xboole_0(k4_xboole_0(k4_xboole_0(sK4,sK3),X0),sK3),sK3) = k1_xboole_0
    | sK3 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2673,c_5101])).

cnf(c_5563,plain,
    ( k4_xboole_0(k4_xboole_0(sK4,sK3),X0) = k1_xboole_0
    | sK3 = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_5546,c_11,c_14,c_1953])).

cnf(c_19503,plain,
    ( k5_xboole_0(sK3,k5_xboole_0(k4_xboole_0(sK4,sK3),k4_xboole_0(X0,k4_xboole_0(X0,sK3)))) = k4_xboole_0(k5_xboole_0(sK3,k4_xboole_0(sK4,sK3)),X0)
    | sK3 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1,c_18437])).

cnf(c_20208,plain,
    ( k5_xboole_0(sK3,k5_xboole_0(k4_xboole_0(sK4,sK3),k4_xboole_0(k4_xboole_0(sK4,sK3),k1_xboole_0))) = k4_xboole_0(k5_xboole_0(sK3,k4_xboole_0(sK4,sK3)),k4_xboole_0(sK4,sK3))
    | sK3 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_5563,c_19503])).

cnf(c_2402,plain,
    ( k5_xboole_0(k1_xboole_0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k5_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(superposition,[status(thm)],[c_0,c_975])).

cnf(c_2519,plain,
    ( k5_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(demodulation,[status(thm)],[c_2402,c_2434])).

cnf(c_20263,plain,
    ( k5_xboole_0(sK3,k4_xboole_0(k4_xboole_0(sK4,sK3),k4_xboole_0(k4_xboole_0(sK4,sK3),k1_xboole_0))) = k4_xboole_0(k5_xboole_0(sK3,k4_xboole_0(sK4,sK3)),k4_xboole_0(sK4,sK3))
    | sK3 = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_20208,c_2519])).

cnf(c_20264,plain,
    ( k4_xboole_0(k5_xboole_0(sK3,k4_xboole_0(sK4,sK3)),k4_xboole_0(sK4,sK3)) = sK3
    | sK3 = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_20263,c_11,c_926,c_1410])).

cnf(c_5,plain,
    ( r1_xboole_0(X0,X1)
    | k4_xboole_0(X0,k4_xboole_0(X0,X1)) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f81])).

cnf(c_740,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) != k1_xboole_0
    | r1_xboole_0(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_43838,plain,
    ( k4_xboole_0(k5_xboole_0(sK3,k4_xboole_0(sK4,sK3)),sK3) != k1_xboole_0
    | sK3 = k1_xboole_0
    | r1_xboole_0(k5_xboole_0(sK3,k4_xboole_0(sK4,sK3)),k4_xboole_0(sK4,sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_20264,c_740])).

cnf(c_44061,plain,
    ( sK3 = k1_xboole_0
    | r2_hidden(X0,k4_xboole_0(k5_xboole_0(sK3,k4_xboole_0(sK4,sK3)),k5_xboole_0(sK3,k4_xboole_0(k4_xboole_0(sK4,sK3),sK3)))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_20072,c_19540,c_43838])).

cnf(c_44069,plain,
    ( sK3 = k1_xboole_0
    | r2_hidden(X0,k4_xboole_0(sK3,k5_xboole_0(sK3,k5_xboole_0(k4_xboole_0(sK4,sK3),k4_xboole_0(X1,sK3))))) != iProver_top ),
    inference(superposition,[status(thm)],[c_30130,c_44061])).

cnf(c_44506,plain,
    ( sK3 = k1_xboole_0
    | r2_hidden(X0,k4_xboole_0(k5_xboole_0(sK3,k4_xboole_0(sK4,sK3)),k5_xboole_0(sK3,k5_xboole_0(k4_xboole_0(sK4,sK3),k4_xboole_0(X1,sK3))))) != iProver_top ),
    inference(superposition,[status(thm)],[c_27947,c_44069])).

cnf(c_45846,plain,
    ( sK3 = k1_xboole_0
    | r2_hidden(X0,k5_xboole_0(sK3,k5_xboole_0(k4_xboole_0(sK4,sK3),k4_xboole_0(sK3,k4_xboole_0(k5_xboole_0(sK3,k4_xboole_0(sK4,sK3)),k5_xboole_0(sK3,k4_xboole_0(X1,sK3))))))) != iProver_top ),
    inference(superposition,[status(thm)],[c_30391,c_44506])).

cnf(c_56463,plain,
    ( sK3 = k1_xboole_0
    | r2_hidden(X0,k4_xboole_0(k5_xboole_0(sK3,k4_xboole_0(sK4,sK3)),k4_xboole_0(sK3,k4_xboole_0(k5_xboole_0(sK3,k4_xboole_0(sK4,sK3)),k5_xboole_0(sK3,k4_xboole_0(X1,sK3)))))) != iProver_top ),
    inference(superposition,[status(thm)],[c_54704,c_45846])).

cnf(c_59986,plain,
    ( sK3 = k1_xboole_0
    | r2_hidden(X0,k4_xboole_0(sP0_iProver_split(sK3,k4_xboole_0(sK4,sK3)),k4_xboole_0(sK3,k4_xboole_0(sP0_iProver_split(sK3,k4_xboole_0(sK4,sK3)),sP0_iProver_split(sK3,k4_xboole_0(X1,sK3)))))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_56463,c_58408])).

cnf(c_69505,plain,
    ( sK3 = k1_xboole_0
    | r2_hidden(X0,k4_xboole_0(sK4,k4_xboole_0(sK3,k4_xboole_0(sK4,sP0_iProver_split(sK3,k4_xboole_0(X1,sK3)))))) != iProver_top ),
    inference(superposition,[status(thm)],[c_69457,c_59986])).

cnf(c_21,negated_conjecture,
    ( k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) != sK3
    | k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) != sK4 ),
    inference(cnf_transformation,[],[f94])).

cnf(c_746,plain,
    ( k5_xboole_0(sK3,k4_xboole_0(sK4,sK3)) != sK3
    | k5_xboole_0(sK3,k4_xboole_0(sK4,sK3)) != sK4 ),
    inference(light_normalisation,[status(thm)],[c_21,c_22])).

cnf(c_1083,plain,
    ( k5_xboole_0(sK3,k4_xboole_0(sK4,sK3)) != sK3
    | sK3 != sK4
    | sK3 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1078,c_746])).

cnf(c_1167,plain,
    ( sK3 != sK4
    | sK3 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1083,c_1078])).

cnf(c_69458,plain,
    ( sP0_iProver_split(sK3,k1_xboole_0) = sK4
    | sK3 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2515,c_69457])).

cnf(c_3448,plain,
    ( k5_xboole_0(X0,k5_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X2)) = k5_xboole_0(k4_xboole_0(X0,X1),X2) ),
    inference(superposition,[status(thm)],[c_962,c_13])).

cnf(c_28998,plain,
    ( k5_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X1,X0))))) = k5_xboole_0(X0,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_16579,c_3448])).

cnf(c_29204,plain,
    ( k5_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X1,X0))))) = X0 ),
    inference(light_normalisation,[status(thm)],[c_28998,c_11])).

cnf(c_51903,plain,
    ( k5_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X0,k4_xboole_0(X0,X1))))) = X0 ),
    inference(superposition,[status(thm)],[c_1,c_29204])).

cnf(c_57903,plain,
    ( k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X1,X2),k5_xboole_0(X0,k1_xboole_0))) = k5_xboole_0(X3,k5_xboole_0(X1,k5_xboole_0(X2,X3))) ),
    inference(superposition,[status(thm)],[c_2548,c_2501])).

cnf(c_58808,plain,
    ( sP0_iProver_split(X0,sP0_iProver_split(k5_xboole_0(X1,X2),k5_xboole_0(X0,k1_xboole_0))) = sP0_iProver_split(X3,sP0_iProver_split(X1,k5_xboole_0(X2,X3))) ),
    inference(demodulation,[status(thm)],[c_57903,c_58408])).

cnf(c_57919,plain,
    ( k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X1,X2),k5_xboole_0(X0,k1_xboole_0))) = k5_xboole_0(X2,X1) ),
    inference(superposition,[status(thm)],[c_5101,c_2501])).

cnf(c_58771,plain,
    ( sP0_iProver_split(X0,sP0_iProver_split(k5_xboole_0(X1,X2),k5_xboole_0(X0,k1_xboole_0))) = sP0_iProver_split(X2,X1) ),
    inference(demodulation,[status(thm)],[c_57919,c_58408])).

cnf(c_58772,plain,
    ( sP0_iProver_split(X0,sP0_iProver_split(sP0_iProver_split(X1,X2),sP0_iProver_split(X0,k1_xboole_0))) = sP0_iProver_split(X2,X1) ),
    inference(demodulation,[status(thm)],[c_58771,c_58408])).

cnf(c_58809,plain,
    ( sP0_iProver_split(X0,sP0_iProver_split(X1,sP0_iProver_split(X2,X0))) = sP0_iProver_split(X2,X1) ),
    inference(demodulation,[status(thm)],[c_58808,c_58408,c_58772])).

cnf(c_5300,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,X2)),k5_xboole_0(X2,k5_xboole_0(X0,X1))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_13,c_5101])).

cnf(c_57922,plain,
    ( k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X1,k5_xboole_0(X2,X3)),k5_xboole_0(X0,k1_xboole_0))) = k5_xboole_0(X3,k5_xboole_0(X1,X2)) ),
    inference(superposition,[status(thm)],[c_5300,c_2501])).

cnf(c_58695,plain,
    ( sP0_iProver_split(X0,sP0_iProver_split(k5_xboole_0(X1,k5_xboole_0(X2,X3)),k5_xboole_0(X0,k1_xboole_0))) = sP0_iProver_split(X3,sP0_iProver_split(X1,X2)) ),
    inference(demodulation,[status(thm)],[c_57922,c_58408])).

cnf(c_58696,plain,
    ( sP0_iProver_split(X0,sP0_iProver_split(sP0_iProver_split(X1,k5_xboole_0(X2,X3)),sP0_iProver_split(X0,k1_xboole_0))) = sP0_iProver_split(X3,sP0_iProver_split(X1,X2)) ),
    inference(demodulation,[status(thm)],[c_58695,c_58408])).

cnf(c_5339,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,X2)),k5_xboole_0(X1,k5_xboole_0(X2,X0))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_13,c_5101])).

cnf(c_57924,plain,
    ( k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X1,k5_xboole_0(X2,X3)),k5_xboole_0(X0,k1_xboole_0))) = k5_xboole_0(X2,k5_xboole_0(X3,X1)) ),
    inference(superposition,[status(thm)],[c_5339,c_2501])).

cnf(c_58690,plain,
    ( sP0_iProver_split(X0,sP0_iProver_split(k5_xboole_0(X1,k5_xboole_0(X2,X3)),k5_xboole_0(X0,k1_xboole_0))) = sP0_iProver_split(X2,sP0_iProver_split(X3,X1)) ),
    inference(demodulation,[status(thm)],[c_57924,c_58408])).

cnf(c_58691,plain,
    ( sP0_iProver_split(X0,sP0_iProver_split(sP0_iProver_split(X1,k5_xboole_0(X2,X3)),sP0_iProver_split(X0,k1_xboole_0))) = sP0_iProver_split(X2,sP0_iProver_split(X3,X1)) ),
    inference(demodulation,[status(thm)],[c_58690,c_58408])).

cnf(c_58692,plain,
    ( sP0_iProver_split(X0,sP0_iProver_split(sP0_iProver_split(X1,sP0_iProver_split(X2,X3)),sP0_iProver_split(X0,k1_xboole_0))) = sP0_iProver_split(X2,sP0_iProver_split(X3,X1)) ),
    inference(demodulation,[status(thm)],[c_58691,c_58408])).

cnf(c_58697,plain,
    ( sP0_iProver_split(X0,sP0_iProver_split(X1,X2)) = sP0_iProver_split(X2,sP0_iProver_split(X0,X1)) ),
    inference(demodulation,[status(thm)],[c_58696,c_58408,c_58692])).

cnf(c_57942,plain,
    ( k5_xboole_0(X0,k5_xboole_0(k4_xboole_0(X1,X2),k5_xboole_0(X0,X1))) = k4_xboole_0(X1,k4_xboole_0(X1,X2)) ),
    inference(superposition,[status(thm)],[c_16222,c_2501])).

cnf(c_58642,plain,
    ( sP0_iProver_split(X0,sP0_iProver_split(k4_xboole_0(X1,X2),k5_xboole_0(X0,X1))) = k4_xboole_0(X1,k4_xboole_0(X1,X2)) ),
    inference(demodulation,[status(thm)],[c_57942,c_58408])).

cnf(c_58643,plain,
    ( sP0_iProver_split(X0,sP0_iProver_split(k4_xboole_0(X1,X2),sP0_iProver_split(X0,X1))) = k4_xboole_0(X1,k4_xboole_0(X1,X2)) ),
    inference(demodulation,[status(thm)],[c_58642,c_58408])).

cnf(c_58743,plain,
    ( sP0_iProver_split(X0,sP0_iProver_split(X1,sP0_iProver_split(k4_xboole_0(X1,X2),X0))) = k4_xboole_0(X1,k4_xboole_0(X1,X2)) ),
    inference(demodulation,[status(thm)],[c_58697,c_58643])).

cnf(c_58836,plain,
    ( sP0_iProver_split(k4_xboole_0(X0,X1),X0) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(demodulation,[status(thm)],[c_58809,c_58743])).

cnf(c_68982,plain,
    ( k5_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,k4_xboole_0(X1,sP0_iProver_split(k4_xboole_0(X0,X1),X0)))) = X0 ),
    inference(light_normalisation,[status(thm)],[c_51903,c_51903,c_58836])).

cnf(c_68983,plain,
    ( sP0_iProver_split(k4_xboole_0(X0,X1),sP0_iProver_split(k4_xboole_0(X1,sP0_iProver_split(k4_xboole_0(X0,X1),X0)),X1)) = X0 ),
    inference(demodulation,[status(thm)],[c_68982,c_58408,c_58836])).

cnf(c_21523,plain,
    ( k5_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0)))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1,c_16579])).

cnf(c_53652,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0))) = k5_xboole_0(k4_xboole_0(X0,X1),k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_21523,c_2435])).

cnf(c_54158,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0))) = k4_xboole_0(X0,X1) ),
    inference(demodulation,[status(thm)],[c_53652,c_11])).

cnf(c_16564,plain,
    ( k5_xboole_0(k4_xboole_0(X0,X1),k5_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2)) = k5_xboole_0(X0,X2) ),
    inference(superposition,[status(thm)],[c_16222,c_13])).

cnf(c_35238,plain,
    ( k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))))) = k5_xboole_0(k4_xboole_0(X0,X1),k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_16579,c_16564])).

cnf(c_35420,plain,
    ( k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))))) = k4_xboole_0(X0,X1) ),
    inference(demodulation,[status(thm)],[c_35238,c_0,c_11])).

cnf(c_64484,plain,
    ( k5_xboole_0(X0,sP0_iProver_split(k4_xboole_0(X0,X1),X0)) = k4_xboole_0(X0,X1) ),
    inference(light_normalisation,[status(thm)],[c_35420,c_35420,c_53992,c_58836])).

cnf(c_64504,plain,
    ( k5_xboole_0(X0,sP0_iProver_split(k4_xboole_0(X0,X1),X0)) = k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0))) ),
    inference(superposition,[status(thm)],[c_54158,c_64484])).

cnf(c_64788,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0))) = k4_xboole_0(X0,X1) ),
    inference(demodulation,[status(thm)],[c_64504,c_64484])).

cnf(c_64789,plain,
    ( k4_xboole_0(X0,sP0_iProver_split(k4_xboole_0(X1,X0),X1)) = k4_xboole_0(X0,X1) ),
    inference(demodulation,[status(thm)],[c_64788,c_58836])).

cnf(c_68984,plain,
    ( sP0_iProver_split(k4_xboole_0(X0,X1),sP0_iProver_split(k4_xboole_0(X1,X0),X1)) = X0 ),
    inference(demodulation,[status(thm)],[c_68983,c_64789])).

cnf(c_69046,plain,
    ( sP0_iProver_split(k4_xboole_0(X0,k1_xboole_0),sP0_iProver_split(k1_xboole_0,k1_xboole_0)) = X0 ),
    inference(superposition,[status(thm)],[c_1509,c_68984])).

cnf(c_69185,plain,
    ( sP0_iProver_split(X0,sP0_iProver_split(k1_xboole_0,k1_xboole_0)) = X0 ),
    inference(light_normalisation,[status(thm)],[c_69046,c_926])).

cnf(c_57732,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(k1_xboole_0,X1))) = X1 ),
    inference(superposition,[status(thm)],[c_2434,c_2501])).

cnf(c_59215,plain,
    ( sP0_iProver_split(X0,sP0_iProver_split(X0,k5_xboole_0(k1_xboole_0,X1))) = X1 ),
    inference(demodulation,[status(thm)],[c_57732,c_58408])).

cnf(c_58015,plain,
    ( k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X1,k5_xboole_0(X0,k5_xboole_0(X1,X2))),X3)) = k5_xboole_0(X2,X3) ),
    inference(superposition,[status(thm)],[c_2501,c_13])).

cnf(c_58370,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,X2)),X3))) = k5_xboole_0(X2,X3) ),
    inference(demodulation,[status(thm)],[c_58015,c_1953])).

cnf(c_58371,plain,
    ( sP0_iProver_split(X0,k5_xboole_0(k5_xboole_0(X0,X1),X2)) = k5_xboole_0(X1,X2) ),
    inference(demodulation,[status(thm)],[c_58370,c_1953,c_58228])).

cnf(c_58372,plain,
    ( sP0_iProver_split(X0,k5_xboole_0(X0,k5_xboole_0(X1,X2))) = k5_xboole_0(X1,X2) ),
    inference(light_normalisation,[status(thm)],[c_58371,c_1953])).

cnf(c_58412,plain,
    ( sP0_iProver_split(X0,k5_xboole_0(X0,sP0_iProver_split(X1,X2))) = sP0_iProver_split(X1,X2) ),
    inference(demodulation,[status(thm)],[c_58408,c_58372])).

cnf(c_58463,plain,
    ( sP0_iProver_split(X0,sP0_iProver_split(X0,sP0_iProver_split(X1,X2))) = sP0_iProver_split(X1,X2) ),
    inference(demodulation,[status(thm)],[c_58412,c_58408])).

cnf(c_59216,plain,
    ( sP0_iProver_split(k1_xboole_0,X0) = X0 ),
    inference(demodulation,[status(thm)],[c_59215,c_58408,c_58463])).

cnf(c_69186,plain,
    ( sP0_iProver_split(X0,k1_xboole_0) = X0 ),
    inference(demodulation,[status(thm)],[c_69185,c_59216])).

cnf(c_69520,plain,
    ( sK3 = sK4
    | sK3 = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_69458,c_69186])).

cnf(c_69753,plain,
    ( sK3 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_69505,c_1167,c_69520])).

cnf(c_20,negated_conjecture,
    ( k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) != sK4
    | k1_xboole_0 != sK3 ),
    inference(cnf_transformation,[],[f93])).

cnf(c_744,plain,
    ( k5_xboole_0(sK3,k4_xboole_0(sK4,sK3)) != sK4
    | sK3 != k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_20,c_22])).

cnf(c_69921,plain,
    ( k5_xboole_0(k1_xboole_0,k4_xboole_0(sK4,k1_xboole_0)) != sK4
    | k1_xboole_0 != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_69753,c_744])).

cnf(c_69924,plain,
    ( k5_xboole_0(k1_xboole_0,k4_xboole_0(sK4,k1_xboole_0)) != sK4 ),
    inference(equality_resolution_simp,[status(thm)],[c_69921])).

cnf(c_69925,plain,
    ( sK4 != sK4 ),
    inference(demodulation,[status(thm)],[c_69924,c_926,c_2434])).

cnf(c_69926,plain,
    ( $false ),
    inference(equality_resolution_simp,[status(thm)],[c_69925])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n010.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 16:28:44 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  % Running in FOF mode
% 22.95/3.49  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 22.95/3.49  
% 22.95/3.49  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 22.95/3.49  
% 22.95/3.49  ------  iProver source info
% 22.95/3.49  
% 22.95/3.49  git: date: 2020-06-30 10:37:57 +0100
% 22.95/3.49  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 22.95/3.49  git: non_committed_changes: false
% 22.95/3.49  git: last_make_outside_of_git: false
% 22.95/3.49  
% 22.95/3.49  ------ 
% 22.95/3.49  
% 22.95/3.49  ------ Input Options
% 22.95/3.49  
% 22.95/3.49  --out_options                           all
% 22.95/3.49  --tptp_safe_out                         true
% 22.95/3.49  --problem_path                          ""
% 22.95/3.49  --include_path                          ""
% 22.95/3.49  --clausifier                            res/vclausify_rel
% 22.95/3.49  --clausifier_options                    ""
% 22.95/3.49  --stdin                                 false
% 22.95/3.49  --stats_out                             all
% 22.95/3.49  
% 22.95/3.49  ------ General Options
% 22.95/3.49  
% 22.95/3.49  --fof                                   false
% 22.95/3.49  --time_out_real                         305.
% 22.95/3.49  --time_out_virtual                      -1.
% 22.95/3.49  --symbol_type_check                     false
% 22.95/3.49  --clausify_out                          false
% 22.95/3.49  --sig_cnt_out                           false
% 22.95/3.49  --trig_cnt_out                          false
% 22.95/3.49  --trig_cnt_out_tolerance                1.
% 22.95/3.49  --trig_cnt_out_sk_spl                   false
% 22.95/3.49  --abstr_cl_out                          false
% 22.95/3.49  
% 22.95/3.49  ------ Global Options
% 22.95/3.49  
% 22.95/3.49  --schedule                              default
% 22.95/3.49  --add_important_lit                     false
% 22.95/3.49  --prop_solver_per_cl                    1000
% 22.95/3.49  --min_unsat_core                        false
% 22.95/3.49  --soft_assumptions                      false
% 22.95/3.49  --soft_lemma_size                       3
% 22.95/3.49  --prop_impl_unit_size                   0
% 22.95/3.49  --prop_impl_unit                        []
% 22.95/3.49  --share_sel_clauses                     true
% 22.95/3.49  --reset_solvers                         false
% 22.95/3.49  --bc_imp_inh                            [conj_cone]
% 22.95/3.49  --conj_cone_tolerance                   3.
% 22.95/3.49  --extra_neg_conj                        none
% 22.95/3.49  --large_theory_mode                     true
% 22.95/3.49  --prolific_symb_bound                   200
% 22.95/3.49  --lt_threshold                          2000
% 22.95/3.49  --clause_weak_htbl                      true
% 22.95/3.49  --gc_record_bc_elim                     false
% 22.95/3.49  
% 22.95/3.49  ------ Preprocessing Options
% 22.95/3.49  
% 22.95/3.49  --preprocessing_flag                    true
% 22.95/3.49  --time_out_prep_mult                    0.1
% 22.95/3.49  --splitting_mode                        input
% 22.95/3.49  --splitting_grd                         true
% 22.95/3.49  --splitting_cvd                         false
% 22.95/3.49  --splitting_cvd_svl                     false
% 22.95/3.49  --splitting_nvd                         32
% 22.95/3.49  --sub_typing                            true
% 22.95/3.49  --prep_gs_sim                           true
% 22.95/3.49  --prep_unflatten                        true
% 22.95/3.49  --prep_res_sim                          true
% 22.95/3.49  --prep_upred                            true
% 22.95/3.49  --prep_sem_filter                       exhaustive
% 22.95/3.49  --prep_sem_filter_out                   false
% 22.95/3.49  --pred_elim                             true
% 22.95/3.49  --res_sim_input                         true
% 22.95/3.49  --eq_ax_congr_red                       true
% 22.95/3.49  --pure_diseq_elim                       true
% 22.95/3.49  --brand_transform                       false
% 22.95/3.49  --non_eq_to_eq                          false
% 22.95/3.49  --prep_def_merge                        true
% 22.95/3.49  --prep_def_merge_prop_impl              false
% 22.95/3.49  --prep_def_merge_mbd                    true
% 22.95/3.49  --prep_def_merge_tr_red                 false
% 22.95/3.49  --prep_def_merge_tr_cl                  false
% 22.95/3.49  --smt_preprocessing                     true
% 22.95/3.49  --smt_ac_axioms                         fast
% 22.95/3.49  --preprocessed_out                      false
% 22.95/3.49  --preprocessed_stats                    false
% 22.95/3.49  
% 22.95/3.49  ------ Abstraction refinement Options
% 22.95/3.49  
% 22.95/3.49  --abstr_ref                             []
% 22.95/3.49  --abstr_ref_prep                        false
% 22.95/3.49  --abstr_ref_until_sat                   false
% 22.95/3.49  --abstr_ref_sig_restrict                funpre
% 22.95/3.49  --abstr_ref_af_restrict_to_split_sk     false
% 22.95/3.49  --abstr_ref_under                       []
% 22.95/3.49  
% 22.95/3.49  ------ SAT Options
% 22.95/3.49  
% 22.95/3.49  --sat_mode                              false
% 22.95/3.49  --sat_fm_restart_options                ""
% 22.95/3.49  --sat_gr_def                            false
% 22.95/3.49  --sat_epr_types                         true
% 22.95/3.49  --sat_non_cyclic_types                  false
% 22.95/3.49  --sat_finite_models                     false
% 22.95/3.49  --sat_fm_lemmas                         false
% 22.95/3.49  --sat_fm_prep                           false
% 22.95/3.49  --sat_fm_uc_incr                        true
% 22.95/3.49  --sat_out_model                         small
% 22.95/3.49  --sat_out_clauses                       false
% 22.95/3.49  
% 22.95/3.49  ------ QBF Options
% 22.95/3.49  
% 22.95/3.49  --qbf_mode                              false
% 22.95/3.49  --qbf_elim_univ                         false
% 22.95/3.49  --qbf_dom_inst                          none
% 22.95/3.49  --qbf_dom_pre_inst                      false
% 22.95/3.49  --qbf_sk_in                             false
% 22.95/3.49  --qbf_pred_elim                         true
% 22.95/3.49  --qbf_split                             512
% 22.95/3.49  
% 22.95/3.49  ------ BMC1 Options
% 22.95/3.49  
% 22.95/3.49  --bmc1_incremental                      false
% 22.95/3.49  --bmc1_axioms                           reachable_all
% 22.95/3.49  --bmc1_min_bound                        0
% 22.95/3.49  --bmc1_max_bound                        -1
% 22.95/3.49  --bmc1_max_bound_default                -1
% 22.95/3.49  --bmc1_symbol_reachability              true
% 22.95/3.49  --bmc1_property_lemmas                  false
% 22.95/3.49  --bmc1_k_induction                      false
% 22.95/3.49  --bmc1_non_equiv_states                 false
% 22.95/3.49  --bmc1_deadlock                         false
% 22.95/3.49  --bmc1_ucm                              false
% 22.95/3.49  --bmc1_add_unsat_core                   none
% 22.95/3.49  --bmc1_unsat_core_children              false
% 22.95/3.49  --bmc1_unsat_core_extrapolate_axioms    false
% 22.95/3.49  --bmc1_out_stat                         full
% 22.95/3.49  --bmc1_ground_init                      false
% 22.95/3.49  --bmc1_pre_inst_next_state              false
% 22.95/3.49  --bmc1_pre_inst_state                   false
% 22.95/3.49  --bmc1_pre_inst_reach_state             false
% 22.95/3.49  --bmc1_out_unsat_core                   false
% 22.95/3.49  --bmc1_aig_witness_out                  false
% 22.95/3.49  --bmc1_verbose                          false
% 22.95/3.49  --bmc1_dump_clauses_tptp                false
% 22.95/3.49  --bmc1_dump_unsat_core_tptp             false
% 22.95/3.49  --bmc1_dump_file                        -
% 22.95/3.49  --bmc1_ucm_expand_uc_limit              128
% 22.95/3.49  --bmc1_ucm_n_expand_iterations          6
% 22.95/3.49  --bmc1_ucm_extend_mode                  1
% 22.95/3.49  --bmc1_ucm_init_mode                    2
% 22.95/3.49  --bmc1_ucm_cone_mode                    none
% 22.95/3.49  --bmc1_ucm_reduced_relation_type        0
% 22.95/3.49  --bmc1_ucm_relax_model                  4
% 22.95/3.49  --bmc1_ucm_full_tr_after_sat            true
% 22.95/3.49  --bmc1_ucm_expand_neg_assumptions       false
% 22.95/3.49  --bmc1_ucm_layered_model                none
% 22.95/3.49  --bmc1_ucm_max_lemma_size               10
% 22.95/3.49  
% 22.95/3.49  ------ AIG Options
% 22.95/3.49  
% 22.95/3.49  --aig_mode                              false
% 22.95/3.49  
% 22.95/3.49  ------ Instantiation Options
% 22.95/3.49  
% 22.95/3.49  --instantiation_flag                    true
% 22.95/3.49  --inst_sos_flag                         true
% 22.95/3.49  --inst_sos_phase                        true
% 22.95/3.49  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 22.95/3.49  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 22.95/3.49  --inst_lit_sel_side                     num_symb
% 22.95/3.49  --inst_solver_per_active                1400
% 22.95/3.49  --inst_solver_calls_frac                1.
% 22.95/3.49  --inst_passive_queue_type               priority_queues
% 22.95/3.49  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 22.95/3.49  --inst_passive_queues_freq              [25;2]
% 22.95/3.49  --inst_dismatching                      true
% 22.95/3.49  --inst_eager_unprocessed_to_passive     true
% 22.95/3.49  --inst_prop_sim_given                   true
% 22.95/3.49  --inst_prop_sim_new                     false
% 22.95/3.49  --inst_subs_new                         false
% 22.95/3.49  --inst_eq_res_simp                      false
% 22.95/3.49  --inst_subs_given                       false
% 22.95/3.49  --inst_orphan_elimination               true
% 22.95/3.49  --inst_learning_loop_flag               true
% 22.95/3.49  --inst_learning_start                   3000
% 22.95/3.49  --inst_learning_factor                  2
% 22.95/3.49  --inst_start_prop_sim_after_learn       3
% 22.95/3.49  --inst_sel_renew                        solver
% 22.95/3.49  --inst_lit_activity_flag                true
% 22.95/3.49  --inst_restr_to_given                   false
% 22.95/3.49  --inst_activity_threshold               500
% 22.95/3.49  --inst_out_proof                        true
% 22.95/3.49  
% 22.95/3.49  ------ Resolution Options
% 22.95/3.49  
% 22.95/3.49  --resolution_flag                       true
% 22.95/3.49  --res_lit_sel                           adaptive
% 22.95/3.49  --res_lit_sel_side                      none
% 22.95/3.49  --res_ordering                          kbo
% 22.95/3.49  --res_to_prop_solver                    active
% 22.95/3.49  --res_prop_simpl_new                    false
% 22.95/3.49  --res_prop_simpl_given                  true
% 22.95/3.49  --res_passive_queue_type                priority_queues
% 22.95/3.49  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 22.95/3.49  --res_passive_queues_freq               [15;5]
% 22.95/3.49  --res_forward_subs                      full
% 22.95/3.49  --res_backward_subs                     full
% 22.95/3.49  --res_forward_subs_resolution           true
% 22.95/3.49  --res_backward_subs_resolution          true
% 22.95/3.49  --res_orphan_elimination                true
% 22.95/3.49  --res_time_limit                        2.
% 22.95/3.49  --res_out_proof                         true
% 22.95/3.49  
% 22.95/3.49  ------ Superposition Options
% 22.95/3.49  
% 22.95/3.49  --superposition_flag                    true
% 22.95/3.49  --sup_passive_queue_type                priority_queues
% 22.95/3.49  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 22.95/3.49  --sup_passive_queues_freq               [8;1;4]
% 22.95/3.49  --demod_completeness_check              fast
% 22.95/3.49  --demod_use_ground                      true
% 22.95/3.49  --sup_to_prop_solver                    passive
% 22.95/3.49  --sup_prop_simpl_new                    true
% 22.95/3.49  --sup_prop_simpl_given                  true
% 22.95/3.49  --sup_fun_splitting                     true
% 22.95/3.49  --sup_smt_interval                      50000
% 22.95/3.49  
% 22.95/3.49  ------ Superposition Simplification Setup
% 22.95/3.49  
% 22.95/3.49  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 22.95/3.49  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 22.95/3.49  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 22.95/3.49  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 22.95/3.49  --sup_full_triv                         [TrivRules;PropSubs]
% 22.95/3.49  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 22.95/3.49  --sup_full_bw                           [BwDemod;BwSubsumption]
% 22.95/3.49  --sup_immed_triv                        [TrivRules]
% 22.95/3.49  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 22.95/3.49  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 22.95/3.49  --sup_immed_bw_main                     []
% 22.95/3.49  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 22.95/3.49  --sup_input_triv                        [Unflattening;TrivRules]
% 22.95/3.49  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 22.95/3.49  --sup_input_bw                          []
% 22.95/3.49  
% 22.95/3.49  ------ Combination Options
% 22.95/3.49  
% 22.95/3.49  --comb_res_mult                         3
% 22.95/3.49  --comb_sup_mult                         2
% 22.95/3.49  --comb_inst_mult                        10
% 22.95/3.49  
% 22.95/3.49  ------ Debug Options
% 22.95/3.49  
% 22.95/3.49  --dbg_backtrace                         false
% 22.95/3.49  --dbg_dump_prop_clauses                 false
% 22.95/3.49  --dbg_dump_prop_clauses_file            -
% 22.95/3.49  --dbg_out_stat                          false
% 22.95/3.49  ------ Parsing...
% 22.95/3.49  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 22.95/3.49  
% 22.95/3.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 22.95/3.49  
% 22.95/3.49  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 22.95/3.49  
% 22.95/3.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 22.95/3.49  ------ Proving...
% 22.95/3.49  ------ Problem Properties 
% 22.95/3.49  
% 22.95/3.49  
% 22.95/3.49  clauses                                 23
% 22.95/3.49  conjectures                             4
% 22.95/3.49  EPR                                     1
% 22.95/3.49  Horn                                    20
% 22.95/3.49  unary                                   11
% 22.95/3.49  binary                                  10
% 22.95/3.49  lits                                    37
% 22.95/3.49  lits eq                                 19
% 22.95/3.49  fd_pure                                 0
% 22.95/3.49  fd_pseudo                               0
% 22.95/3.49  fd_cond                                 0
% 22.95/3.49  fd_pseudo_cond                          1
% 22.95/3.49  AC symbols                              0
% 22.95/3.49  
% 22.95/3.49  ------ Schedule dynamic 5 is on 
% 22.95/3.49  
% 22.95/3.49  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 22.95/3.49  
% 22.95/3.49  
% 22.95/3.49  ------ 
% 22.95/3.49  Current options:
% 22.95/3.49  ------ 
% 22.95/3.49  
% 22.95/3.49  ------ Input Options
% 22.95/3.49  
% 22.95/3.49  --out_options                           all
% 22.95/3.49  --tptp_safe_out                         true
% 22.95/3.49  --problem_path                          ""
% 22.95/3.49  --include_path                          ""
% 22.95/3.49  --clausifier                            res/vclausify_rel
% 22.95/3.49  --clausifier_options                    ""
% 22.95/3.49  --stdin                                 false
% 22.95/3.49  --stats_out                             all
% 22.95/3.49  
% 22.95/3.49  ------ General Options
% 22.95/3.49  
% 22.95/3.49  --fof                                   false
% 22.95/3.49  --time_out_real                         305.
% 22.95/3.49  --time_out_virtual                      -1.
% 22.95/3.49  --symbol_type_check                     false
% 22.95/3.49  --clausify_out                          false
% 22.95/3.49  --sig_cnt_out                           false
% 22.95/3.49  --trig_cnt_out                          false
% 22.95/3.49  --trig_cnt_out_tolerance                1.
% 22.95/3.49  --trig_cnt_out_sk_spl                   false
% 22.95/3.49  --abstr_cl_out                          false
% 22.95/3.49  
% 22.95/3.49  ------ Global Options
% 22.95/3.49  
% 22.95/3.49  --schedule                              default
% 22.95/3.49  --add_important_lit                     false
% 22.95/3.49  --prop_solver_per_cl                    1000
% 22.95/3.49  --min_unsat_core                        false
% 22.95/3.49  --soft_assumptions                      false
% 22.95/3.49  --soft_lemma_size                       3
% 22.95/3.49  --prop_impl_unit_size                   0
% 22.95/3.49  --prop_impl_unit                        []
% 22.95/3.49  --share_sel_clauses                     true
% 22.95/3.49  --reset_solvers                         false
% 22.95/3.49  --bc_imp_inh                            [conj_cone]
% 22.95/3.49  --conj_cone_tolerance                   3.
% 22.95/3.49  --extra_neg_conj                        none
% 22.95/3.49  --large_theory_mode                     true
% 22.95/3.49  --prolific_symb_bound                   200
% 22.95/3.49  --lt_threshold                          2000
% 22.95/3.49  --clause_weak_htbl                      true
% 22.95/3.49  --gc_record_bc_elim                     false
% 22.95/3.49  
% 22.95/3.49  ------ Preprocessing Options
% 22.95/3.49  
% 22.95/3.49  --preprocessing_flag                    true
% 22.95/3.49  --time_out_prep_mult                    0.1
% 22.95/3.49  --splitting_mode                        input
% 22.95/3.49  --splitting_grd                         true
% 22.95/3.49  --splitting_cvd                         false
% 22.95/3.49  --splitting_cvd_svl                     false
% 22.95/3.49  --splitting_nvd                         32
% 22.95/3.49  --sub_typing                            true
% 22.95/3.49  --prep_gs_sim                           true
% 22.95/3.49  --prep_unflatten                        true
% 22.95/3.49  --prep_res_sim                          true
% 22.95/3.49  --prep_upred                            true
% 22.95/3.49  --prep_sem_filter                       exhaustive
% 22.95/3.49  --prep_sem_filter_out                   false
% 22.95/3.49  --pred_elim                             true
% 22.95/3.49  --res_sim_input                         true
% 22.95/3.49  --eq_ax_congr_red                       true
% 22.95/3.49  --pure_diseq_elim                       true
% 22.95/3.49  --brand_transform                       false
% 22.95/3.49  --non_eq_to_eq                          false
% 22.95/3.49  --prep_def_merge                        true
% 22.95/3.49  --prep_def_merge_prop_impl              false
% 22.95/3.49  --prep_def_merge_mbd                    true
% 22.95/3.49  --prep_def_merge_tr_red                 false
% 22.95/3.49  --prep_def_merge_tr_cl                  false
% 22.95/3.49  --smt_preprocessing                     true
% 22.95/3.49  --smt_ac_axioms                         fast
% 22.95/3.49  --preprocessed_out                      false
% 22.95/3.49  --preprocessed_stats                    false
% 22.95/3.49  
% 22.95/3.49  ------ Abstraction refinement Options
% 22.95/3.49  
% 22.95/3.49  --abstr_ref                             []
% 22.95/3.49  --abstr_ref_prep                        false
% 22.95/3.49  --abstr_ref_until_sat                   false
% 22.95/3.49  --abstr_ref_sig_restrict                funpre
% 22.95/3.49  --abstr_ref_af_restrict_to_split_sk     false
% 22.95/3.49  --abstr_ref_under                       []
% 22.95/3.49  
% 22.95/3.49  ------ SAT Options
% 22.95/3.49  
% 22.95/3.49  --sat_mode                              false
% 22.95/3.49  --sat_fm_restart_options                ""
% 22.95/3.49  --sat_gr_def                            false
% 22.95/3.49  --sat_epr_types                         true
% 22.95/3.49  --sat_non_cyclic_types                  false
% 22.95/3.49  --sat_finite_models                     false
% 22.95/3.49  --sat_fm_lemmas                         false
% 22.95/3.49  --sat_fm_prep                           false
% 22.95/3.49  --sat_fm_uc_incr                        true
% 22.95/3.49  --sat_out_model                         small
% 22.95/3.49  --sat_out_clauses                       false
% 22.95/3.49  
% 22.95/3.49  ------ QBF Options
% 22.95/3.49  
% 22.95/3.49  --qbf_mode                              false
% 22.95/3.49  --qbf_elim_univ                         false
% 22.95/3.49  --qbf_dom_inst                          none
% 22.95/3.49  --qbf_dom_pre_inst                      false
% 22.95/3.49  --qbf_sk_in                             false
% 22.95/3.49  --qbf_pred_elim                         true
% 22.95/3.49  --qbf_split                             512
% 22.95/3.49  
% 22.95/3.49  ------ BMC1 Options
% 22.95/3.49  
% 22.95/3.49  --bmc1_incremental                      false
% 22.95/3.49  --bmc1_axioms                           reachable_all
% 22.95/3.49  --bmc1_min_bound                        0
% 22.95/3.49  --bmc1_max_bound                        -1
% 22.95/3.49  --bmc1_max_bound_default                -1
% 22.95/3.49  --bmc1_symbol_reachability              true
% 22.95/3.49  --bmc1_property_lemmas                  false
% 22.95/3.49  --bmc1_k_induction                      false
% 22.95/3.49  --bmc1_non_equiv_states                 false
% 22.95/3.49  --bmc1_deadlock                         false
% 22.95/3.49  --bmc1_ucm                              false
% 22.95/3.49  --bmc1_add_unsat_core                   none
% 22.95/3.49  --bmc1_unsat_core_children              false
% 22.95/3.49  --bmc1_unsat_core_extrapolate_axioms    false
% 22.95/3.49  --bmc1_out_stat                         full
% 22.95/3.49  --bmc1_ground_init                      false
% 22.95/3.49  --bmc1_pre_inst_next_state              false
% 22.95/3.49  --bmc1_pre_inst_state                   false
% 22.95/3.49  --bmc1_pre_inst_reach_state             false
% 22.95/3.49  --bmc1_out_unsat_core                   false
% 22.95/3.49  --bmc1_aig_witness_out                  false
% 22.95/3.49  --bmc1_verbose                          false
% 22.95/3.49  --bmc1_dump_clauses_tptp                false
% 22.95/3.49  --bmc1_dump_unsat_core_tptp             false
% 22.95/3.49  --bmc1_dump_file                        -
% 22.95/3.49  --bmc1_ucm_expand_uc_limit              128
% 22.95/3.49  --bmc1_ucm_n_expand_iterations          6
% 22.95/3.49  --bmc1_ucm_extend_mode                  1
% 22.95/3.49  --bmc1_ucm_init_mode                    2
% 22.95/3.49  --bmc1_ucm_cone_mode                    none
% 22.95/3.49  --bmc1_ucm_reduced_relation_type        0
% 22.95/3.49  --bmc1_ucm_relax_model                  4
% 22.95/3.49  --bmc1_ucm_full_tr_after_sat            true
% 22.95/3.49  --bmc1_ucm_expand_neg_assumptions       false
% 22.95/3.49  --bmc1_ucm_layered_model                none
% 22.95/3.49  --bmc1_ucm_max_lemma_size               10
% 22.95/3.49  
% 22.95/3.49  ------ AIG Options
% 22.95/3.49  
% 22.95/3.49  --aig_mode                              false
% 22.95/3.49  
% 22.95/3.49  ------ Instantiation Options
% 22.95/3.49  
% 22.95/3.49  --instantiation_flag                    true
% 22.95/3.49  --inst_sos_flag                         true
% 22.95/3.49  --inst_sos_phase                        true
% 22.95/3.49  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 22.95/3.49  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 22.95/3.49  --inst_lit_sel_side                     none
% 22.95/3.49  --inst_solver_per_active                1400
% 22.95/3.49  --inst_solver_calls_frac                1.
% 22.95/3.49  --inst_passive_queue_type               priority_queues
% 22.95/3.49  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 22.95/3.49  --inst_passive_queues_freq              [25;2]
% 22.95/3.49  --inst_dismatching                      true
% 22.95/3.49  --inst_eager_unprocessed_to_passive     true
% 22.95/3.49  --inst_prop_sim_given                   true
% 22.95/3.49  --inst_prop_sim_new                     false
% 22.95/3.49  --inst_subs_new                         false
% 22.95/3.49  --inst_eq_res_simp                      false
% 22.95/3.49  --inst_subs_given                       false
% 22.95/3.49  --inst_orphan_elimination               true
% 22.95/3.49  --inst_learning_loop_flag               true
% 22.95/3.49  --inst_learning_start                   3000
% 22.95/3.49  --inst_learning_factor                  2
% 22.95/3.49  --inst_start_prop_sim_after_learn       3
% 22.95/3.49  --inst_sel_renew                        solver
% 22.95/3.49  --inst_lit_activity_flag                true
% 22.95/3.49  --inst_restr_to_given                   false
% 22.95/3.49  --inst_activity_threshold               500
% 22.95/3.49  --inst_out_proof                        true
% 22.95/3.49  
% 22.95/3.49  ------ Resolution Options
% 22.95/3.49  
% 22.95/3.49  --resolution_flag                       false
% 22.95/3.49  --res_lit_sel                           adaptive
% 22.95/3.49  --res_lit_sel_side                      none
% 22.95/3.49  --res_ordering                          kbo
% 22.95/3.49  --res_to_prop_solver                    active
% 22.95/3.49  --res_prop_simpl_new                    false
% 22.95/3.49  --res_prop_simpl_given                  true
% 22.95/3.49  --res_passive_queue_type                priority_queues
% 22.95/3.49  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 22.95/3.49  --res_passive_queues_freq               [15;5]
% 22.95/3.49  --res_forward_subs                      full
% 22.95/3.49  --res_backward_subs                     full
% 22.95/3.49  --res_forward_subs_resolution           true
% 22.95/3.49  --res_backward_subs_resolution          true
% 22.95/3.49  --res_orphan_elimination                true
% 22.95/3.49  --res_time_limit                        2.
% 22.95/3.49  --res_out_proof                         true
% 22.95/3.49  
% 22.95/3.49  ------ Superposition Options
% 22.95/3.49  
% 22.95/3.49  --superposition_flag                    true
% 22.95/3.49  --sup_passive_queue_type                priority_queues
% 22.95/3.49  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 22.95/3.49  --sup_passive_queues_freq               [8;1;4]
% 22.95/3.49  --demod_completeness_check              fast
% 22.95/3.49  --demod_use_ground                      true
% 22.95/3.49  --sup_to_prop_solver                    passive
% 22.95/3.49  --sup_prop_simpl_new                    true
% 22.95/3.49  --sup_prop_simpl_given                  true
% 22.95/3.49  --sup_fun_splitting                     true
% 22.95/3.49  --sup_smt_interval                      50000
% 22.95/3.49  
% 22.95/3.49  ------ Superposition Simplification Setup
% 22.95/3.49  
% 22.95/3.49  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 22.95/3.49  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 22.95/3.49  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 22.95/3.49  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 22.95/3.49  --sup_full_triv                         [TrivRules;PropSubs]
% 22.95/3.49  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 22.95/3.49  --sup_full_bw                           [BwDemod;BwSubsumption]
% 22.95/3.49  --sup_immed_triv                        [TrivRules]
% 22.95/3.49  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 22.95/3.49  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 22.95/3.49  --sup_immed_bw_main                     []
% 22.95/3.49  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 22.95/3.49  --sup_input_triv                        [Unflattening;TrivRules]
% 22.95/3.49  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 22.95/3.49  --sup_input_bw                          []
% 22.95/3.49  
% 22.95/3.49  ------ Combination Options
% 22.95/3.49  
% 22.95/3.49  --comb_res_mult                         3
% 22.95/3.49  --comb_sup_mult                         2
% 22.95/3.49  --comb_inst_mult                        10
% 22.95/3.49  
% 22.95/3.49  ------ Debug Options
% 22.95/3.49  
% 22.95/3.49  --dbg_backtrace                         false
% 22.95/3.49  --dbg_dump_prop_clauses                 false
% 22.95/3.49  --dbg_dump_prop_clauses_file            -
% 22.95/3.49  --dbg_out_stat                          false
% 22.95/3.49  
% 22.95/3.49  
% 22.95/3.49  
% 22.95/3.49  
% 22.95/3.49  ------ Proving...
% 22.95/3.49  
% 22.95/3.49  
% 22.95/3.49  % SZS status Theorem for theBenchmark.p
% 22.95/3.49  
% 22.95/3.49   Resolution empty clause
% 22.95/3.49  
% 22.95/3.49  % SZS output start CNFRefutation for theBenchmark.p
% 22.95/3.49  
% 22.95/3.49  fof(f1,axiom,(
% 22.95/3.49    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 22.95/3.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 22.95/3.49  
% 22.95/3.49  fof(f41,plain,(
% 22.95/3.49    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 22.95/3.49    inference(cnf_transformation,[],[f1])).
% 22.95/3.49  
% 22.95/3.49  fof(f8,axiom,(
% 22.95/3.49    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 22.95/3.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 22.95/3.49  
% 22.95/3.49  fof(f52,plain,(
% 22.95/3.49    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 22.95/3.49    inference(cnf_transformation,[],[f8])).
% 22.95/3.49  
% 22.95/3.49  fof(f80,plain,(
% 22.95/3.49    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0))) )),
% 22.95/3.49    inference(definition_unfolding,[],[f41,f52,f52])).
% 22.95/3.49  
% 22.95/3.49  fof(f12,axiom,(
% 22.95/3.49    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0)),
% 22.95/3.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 22.95/3.49  
% 22.95/3.49  fof(f56,plain,(
% 22.95/3.49    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(X0,X0)) )),
% 22.95/3.49    inference(cnf_transformation,[],[f12])).
% 22.95/3.49  
% 22.95/3.49  fof(f5,axiom,(
% 22.95/3.49    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 22.95/3.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 22.95/3.49  
% 22.95/3.49  fof(f49,plain,(
% 22.95/3.49    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 22.95/3.49    inference(cnf_transformation,[],[f5])).
% 22.95/3.49  
% 22.95/3.49  fof(f79,plain,(
% 22.95/3.49    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 22.95/3.49    inference(definition_unfolding,[],[f49,f52])).
% 22.95/3.49  
% 22.95/3.49  fof(f11,axiom,(
% 22.95/3.49    ! [X0,X1,X2] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2)),
% 22.95/3.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 22.95/3.49  
% 22.95/3.49  fof(f55,plain,(
% 22.95/3.49    ( ! [X2,X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2)) )),
% 22.95/3.49    inference(cnf_transformation,[],[f11])).
% 22.95/3.49  
% 22.95/3.49  fof(f9,axiom,(
% 22.95/3.49    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 22.95/3.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 22.95/3.49  
% 22.95/3.49  fof(f53,plain,(
% 22.95/3.49    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 22.95/3.49    inference(cnf_transformation,[],[f9])).
% 22.95/3.49  
% 22.95/3.49  fof(f10,axiom,(
% 22.95/3.49    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 22.95/3.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 22.95/3.49  
% 22.95/3.49  fof(f54,plain,(
% 22.95/3.49    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 22.95/3.49    inference(cnf_transformation,[],[f10])).
% 22.95/3.49  
% 22.95/3.49  fof(f13,axiom,(
% 22.95/3.49    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)),
% 22.95/3.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 22.95/3.49  
% 22.95/3.49  fof(f57,plain,(
% 22.95/3.49    ( ! [X0,X1] : (k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)) )),
% 22.95/3.49    inference(cnf_transformation,[],[f13])).
% 22.95/3.49  
% 22.95/3.49  fof(f87,plain,(
% 22.95/3.49    ( ! [X0,X1] : (r1_tarski(X0,k5_xboole_0(X0,k4_xboole_0(X1,X0)))) )),
% 22.95/3.49    inference(definition_unfolding,[],[f54,f57])).
% 22.95/3.49  
% 22.95/3.49  fof(f23,conjecture,(
% 22.95/3.49    ! [X0,X1,X2] : ~(~(k1_xboole_0 = X2 & k1_tarski(X0) = X1) & ~(k1_tarski(X0) = X2 & k1_xboole_0 = X1) & ~(k1_tarski(X0) = X2 & k1_tarski(X0) = X1) & k2_xboole_0(X1,X2) = k1_tarski(X0))),
% 22.95/3.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 22.95/3.49  
% 22.95/3.49  fof(f24,negated_conjecture,(
% 22.95/3.49    ~! [X0,X1,X2] : ~(~(k1_xboole_0 = X2 & k1_tarski(X0) = X1) & ~(k1_tarski(X0) = X2 & k1_xboole_0 = X1) & ~(k1_tarski(X0) = X2 & k1_tarski(X0) = X1) & k2_xboole_0(X1,X2) = k1_tarski(X0))),
% 22.95/3.49    inference(negated_conjecture,[],[f23])).
% 22.95/3.49  
% 22.95/3.49  fof(f29,plain,(
% 22.95/3.49    ? [X0,X1,X2] : ((k1_xboole_0 != X2 | k1_tarski(X0) != X1) & (k1_tarski(X0) != X2 | k1_xboole_0 != X1) & (k1_tarski(X0) != X2 | k1_tarski(X0) != X1) & k2_xboole_0(X1,X2) = k1_tarski(X0))),
% 22.95/3.49    inference(ennf_transformation,[],[f24])).
% 22.95/3.49  
% 22.95/3.49  fof(f39,plain,(
% 22.95/3.49    ? [X0,X1,X2] : ((k1_xboole_0 != X2 | k1_tarski(X0) != X1) & (k1_tarski(X0) != X2 | k1_xboole_0 != X1) & (k1_tarski(X0) != X2 | k1_tarski(X0) != X1) & k2_xboole_0(X1,X2) = k1_tarski(X0)) => ((k1_xboole_0 != sK4 | k1_tarski(sK2) != sK3) & (k1_tarski(sK2) != sK4 | k1_xboole_0 != sK3) & (k1_tarski(sK2) != sK4 | k1_tarski(sK2) != sK3) & k2_xboole_0(sK3,sK4) = k1_tarski(sK2))),
% 22.95/3.49    introduced(choice_axiom,[])).
% 22.95/3.49  
% 22.95/3.49  fof(f40,plain,(
% 22.95/3.49    (k1_xboole_0 != sK4 | k1_tarski(sK2) != sK3) & (k1_tarski(sK2) != sK4 | k1_xboole_0 != sK3) & (k1_tarski(sK2) != sK4 | k1_tarski(sK2) != sK3) & k2_xboole_0(sK3,sK4) = k1_tarski(sK2)),
% 22.95/3.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f29,f39])).
% 22.95/3.49  
% 22.95/3.49  fof(f69,plain,(
% 22.95/3.49    k2_xboole_0(sK3,sK4) = k1_tarski(sK2)),
% 22.95/3.49    inference(cnf_transformation,[],[f40])).
% 22.95/3.49  
% 22.95/3.49  fof(f14,axiom,(
% 22.95/3.49    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 22.95/3.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 22.95/3.49  
% 22.95/3.49  fof(f58,plain,(
% 22.95/3.49    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 22.95/3.49    inference(cnf_transformation,[],[f14])).
% 22.95/3.49  
% 22.95/3.49  fof(f15,axiom,(
% 22.95/3.49    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 22.95/3.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 22.95/3.49  
% 22.95/3.49  fof(f59,plain,(
% 22.95/3.49    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 22.95/3.49    inference(cnf_transformation,[],[f15])).
% 22.95/3.49  
% 22.95/3.49  fof(f16,axiom,(
% 22.95/3.49    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 22.95/3.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 22.95/3.49  
% 22.95/3.49  fof(f60,plain,(
% 22.95/3.49    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 22.95/3.49    inference(cnf_transformation,[],[f16])).
% 22.95/3.49  
% 22.95/3.49  fof(f17,axiom,(
% 22.95/3.49    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 22.95/3.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 22.95/3.49  
% 22.95/3.49  fof(f61,plain,(
% 22.95/3.49    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 22.95/3.49    inference(cnf_transformation,[],[f17])).
% 22.95/3.49  
% 22.95/3.49  fof(f18,axiom,(
% 22.95/3.49    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)),
% 22.95/3.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 22.95/3.49  
% 22.95/3.49  fof(f62,plain,(
% 22.95/3.49    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)) )),
% 22.95/3.49    inference(cnf_transformation,[],[f18])).
% 22.95/3.49  
% 22.95/3.49  fof(f19,axiom,(
% 22.95/3.49    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)),
% 22.95/3.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 22.95/3.49  
% 22.95/3.49  fof(f63,plain,(
% 22.95/3.49    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)) )),
% 22.95/3.49    inference(cnf_transformation,[],[f19])).
% 22.95/3.49  
% 22.95/3.49  fof(f20,axiom,(
% 22.95/3.49    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)),
% 22.95/3.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 22.95/3.49  
% 22.95/3.49  fof(f64,plain,(
% 22.95/3.49    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)) )),
% 22.95/3.49    inference(cnf_transformation,[],[f20])).
% 22.95/3.49  
% 22.95/3.49  fof(f73,plain,(
% 22.95/3.49    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 22.95/3.49    inference(definition_unfolding,[],[f63,f64])).
% 22.95/3.49  
% 22.95/3.49  fof(f74,plain,(
% 22.95/3.49    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 22.95/3.49    inference(definition_unfolding,[],[f62,f73])).
% 22.95/3.49  
% 22.95/3.49  fof(f75,plain,(
% 22.95/3.49    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 22.95/3.49    inference(definition_unfolding,[],[f61,f74])).
% 22.95/3.49  
% 22.95/3.49  fof(f76,plain,(
% 22.95/3.49    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 22.95/3.49    inference(definition_unfolding,[],[f60,f75])).
% 22.95/3.49  
% 22.95/3.49  fof(f77,plain,(
% 22.95/3.49    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 22.95/3.49    inference(definition_unfolding,[],[f59,f76])).
% 22.95/3.49  
% 22.95/3.49  fof(f78,plain,(
% 22.95/3.49    ( ! [X0] : (k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) )),
% 22.95/3.49    inference(definition_unfolding,[],[f58,f77])).
% 22.95/3.49  
% 22.95/3.49  fof(f95,plain,(
% 22.95/3.49    k5_xboole_0(sK3,k4_xboole_0(sK4,sK3)) = k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)),
% 22.95/3.49    inference(definition_unfolding,[],[f69,f57,f78])).
% 22.95/3.49  
% 22.95/3.49  fof(f21,axiom,(
% 22.95/3.49    ! [X0,X1] : (r1_tarski(X0,k1_tarski(X1)) <=> (k1_tarski(X1) = X0 | k1_xboole_0 = X0))),
% 22.95/3.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 22.95/3.49  
% 22.95/3.49  fof(f37,plain,(
% 22.95/3.49    ! [X0,X1] : ((r1_tarski(X0,k1_tarski(X1)) | (k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & ((k1_tarski(X1) = X0 | k1_xboole_0 = X0) | ~r1_tarski(X0,k1_tarski(X1))))),
% 22.95/3.49    inference(nnf_transformation,[],[f21])).
% 22.95/3.49  
% 22.95/3.49  fof(f38,plain,(
% 22.95/3.49    ! [X0,X1] : ((r1_tarski(X0,k1_tarski(X1)) | (k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & (k1_tarski(X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k1_tarski(X1))))),
% 22.95/3.49    inference(flattening,[],[f37])).
% 22.95/3.49  
% 22.95/3.49  fof(f65,plain,(
% 22.95/3.49    ( ! [X0,X1] : (k1_tarski(X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k1_tarski(X1))) )),
% 22.95/3.49    inference(cnf_transformation,[],[f38])).
% 22.95/3.49  
% 22.95/3.49  fof(f90,plain,(
% 22.95/3.49    ( ! [X0,X1] : (k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))) )),
% 22.95/3.49    inference(definition_unfolding,[],[f65,f78,f78])).
% 22.95/3.49  
% 22.95/3.49  fof(f7,axiom,(
% 22.95/3.49    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0),
% 22.95/3.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 22.95/3.49  
% 22.95/3.49  fof(f51,plain,(
% 22.95/3.49    ( ! [X0] : (k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0) )),
% 22.95/3.49    inference(cnf_transformation,[],[f7])).
% 22.95/3.49  
% 22.95/3.49  fof(f86,plain,(
% 22.95/3.49    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0))) )),
% 22.95/3.49    inference(definition_unfolding,[],[f51,f52])).
% 22.95/3.49  
% 22.95/3.49  fof(f72,plain,(
% 22.95/3.49    k1_xboole_0 != sK4 | k1_tarski(sK2) != sK3),
% 22.95/3.49    inference(cnf_transformation,[],[f40])).
% 22.95/3.49  
% 22.95/3.49  fof(f92,plain,(
% 22.95/3.49    k1_xboole_0 != sK4 | k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) != sK3),
% 22.95/3.49    inference(definition_unfolding,[],[f72,f78])).
% 22.95/3.49  
% 22.95/3.49  fof(f6,axiom,(
% 22.95/3.49    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 22.95/3.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 22.95/3.49  
% 22.95/3.49  fof(f28,plain,(
% 22.95/3.49    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 22.95/3.49    inference(ennf_transformation,[],[f6])).
% 22.95/3.49  
% 22.95/3.49  fof(f50,plain,(
% 22.95/3.49    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 22.95/3.49    inference(cnf_transformation,[],[f28])).
% 22.95/3.49  
% 22.95/3.49  fof(f85,plain,(
% 22.95/3.49    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0 | ~r1_tarski(X0,X1)) )),
% 22.95/3.49    inference(definition_unfolding,[],[f50,f52])).
% 22.95/3.49  
% 22.95/3.49  fof(f4,axiom,(
% 22.95/3.49    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 22.95/3.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 22.95/3.49  
% 22.95/3.49  fof(f25,plain,(
% 22.95/3.49    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X3] : ~r2_hidden(X3,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 22.95/3.49    inference(rectify,[],[f4])).
% 22.95/3.49  
% 22.95/3.49  fof(f27,plain,(
% 22.95/3.49    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 22.95/3.49    inference(ennf_transformation,[],[f25])).
% 22.95/3.49  
% 22.95/3.49  fof(f35,plain,(
% 22.95/3.49    ! [X1,X0] : (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) => r2_hidden(sK1(X0,X1),k3_xboole_0(X0,X1)))),
% 22.95/3.49    introduced(choice_axiom,[])).
% 22.95/3.49  
% 22.95/3.49  fof(f36,plain,(
% 22.95/3.49    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (r2_hidden(sK1(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 22.95/3.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f27,f35])).
% 22.95/3.49  
% 22.95/3.49  fof(f48,plain,(
% 22.95/3.49    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,k3_xboole_0(X0,X1))) )),
% 22.95/3.49    inference(cnf_transformation,[],[f36])).
% 22.95/3.49  
% 22.95/3.49  fof(f83,plain,(
% 22.95/3.49    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 22.95/3.49    inference(definition_unfolding,[],[f48,f52])).
% 22.95/3.49  
% 22.95/3.49  fof(f3,axiom,(
% 22.95/3.49    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 22.95/3.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 22.95/3.49  
% 22.95/3.49  fof(f34,plain,(
% 22.95/3.49    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) & (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)))),
% 22.95/3.49    inference(nnf_transformation,[],[f3])).
% 22.95/3.49  
% 22.95/3.49  fof(f46,plain,(
% 22.95/3.49    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) )),
% 22.95/3.49    inference(cnf_transformation,[],[f34])).
% 22.95/3.49  
% 22.95/3.49  fof(f81,plain,(
% 22.95/3.49    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k1_xboole_0 != k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 22.95/3.49    inference(definition_unfolding,[],[f46,f52])).
% 22.95/3.49  
% 22.95/3.49  fof(f70,plain,(
% 22.95/3.49    k1_tarski(sK2) != sK4 | k1_tarski(sK2) != sK3),
% 22.95/3.49    inference(cnf_transformation,[],[f40])).
% 22.95/3.49  
% 22.95/3.49  fof(f94,plain,(
% 22.95/3.49    k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) != sK4 | k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) != sK3),
% 22.95/3.49    inference(definition_unfolding,[],[f70,f78,f78])).
% 22.95/3.49  
% 22.95/3.49  fof(f71,plain,(
% 22.95/3.49    k1_tarski(sK2) != sK4 | k1_xboole_0 != sK3),
% 22.95/3.49    inference(cnf_transformation,[],[f40])).
% 22.95/3.49  
% 22.95/3.49  fof(f93,plain,(
% 22.95/3.49    k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) != sK4 | k1_xboole_0 != sK3),
% 22.95/3.49    inference(definition_unfolding,[],[f71,f78])).
% 22.95/3.49  
% 22.95/3.49  cnf(c_1,plain,
% 22.95/3.49      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
% 22.95/3.49      inference(cnf_transformation,[],[f80]) ).
% 22.95/3.49  
% 22.95/3.49  cnf(c_14,plain,
% 22.95/3.49      ( k5_xboole_0(X0,X0) = k1_xboole_0 ),
% 22.95/3.49      inference(cnf_transformation,[],[f56]) ).
% 22.95/3.49  
% 22.95/3.49  cnf(c_0,plain,
% 22.95/3.49      ( k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,X1) ),
% 22.95/3.49      inference(cnf_transformation,[],[f79]) ).
% 22.95/3.49  
% 22.95/3.49  cnf(c_13,plain,
% 22.95/3.49      ( k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
% 22.95/3.49      inference(cnf_transformation,[],[f55]) ).
% 22.95/3.49  
% 22.95/3.49  cnf(c_973,plain,
% 22.95/3.49      ( k5_xboole_0(X0,k5_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2)) = k5_xboole_0(k4_xboole_0(X0,X1),X2) ),
% 22.95/3.49      inference(superposition,[status(thm)],[c_0,c_13]) ).
% 22.95/3.49  
% 22.95/3.49  cnf(c_16070,plain,
% 22.95/3.49      ( k5_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k5_xboole_0(X0,k1_xboole_0) ),
% 22.95/3.49      inference(superposition,[status(thm)],[c_14,c_973]) ).
% 22.95/3.49  
% 22.95/3.49  cnf(c_11,plain,
% 22.95/3.49      ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
% 22.95/3.49      inference(cnf_transformation,[],[f53]) ).
% 22.95/3.49  
% 22.95/3.49  cnf(c_16222,plain,
% 22.95/3.49      ( k5_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) = X0 ),
% 22.95/3.49      inference(light_normalisation,[status(thm)],[c_16070,c_11]) ).
% 22.95/3.49  
% 22.95/3.49  cnf(c_16535,plain,
% 22.95/3.49      ( k5_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,k4_xboole_0(X1,X0))) = X0 ),
% 22.95/3.49      inference(superposition,[status(thm)],[c_1,c_16222]) ).
% 22.95/3.49  
% 22.95/3.49  cnf(c_12,plain,
% 22.95/3.49      ( r1_tarski(X0,k5_xboole_0(X0,k4_xboole_0(X1,X0))) ),
% 22.95/3.49      inference(cnf_transformation,[],[f87]) ).
% 22.95/3.49  
% 22.95/3.49  cnf(c_735,plain,
% 22.95/3.49      ( r1_tarski(X0,k5_xboole_0(X0,k4_xboole_0(X1,X0))) = iProver_top ),
% 22.95/3.49      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 22.95/3.49  
% 22.95/3.49  cnf(c_22,negated_conjecture,
% 22.95/3.49      ( k5_xboole_0(sK3,k4_xboole_0(sK4,sK3)) = k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) ),
% 22.95/3.49      inference(cnf_transformation,[],[f95]) ).
% 22.95/3.49  
% 22.95/3.49  cnf(c_17,plain,
% 22.95/3.49      ( ~ r1_tarski(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))
% 22.95/3.49      | k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) = X0
% 22.95/3.49      | k1_xboole_0 = X0 ),
% 22.95/3.49      inference(cnf_transformation,[],[f90]) ).
% 22.95/3.49  
% 22.95/3.49  cnf(c_732,plain,
% 22.95/3.49      ( k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) = X1
% 22.95/3.49      | k1_xboole_0 = X1
% 22.95/3.49      | r1_tarski(X1,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) != iProver_top ),
% 22.95/3.49      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 22.95/3.49  
% 22.95/3.49  cnf(c_918,plain,
% 22.95/3.49      ( k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) = X0
% 22.95/3.49      | k1_xboole_0 = X0
% 22.95/3.49      | r1_tarski(X0,k5_xboole_0(sK3,k4_xboole_0(sK4,sK3))) != iProver_top ),
% 22.95/3.49      inference(superposition,[status(thm)],[c_22,c_732]) ).
% 22.95/3.49  
% 22.95/3.49  cnf(c_919,plain,
% 22.95/3.49      ( k5_xboole_0(sK3,k4_xboole_0(sK4,sK3)) = X0
% 22.95/3.49      | k1_xboole_0 = X0
% 22.95/3.49      | r1_tarski(X0,k5_xboole_0(sK3,k4_xboole_0(sK4,sK3))) != iProver_top ),
% 22.95/3.49      inference(demodulation,[status(thm)],[c_918,c_22]) ).
% 22.95/3.49  
% 22.95/3.49  cnf(c_1078,plain,
% 22.95/3.49      ( k5_xboole_0(sK3,k4_xboole_0(sK4,sK3)) = sK3 | sK3 = k1_xboole_0 ),
% 22.95/3.49      inference(superposition,[status(thm)],[c_735,c_919]) ).
% 22.95/3.49  
% 22.95/3.49  cnf(c_976,plain,
% 22.95/3.49      ( k5_xboole_0(X0,k5_xboole_0(X1,k4_xboole_0(k5_xboole_0(X0,X1),k4_xboole_0(k5_xboole_0(X0,X1),X2)))) = k4_xboole_0(k5_xboole_0(X0,X1),X2) ),
% 22.95/3.49      inference(superposition,[status(thm)],[c_13,c_0]) ).
% 22.95/3.49  
% 22.95/3.49  cnf(c_18437,plain,
% 22.95/3.49      ( k5_xboole_0(sK3,k5_xboole_0(k4_xboole_0(sK4,sK3),k4_xboole_0(sK3,k4_xboole_0(sK3,X0)))) = k4_xboole_0(k5_xboole_0(sK3,k4_xboole_0(sK4,sK3)),X0)
% 22.95/3.49      | sK3 = k1_xboole_0 ),
% 22.95/3.49      inference(superposition,[status(thm)],[c_1078,c_976]) ).
% 22.95/3.49  
% 22.95/3.49  cnf(c_19500,plain,
% 22.95/3.49      ( k4_xboole_0(k5_xboole_0(sK3,k4_xboole_0(sK4,sK3)),sK4) = k5_xboole_0(sK3,sK4)
% 22.95/3.49      | sK3 = k1_xboole_0 ),
% 22.95/3.49      inference(superposition,[status(thm)],[c_16535,c_18437]) ).
% 22.95/3.49  
% 22.95/3.49  cnf(c_19787,plain,
% 22.95/3.49      ( sK3 = k1_xboole_0
% 22.95/3.49      | r1_tarski(sK4,k5_xboole_0(sK4,k5_xboole_0(sK3,sK4))) = iProver_top ),
% 22.95/3.49      inference(superposition,[status(thm)],[c_19500,c_735]) ).
% 22.95/3.49  
% 22.95/3.49  cnf(c_10,plain,
% 22.95/3.49      ( k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) = k1_xboole_0 ),
% 22.95/3.49      inference(cnf_transformation,[],[f86]) ).
% 22.95/3.49  
% 22.95/3.49  cnf(c_923,plain,
% 22.95/3.49      ( k5_xboole_0(X0,k1_xboole_0) = k4_xboole_0(X0,k1_xboole_0) ),
% 22.95/3.49      inference(superposition,[status(thm)],[c_10,c_0]) ).
% 22.95/3.49  
% 22.95/3.49  cnf(c_926,plain,
% 22.95/3.49      ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
% 22.95/3.49      inference(light_normalisation,[status(thm)],[c_923,c_11]) ).
% 22.95/3.49  
% 22.95/3.49  cnf(c_1410,plain,
% 22.95/3.49      ( k4_xboole_0(X0,X0) = k1_xboole_0 ),
% 22.95/3.49      inference(demodulation,[status(thm)],[c_926,c_10]) ).
% 22.95/3.49  
% 22.95/3.49  cnf(c_979,plain,
% 22.95/3.49      ( k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X0,X1))) = k1_xboole_0 ),
% 22.95/3.49      inference(superposition,[status(thm)],[c_13,c_14]) ).
% 22.95/3.49  
% 22.95/3.49  cnf(c_16073,plain,
% 22.95/3.49      ( k5_xboole_0(k4_xboole_0(X0,X1),k5_xboole_0(X2,k5_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2))) = k5_xboole_0(X0,k1_xboole_0) ),
% 22.95/3.49      inference(superposition,[status(thm)],[c_979,c_973]) ).
% 22.95/3.49  
% 22.95/3.49  cnf(c_16221,plain,
% 22.95/3.49      ( k5_xboole_0(k4_xboole_0(X0,X1),k5_xboole_0(X2,k5_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2))) = X0 ),
% 22.95/3.49      inference(light_normalisation,[status(thm)],[c_16073,c_11]) ).
% 22.95/3.49  
% 22.95/3.49  cnf(c_34128,plain,
% 22.95/3.49      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(X0,k5_xboole_0(k4_xboole_0(X1,k1_xboole_0),X0))) = X1 ),
% 22.95/3.49      inference(superposition,[status(thm)],[c_1410,c_16221]) ).
% 22.95/3.49  
% 22.95/3.49  cnf(c_975,plain,
% 22.95/3.49      ( k5_xboole_0(X0,k5_xboole_0(X0,X1)) = k5_xboole_0(k1_xboole_0,X1) ),
% 22.95/3.49      inference(superposition,[status(thm)],[c_14,c_13]) ).
% 22.95/3.49  
% 22.95/3.49  cnf(c_2405,plain,
% 22.95/3.49      ( k5_xboole_0(k1_xboole_0,X0) = k5_xboole_0(X0,k1_xboole_0) ),
% 22.95/3.49      inference(superposition,[status(thm)],[c_14,c_975]) ).
% 22.95/3.49  
% 22.95/3.49  cnf(c_2434,plain,
% 22.95/3.49      ( k5_xboole_0(k1_xboole_0,X0) = X0 ),
% 22.95/3.49      inference(light_normalisation,[status(thm)],[c_2405,c_11]) ).
% 22.95/3.49  
% 22.95/3.49  cnf(c_34270,plain,
% 22.95/3.49      ( k5_xboole_0(X0,k5_xboole_0(X1,X0)) = X1 ),
% 22.95/3.49      inference(demodulation,[status(thm)],[c_34128,c_926,c_2434]) ).
% 22.95/3.49  
% 22.95/3.49  cnf(c_69451,plain,
% 22.95/3.49      ( sK3 = k1_xboole_0 | r1_tarski(sK4,sK3) = iProver_top ),
% 22.95/3.49      inference(demodulation,[status(thm)],[c_19787,c_34270]) ).
% 22.95/3.49  
% 22.95/3.49  cnf(c_1081,plain,
% 22.95/3.49      ( k5_xboole_0(sK3,k4_xboole_0(sK4,sK3)) = X0
% 22.95/3.49      | sK3 = k1_xboole_0
% 22.95/3.49      | k1_xboole_0 = X0
% 22.95/3.49      | r1_tarski(X0,sK3) != iProver_top ),
% 22.95/3.49      inference(superposition,[status(thm)],[c_1078,c_919]) ).
% 22.95/3.49  
% 22.95/3.49  cnf(c_69454,plain,
% 22.95/3.49      ( k5_xboole_0(sK3,k4_xboole_0(sK4,sK3)) = sK4
% 22.95/3.49      | sK3 = k1_xboole_0
% 22.95/3.49      | sK4 = k1_xboole_0 ),
% 22.95/3.49      inference(superposition,[status(thm)],[c_69451,c_1081]) ).
% 22.95/3.49  
% 22.95/3.49  cnf(c_2419,plain,
% 22.95/3.49      ( k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(k5_xboole_0(X0,X1),X2))) = k5_xboole_0(k1_xboole_0,X2) ),
% 22.95/3.49      inference(superposition,[status(thm)],[c_975,c_13]) ).
% 22.95/3.49  
% 22.95/3.49  cnf(c_974,plain,
% 22.95/3.49      ( k5_xboole_0(X0,k5_xboole_0(k1_xboole_0,X1)) = k5_xboole_0(X0,X1) ),
% 22.95/3.49      inference(superposition,[status(thm)],[c_11,c_13]) ).
% 22.95/3.49  
% 22.95/3.49  cnf(c_1947,plain,
% 22.95/3.49      ( k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(k1_xboole_0,X2))) = k5_xboole_0(k5_xboole_0(X0,X1),X2) ),
% 22.95/3.49      inference(superposition,[status(thm)],[c_974,c_13]) ).
% 22.95/3.49  
% 22.95/3.49  cnf(c_1953,plain,
% 22.95/3.49      ( k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2) ),
% 22.95/3.49      inference(demodulation,[status(thm)],[c_1947,c_974]) ).
% 22.95/3.49  
% 22.95/3.49  cnf(c_2500,plain,
% 22.95/3.49      ( k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X0,k5_xboole_0(X1,X2)))) = k5_xboole_0(k1_xboole_0,X2) ),
% 22.95/3.49      inference(light_normalisation,[status(thm)],[c_2419,c_1953]) ).
% 22.95/3.49  
% 22.95/3.49  cnf(c_2501,plain,
% 22.95/3.49      ( k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X0,k5_xboole_0(X1,X2)))) = X2 ),
% 22.95/3.49      inference(demodulation,[status(thm)],[c_2500,c_2434]) ).
% 22.95/3.49  
% 22.95/3.49  cnf(c_2435,plain,
% 22.95/3.49      ( k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1 ),
% 22.95/3.49      inference(demodulation,[status(thm)],[c_2434,c_975]) ).
% 22.95/3.49  
% 22.95/3.49  cnf(c_58003,plain,
% 22.95/3.49      ( k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X0,X2))) = k5_xboole_0(X1,X2) ),
% 22.95/3.49      inference(superposition,[status(thm)],[c_2501,c_2435]) ).
% 22.95/3.49  
% 22.95/3.49  cnf(c_58018,plain,
% 22.95/3.49      ( k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X0,X2))) = k5_xboole_0(X3,k5_xboole_0(X1,k5_xboole_0(X3,X2))) ),
% 22.95/3.49      inference(superposition,[status(thm)],[c_2501,c_2501]) ).
% 22.95/3.49  
% 22.95/3.49  cnf(c_58228,plain,
% 22.95/3.49      ( k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X0,X2))) = sP0_iProver_split(X1,X2) ),
% 22.95/3.49      inference(splitting,
% 22.95/3.49                [splitting(split),new_symbols(definition,[sP0_iProver_split])],
% 22.95/3.49                [c_58018]) ).
% 22.95/3.49  
% 22.95/3.49  cnf(c_58408,plain,
% 22.95/3.49      ( sP0_iProver_split(X0,X1) = k5_xboole_0(X0,X1) ),
% 22.95/3.49      inference(light_normalisation,[status(thm)],[c_58003,c_58228]) ).
% 22.95/3.49  
% 22.95/3.49  cnf(c_69455,plain,
% 22.95/3.49      ( sP0_iProver_split(sK3,k4_xboole_0(sK4,sK3)) = sK4
% 22.95/3.49      | sK3 = k1_xboole_0
% 22.95/3.49      | sK4 = k1_xboole_0 ),
% 22.95/3.49      inference(demodulation,[status(thm)],[c_69454,c_58408]) ).
% 22.95/3.49  
% 22.95/3.49  cnf(c_19,negated_conjecture,
% 22.95/3.49      ( k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) != sK3
% 22.95/3.49      | k1_xboole_0 != sK4 ),
% 22.95/3.49      inference(cnf_transformation,[],[f92]) ).
% 22.95/3.49  
% 22.95/3.49  cnf(c_745,plain,
% 22.95/3.49      ( k5_xboole_0(sK3,k4_xboole_0(sK4,sK3)) != sK3 | sK4 != k1_xboole_0 ),
% 22.95/3.49      inference(light_normalisation,[status(thm)],[c_19,c_22]) ).
% 22.95/3.49  
% 22.95/3.49  cnf(c_1084,plain,
% 22.95/3.49      ( sK3 = k1_xboole_0 | sK4 != k1_xboole_0 ),
% 22.95/3.49      inference(superposition,[status(thm)],[c_1078,c_745]) ).
% 22.95/3.49  
% 22.95/3.49  cnf(c_69456,plain,
% 22.95/3.49      ( sK3 = k1_xboole_0 | sP0_iProver_split(sK3,k4_xboole_0(sK4,sK3)) = sK4 ),
% 22.95/3.49      inference(global_propositional_subsumption,
% 22.95/3.49                [status(thm)],
% 22.95/3.49                [c_69455,c_1084]) ).
% 22.95/3.49  
% 22.95/3.49  cnf(c_69457,plain,
% 22.95/3.49      ( sP0_iProver_split(sK3,k4_xboole_0(sK4,sK3)) = sK4 | sK3 = k1_xboole_0 ),
% 22.95/3.49      inference(renaming,[status(thm)],[c_69456]) ).
% 22.95/3.49  
% 22.95/3.49  cnf(c_16569,plain,
% 22.95/3.49      ( k5_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) = k5_xboole_0(X0,X0) ),
% 22.95/3.49      inference(superposition,[status(thm)],[c_16222,c_973]) ).
% 22.95/3.49  
% 22.95/3.49  cnf(c_16579,plain,
% 22.95/3.49      ( k5_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) = k1_xboole_0 ),
% 22.95/3.49      inference(light_normalisation,[status(thm)],[c_16569,c_14]) ).
% 22.95/3.49  
% 22.95/3.49  cnf(c_53725,plain,
% 22.95/3.49      ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k5_xboole_0(k4_xboole_0(X0,X1),k1_xboole_0) ),
% 22.95/3.49      inference(superposition,[status(thm)],[c_16579,c_2435]) ).
% 22.95/3.49  
% 22.95/3.49  cnf(c_53992,plain,
% 22.95/3.49      ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,X1) ),
% 22.95/3.49      inference(demodulation,[status(thm)],[c_53725,c_11]) ).
% 22.95/3.49  
% 22.95/3.49  cnf(c_54704,plain,
% 22.95/3.49      ( k5_xboole_0(sK3,k5_xboole_0(k4_xboole_0(sK4,sK3),k4_xboole_0(sK3,X0))) = k4_xboole_0(k5_xboole_0(sK3,k4_xboole_0(sK4,sK3)),k4_xboole_0(sK3,X0))
% 22.95/3.49      | sK3 = k1_xboole_0 ),
% 22.95/3.49      inference(superposition,[status(thm)],[c_53992,c_18437]) ).
% 22.95/3.49  
% 22.95/3.49  cnf(c_1080,plain,
% 22.95/3.49      ( k5_xboole_0(sK3,k5_xboole_0(k4_xboole_0(sK4,sK3),X0)) = k5_xboole_0(sK3,X0)
% 22.95/3.49      | sK3 = k1_xboole_0 ),
% 22.95/3.49      inference(superposition,[status(thm)],[c_1078,c_13]) ).
% 22.95/3.49  
% 22.95/3.49  cnf(c_978,plain,
% 22.95/3.49      ( r1_tarski(k5_xboole_0(X0,X1),k5_xboole_0(X0,k5_xboole_0(X1,k4_xboole_0(X2,k5_xboole_0(X0,X1))))) = iProver_top ),
% 22.95/3.49      inference(superposition,[status(thm)],[c_13,c_735]) ).
% 22.95/3.49  
% 22.95/3.49  cnf(c_20825,plain,
% 22.95/3.49      ( sK3 = k1_xboole_0
% 22.95/3.49      | r1_tarski(sK3,k5_xboole_0(sK3,k5_xboole_0(k4_xboole_0(sK4,sK3),k4_xboole_0(X0,sK3)))) = iProver_top ),
% 22.95/3.49      inference(superposition,[status(thm)],[c_1078,c_978]) ).
% 22.95/3.49  
% 22.95/3.49  cnf(c_9,plain,
% 22.95/3.49      ( ~ r1_tarski(X0,X1) | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0 ),
% 22.95/3.49      inference(cnf_transformation,[],[f85]) ).
% 22.95/3.49  
% 22.95/3.49  cnf(c_736,plain,
% 22.95/3.49      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0
% 22.95/3.49      | r1_tarski(X0,X1) != iProver_top ),
% 22.95/3.49      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 22.95/3.49  
% 22.95/3.49  cnf(c_22225,plain,
% 22.95/3.49      ( k4_xboole_0(sK3,k4_xboole_0(sK3,k5_xboole_0(sK3,k5_xboole_0(k4_xboole_0(sK4,sK3),k4_xboole_0(X0,sK3))))) = sK3
% 22.95/3.49      | sK3 = k1_xboole_0 ),
% 22.95/3.49      inference(superposition,[status(thm)],[c_20825,c_736]) ).
% 22.95/3.49  
% 22.95/3.49  cnf(c_22298,plain,
% 22.95/3.49      ( k4_xboole_0(k5_xboole_0(sK3,k4_xboole_0(sK4,sK3)),k5_xboole_0(sK3,k5_xboole_0(k4_xboole_0(sK4,sK3),k4_xboole_0(X0,sK3)))) = k5_xboole_0(sK3,k5_xboole_0(k4_xboole_0(sK4,sK3),sK3))
% 22.95/3.49      | sK3 = k1_xboole_0 ),
% 22.95/3.49      inference(superposition,[status(thm)],[c_22225,c_18437]) ).
% 22.95/3.49  
% 22.95/3.49  cnf(c_23510,plain,
% 22.95/3.49      ( k4_xboole_0(sK3,k5_xboole_0(sK3,k5_xboole_0(k4_xboole_0(sK4,sK3),k4_xboole_0(X0,sK3)))) = k5_xboole_0(sK3,k5_xboole_0(k4_xboole_0(sK4,sK3),sK3))
% 22.95/3.49      | sK3 = k1_xboole_0 ),
% 22.95/3.49      inference(superposition,[status(thm)],[c_1078,c_22298]) ).
% 22.95/3.49  
% 22.95/3.49  cnf(c_23668,plain,
% 22.95/3.49      ( k4_xboole_0(k5_xboole_0(sK3,k4_xboole_0(sK4,sK3)),k5_xboole_0(sK3,k5_xboole_0(k4_xboole_0(sK4,sK3),k4_xboole_0(X0,sK3)))) = k5_xboole_0(sK3,k5_xboole_0(k4_xboole_0(sK4,sK3),k4_xboole_0(sK3,k5_xboole_0(sK3,k5_xboole_0(k4_xboole_0(sK4,sK3),sK3)))))
% 22.95/3.49      | sK3 = k1_xboole_0 ),
% 22.95/3.49      inference(superposition,[status(thm)],[c_23510,c_18437]) ).
% 22.95/3.49  
% 22.95/3.49  cnf(c_27706,plain,
% 22.95/3.49      ( k5_xboole_0(sK3,k5_xboole_0(k4_xboole_0(sK4,sK3),k4_xboole_0(sK3,k5_xboole_0(sK3,k5_xboole_0(k4_xboole_0(sK4,sK3),sK3))))) = k4_xboole_0(k5_xboole_0(sK3,k4_xboole_0(sK4,sK3)),k5_xboole_0(sK3,k4_xboole_0(X0,sK3)))
% 22.95/3.49      | sK3 = k1_xboole_0 ),
% 22.95/3.49      inference(superposition,[status(thm)],[c_1080,c_23668]) ).
% 22.95/3.49  
% 22.95/3.49  cnf(c_27704,plain,
% 22.95/3.49      ( k5_xboole_0(sK3,k5_xboole_0(k4_xboole_0(sK4,sK3),k4_xboole_0(sK3,k5_xboole_0(sK3,k5_xboole_0(k4_xboole_0(sK4,sK3),sK3))))) = k4_xboole_0(sK3,k5_xboole_0(sK3,k5_xboole_0(k4_xboole_0(sK4,sK3),k4_xboole_0(X0,sK3))))
% 22.95/3.49      | sK3 = k1_xboole_0 ),
% 22.95/3.49      inference(superposition,[status(thm)],[c_1078,c_23668]) ).
% 22.95/3.49  
% 22.95/3.49  cnf(c_30130,plain,
% 22.95/3.49      ( k4_xboole_0(k5_xboole_0(sK3,k4_xboole_0(sK4,sK3)),k5_xboole_0(sK3,k4_xboole_0(X0,sK3))) = k4_xboole_0(sK3,k5_xboole_0(sK3,k5_xboole_0(k4_xboole_0(sK4,sK3),k4_xboole_0(X1,sK3))))
% 22.95/3.49      | sK3 = k1_xboole_0 ),
% 22.95/3.49      inference(superposition,[status(thm)],[c_27706,c_27704]) ).
% 22.95/3.49  
% 22.95/3.49  cnf(c_30391,plain,
% 22.95/3.49      ( k5_xboole_0(sK3,k5_xboole_0(k4_xboole_0(sK4,sK3),k4_xboole_0(sK3,k4_xboole_0(k5_xboole_0(sK3,k4_xboole_0(sK4,sK3)),k5_xboole_0(sK3,k4_xboole_0(X0,sK3)))))) = k4_xboole_0(k5_xboole_0(sK3,k4_xboole_0(sK4,sK3)),k5_xboole_0(sK3,k5_xboole_0(k4_xboole_0(sK4,sK3),k4_xboole_0(X1,sK3))))
% 22.95/3.49      | sK3 = k1_xboole_0 ),
% 22.95/3.49      inference(superposition,[status(thm)],[c_30130,c_18437]) ).
% 22.95/3.49  
% 22.95/3.49  cnf(c_27947,plain,
% 22.95/3.49      ( k4_xboole_0(k5_xboole_0(sK3,k4_xboole_0(sK4,sK3)),k5_xboole_0(sK3,k5_xboole_0(k4_xboole_0(sK4,sK3),k4_xboole_0(X0,sK3)))) = k4_xboole_0(sK3,k5_xboole_0(sK3,k5_xboole_0(k4_xboole_0(sK4,sK3),k4_xboole_0(X1,sK3))))
% 22.95/3.49      | sK3 = k1_xboole_0 ),
% 22.95/3.49      inference(superposition,[status(thm)],[c_27704,c_23668]) ).
% 22.95/3.49  
% 22.95/3.49  cnf(c_962,plain,
% 22.95/3.49      ( k5_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0))) = k4_xboole_0(X0,X1) ),
% 22.95/3.49      inference(superposition,[status(thm)],[c_1,c_0]) ).
% 22.95/3.49  
% 22.95/3.49  cnf(c_19499,plain,
% 22.95/3.49      ( k4_xboole_0(k5_xboole_0(sK3,k4_xboole_0(sK4,sK3)),k4_xboole_0(sK4,sK3)) = k5_xboole_0(sK3,k4_xboole_0(k4_xboole_0(sK4,sK3),sK3))
% 22.95/3.49      | sK3 = k1_xboole_0 ),
% 22.95/3.49      inference(superposition,[status(thm)],[c_962,c_18437]) ).
% 22.95/3.49  
% 22.95/3.49  cnf(c_7,plain,
% 22.95/3.49      ( ~ r1_xboole_0(X0,X1)
% 22.95/3.49      | ~ r2_hidden(X2,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
% 22.95/3.49      inference(cnf_transformation,[],[f83]) ).
% 22.95/3.49  
% 22.95/3.49  cnf(c_738,plain,
% 22.95/3.49      ( r1_xboole_0(X0,X1) != iProver_top
% 22.95/3.49      | r2_hidden(X2,k4_xboole_0(X0,k4_xboole_0(X0,X1))) != iProver_top ),
% 22.95/3.49      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 22.95/3.49  
% 22.95/3.49  cnf(c_20072,plain,
% 22.95/3.49      ( sK3 = k1_xboole_0
% 22.95/3.49      | r1_xboole_0(k5_xboole_0(sK3,k4_xboole_0(sK4,sK3)),k4_xboole_0(sK4,sK3)) != iProver_top
% 22.95/3.49      | r2_hidden(X0,k4_xboole_0(k5_xboole_0(sK3,k4_xboole_0(sK4,sK3)),k5_xboole_0(sK3,k4_xboole_0(k4_xboole_0(sK4,sK3),sK3)))) != iProver_top ),
% 22.95/3.49      inference(superposition,[status(thm)],[c_19499,c_738]) ).
% 22.95/3.49  
% 22.95/3.49  cnf(c_2548,plain,
% 22.95/3.49      ( k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X2,k5_xboole_0(X0,k5_xboole_0(X1,X2)))) = k1_xboole_0 ),
% 22.95/3.49      inference(superposition,[status(thm)],[c_13,c_979]) ).
% 22.95/3.49  
% 22.95/3.49  cnf(c_4888,plain,
% 22.95/3.49      ( k5_xboole_0(sK3,k5_xboole_0(X0,k5_xboole_0(sK3,k5_xboole_0(k4_xboole_0(sK4,sK3),X0)))) = k1_xboole_0
% 22.95/3.49      | sK3 = k1_xboole_0 ),
% 22.95/3.49      inference(superposition,[status(thm)],[c_1078,c_2548]) ).
% 22.95/3.49  
% 22.95/3.49  cnf(c_16146,plain,
% 22.95/3.49      ( k5_xboole_0(k4_xboole_0(sK3,X0),k5_xboole_0(sK3,k5_xboole_0(k4_xboole_0(sK4,sK3),k4_xboole_0(sK3,k4_xboole_0(sK3,X0))))) = k1_xboole_0
% 22.95/3.49      | sK3 = k1_xboole_0 ),
% 22.95/3.49      inference(superposition,[status(thm)],[c_973,c_4888]) ).
% 22.95/3.49  
% 22.95/3.49  cnf(c_16979,plain,
% 22.95/3.49      ( k5_xboole_0(k4_xboole_0(sK3,X0),k5_xboole_0(sK3,k5_xboole_0(k4_xboole_0(sK4,sK3),k4_xboole_0(X0,k4_xboole_0(X0,sK3))))) = k1_xboole_0
% 22.95/3.49      | sK3 = k1_xboole_0 ),
% 22.95/3.49      inference(superposition,[status(thm)],[c_1,c_16146]) ).
% 22.95/3.49  
% 22.95/3.49  cnf(c_19539,plain,
% 22.95/3.49      ( k5_xboole_0(k4_xboole_0(sK3,sK3),k4_xboole_0(k5_xboole_0(sK3,k4_xboole_0(sK4,sK3)),sK3)) = k1_xboole_0
% 22.95/3.49      | sK3 = k1_xboole_0 ),
% 22.95/3.49      inference(superposition,[status(thm)],[c_18437,c_16979]) ).
% 22.95/3.49  
% 22.95/3.49  cnf(c_19540,plain,
% 22.95/3.49      ( k4_xboole_0(k5_xboole_0(sK3,k4_xboole_0(sK4,sK3)),sK3) = k1_xboole_0
% 22.95/3.49      | sK3 = k1_xboole_0 ),
% 22.95/3.49      inference(demodulation,[status(thm)],[c_19539,c_1410,c_2434]) ).
% 22.95/3.49  
% 22.95/3.49  cnf(c_2406,plain,
% 22.95/3.49      ( k5_xboole_0(k1_xboole_0,k4_xboole_0(sK4,sK3)) = k5_xboole_0(sK3,sK3)
% 22.95/3.49      | sK3 = k1_xboole_0 ),
% 22.95/3.49      inference(superposition,[status(thm)],[c_1078,c_975]) ).
% 22.95/3.49  
% 22.95/3.49  cnf(c_2515,plain,
% 22.95/3.49      ( k4_xboole_0(sK4,sK3) = k1_xboole_0 | sK3 = k1_xboole_0 ),
% 22.95/3.49      inference(demodulation,[status(thm)],[c_2406,c_14,c_2434]) ).
% 22.95/3.49  
% 22.95/3.49  cnf(c_1743,plain,
% 22.95/3.49      ( k5_xboole_0(sK3,k4_xboole_0(k4_xboole_0(sK4,sK3),k4_xboole_0(k4_xboole_0(sK4,sK3),X0))) = k5_xboole_0(sK3,k4_xboole_0(k4_xboole_0(sK4,sK3),X0))
% 22.95/3.49      | sK3 = k1_xboole_0 ),
% 22.95/3.49      inference(superposition,[status(thm)],[c_0,c_1080]) ).
% 22.95/3.49  
% 22.95/3.49  cnf(c_2656,plain,
% 22.95/3.49      ( k5_xboole_0(sK3,k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0))) = k5_xboole_0(sK3,k4_xboole_0(k4_xboole_0(sK4,sK3),X0))
% 22.95/3.49      | sK3 = k1_xboole_0 ),
% 22.95/3.49      inference(superposition,[status(thm)],[c_2515,c_1743]) ).
% 22.95/3.49  
% 22.95/3.49  cnf(c_964,plain,
% 22.95/3.49      ( k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0)) = k1_xboole_0 ),
% 22.95/3.49      inference(superposition,[status(thm)],[c_1,c_10]) ).
% 22.95/3.49  
% 22.95/3.49  cnf(c_1504,plain,
% 22.95/3.49      ( k4_xboole_0(k1_xboole_0,X0) = k5_xboole_0(k1_xboole_0,k1_xboole_0) ),
% 22.95/3.49      inference(superposition,[status(thm)],[c_964,c_0]) ).
% 22.95/3.49  
% 22.95/3.49  cnf(c_1509,plain,
% 22.95/3.49      ( k4_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
% 22.95/3.49      inference(demodulation,[status(thm)],[c_1504,c_11]) ).
% 22.95/3.49  
% 22.95/3.49  cnf(c_2672,plain,
% 22.95/3.49      ( k5_xboole_0(sK3,k4_xboole_0(k4_xboole_0(sK4,sK3),X0)) = k5_xboole_0(sK3,k4_xboole_0(k1_xboole_0,k1_xboole_0))
% 22.95/3.49      | sK3 = k1_xboole_0 ),
% 22.95/3.49      inference(light_normalisation,[status(thm)],[c_2656,c_1509]) ).
% 22.95/3.49  
% 22.95/3.49  cnf(c_2673,plain,
% 22.95/3.49      ( k5_xboole_0(sK3,k4_xboole_0(k4_xboole_0(sK4,sK3),X0)) = sK3
% 22.95/3.49      | sK3 = k1_xboole_0 ),
% 22.95/3.49      inference(demodulation,[status(thm)],[c_2672,c_11,c_1509]) ).
% 22.95/3.49  
% 22.95/3.49  cnf(c_4964,plain,
% 22.95/3.49      ( k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X1,k5_xboole_0(X0,k1_xboole_0))) = k1_xboole_0 ),
% 22.95/3.49      inference(superposition,[status(thm)],[c_14,c_2548]) ).
% 22.95/3.49  
% 22.95/3.49  cnf(c_5101,plain,
% 22.95/3.49      ( k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X1,X0)) = k1_xboole_0 ),
% 22.95/3.49      inference(light_normalisation,[status(thm)],[c_4964,c_11]) ).
% 22.95/3.49  
% 22.95/3.49  cnf(c_5546,plain,
% 22.95/3.49      ( k5_xboole_0(k5_xboole_0(k4_xboole_0(k4_xboole_0(sK4,sK3),X0),sK3),sK3) = k1_xboole_0
% 22.95/3.49      | sK3 = k1_xboole_0 ),
% 22.95/3.49      inference(superposition,[status(thm)],[c_2673,c_5101]) ).
% 22.95/3.49  
% 22.95/3.49  cnf(c_5563,plain,
% 22.95/3.49      ( k4_xboole_0(k4_xboole_0(sK4,sK3),X0) = k1_xboole_0
% 22.95/3.49      | sK3 = k1_xboole_0 ),
% 22.95/3.49      inference(demodulation,[status(thm)],[c_5546,c_11,c_14,c_1953]) ).
% 22.95/3.49  
% 22.95/3.49  cnf(c_19503,plain,
% 22.95/3.49      ( k5_xboole_0(sK3,k5_xboole_0(k4_xboole_0(sK4,sK3),k4_xboole_0(X0,k4_xboole_0(X0,sK3)))) = k4_xboole_0(k5_xboole_0(sK3,k4_xboole_0(sK4,sK3)),X0)
% 22.95/3.49      | sK3 = k1_xboole_0 ),
% 22.95/3.49      inference(superposition,[status(thm)],[c_1,c_18437]) ).
% 22.95/3.49  
% 22.95/3.49  cnf(c_20208,plain,
% 22.95/3.49      ( k5_xboole_0(sK3,k5_xboole_0(k4_xboole_0(sK4,sK3),k4_xboole_0(k4_xboole_0(sK4,sK3),k1_xboole_0))) = k4_xboole_0(k5_xboole_0(sK3,k4_xboole_0(sK4,sK3)),k4_xboole_0(sK4,sK3))
% 22.95/3.49      | sK3 = k1_xboole_0 ),
% 22.95/3.49      inference(superposition,[status(thm)],[c_5563,c_19503]) ).
% 22.95/3.49  
% 22.95/3.49  cnf(c_2402,plain,
% 22.95/3.49      ( k5_xboole_0(k1_xboole_0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k5_xboole_0(X0,k4_xboole_0(X0,X1)) ),
% 22.95/3.49      inference(superposition,[status(thm)],[c_0,c_975]) ).
% 22.95/3.49  
% 22.95/3.49  cnf(c_2519,plain,
% 22.95/3.49      ( k5_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
% 22.95/3.49      inference(demodulation,[status(thm)],[c_2402,c_2434]) ).
% 22.95/3.49  
% 22.95/3.49  cnf(c_20263,plain,
% 22.95/3.49      ( k5_xboole_0(sK3,k4_xboole_0(k4_xboole_0(sK4,sK3),k4_xboole_0(k4_xboole_0(sK4,sK3),k1_xboole_0))) = k4_xboole_0(k5_xboole_0(sK3,k4_xboole_0(sK4,sK3)),k4_xboole_0(sK4,sK3))
% 22.95/3.49      | sK3 = k1_xboole_0 ),
% 22.95/3.49      inference(demodulation,[status(thm)],[c_20208,c_2519]) ).
% 22.95/3.49  
% 22.95/3.49  cnf(c_20264,plain,
% 22.95/3.49      ( k4_xboole_0(k5_xboole_0(sK3,k4_xboole_0(sK4,sK3)),k4_xboole_0(sK4,sK3)) = sK3
% 22.95/3.49      | sK3 = k1_xboole_0 ),
% 22.95/3.49      inference(demodulation,[status(thm)],[c_20263,c_11,c_926,c_1410]) ).
% 22.95/3.49  
% 22.95/3.49  cnf(c_5,plain,
% 22.95/3.49      ( r1_xboole_0(X0,X1)
% 22.95/3.49      | k4_xboole_0(X0,k4_xboole_0(X0,X1)) != k1_xboole_0 ),
% 22.95/3.49      inference(cnf_transformation,[],[f81]) ).
% 22.95/3.49  
% 22.95/3.49  cnf(c_740,plain,
% 22.95/3.49      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) != k1_xboole_0
% 22.95/3.49      | r1_xboole_0(X0,X1) = iProver_top ),
% 22.95/3.49      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 22.95/3.49  
% 22.95/3.49  cnf(c_43838,plain,
% 22.95/3.49      ( k4_xboole_0(k5_xboole_0(sK3,k4_xboole_0(sK4,sK3)),sK3) != k1_xboole_0
% 22.95/3.49      | sK3 = k1_xboole_0
% 22.95/3.49      | r1_xboole_0(k5_xboole_0(sK3,k4_xboole_0(sK4,sK3)),k4_xboole_0(sK4,sK3)) = iProver_top ),
% 22.95/3.49      inference(superposition,[status(thm)],[c_20264,c_740]) ).
% 22.95/3.49  
% 22.95/3.49  cnf(c_44061,plain,
% 22.95/3.49      ( sK3 = k1_xboole_0
% 22.95/3.49      | r2_hidden(X0,k4_xboole_0(k5_xboole_0(sK3,k4_xboole_0(sK4,sK3)),k5_xboole_0(sK3,k4_xboole_0(k4_xboole_0(sK4,sK3),sK3)))) != iProver_top ),
% 22.95/3.49      inference(global_propositional_subsumption,
% 22.95/3.49                [status(thm)],
% 22.95/3.49                [c_20072,c_19540,c_43838]) ).
% 22.95/3.49  
% 22.95/3.49  cnf(c_44069,plain,
% 22.95/3.49      ( sK3 = k1_xboole_0
% 22.95/3.49      | r2_hidden(X0,k4_xboole_0(sK3,k5_xboole_0(sK3,k5_xboole_0(k4_xboole_0(sK4,sK3),k4_xboole_0(X1,sK3))))) != iProver_top ),
% 22.95/3.49      inference(superposition,[status(thm)],[c_30130,c_44061]) ).
% 22.95/3.49  
% 22.95/3.49  cnf(c_44506,plain,
% 22.95/3.49      ( sK3 = k1_xboole_0
% 22.95/3.49      | r2_hidden(X0,k4_xboole_0(k5_xboole_0(sK3,k4_xboole_0(sK4,sK3)),k5_xboole_0(sK3,k5_xboole_0(k4_xboole_0(sK4,sK3),k4_xboole_0(X1,sK3))))) != iProver_top ),
% 22.95/3.49      inference(superposition,[status(thm)],[c_27947,c_44069]) ).
% 22.95/3.49  
% 22.95/3.49  cnf(c_45846,plain,
% 22.95/3.49      ( sK3 = k1_xboole_0
% 22.95/3.49      | r2_hidden(X0,k5_xboole_0(sK3,k5_xboole_0(k4_xboole_0(sK4,sK3),k4_xboole_0(sK3,k4_xboole_0(k5_xboole_0(sK3,k4_xboole_0(sK4,sK3)),k5_xboole_0(sK3,k4_xboole_0(X1,sK3))))))) != iProver_top ),
% 22.95/3.49      inference(superposition,[status(thm)],[c_30391,c_44506]) ).
% 22.95/3.49  
% 22.95/3.49  cnf(c_56463,plain,
% 22.95/3.49      ( sK3 = k1_xboole_0
% 22.95/3.49      | r2_hidden(X0,k4_xboole_0(k5_xboole_0(sK3,k4_xboole_0(sK4,sK3)),k4_xboole_0(sK3,k4_xboole_0(k5_xboole_0(sK3,k4_xboole_0(sK4,sK3)),k5_xboole_0(sK3,k4_xboole_0(X1,sK3)))))) != iProver_top ),
% 22.95/3.49      inference(superposition,[status(thm)],[c_54704,c_45846]) ).
% 22.95/3.49  
% 22.95/3.49  cnf(c_59986,plain,
% 22.95/3.49      ( sK3 = k1_xboole_0
% 22.95/3.49      | r2_hidden(X0,k4_xboole_0(sP0_iProver_split(sK3,k4_xboole_0(sK4,sK3)),k4_xboole_0(sK3,k4_xboole_0(sP0_iProver_split(sK3,k4_xboole_0(sK4,sK3)),sP0_iProver_split(sK3,k4_xboole_0(X1,sK3)))))) != iProver_top ),
% 22.95/3.49      inference(demodulation,[status(thm)],[c_56463,c_58408]) ).
% 22.95/3.49  
% 22.95/3.49  cnf(c_69505,plain,
% 22.95/3.49      ( sK3 = k1_xboole_0
% 22.95/3.49      | r2_hidden(X0,k4_xboole_0(sK4,k4_xboole_0(sK3,k4_xboole_0(sK4,sP0_iProver_split(sK3,k4_xboole_0(X1,sK3)))))) != iProver_top ),
% 22.95/3.49      inference(superposition,[status(thm)],[c_69457,c_59986]) ).
% 22.95/3.49  
% 22.95/3.49  cnf(c_21,negated_conjecture,
% 22.95/3.49      ( k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) != sK3
% 22.95/3.49      | k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) != sK4 ),
% 22.95/3.49      inference(cnf_transformation,[],[f94]) ).
% 22.95/3.49  
% 22.95/3.49  cnf(c_746,plain,
% 22.95/3.49      ( k5_xboole_0(sK3,k4_xboole_0(sK4,sK3)) != sK3
% 22.95/3.49      | k5_xboole_0(sK3,k4_xboole_0(sK4,sK3)) != sK4 ),
% 22.95/3.49      inference(light_normalisation,[status(thm)],[c_21,c_22]) ).
% 22.95/3.49  
% 22.95/3.49  cnf(c_1083,plain,
% 22.95/3.49      ( k5_xboole_0(sK3,k4_xboole_0(sK4,sK3)) != sK3
% 22.95/3.49      | sK3 != sK4
% 22.95/3.49      | sK3 = k1_xboole_0 ),
% 22.95/3.49      inference(superposition,[status(thm)],[c_1078,c_746]) ).
% 22.95/3.49  
% 22.95/3.49  cnf(c_1167,plain,
% 22.95/3.49      ( sK3 != sK4 | sK3 = k1_xboole_0 ),
% 22.95/3.49      inference(global_propositional_subsumption,[status(thm)],[c_1083,c_1078]) ).
% 22.95/3.49  
% 22.95/3.49  cnf(c_69458,plain,
% 22.95/3.49      ( sP0_iProver_split(sK3,k1_xboole_0) = sK4 | sK3 = k1_xboole_0 ),
% 22.95/3.49      inference(superposition,[status(thm)],[c_2515,c_69457]) ).
% 22.95/3.49  
% 22.95/3.49  cnf(c_3448,plain,
% 22.95/3.49      ( k5_xboole_0(X0,k5_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X2)) = k5_xboole_0(k4_xboole_0(X0,X1),X2) ),
% 22.95/3.49      inference(superposition,[status(thm)],[c_962,c_13]) ).
% 22.95/3.49  
% 22.95/3.49  cnf(c_28998,plain,
% 22.95/3.49      ( k5_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X1,X0))))) = k5_xboole_0(X0,k1_xboole_0) ),
% 22.95/3.49      inference(superposition,[status(thm)],[c_16579,c_3448]) ).
% 22.95/3.49  
% 22.95/3.49  cnf(c_29204,plain,
% 22.95/3.49      ( k5_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X1,X0))))) = X0 ),
% 22.95/3.49      inference(light_normalisation,[status(thm)],[c_28998,c_11]) ).
% 22.95/3.49  
% 22.95/3.49  cnf(c_51903,plain,
% 22.95/3.49      ( k5_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X0,k4_xboole_0(X0,X1))))) = X0 ),
% 22.95/3.49      inference(superposition,[status(thm)],[c_1,c_29204]) ).
% 22.95/3.49  
% 22.95/3.49  cnf(c_57903,plain,
% 22.95/3.49      ( k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X1,X2),k5_xboole_0(X0,k1_xboole_0))) = k5_xboole_0(X3,k5_xboole_0(X1,k5_xboole_0(X2,X3))) ),
% 22.95/3.49      inference(superposition,[status(thm)],[c_2548,c_2501]) ).
% 22.95/3.49  
% 22.95/3.49  cnf(c_58808,plain,
% 22.95/3.49      ( sP0_iProver_split(X0,sP0_iProver_split(k5_xboole_0(X1,X2),k5_xboole_0(X0,k1_xboole_0))) = sP0_iProver_split(X3,sP0_iProver_split(X1,k5_xboole_0(X2,X3))) ),
% 22.95/3.49      inference(demodulation,[status(thm)],[c_57903,c_58408]) ).
% 22.95/3.49  
% 22.95/3.49  cnf(c_57919,plain,
% 22.95/3.49      ( k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X1,X2),k5_xboole_0(X0,k1_xboole_0))) = k5_xboole_0(X2,X1) ),
% 22.95/3.49      inference(superposition,[status(thm)],[c_5101,c_2501]) ).
% 22.95/3.49  
% 22.95/3.49  cnf(c_58771,plain,
% 22.95/3.49      ( sP0_iProver_split(X0,sP0_iProver_split(k5_xboole_0(X1,X2),k5_xboole_0(X0,k1_xboole_0))) = sP0_iProver_split(X2,X1) ),
% 22.95/3.49      inference(demodulation,[status(thm)],[c_57919,c_58408]) ).
% 22.95/3.49  
% 22.95/3.49  cnf(c_58772,plain,
% 22.95/3.49      ( sP0_iProver_split(X0,sP0_iProver_split(sP0_iProver_split(X1,X2),sP0_iProver_split(X0,k1_xboole_0))) = sP0_iProver_split(X2,X1) ),
% 22.95/3.49      inference(demodulation,[status(thm)],[c_58771,c_58408]) ).
% 22.95/3.49  
% 22.95/3.49  cnf(c_58809,plain,
% 22.95/3.49      ( sP0_iProver_split(X0,sP0_iProver_split(X1,sP0_iProver_split(X2,X0))) = sP0_iProver_split(X2,X1) ),
% 22.95/3.49      inference(demodulation,[status(thm)],[c_58808,c_58408,c_58772]) ).
% 22.95/3.49  
% 22.95/3.49  cnf(c_5300,plain,
% 22.95/3.49      ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,X2)),k5_xboole_0(X2,k5_xboole_0(X0,X1))) = k1_xboole_0 ),
% 22.95/3.49      inference(superposition,[status(thm)],[c_13,c_5101]) ).
% 22.95/3.49  
% 22.95/3.49  cnf(c_57922,plain,
% 22.95/3.49      ( k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X1,k5_xboole_0(X2,X3)),k5_xboole_0(X0,k1_xboole_0))) = k5_xboole_0(X3,k5_xboole_0(X1,X2)) ),
% 22.95/3.49      inference(superposition,[status(thm)],[c_5300,c_2501]) ).
% 22.95/3.49  
% 22.95/3.49  cnf(c_58695,plain,
% 22.95/3.49      ( sP0_iProver_split(X0,sP0_iProver_split(k5_xboole_0(X1,k5_xboole_0(X2,X3)),k5_xboole_0(X0,k1_xboole_0))) = sP0_iProver_split(X3,sP0_iProver_split(X1,X2)) ),
% 22.95/3.49      inference(demodulation,[status(thm)],[c_57922,c_58408]) ).
% 22.95/3.49  
% 22.95/3.49  cnf(c_58696,plain,
% 22.95/3.49      ( sP0_iProver_split(X0,sP0_iProver_split(sP0_iProver_split(X1,k5_xboole_0(X2,X3)),sP0_iProver_split(X0,k1_xboole_0))) = sP0_iProver_split(X3,sP0_iProver_split(X1,X2)) ),
% 22.95/3.49      inference(demodulation,[status(thm)],[c_58695,c_58408]) ).
% 22.95/3.49  
% 22.95/3.49  cnf(c_5339,plain,
% 22.95/3.49      ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,X2)),k5_xboole_0(X1,k5_xboole_0(X2,X0))) = k1_xboole_0 ),
% 22.95/3.49      inference(superposition,[status(thm)],[c_13,c_5101]) ).
% 22.95/3.49  
% 22.95/3.49  cnf(c_57924,plain,
% 22.95/3.49      ( k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X1,k5_xboole_0(X2,X3)),k5_xboole_0(X0,k1_xboole_0))) = k5_xboole_0(X2,k5_xboole_0(X3,X1)) ),
% 22.95/3.49      inference(superposition,[status(thm)],[c_5339,c_2501]) ).
% 22.95/3.49  
% 22.95/3.49  cnf(c_58690,plain,
% 22.95/3.49      ( sP0_iProver_split(X0,sP0_iProver_split(k5_xboole_0(X1,k5_xboole_0(X2,X3)),k5_xboole_0(X0,k1_xboole_0))) = sP0_iProver_split(X2,sP0_iProver_split(X3,X1)) ),
% 22.95/3.49      inference(demodulation,[status(thm)],[c_57924,c_58408]) ).
% 22.95/3.49  
% 22.95/3.49  cnf(c_58691,plain,
% 22.95/3.49      ( sP0_iProver_split(X0,sP0_iProver_split(sP0_iProver_split(X1,k5_xboole_0(X2,X3)),sP0_iProver_split(X0,k1_xboole_0))) = sP0_iProver_split(X2,sP0_iProver_split(X3,X1)) ),
% 22.95/3.49      inference(demodulation,[status(thm)],[c_58690,c_58408]) ).
% 22.95/3.49  
% 22.95/3.49  cnf(c_58692,plain,
% 22.95/3.49      ( sP0_iProver_split(X0,sP0_iProver_split(sP0_iProver_split(X1,sP0_iProver_split(X2,X3)),sP0_iProver_split(X0,k1_xboole_0))) = sP0_iProver_split(X2,sP0_iProver_split(X3,X1)) ),
% 22.95/3.49      inference(demodulation,[status(thm)],[c_58691,c_58408]) ).
% 22.95/3.49  
% 22.95/3.49  cnf(c_58697,plain,
% 22.95/3.49      ( sP0_iProver_split(X0,sP0_iProver_split(X1,X2)) = sP0_iProver_split(X2,sP0_iProver_split(X0,X1)) ),
% 22.95/3.49      inference(demodulation,[status(thm)],[c_58696,c_58408,c_58692]) ).
% 22.95/3.49  
% 22.95/3.49  cnf(c_57942,plain,
% 22.95/3.49      ( k5_xboole_0(X0,k5_xboole_0(k4_xboole_0(X1,X2),k5_xboole_0(X0,X1))) = k4_xboole_0(X1,k4_xboole_0(X1,X2)) ),
% 22.95/3.49      inference(superposition,[status(thm)],[c_16222,c_2501]) ).
% 22.95/3.49  
% 22.95/3.49  cnf(c_58642,plain,
% 22.95/3.49      ( sP0_iProver_split(X0,sP0_iProver_split(k4_xboole_0(X1,X2),k5_xboole_0(X0,X1))) = k4_xboole_0(X1,k4_xboole_0(X1,X2)) ),
% 22.95/3.49      inference(demodulation,[status(thm)],[c_57942,c_58408]) ).
% 22.95/3.49  
% 22.95/3.49  cnf(c_58643,plain,
% 22.95/3.49      ( sP0_iProver_split(X0,sP0_iProver_split(k4_xboole_0(X1,X2),sP0_iProver_split(X0,X1))) = k4_xboole_0(X1,k4_xboole_0(X1,X2)) ),
% 22.95/3.49      inference(demodulation,[status(thm)],[c_58642,c_58408]) ).
% 22.95/3.49  
% 22.95/3.49  cnf(c_58743,plain,
% 22.95/3.49      ( sP0_iProver_split(X0,sP0_iProver_split(X1,sP0_iProver_split(k4_xboole_0(X1,X2),X0))) = k4_xboole_0(X1,k4_xboole_0(X1,X2)) ),
% 22.95/3.49      inference(demodulation,[status(thm)],[c_58697,c_58643]) ).
% 22.95/3.49  
% 22.95/3.49  cnf(c_58836,plain,
% 22.95/3.49      ( sP0_iProver_split(k4_xboole_0(X0,X1),X0) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
% 22.95/3.49      inference(demodulation,[status(thm)],[c_58809,c_58743]) ).
% 22.95/3.49  
% 22.95/3.49  cnf(c_68982,plain,
% 22.95/3.49      ( k5_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,k4_xboole_0(X1,sP0_iProver_split(k4_xboole_0(X0,X1),X0)))) = X0 ),
% 22.95/3.49      inference(light_normalisation,[status(thm)],[c_51903,c_51903,c_58836]) ).
% 22.95/3.49  
% 22.95/3.49  cnf(c_68983,plain,
% 22.95/3.49      ( sP0_iProver_split(k4_xboole_0(X0,X1),sP0_iProver_split(k4_xboole_0(X1,sP0_iProver_split(k4_xboole_0(X0,X1),X0)),X1)) = X0 ),
% 22.95/3.49      inference(demodulation,[status(thm)],[c_68982,c_58408,c_58836]) ).
% 22.95/3.49  
% 22.95/3.49  cnf(c_21523,plain,
% 22.95/3.49      ( k5_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0)))) = k1_xboole_0 ),
% 22.95/3.49      inference(superposition,[status(thm)],[c_1,c_16579]) ).
% 22.95/3.49  
% 22.95/3.49  cnf(c_53652,plain,
% 22.95/3.49      ( k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0))) = k5_xboole_0(k4_xboole_0(X0,X1),k1_xboole_0) ),
% 22.95/3.49      inference(superposition,[status(thm)],[c_21523,c_2435]) ).
% 22.95/3.49  
% 22.95/3.49  cnf(c_54158,plain,
% 22.95/3.49      ( k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0))) = k4_xboole_0(X0,X1) ),
% 22.95/3.49      inference(demodulation,[status(thm)],[c_53652,c_11]) ).
% 22.95/3.49  
% 22.95/3.49  cnf(c_16564,plain,
% 22.95/3.49      ( k5_xboole_0(k4_xboole_0(X0,X1),k5_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2)) = k5_xboole_0(X0,X2) ),
% 22.95/3.49      inference(superposition,[status(thm)],[c_16222,c_13]) ).
% 22.95/3.49  
% 22.95/3.49  cnf(c_35238,plain,
% 22.95/3.49      ( k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))))) = k5_xboole_0(k4_xboole_0(X0,X1),k1_xboole_0) ),
% 22.95/3.49      inference(superposition,[status(thm)],[c_16579,c_16564]) ).
% 22.95/3.49  
% 22.95/3.49  cnf(c_35420,plain,
% 22.95/3.49      ( k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))))) = k4_xboole_0(X0,X1) ),
% 22.95/3.49      inference(demodulation,[status(thm)],[c_35238,c_0,c_11]) ).
% 22.95/3.49  
% 22.95/3.49  cnf(c_64484,plain,
% 22.95/3.49      ( k5_xboole_0(X0,sP0_iProver_split(k4_xboole_0(X0,X1),X0)) = k4_xboole_0(X0,X1) ),
% 22.95/3.49      inference(light_normalisation,
% 22.95/3.49                [status(thm)],
% 22.95/3.49                [c_35420,c_35420,c_53992,c_58836]) ).
% 22.95/3.49  
% 22.95/3.49  cnf(c_64504,plain,
% 22.95/3.49      ( k5_xboole_0(X0,sP0_iProver_split(k4_xboole_0(X0,X1),X0)) = k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0))) ),
% 22.95/3.49      inference(superposition,[status(thm)],[c_54158,c_64484]) ).
% 22.95/3.49  
% 22.95/3.49  cnf(c_64788,plain,
% 22.95/3.49      ( k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0))) = k4_xboole_0(X0,X1) ),
% 22.95/3.49      inference(demodulation,[status(thm)],[c_64504,c_64484]) ).
% 22.95/3.49  
% 22.95/3.49  cnf(c_64789,plain,
% 22.95/3.49      ( k4_xboole_0(X0,sP0_iProver_split(k4_xboole_0(X1,X0),X1)) = k4_xboole_0(X0,X1) ),
% 22.95/3.49      inference(demodulation,[status(thm)],[c_64788,c_58836]) ).
% 22.95/3.49  
% 22.95/3.49  cnf(c_68984,plain,
% 22.95/3.49      ( sP0_iProver_split(k4_xboole_0(X0,X1),sP0_iProver_split(k4_xboole_0(X1,X0),X1)) = X0 ),
% 22.95/3.49      inference(demodulation,[status(thm)],[c_68983,c_64789]) ).
% 22.95/3.49  
% 22.95/3.49  cnf(c_69046,plain,
% 22.95/3.49      ( sP0_iProver_split(k4_xboole_0(X0,k1_xboole_0),sP0_iProver_split(k1_xboole_0,k1_xboole_0)) = X0 ),
% 22.95/3.49      inference(superposition,[status(thm)],[c_1509,c_68984]) ).
% 22.95/3.49  
% 22.95/3.49  cnf(c_69185,plain,
% 22.95/3.49      ( sP0_iProver_split(X0,sP0_iProver_split(k1_xboole_0,k1_xboole_0)) = X0 ),
% 22.95/3.49      inference(light_normalisation,[status(thm)],[c_69046,c_926]) ).
% 22.95/3.49  
% 22.95/3.49  cnf(c_57732,plain,
% 22.95/3.49      ( k5_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(k1_xboole_0,X1))) = X1 ),
% 22.95/3.49      inference(superposition,[status(thm)],[c_2434,c_2501]) ).
% 22.95/3.49  
% 22.95/3.49  cnf(c_59215,plain,
% 22.95/3.49      ( sP0_iProver_split(X0,sP0_iProver_split(X0,k5_xboole_0(k1_xboole_0,X1))) = X1 ),
% 22.95/3.49      inference(demodulation,[status(thm)],[c_57732,c_58408]) ).
% 22.95/3.49  
% 22.95/3.49  cnf(c_58015,plain,
% 22.95/3.49      ( k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X1,k5_xboole_0(X0,k5_xboole_0(X1,X2))),X3)) = k5_xboole_0(X2,X3) ),
% 22.95/3.49      inference(superposition,[status(thm)],[c_2501,c_13]) ).
% 22.95/3.49  
% 22.95/3.49  cnf(c_58370,plain,
% 22.95/3.49      ( k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,X2)),X3))) = k5_xboole_0(X2,X3) ),
% 22.95/3.49      inference(demodulation,[status(thm)],[c_58015,c_1953]) ).
% 22.95/3.49  
% 22.95/3.49  cnf(c_58371,plain,
% 22.95/3.49      ( sP0_iProver_split(X0,k5_xboole_0(k5_xboole_0(X0,X1),X2)) = k5_xboole_0(X1,X2) ),
% 22.95/3.49      inference(demodulation,[status(thm)],[c_58370,c_1953,c_58228]) ).
% 22.95/3.49  
% 22.95/3.49  cnf(c_58372,plain,
% 22.95/3.49      ( sP0_iProver_split(X0,k5_xboole_0(X0,k5_xboole_0(X1,X2))) = k5_xboole_0(X1,X2) ),
% 22.95/3.49      inference(light_normalisation,[status(thm)],[c_58371,c_1953]) ).
% 22.95/3.49  
% 22.95/3.49  cnf(c_58412,plain,
% 22.95/3.49      ( sP0_iProver_split(X0,k5_xboole_0(X0,sP0_iProver_split(X1,X2))) = sP0_iProver_split(X1,X2) ),
% 22.95/3.49      inference(demodulation,[status(thm)],[c_58408,c_58372]) ).
% 22.95/3.49  
% 22.95/3.49  cnf(c_58463,plain,
% 22.95/3.49      ( sP0_iProver_split(X0,sP0_iProver_split(X0,sP0_iProver_split(X1,X2))) = sP0_iProver_split(X1,X2) ),
% 22.95/3.49      inference(demodulation,[status(thm)],[c_58412,c_58408]) ).
% 22.95/3.49  
% 22.95/3.49  cnf(c_59216,plain,
% 22.95/3.49      ( sP0_iProver_split(k1_xboole_0,X0) = X0 ),
% 22.95/3.49      inference(demodulation,[status(thm)],[c_59215,c_58408,c_58463]) ).
% 22.95/3.49  
% 22.95/3.49  cnf(c_69186,plain,
% 22.95/3.49      ( sP0_iProver_split(X0,k1_xboole_0) = X0 ),
% 22.95/3.49      inference(demodulation,[status(thm)],[c_69185,c_59216]) ).
% 22.95/3.49  
% 22.95/3.49  cnf(c_69520,plain,
% 22.95/3.49      ( sK3 = sK4 | sK3 = k1_xboole_0 ),
% 22.95/3.49      inference(demodulation,[status(thm)],[c_69458,c_69186]) ).
% 22.95/3.49  
% 22.95/3.49  cnf(c_69753,plain,
% 22.95/3.49      ( sK3 = k1_xboole_0 ),
% 22.95/3.49      inference(global_propositional_subsumption,
% 22.95/3.49                [status(thm)],
% 22.95/3.49                [c_69505,c_1167,c_69520]) ).
% 22.95/3.49  
% 22.95/3.49  cnf(c_20,negated_conjecture,
% 22.95/3.49      ( k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) != sK4
% 22.95/3.49      | k1_xboole_0 != sK3 ),
% 22.95/3.49      inference(cnf_transformation,[],[f93]) ).
% 22.95/3.49  
% 22.95/3.49  cnf(c_744,plain,
% 22.95/3.49      ( k5_xboole_0(sK3,k4_xboole_0(sK4,sK3)) != sK4 | sK3 != k1_xboole_0 ),
% 22.95/3.49      inference(light_normalisation,[status(thm)],[c_20,c_22]) ).
% 22.95/3.49  
% 22.95/3.49  cnf(c_69921,plain,
% 22.95/3.49      ( k5_xboole_0(k1_xboole_0,k4_xboole_0(sK4,k1_xboole_0)) != sK4
% 22.95/3.49      | k1_xboole_0 != k1_xboole_0 ),
% 22.95/3.49      inference(demodulation,[status(thm)],[c_69753,c_744]) ).
% 22.95/3.49  
% 22.95/3.49  cnf(c_69924,plain,
% 22.95/3.49      ( k5_xboole_0(k1_xboole_0,k4_xboole_0(sK4,k1_xboole_0)) != sK4 ),
% 22.95/3.49      inference(equality_resolution_simp,[status(thm)],[c_69921]) ).
% 22.95/3.49  
% 22.95/3.49  cnf(c_69925,plain,
% 22.95/3.49      ( sK4 != sK4 ),
% 22.95/3.49      inference(demodulation,[status(thm)],[c_69924,c_926,c_2434]) ).
% 22.95/3.49  
% 22.95/3.49  cnf(c_69926,plain,
% 22.95/3.49      ( $false ),
% 22.95/3.49      inference(equality_resolution_simp,[status(thm)],[c_69925]) ).
% 22.95/3.49  
% 22.95/3.49  
% 22.95/3.49  % SZS output end CNFRefutation for theBenchmark.p
% 22.95/3.49  
% 22.95/3.49  ------                               Statistics
% 22.95/3.49  
% 22.95/3.49  ------ General
% 22.95/3.49  
% 22.95/3.49  abstr_ref_over_cycles:                  0
% 22.95/3.49  abstr_ref_under_cycles:                 0
% 22.95/3.49  gc_basic_clause_elim:                   0
% 22.95/3.49  forced_gc_time:                         0
% 22.95/3.49  parsing_time:                           0.007
% 22.95/3.49  unif_index_cands_time:                  0.
% 22.95/3.49  unif_index_add_time:                    0.
% 22.95/3.49  orderings_time:                         0.
% 22.95/3.49  out_proof_time:                         0.02
% 22.95/3.49  total_time:                             2.66
% 22.95/3.49  num_of_symbols:                         45
% 22.95/3.49  num_of_terms:                           116065
% 22.95/3.49  
% 22.95/3.49  ------ Preprocessing
% 22.95/3.49  
% 22.95/3.49  num_of_splits:                          0
% 22.95/3.49  num_of_split_atoms:                     1
% 22.95/3.49  num_of_reused_defs:                     0
% 22.95/3.49  num_eq_ax_congr_red:                    12
% 22.95/3.49  num_of_sem_filtered_clauses:            1
% 22.95/3.49  num_of_subtypes:                        0
% 22.95/3.49  monotx_restored_types:                  0
% 22.95/3.49  sat_num_of_epr_types:                   0
% 22.95/3.49  sat_num_of_non_cyclic_types:            0
% 22.95/3.49  sat_guarded_non_collapsed_types:        0
% 22.95/3.49  num_pure_diseq_elim:                    0
% 22.95/3.49  simp_replaced_by:                       0
% 22.95/3.49  res_preprocessed:                       86
% 22.95/3.49  prep_upred:                             0
% 22.95/3.49  prep_unflattend:                        23
% 22.95/3.49  smt_new_axioms:                         0
% 22.95/3.49  pred_elim_cands:                        3
% 22.95/3.49  pred_elim:                              0
% 22.95/3.49  pred_elim_cl:                           0
% 22.95/3.49  pred_elim_cycles:                       2
% 22.95/3.49  merged_defs:                            6
% 22.95/3.49  merged_defs_ncl:                        0
% 22.95/3.49  bin_hyper_res:                          6
% 22.95/3.49  prep_cycles:                            3
% 22.95/3.49  pred_elim_time:                         0.003
% 22.95/3.49  splitting_time:                         0.
% 22.95/3.49  sem_filter_time:                        0.
% 22.95/3.49  monotx_time:                            0.
% 22.95/3.49  subtype_inf_time:                       0.
% 22.95/3.49  
% 22.95/3.49  ------ Problem properties
% 22.95/3.49  
% 22.95/3.49  clauses:                                23
% 22.95/3.49  conjectures:                            4
% 22.95/3.49  epr:                                    1
% 22.95/3.49  horn:                                   20
% 22.95/3.49  ground:                                 4
% 22.95/3.49  unary:                                  11
% 22.95/3.49  binary:                                 10
% 22.95/3.49  lits:                                   37
% 22.95/3.49  lits_eq:                                19
% 22.95/3.49  fd_pure:                                0
% 22.95/3.49  fd_pseudo:                              0
% 22.95/3.49  fd_cond:                                0
% 22.95/3.49  fd_pseudo_cond:                         1
% 22.95/3.49  ac_symbols:                             0
% 22.95/3.49  
% 22.95/3.49  ------ Propositional Solver
% 22.95/3.49  
% 22.95/3.49  prop_solver_calls:                      34
% 22.95/3.49  prop_fast_solver_calls:                 1320
% 22.95/3.49  smt_solver_calls:                       0
% 22.95/3.49  smt_fast_solver_calls:                  0
% 22.95/3.49  prop_num_of_clauses:                    21886
% 22.95/3.49  prop_preprocess_simplified:             22361
% 22.95/3.49  prop_fo_subsumed:                       5
% 22.95/3.49  prop_solver_time:                       0.
% 22.95/3.49  smt_solver_time:                        0.
% 22.95/3.49  smt_fast_solver_time:                   0.
% 22.95/3.49  prop_fast_solver_time:                  0.
% 22.95/3.49  prop_unsat_core_time:                   0.
% 22.95/3.49  
% 22.95/3.49  ------ QBF
% 22.95/3.49  
% 22.95/3.49  qbf_q_res:                              0
% 22.95/3.49  qbf_num_tautologies:                    0
% 22.95/3.49  qbf_prep_cycles:                        0
% 22.95/3.49  
% 22.95/3.49  ------ BMC1
% 22.95/3.49  
% 22.95/3.49  bmc1_current_bound:                     -1
% 22.95/3.49  bmc1_last_solved_bound:                 -1
% 22.95/3.49  bmc1_unsat_core_size:                   -1
% 22.95/3.49  bmc1_unsat_core_parents_size:           -1
% 22.95/3.49  bmc1_merge_next_fun:                    0
% 22.95/3.49  bmc1_unsat_core_clauses_time:           0.
% 22.95/3.49  
% 22.95/3.49  ------ Instantiation
% 22.95/3.49  
% 22.95/3.49  inst_num_of_clauses:                    4630
% 22.95/3.49  inst_num_in_passive:                    2140
% 22.95/3.49  inst_num_in_active:                     1688
% 22.95/3.49  inst_num_in_unprocessed:                804
% 22.95/3.49  inst_num_of_loops:                      1950
% 22.95/3.49  inst_num_of_learning_restarts:          0
% 22.95/3.49  inst_num_moves_active_passive:          255
% 22.95/3.49  inst_lit_activity:                      0
% 22.95/3.49  inst_lit_activity_moves:                0
% 22.95/3.49  inst_num_tautologies:                   0
% 22.95/3.49  inst_num_prop_implied:                  0
% 22.95/3.49  inst_num_existing_simplified:           0
% 22.95/3.49  inst_num_eq_res_simplified:             0
% 22.95/3.49  inst_num_child_elim:                    0
% 22.95/3.49  inst_num_of_dismatching_blockings:      5714
% 22.95/3.49  inst_num_of_non_proper_insts:           6073
% 22.95/3.49  inst_num_of_duplicates:                 0
% 22.95/3.49  inst_inst_num_from_inst_to_res:         0
% 22.95/3.49  inst_dismatching_checking_time:         0.
% 22.95/3.49  
% 22.95/3.49  ------ Resolution
% 22.95/3.49  
% 22.95/3.49  res_num_of_clauses:                     0
% 22.95/3.49  res_num_in_passive:                     0
% 22.95/3.49  res_num_in_active:                      0
% 22.95/3.49  res_num_of_loops:                       89
% 22.95/3.49  res_forward_subset_subsumed:            978
% 22.95/3.49  res_backward_subset_subsumed:           6
% 22.95/3.49  res_forward_subsumed:                   0
% 22.95/3.49  res_backward_subsumed:                  0
% 22.95/3.49  res_forward_subsumption_resolution:     0
% 22.95/3.49  res_backward_subsumption_resolution:    0
% 22.95/3.49  res_clause_to_clause_subsumption:       43010
% 22.95/3.49  res_orphan_elimination:                 0
% 22.95/3.49  res_tautology_del:                      342
% 22.95/3.49  res_num_eq_res_simplified:              0
% 22.95/3.49  res_num_sel_changes:                    0
% 22.95/3.49  res_moves_from_active_to_pass:          0
% 22.95/3.49  
% 22.95/3.49  ------ Superposition
% 22.95/3.49  
% 22.95/3.49  sup_time_total:                         0.
% 22.95/3.49  sup_time_generating:                    0.
% 22.95/3.49  sup_time_sim_full:                      0.
% 22.95/3.49  sup_time_sim_immed:                     0.
% 22.95/3.49  
% 22.95/3.49  sup_num_of_clauses:                     4848
% 22.95/3.49  sup_num_in_active:                      52
% 22.95/3.49  sup_num_in_passive:                     4796
% 22.95/3.49  sup_num_of_loops:                       388
% 22.95/3.49  sup_fw_superposition:                   9560
% 22.95/3.49  sup_bw_superposition:                   8183
% 22.95/3.49  sup_immediate_simplified:               9631
% 22.95/3.49  sup_given_eliminated:                   6
% 22.95/3.49  comparisons_done:                       0
% 22.95/3.49  comparisons_avoided:                    261
% 22.95/3.49  
% 22.95/3.49  ------ Simplifications
% 22.95/3.49  
% 22.95/3.49  
% 22.95/3.49  sim_fw_subset_subsumed:                 22
% 22.95/3.49  sim_bw_subset_subsumed:                 811
% 22.95/3.49  sim_fw_subsumed:                        644
% 22.95/3.49  sim_bw_subsumed:                        56
% 22.95/3.49  sim_fw_subsumption_res:                 0
% 22.95/3.49  sim_bw_subsumption_res:                 0
% 22.95/3.49  sim_tautology_del:                      19
% 22.95/3.49  sim_eq_tautology_del:                   1372
% 22.95/3.49  sim_eq_res_simp:                        22
% 22.95/3.49  sim_fw_demodulated:                     15112
% 22.95/3.49  sim_bw_demodulated:                     542
% 22.95/3.49  sim_light_normalised:                   1380
% 22.95/3.49  sim_joinable_taut:                      0
% 22.95/3.49  sim_joinable_simp:                      0
% 22.95/3.49  sim_ac_normalised:                      0
% 22.95/3.49  sim_smt_subsumption:                    0
% 22.95/3.49  
%------------------------------------------------------------------------------
