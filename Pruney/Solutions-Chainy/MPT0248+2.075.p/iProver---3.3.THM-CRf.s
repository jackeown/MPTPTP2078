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
% DateTime   : Thu Dec  3 11:32:19 EST 2020

% Result     : Theorem 6.67s
% Output     : CNFRefutation 6.67s
% Verified   : 
% Statistics : Number of formulae       :  109 (1551 expanded)
%              Number of clauses        :   48 ( 148 expanded)
%              Number of leaves         :   19 ( 486 expanded)
%              Depth                    :   24
%              Number of atoms          :  196 (2369 expanded)
%              Number of equality atoms :  171 (2243 expanded)
%              Maximal formula depth    :   11 (   3 average)
%              Maximal clause size      :   14 (   2 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f25,conjecture,(
    ! [X0,X1,X2] :
      ~ ( ~ ( k1_xboole_0 = X2
            & k1_tarski(X0) = X1 )
        & ~ ( k1_tarski(X0) = X2
            & k1_xboole_0 = X1 )
        & ~ ( k1_tarski(X0) = X2
            & k1_tarski(X0) = X1 )
        & k2_xboole_0(X1,X2) = k1_tarski(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ~ ( ~ ( k1_xboole_0 = X2
              & k1_tarski(X0) = X1 )
          & ~ ( k1_tarski(X0) = X2
              & k1_xboole_0 = X1 )
          & ~ ( k1_tarski(X0) = X2
              & k1_tarski(X0) = X1 )
          & k2_xboole_0(X1,X2) = k1_tarski(X0) ) ),
    inference(negated_conjecture,[],[f25])).

fof(f34,plain,(
    ? [X0,X1,X2] :
      ( ( k1_xboole_0 != X2
        | k1_tarski(X0) != X1 )
      & ( k1_tarski(X0) != X2
        | k1_xboole_0 != X1 )
      & ( k1_tarski(X0) != X2
        | k1_tarski(X0) != X1 )
      & k2_xboole_0(X1,X2) = k1_tarski(X0) ) ),
    inference(ennf_transformation,[],[f26])).

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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f34,f46])).

fof(f80,plain,(
    k2_xboole_0(sK3,sK4) = k1_tarski(sK2) ),
    inference(cnf_transformation,[],[f47])).

fof(f24,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f79,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f24])).

fof(f89,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f79,f88])).

fof(f14,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f66,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f14])).

fof(f15,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f67,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f15])).

fof(f16,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f68,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f16])).

fof(f17,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f69,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f17])).

fof(f18,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f70,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f18])).

fof(f19,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f71,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f19])).

fof(f20,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f72,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f20])).

fof(f84,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f71,f72])).

fof(f85,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f70,f84])).

fof(f86,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f69,f85])).

fof(f87,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f68,f86])).

fof(f88,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f67,f87])).

fof(f91,plain,(
    ! [X0] : k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f66,f88])).

fof(f107,plain,(
    k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) = k3_tarski(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4)) ),
    inference(definition_unfolding,[],[f80,f89,f91])).

fof(f7,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f59,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f7])).

fof(f13,axiom,(
    ! [X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f65,plain,(
    ! [X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f13])).

fof(f90,plain,(
    ! [X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) = k3_xboole_0(X0,X1) ),
    inference(definition_unfolding,[],[f65,f89])).

fof(f96,plain,(
    ! [X0,X1] : r1_tarski(k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))),X0) ),
    inference(definition_unfolding,[],[f59,f90])).

fof(f11,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f63,plain,(
    ! [X2,X0,X1] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f11])).

fof(f1,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f10,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f62,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f10])).

fof(f97,plain,(
    ! [X0,X1] : r1_tarski(X0,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) ),
    inference(definition_unfolding,[],[f62,f89])).

fof(f23,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,k1_tarski(X1))
    <=> ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,k1_tarski(X1))
        | ( k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k1_tarski(X1)) ) ) ),
    inference(nnf_transformation,[],[f23])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,k1_tarski(X1))
        | ( k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k1_tarski(X1)) ) ) ),
    inference(flattening,[],[f44])).

fof(f76,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = X0
      | k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_tarski(X1)) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f103,plain,(
    ! [X0,X1] :
      ( k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) = X0
      | k1_xboole_0 = X0
      | ~ r1_tarski(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)) ) ),
    inference(definition_unfolding,[],[f76,f91,f91])).

fof(f83,plain,
    ( k1_xboole_0 != sK4
    | k1_tarski(sK2) != sK3 ),
    inference(cnf_transformation,[],[f47])).

fof(f104,plain,
    ( k1_xboole_0 != sK4
    | k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) != sK3 ),
    inference(definition_unfolding,[],[f83,f91])).

fof(f81,plain,
    ( k1_tarski(sK2) != sK4
    | k1_tarski(sK2) != sK3 ),
    inference(cnf_transformation,[],[f47])).

fof(f106,plain,
    ( k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) != sK4
    | k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) != sK3 ),
    inference(definition_unfolding,[],[f81,f91,f91])).

fof(f82,plain,
    ( k1_tarski(sK2) != sK4
    | k1_xboole_0 != sK3 ),
    inference(cnf_transformation,[],[f47])).

fof(f105,plain,
    ( k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) != sK4
    | k1_xboole_0 != sK3 ),
    inference(definition_unfolding,[],[f82,f91])).

fof(f12,axiom,(
    ! [X0] : k5_xboole_0(X0,X0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f64,plain,(
    ! [X0] : k5_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f12])).

fof(f9,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f61,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f9])).

fof(f8,axiom,(
    ! [X0] :
      ( r1_tarski(X0,k1_xboole_0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_xboole_0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f60,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_xboole_0) ) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_26,negated_conjecture,
    ( k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) = k3_tarski(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4)) ),
    inference(cnf_transformation,[],[f107])).

cnf(c_11,plain,
    ( r1_tarski(k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))),X0) ),
    inference(cnf_transformation,[],[f96])).

cnf(c_15,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_0,plain,
    ( k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_457,plain,
    ( r1_tarski(k5_xboole_0(X0,k5_xboole_0(X1,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))),X0) ),
    inference(theory_normalisation,[status(thm)],[c_11,c_15,c_0])).

cnf(c_896,plain,
    ( r1_tarski(k5_xboole_0(X0,k5_xboole_0(X1,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_457])).

cnf(c_20223,plain,
    ( r1_tarski(k5_xboole_0(sK3,k5_xboole_0(sK4,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))),sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_26,c_896])).

cnf(c_14,plain,
    ( r1_tarski(X0,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) ),
    inference(cnf_transformation,[],[f97])).

cnf(c_894,plain,
    ( r1_tarski(X0,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_16908,plain,
    ( r1_tarski(sK3,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_26,c_894])).

cnf(c_22,plain,
    ( ~ r1_tarski(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))
    | k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) = X0
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f103])).

cnf(c_888,plain,
    ( k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) = X1
    | k1_xboole_0 = X1
    | r1_tarski(X1,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_19776,plain,
    ( k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) = sK3
    | sK3 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_16908,c_888])).

cnf(c_19867,plain,
    ( k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) = X0
    | sK3 = k1_xboole_0
    | k1_xboole_0 = X0
    | r1_tarski(X0,sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_19776,c_888])).

cnf(c_24891,plain,
    ( k5_xboole_0(sK3,k5_xboole_0(sK4,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))) = k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)
    | k5_xboole_0(sK3,k5_xboole_0(sK4,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))) = k1_xboole_0
    | sK3 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_20223,c_19867])).

cnf(c_23,negated_conjecture,
    ( k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) != sK3
    | k1_xboole_0 != sK4 ),
    inference(cnf_transformation,[],[f104])).

cnf(c_19872,plain,
    ( sK3 = k1_xboole_0
    | sK4 != k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_19776,c_23])).

cnf(c_25,negated_conjecture,
    ( k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) != sK3
    | k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) != sK4 ),
    inference(cnf_transformation,[],[f106])).

cnf(c_19870,plain,
    ( k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) != sK4
    | sK3 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_19776,c_25])).

cnf(c_24,negated_conjecture,
    ( k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) != sK4
    | k1_xboole_0 != sK3 ),
    inference(cnf_transformation,[],[f105])).

cnf(c_1811,plain,
    ( ~ r1_tarski(sK3,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))
    | k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) = sK3
    | k1_xboole_0 = sK3 ),
    inference(instantiation,[status(thm)],[c_22])).

cnf(c_1814,plain,
    ( ~ r1_tarski(sK3,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))
    | k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) = sK3
    | k1_xboole_0 = sK3 ),
    inference(instantiation,[status(thm)],[c_1811])).

cnf(c_16914,plain,
    ( r1_tarski(sK3,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_16908])).

cnf(c_20072,plain,
    ( k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) != sK4 ),
    inference(global_propositional_subsumption,[status(thm)],[c_19870,c_25,c_24,c_1814,c_16914])).

cnf(c_22482,plain,
    ( sK3 = k1_xboole_0
    | r1_tarski(k5_xboole_0(sK3,k5_xboole_0(sK4,sK3)),sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_19776,c_20223])).

cnf(c_16,plain,
    ( k5_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f64])).

cnf(c_1218,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X0,X1)) = k5_xboole_0(k1_xboole_0,X1) ),
    inference(superposition,[status(thm)],[c_16,c_15])).

cnf(c_13,plain,
    ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f61])).

cnf(c_1174,plain,
    ( k5_xboole_0(k1_xboole_0,X0) = X0 ),
    inference(superposition,[status(thm)],[c_13,c_0])).

cnf(c_1353,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1 ),
    inference(demodulation,[status(thm)],[c_1218,c_1174])).

cnf(c_1358,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,X0)) = X1 ),
    inference(superposition,[status(thm)],[c_0,c_1353])).

cnf(c_22485,plain,
    ( sK3 = k1_xboole_0
    | r1_tarski(sK4,sK3) = iProver_top ),
    inference(demodulation,[status(thm)],[c_22482,c_1358])).

cnf(c_24890,plain,
    ( k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) = sK4
    | sK3 = k1_xboole_0
    | sK4 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_22485,c_19867])).

cnf(c_24964,plain,
    ( sK3 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_24891,c_25,c_24,c_1814,c_16914,c_19872,c_24890])).

cnf(c_24973,plain,
    ( r1_tarski(k5_xboole_0(k1_xboole_0,k5_xboole_0(sK4,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))),k1_xboole_0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_24964,c_20223])).

cnf(c_1003,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(X2,k5_xboole_0(X1,X0)) ),
    inference(superposition,[status(thm)],[c_15,c_0])).

cnf(c_1722,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(X0,X1)) = k5_xboole_0(X1,X0) ),
    inference(superposition,[status(thm)],[c_13,c_1003])).

cnf(c_24989,plain,
    ( r1_tarski(k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK4),k1_xboole_0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_24973,c_1722])).

cnf(c_12,plain,
    ( ~ r1_tarski(X0,k1_xboole_0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f60])).

cnf(c_895,plain,
    ( k1_xboole_0 = X0
    | r1_tarski(X0,k1_xboole_0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_26989,plain,
    ( k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK4) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_24989,c_895])).

cnf(c_1002,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(X1,k5_xboole_0(X0,X2)) ),
    inference(superposition,[status(thm)],[c_15,c_0])).

cnf(c_1608,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X0,k5_xboole_0(X2,X1))) = X2 ),
    inference(superposition,[status(thm)],[c_1002,c_1358])).

cnf(c_27816,plain,
    ( k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) = k5_xboole_0(k5_xboole_0(X0,sK4),k5_xboole_0(X0,k1_xboole_0)) ),
    inference(superposition,[status(thm)],[c_26989,c_1608])).

cnf(c_27826,plain,
    ( k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) = k5_xboole_0(k5_xboole_0(X0,sK4),X0) ),
    inference(light_normalisation,[status(thm)],[c_27816,c_13])).

cnf(c_1391,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),X0) = X1 ),
    inference(superposition,[status(thm)],[c_1358,c_1358])).

cnf(c_27827,plain,
    ( k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) = sK4 ),
    inference(demodulation,[status(thm)],[c_27826,c_1391])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_27827,c_20072])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 18:30:26 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 6.67/1.49  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.67/1.49  
% 6.67/1.49  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 6.67/1.49  
% 6.67/1.49  ------  iProver source info
% 6.67/1.49  
% 6.67/1.49  git: date: 2020-06-30 10:37:57 +0100
% 6.67/1.49  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 6.67/1.49  git: non_committed_changes: false
% 6.67/1.49  git: last_make_outside_of_git: false
% 6.67/1.49  
% 6.67/1.49  ------ 
% 6.67/1.49  
% 6.67/1.49  ------ Input Options
% 6.67/1.49  
% 6.67/1.49  --out_options                           all
% 6.67/1.49  --tptp_safe_out                         true
% 6.67/1.49  --problem_path                          ""
% 6.67/1.49  --include_path                          ""
% 6.67/1.49  --clausifier                            res/vclausify_rel
% 6.67/1.49  --clausifier_options                    --mode clausify
% 6.67/1.49  --stdin                                 false
% 6.67/1.49  --stats_out                             all
% 6.67/1.49  
% 6.67/1.49  ------ General Options
% 6.67/1.49  
% 6.67/1.49  --fof                                   false
% 6.67/1.49  --time_out_real                         305.
% 6.67/1.49  --time_out_virtual                      -1.
% 6.67/1.49  --symbol_type_check                     false
% 6.67/1.49  --clausify_out                          false
% 6.67/1.49  --sig_cnt_out                           false
% 6.67/1.49  --trig_cnt_out                          false
% 6.67/1.49  --trig_cnt_out_tolerance                1.
% 6.67/1.49  --trig_cnt_out_sk_spl                   false
% 6.67/1.49  --abstr_cl_out                          false
% 6.67/1.49  
% 6.67/1.49  ------ Global Options
% 6.67/1.49  
% 6.67/1.49  --schedule                              default
% 6.67/1.49  --add_important_lit                     false
% 6.67/1.49  --prop_solver_per_cl                    1000
% 6.67/1.49  --min_unsat_core                        false
% 6.67/1.49  --soft_assumptions                      false
% 6.67/1.49  --soft_lemma_size                       3
% 6.67/1.49  --prop_impl_unit_size                   0
% 6.67/1.49  --prop_impl_unit                        []
% 6.67/1.49  --share_sel_clauses                     true
% 6.67/1.49  --reset_solvers                         false
% 6.67/1.49  --bc_imp_inh                            [conj_cone]
% 6.67/1.49  --conj_cone_tolerance                   3.
% 6.67/1.49  --extra_neg_conj                        none
% 6.67/1.49  --large_theory_mode                     true
% 6.67/1.49  --prolific_symb_bound                   200
% 6.67/1.49  --lt_threshold                          2000
% 6.67/1.49  --clause_weak_htbl                      true
% 6.67/1.49  --gc_record_bc_elim                     false
% 6.67/1.49  
% 6.67/1.49  ------ Preprocessing Options
% 6.67/1.49  
% 6.67/1.49  --preprocessing_flag                    true
% 6.67/1.49  --time_out_prep_mult                    0.1
% 6.67/1.49  --splitting_mode                        input
% 6.67/1.49  --splitting_grd                         true
% 6.67/1.49  --splitting_cvd                         false
% 6.67/1.49  --splitting_cvd_svl                     false
% 6.67/1.49  --splitting_nvd                         32
% 6.67/1.49  --sub_typing                            true
% 6.67/1.49  --prep_gs_sim                           true
% 6.67/1.49  --prep_unflatten                        true
% 6.67/1.49  --prep_res_sim                          true
% 6.67/1.49  --prep_upred                            true
% 6.67/1.49  --prep_sem_filter                       exhaustive
% 6.67/1.49  --prep_sem_filter_out                   false
% 6.67/1.49  --pred_elim                             true
% 6.67/1.49  --res_sim_input                         true
% 6.67/1.49  --eq_ax_congr_red                       true
% 6.67/1.49  --pure_diseq_elim                       true
% 6.67/1.49  --brand_transform                       false
% 6.67/1.49  --non_eq_to_eq                          false
% 6.67/1.49  --prep_def_merge                        true
% 6.67/1.49  --prep_def_merge_prop_impl              false
% 6.67/1.49  --prep_def_merge_mbd                    true
% 6.67/1.49  --prep_def_merge_tr_red                 false
% 6.67/1.49  --prep_def_merge_tr_cl                  false
% 6.67/1.49  --smt_preprocessing                     true
% 6.67/1.49  --smt_ac_axioms                         fast
% 6.67/1.49  --preprocessed_out                      false
% 6.67/1.49  --preprocessed_stats                    false
% 6.67/1.49  
% 6.67/1.49  ------ Abstraction refinement Options
% 6.67/1.49  
% 6.67/1.49  --abstr_ref                             []
% 6.67/1.49  --abstr_ref_prep                        false
% 6.67/1.49  --abstr_ref_until_sat                   false
% 6.67/1.49  --abstr_ref_sig_restrict                funpre
% 6.67/1.49  --abstr_ref_af_restrict_to_split_sk     false
% 6.67/1.49  --abstr_ref_under                       []
% 6.67/1.49  
% 6.67/1.49  ------ SAT Options
% 6.67/1.49  
% 6.67/1.49  --sat_mode                              false
% 6.67/1.49  --sat_fm_restart_options                ""
% 6.67/1.49  --sat_gr_def                            false
% 6.67/1.49  --sat_epr_types                         true
% 6.67/1.49  --sat_non_cyclic_types                  false
% 6.67/1.49  --sat_finite_models                     false
% 6.67/1.49  --sat_fm_lemmas                         false
% 6.67/1.49  --sat_fm_prep                           false
% 6.67/1.49  --sat_fm_uc_incr                        true
% 6.67/1.49  --sat_out_model                         small
% 6.67/1.49  --sat_out_clauses                       false
% 6.67/1.49  
% 6.67/1.49  ------ QBF Options
% 6.67/1.49  
% 6.67/1.49  --qbf_mode                              false
% 6.67/1.49  --qbf_elim_univ                         false
% 6.67/1.49  --qbf_dom_inst                          none
% 6.67/1.49  --qbf_dom_pre_inst                      false
% 6.67/1.49  --qbf_sk_in                             false
% 6.67/1.49  --qbf_pred_elim                         true
% 6.67/1.49  --qbf_split                             512
% 6.67/1.49  
% 6.67/1.49  ------ BMC1 Options
% 6.67/1.49  
% 6.67/1.49  --bmc1_incremental                      false
% 6.67/1.49  --bmc1_axioms                           reachable_all
% 6.67/1.49  --bmc1_min_bound                        0
% 6.67/1.49  --bmc1_max_bound                        -1
% 6.67/1.49  --bmc1_max_bound_default                -1
% 6.67/1.49  --bmc1_symbol_reachability              true
% 6.67/1.49  --bmc1_property_lemmas                  false
% 6.67/1.49  --bmc1_k_induction                      false
% 6.67/1.49  --bmc1_non_equiv_states                 false
% 6.67/1.49  --bmc1_deadlock                         false
% 6.67/1.49  --bmc1_ucm                              false
% 6.67/1.49  --bmc1_add_unsat_core                   none
% 6.67/1.49  --bmc1_unsat_core_children              false
% 6.67/1.49  --bmc1_unsat_core_extrapolate_axioms    false
% 6.67/1.49  --bmc1_out_stat                         full
% 6.67/1.49  --bmc1_ground_init                      false
% 6.67/1.49  --bmc1_pre_inst_next_state              false
% 6.67/1.49  --bmc1_pre_inst_state                   false
% 6.67/1.49  --bmc1_pre_inst_reach_state             false
% 6.67/1.49  --bmc1_out_unsat_core                   false
% 6.67/1.49  --bmc1_aig_witness_out                  false
% 6.67/1.49  --bmc1_verbose                          false
% 6.67/1.49  --bmc1_dump_clauses_tptp                false
% 6.67/1.49  --bmc1_dump_unsat_core_tptp             false
% 6.67/1.49  --bmc1_dump_file                        -
% 6.67/1.49  --bmc1_ucm_expand_uc_limit              128
% 6.67/1.49  --bmc1_ucm_n_expand_iterations          6
% 6.67/1.49  --bmc1_ucm_extend_mode                  1
% 6.67/1.49  --bmc1_ucm_init_mode                    2
% 6.67/1.49  --bmc1_ucm_cone_mode                    none
% 6.67/1.49  --bmc1_ucm_reduced_relation_type        0
% 6.67/1.49  --bmc1_ucm_relax_model                  4
% 6.67/1.49  --bmc1_ucm_full_tr_after_sat            true
% 6.67/1.49  --bmc1_ucm_expand_neg_assumptions       false
% 6.67/1.49  --bmc1_ucm_layered_model                none
% 6.67/1.49  --bmc1_ucm_max_lemma_size               10
% 6.67/1.49  
% 6.67/1.49  ------ AIG Options
% 6.67/1.49  
% 6.67/1.49  --aig_mode                              false
% 6.67/1.49  
% 6.67/1.49  ------ Instantiation Options
% 6.67/1.49  
% 6.67/1.49  --instantiation_flag                    true
% 6.67/1.49  --inst_sos_flag                         false
% 6.67/1.49  --inst_sos_phase                        true
% 6.67/1.49  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 6.67/1.49  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 6.67/1.49  --inst_lit_sel_side                     num_symb
% 6.67/1.49  --inst_solver_per_active                1400
% 6.67/1.49  --inst_solver_calls_frac                1.
% 6.67/1.49  --inst_passive_queue_type               priority_queues
% 6.67/1.49  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 6.67/1.49  --inst_passive_queues_freq              [25;2]
% 6.67/1.49  --inst_dismatching                      true
% 6.67/1.49  --inst_eager_unprocessed_to_passive     true
% 6.67/1.49  --inst_prop_sim_given                   true
% 6.67/1.49  --inst_prop_sim_new                     false
% 6.67/1.49  --inst_subs_new                         false
% 6.67/1.49  --inst_eq_res_simp                      false
% 6.67/1.49  --inst_subs_given                       false
% 6.67/1.49  --inst_orphan_elimination               true
% 6.67/1.49  --inst_learning_loop_flag               true
% 6.67/1.49  --inst_learning_start                   3000
% 6.67/1.49  --inst_learning_factor                  2
% 6.67/1.49  --inst_start_prop_sim_after_learn       3
% 6.67/1.49  --inst_sel_renew                        solver
% 6.67/1.49  --inst_lit_activity_flag                true
% 6.67/1.49  --inst_restr_to_given                   false
% 6.67/1.49  --inst_activity_threshold               500
% 6.67/1.49  --inst_out_proof                        true
% 6.67/1.49  
% 6.67/1.49  ------ Resolution Options
% 6.67/1.49  
% 6.67/1.49  --resolution_flag                       true
% 6.67/1.49  --res_lit_sel                           adaptive
% 6.67/1.49  --res_lit_sel_side                      none
% 6.67/1.49  --res_ordering                          kbo
% 6.67/1.49  --res_to_prop_solver                    active
% 6.67/1.49  --res_prop_simpl_new                    false
% 6.67/1.49  --res_prop_simpl_given                  true
% 6.67/1.49  --res_passive_queue_type                priority_queues
% 6.67/1.49  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 6.67/1.49  --res_passive_queues_freq               [15;5]
% 6.67/1.49  --res_forward_subs                      full
% 6.67/1.49  --res_backward_subs                     full
% 6.67/1.49  --res_forward_subs_resolution           true
% 6.67/1.49  --res_backward_subs_resolution          true
% 6.67/1.49  --res_orphan_elimination                true
% 6.67/1.49  --res_time_limit                        2.
% 6.67/1.49  --res_out_proof                         true
% 6.67/1.49  
% 6.67/1.49  ------ Superposition Options
% 6.67/1.49  
% 6.67/1.49  --superposition_flag                    true
% 6.67/1.49  --sup_passive_queue_type                priority_queues
% 6.67/1.49  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 6.67/1.49  --sup_passive_queues_freq               [8;1;4]
% 6.67/1.49  --demod_completeness_check              fast
% 6.67/1.49  --demod_use_ground                      true
% 6.67/1.49  --sup_to_prop_solver                    passive
% 6.67/1.49  --sup_prop_simpl_new                    true
% 6.67/1.49  --sup_prop_simpl_given                  true
% 6.67/1.49  --sup_fun_splitting                     false
% 6.67/1.49  --sup_smt_interval                      50000
% 6.67/1.49  
% 6.67/1.49  ------ Superposition Simplification Setup
% 6.67/1.49  
% 6.67/1.49  --sup_indices_passive                   []
% 6.67/1.49  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 6.67/1.49  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 6.67/1.49  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 6.67/1.49  --sup_full_triv                         [TrivRules;PropSubs]
% 6.67/1.49  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 6.67/1.49  --sup_full_bw                           [BwDemod]
% 6.67/1.49  --sup_immed_triv                        [TrivRules]
% 6.67/1.49  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 6.67/1.49  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 6.67/1.49  --sup_immed_bw_main                     []
% 6.67/1.49  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 6.67/1.49  --sup_input_triv                        [Unflattening;TrivRules]
% 6.67/1.49  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 6.67/1.49  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 6.67/1.49  
% 6.67/1.49  ------ Combination Options
% 6.67/1.49  
% 6.67/1.49  --comb_res_mult                         3
% 6.67/1.49  --comb_sup_mult                         2
% 6.67/1.49  --comb_inst_mult                        10
% 6.67/1.49  
% 6.67/1.49  ------ Debug Options
% 6.67/1.49  
% 6.67/1.49  --dbg_backtrace                         false
% 6.67/1.49  --dbg_dump_prop_clauses                 false
% 6.67/1.49  --dbg_dump_prop_clauses_file            -
% 6.67/1.49  --dbg_out_stat                          false
% 6.67/1.49  ------ Parsing...
% 6.67/1.49  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 6.67/1.49  
% 6.67/1.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e  sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 6.67/1.49  
% 6.67/1.49  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 6.67/1.49  
% 6.67/1.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 6.67/1.49  ------ Proving...
% 6.67/1.49  ------ Problem Properties 
% 6.67/1.49  
% 6.67/1.49  
% 6.67/1.49  clauses                                 26
% 6.67/1.49  conjectures                             4
% 6.67/1.49  EPR                                     4
% 6.67/1.49  Horn                                    22
% 6.67/1.49  unary                                   12
% 6.67/1.49  binary                                  11
% 6.67/1.49  lits                                    43
% 6.67/1.49  lits eq                                 17
% 6.67/1.49  fd_pure                                 0
% 6.67/1.49  fd_pseudo                               0
% 6.67/1.49  fd_cond                                 1
% 6.67/1.49  fd_pseudo_cond                          2
% 6.67/1.49  AC symbols                              1
% 6.67/1.49  
% 6.67/1.49  ------ Schedule dynamic 5 is on 
% 6.67/1.49  
% 6.67/1.49  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 6.67/1.49  
% 6.67/1.49  
% 6.67/1.49  ------ 
% 6.67/1.49  Current options:
% 6.67/1.49  ------ 
% 6.67/1.49  
% 6.67/1.49  ------ Input Options
% 6.67/1.49  
% 6.67/1.49  --out_options                           all
% 6.67/1.49  --tptp_safe_out                         true
% 6.67/1.49  --problem_path                          ""
% 6.67/1.49  --include_path                          ""
% 6.67/1.49  --clausifier                            res/vclausify_rel
% 6.67/1.49  --clausifier_options                    --mode clausify
% 6.67/1.49  --stdin                                 false
% 6.67/1.49  --stats_out                             all
% 6.67/1.49  
% 6.67/1.49  ------ General Options
% 6.67/1.49  
% 6.67/1.49  --fof                                   false
% 6.67/1.49  --time_out_real                         305.
% 6.67/1.49  --time_out_virtual                      -1.
% 6.67/1.49  --symbol_type_check                     false
% 6.67/1.49  --clausify_out                          false
% 6.67/1.49  --sig_cnt_out                           false
% 6.67/1.49  --trig_cnt_out                          false
% 6.67/1.49  --trig_cnt_out_tolerance                1.
% 6.67/1.49  --trig_cnt_out_sk_spl                   false
% 6.67/1.49  --abstr_cl_out                          false
% 6.67/1.49  
% 6.67/1.49  ------ Global Options
% 6.67/1.49  
% 6.67/1.49  --schedule                              default
% 6.67/1.49  --add_important_lit                     false
% 6.67/1.49  --prop_solver_per_cl                    1000
% 6.67/1.49  --min_unsat_core                        false
% 6.67/1.49  --soft_assumptions                      false
% 6.67/1.49  --soft_lemma_size                       3
% 6.67/1.49  --prop_impl_unit_size                   0
% 6.67/1.49  --prop_impl_unit                        []
% 6.67/1.49  --share_sel_clauses                     true
% 6.67/1.49  --reset_solvers                         false
% 6.67/1.49  --bc_imp_inh                            [conj_cone]
% 6.67/1.49  --conj_cone_tolerance                   3.
% 6.67/1.49  --extra_neg_conj                        none
% 6.67/1.49  --large_theory_mode                     true
% 6.67/1.49  --prolific_symb_bound                   200
% 6.67/1.49  --lt_threshold                          2000
% 6.67/1.49  --clause_weak_htbl                      true
% 6.67/1.49  --gc_record_bc_elim                     false
% 6.67/1.49  
% 6.67/1.49  ------ Preprocessing Options
% 6.67/1.49  
% 6.67/1.49  --preprocessing_flag                    true
% 6.67/1.49  --time_out_prep_mult                    0.1
% 6.67/1.49  --splitting_mode                        input
% 6.67/1.49  --splitting_grd                         true
% 6.67/1.49  --splitting_cvd                         false
% 6.67/1.49  --splitting_cvd_svl                     false
% 6.67/1.49  --splitting_nvd                         32
% 6.67/1.49  --sub_typing                            true
% 6.67/1.49  --prep_gs_sim                           true
% 6.67/1.49  --prep_unflatten                        true
% 6.67/1.49  --prep_res_sim                          true
% 6.67/1.49  --prep_upred                            true
% 6.67/1.49  --prep_sem_filter                       exhaustive
% 6.67/1.49  --prep_sem_filter_out                   false
% 6.67/1.49  --pred_elim                             true
% 6.67/1.49  --res_sim_input                         true
% 6.67/1.49  --eq_ax_congr_red                       true
% 6.67/1.49  --pure_diseq_elim                       true
% 6.67/1.49  --brand_transform                       false
% 6.67/1.49  --non_eq_to_eq                          false
% 6.67/1.49  --prep_def_merge                        true
% 6.67/1.49  --prep_def_merge_prop_impl              false
% 6.67/1.49  --prep_def_merge_mbd                    true
% 6.67/1.49  --prep_def_merge_tr_red                 false
% 6.67/1.49  --prep_def_merge_tr_cl                  false
% 6.67/1.49  --smt_preprocessing                     true
% 6.67/1.49  --smt_ac_axioms                         fast
% 6.67/1.49  --preprocessed_out                      false
% 6.67/1.49  --preprocessed_stats                    false
% 6.67/1.49  
% 6.67/1.49  ------ Abstraction refinement Options
% 6.67/1.49  
% 6.67/1.49  --abstr_ref                             []
% 6.67/1.49  --abstr_ref_prep                        false
% 6.67/1.49  --abstr_ref_until_sat                   false
% 6.67/1.49  --abstr_ref_sig_restrict                funpre
% 6.67/1.49  --abstr_ref_af_restrict_to_split_sk     false
% 6.67/1.49  --abstr_ref_under                       []
% 6.67/1.49  
% 6.67/1.49  ------ SAT Options
% 6.67/1.49  
% 6.67/1.49  --sat_mode                              false
% 6.67/1.49  --sat_fm_restart_options                ""
% 6.67/1.49  --sat_gr_def                            false
% 6.67/1.49  --sat_epr_types                         true
% 6.67/1.49  --sat_non_cyclic_types                  false
% 6.67/1.49  --sat_finite_models                     false
% 6.67/1.49  --sat_fm_lemmas                         false
% 6.67/1.49  --sat_fm_prep                           false
% 6.67/1.49  --sat_fm_uc_incr                        true
% 6.67/1.49  --sat_out_model                         small
% 6.67/1.49  --sat_out_clauses                       false
% 6.67/1.49  
% 6.67/1.49  ------ QBF Options
% 6.67/1.49  
% 6.67/1.49  --qbf_mode                              false
% 6.67/1.49  --qbf_elim_univ                         false
% 6.67/1.49  --qbf_dom_inst                          none
% 6.67/1.49  --qbf_dom_pre_inst                      false
% 6.67/1.49  --qbf_sk_in                             false
% 6.67/1.49  --qbf_pred_elim                         true
% 6.67/1.49  --qbf_split                             512
% 6.67/1.49  
% 6.67/1.49  ------ BMC1 Options
% 6.67/1.49  
% 6.67/1.49  --bmc1_incremental                      false
% 6.67/1.49  --bmc1_axioms                           reachable_all
% 6.67/1.49  --bmc1_min_bound                        0
% 6.67/1.49  --bmc1_max_bound                        -1
% 6.67/1.49  --bmc1_max_bound_default                -1
% 6.67/1.49  --bmc1_symbol_reachability              true
% 6.67/1.49  --bmc1_property_lemmas                  false
% 6.67/1.49  --bmc1_k_induction                      false
% 6.67/1.49  --bmc1_non_equiv_states                 false
% 6.67/1.49  --bmc1_deadlock                         false
% 6.67/1.49  --bmc1_ucm                              false
% 6.67/1.49  --bmc1_add_unsat_core                   none
% 6.67/1.49  --bmc1_unsat_core_children              false
% 6.67/1.49  --bmc1_unsat_core_extrapolate_axioms    false
% 6.67/1.49  --bmc1_out_stat                         full
% 6.67/1.49  --bmc1_ground_init                      false
% 6.67/1.49  --bmc1_pre_inst_next_state              false
% 6.67/1.49  --bmc1_pre_inst_state                   false
% 6.67/1.49  --bmc1_pre_inst_reach_state             false
% 6.67/1.49  --bmc1_out_unsat_core                   false
% 6.67/1.49  --bmc1_aig_witness_out                  false
% 6.67/1.49  --bmc1_verbose                          false
% 6.67/1.49  --bmc1_dump_clauses_tptp                false
% 6.67/1.49  --bmc1_dump_unsat_core_tptp             false
% 6.67/1.49  --bmc1_dump_file                        -
% 6.67/1.49  --bmc1_ucm_expand_uc_limit              128
% 6.67/1.49  --bmc1_ucm_n_expand_iterations          6
% 6.67/1.49  --bmc1_ucm_extend_mode                  1
% 6.67/1.49  --bmc1_ucm_init_mode                    2
% 6.67/1.49  --bmc1_ucm_cone_mode                    none
% 6.67/1.49  --bmc1_ucm_reduced_relation_type        0
% 6.67/1.49  --bmc1_ucm_relax_model                  4
% 6.67/1.49  --bmc1_ucm_full_tr_after_sat            true
% 6.67/1.49  --bmc1_ucm_expand_neg_assumptions       false
% 6.67/1.49  --bmc1_ucm_layered_model                none
% 6.67/1.49  --bmc1_ucm_max_lemma_size               10
% 6.67/1.49  
% 6.67/1.49  ------ AIG Options
% 6.67/1.49  
% 6.67/1.49  --aig_mode                              false
% 6.67/1.49  
% 6.67/1.49  ------ Instantiation Options
% 6.67/1.49  
% 6.67/1.49  --instantiation_flag                    true
% 6.67/1.49  --inst_sos_flag                         false
% 6.67/1.49  --inst_sos_phase                        true
% 6.67/1.49  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 6.67/1.49  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 6.67/1.49  --inst_lit_sel_side                     none
% 6.67/1.49  --inst_solver_per_active                1400
% 6.67/1.49  --inst_solver_calls_frac                1.
% 6.67/1.49  --inst_passive_queue_type               priority_queues
% 6.67/1.49  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 6.67/1.49  --inst_passive_queues_freq              [25;2]
% 6.67/1.49  --inst_dismatching                      true
% 6.67/1.49  --inst_eager_unprocessed_to_passive     true
% 6.67/1.49  --inst_prop_sim_given                   true
% 6.67/1.49  --inst_prop_sim_new                     false
% 6.67/1.49  --inst_subs_new                         false
% 6.67/1.49  --inst_eq_res_simp                      false
% 6.67/1.49  --inst_subs_given                       false
% 6.67/1.49  --inst_orphan_elimination               true
% 6.67/1.49  --inst_learning_loop_flag               true
% 6.67/1.49  --inst_learning_start                   3000
% 6.67/1.49  --inst_learning_factor                  2
% 6.67/1.49  --inst_start_prop_sim_after_learn       3
% 6.67/1.49  --inst_sel_renew                        solver
% 6.67/1.49  --inst_lit_activity_flag                true
% 6.67/1.49  --inst_restr_to_given                   false
% 6.67/1.49  --inst_activity_threshold               500
% 6.67/1.49  --inst_out_proof                        true
% 6.67/1.49  
% 6.67/1.49  ------ Resolution Options
% 6.67/1.49  
% 6.67/1.49  --resolution_flag                       false
% 6.67/1.49  --res_lit_sel                           adaptive
% 6.67/1.49  --res_lit_sel_side                      none
% 6.67/1.49  --res_ordering                          kbo
% 6.67/1.49  --res_to_prop_solver                    active
% 6.67/1.49  --res_prop_simpl_new                    false
% 6.67/1.49  --res_prop_simpl_given                  true
% 6.67/1.49  --res_passive_queue_type                priority_queues
% 6.67/1.49  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 6.67/1.49  --res_passive_queues_freq               [15;5]
% 6.67/1.49  --res_forward_subs                      full
% 6.67/1.49  --res_backward_subs                     full
% 6.67/1.49  --res_forward_subs_resolution           true
% 6.67/1.49  --res_backward_subs_resolution          true
% 6.67/1.49  --res_orphan_elimination                true
% 6.67/1.49  --res_time_limit                        2.
% 6.67/1.49  --res_out_proof                         true
% 6.67/1.49  
% 6.67/1.49  ------ Superposition Options
% 6.67/1.49  
% 6.67/1.49  --superposition_flag                    true
% 6.67/1.49  --sup_passive_queue_type                priority_queues
% 6.67/1.49  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 6.67/1.49  --sup_passive_queues_freq               [8;1;4]
% 6.67/1.49  --demod_completeness_check              fast
% 6.67/1.49  --demod_use_ground                      true
% 6.67/1.49  --sup_to_prop_solver                    passive
% 6.67/1.49  --sup_prop_simpl_new                    true
% 6.67/1.49  --sup_prop_simpl_given                  true
% 6.67/1.49  --sup_fun_splitting                     false
% 6.67/1.49  --sup_smt_interval                      50000
% 6.67/1.49  
% 6.67/1.49  ------ Superposition Simplification Setup
% 6.67/1.49  
% 6.67/1.49  --sup_indices_passive                   []
% 6.67/1.49  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 6.67/1.49  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 6.67/1.49  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 6.67/1.49  --sup_full_triv                         [TrivRules;PropSubs]
% 6.67/1.49  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 6.67/1.49  --sup_full_bw                           [BwDemod]
% 6.67/1.49  --sup_immed_triv                        [TrivRules]
% 6.67/1.49  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 6.67/1.49  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 6.67/1.49  --sup_immed_bw_main                     []
% 6.67/1.49  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 6.67/1.49  --sup_input_triv                        [Unflattening;TrivRules]
% 6.67/1.49  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 6.67/1.49  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 6.67/1.49  
% 6.67/1.49  ------ Combination Options
% 6.67/1.49  
% 6.67/1.49  --comb_res_mult                         3
% 6.67/1.49  --comb_sup_mult                         2
% 6.67/1.49  --comb_inst_mult                        10
% 6.67/1.49  
% 6.67/1.49  ------ Debug Options
% 6.67/1.49  
% 6.67/1.49  --dbg_backtrace                         false
% 6.67/1.49  --dbg_dump_prop_clauses                 false
% 6.67/1.49  --dbg_dump_prop_clauses_file            -
% 6.67/1.49  --dbg_out_stat                          false
% 6.67/1.49  
% 6.67/1.49  
% 6.67/1.49  
% 6.67/1.49  
% 6.67/1.49  ------ Proving...
% 6.67/1.49  
% 6.67/1.49  
% 6.67/1.49  % SZS status Theorem for theBenchmark.p
% 6.67/1.49  
% 6.67/1.49  % SZS output start CNFRefutation for theBenchmark.p
% 6.67/1.49  
% 6.67/1.49  fof(f25,conjecture,(
% 6.67/1.49    ! [X0,X1,X2] : ~(~(k1_xboole_0 = X2 & k1_tarski(X0) = X1) & ~(k1_tarski(X0) = X2 & k1_xboole_0 = X1) & ~(k1_tarski(X0) = X2 & k1_tarski(X0) = X1) & k2_xboole_0(X1,X2) = k1_tarski(X0))),
% 6.67/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.67/1.49  
% 6.67/1.49  fof(f26,negated_conjecture,(
% 6.67/1.49    ~! [X0,X1,X2] : ~(~(k1_xboole_0 = X2 & k1_tarski(X0) = X1) & ~(k1_tarski(X0) = X2 & k1_xboole_0 = X1) & ~(k1_tarski(X0) = X2 & k1_tarski(X0) = X1) & k2_xboole_0(X1,X2) = k1_tarski(X0))),
% 6.67/1.49    inference(negated_conjecture,[],[f25])).
% 6.67/1.49  
% 6.67/1.49  fof(f34,plain,(
% 6.67/1.49    ? [X0,X1,X2] : ((k1_xboole_0 != X2 | k1_tarski(X0) != X1) & (k1_tarski(X0) != X2 | k1_xboole_0 != X1) & (k1_tarski(X0) != X2 | k1_tarski(X0) != X1) & k2_xboole_0(X1,X2) = k1_tarski(X0))),
% 6.67/1.49    inference(ennf_transformation,[],[f26])).
% 6.67/1.49  
% 6.67/1.49  fof(f46,plain,(
% 6.67/1.49    ? [X0,X1,X2] : ((k1_xboole_0 != X2 | k1_tarski(X0) != X1) & (k1_tarski(X0) != X2 | k1_xboole_0 != X1) & (k1_tarski(X0) != X2 | k1_tarski(X0) != X1) & k2_xboole_0(X1,X2) = k1_tarski(X0)) => ((k1_xboole_0 != sK4 | k1_tarski(sK2) != sK3) & (k1_tarski(sK2) != sK4 | k1_xboole_0 != sK3) & (k1_tarski(sK2) != sK4 | k1_tarski(sK2) != sK3) & k2_xboole_0(sK3,sK4) = k1_tarski(sK2))),
% 6.67/1.49    introduced(choice_axiom,[])).
% 6.67/1.49  
% 6.67/1.49  fof(f47,plain,(
% 6.67/1.49    (k1_xboole_0 != sK4 | k1_tarski(sK2) != sK3) & (k1_tarski(sK2) != sK4 | k1_xboole_0 != sK3) & (k1_tarski(sK2) != sK4 | k1_tarski(sK2) != sK3) & k2_xboole_0(sK3,sK4) = k1_tarski(sK2)),
% 6.67/1.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f34,f46])).
% 6.67/1.49  
% 6.67/1.49  fof(f80,plain,(
% 6.67/1.49    k2_xboole_0(sK3,sK4) = k1_tarski(sK2)),
% 6.67/1.49    inference(cnf_transformation,[],[f47])).
% 6.67/1.49  
% 6.67/1.49  fof(f24,axiom,(
% 6.67/1.49    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 6.67/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.67/1.49  
% 6.67/1.49  fof(f79,plain,(
% 6.67/1.49    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 6.67/1.49    inference(cnf_transformation,[],[f24])).
% 6.67/1.49  
% 6.67/1.49  fof(f89,plain,(
% 6.67/1.49    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) )),
% 6.67/1.49    inference(definition_unfolding,[],[f79,f88])).
% 6.67/1.49  
% 6.67/1.49  fof(f14,axiom,(
% 6.67/1.49    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 6.67/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.67/1.49  
% 6.67/1.49  fof(f66,plain,(
% 6.67/1.49    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 6.67/1.49    inference(cnf_transformation,[],[f14])).
% 6.67/1.49  
% 6.67/1.49  fof(f15,axiom,(
% 6.67/1.49    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 6.67/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.67/1.49  
% 6.67/1.49  fof(f67,plain,(
% 6.67/1.49    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 6.67/1.49    inference(cnf_transformation,[],[f15])).
% 6.67/1.49  
% 6.67/1.49  fof(f16,axiom,(
% 6.67/1.49    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 6.67/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.67/1.49  
% 6.67/1.49  fof(f68,plain,(
% 6.67/1.49    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 6.67/1.49    inference(cnf_transformation,[],[f16])).
% 6.67/1.49  
% 6.67/1.49  fof(f17,axiom,(
% 6.67/1.49    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 6.67/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.67/1.49  
% 6.67/1.49  fof(f69,plain,(
% 6.67/1.49    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 6.67/1.49    inference(cnf_transformation,[],[f17])).
% 6.67/1.49  
% 6.67/1.49  fof(f18,axiom,(
% 6.67/1.49    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)),
% 6.67/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.67/1.49  
% 6.67/1.49  fof(f70,plain,(
% 6.67/1.49    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)) )),
% 6.67/1.49    inference(cnf_transformation,[],[f18])).
% 6.67/1.49  
% 6.67/1.49  fof(f19,axiom,(
% 6.67/1.49    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)),
% 6.67/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.67/1.49  
% 6.67/1.49  fof(f71,plain,(
% 6.67/1.49    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)) )),
% 6.67/1.49    inference(cnf_transformation,[],[f19])).
% 6.67/1.49  
% 6.67/1.49  fof(f20,axiom,(
% 6.67/1.49    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)),
% 6.67/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.67/1.49  
% 6.67/1.49  fof(f72,plain,(
% 6.67/1.49    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)) )),
% 6.67/1.49    inference(cnf_transformation,[],[f20])).
% 6.67/1.49  
% 6.67/1.49  fof(f84,plain,(
% 6.67/1.49    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 6.67/1.49    inference(definition_unfolding,[],[f71,f72])).
% 6.67/1.49  
% 6.67/1.49  fof(f85,plain,(
% 6.67/1.49    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 6.67/1.49    inference(definition_unfolding,[],[f70,f84])).
% 6.67/1.49  
% 6.67/1.49  fof(f86,plain,(
% 6.67/1.49    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 6.67/1.49    inference(definition_unfolding,[],[f69,f85])).
% 6.67/1.49  
% 6.67/1.49  fof(f87,plain,(
% 6.67/1.49    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 6.67/1.49    inference(definition_unfolding,[],[f68,f86])).
% 6.67/1.49  
% 6.67/1.49  fof(f88,plain,(
% 6.67/1.49    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 6.67/1.49    inference(definition_unfolding,[],[f67,f87])).
% 6.67/1.49  
% 6.67/1.49  fof(f91,plain,(
% 6.67/1.49    ( ! [X0] : (k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) )),
% 6.67/1.49    inference(definition_unfolding,[],[f66,f88])).
% 6.67/1.49  
% 6.67/1.49  fof(f107,plain,(
% 6.67/1.49    k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) = k3_tarski(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4))),
% 6.67/1.49    inference(definition_unfolding,[],[f80,f89,f91])).
% 6.67/1.49  
% 6.67/1.49  fof(f7,axiom,(
% 6.67/1.49    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 6.67/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.67/1.49  
% 6.67/1.49  fof(f59,plain,(
% 6.67/1.49    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 6.67/1.49    inference(cnf_transformation,[],[f7])).
% 6.67/1.49  
% 6.67/1.49  fof(f13,axiom,(
% 6.67/1.49    ! [X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)),
% 6.67/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.67/1.49  
% 6.67/1.49  fof(f65,plain,(
% 6.67/1.49    ( ! [X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)) )),
% 6.67/1.49    inference(cnf_transformation,[],[f13])).
% 6.67/1.49  
% 6.67/1.49  fof(f90,plain,(
% 6.67/1.49    ( ! [X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) = k3_xboole_0(X0,X1)) )),
% 6.67/1.49    inference(definition_unfolding,[],[f65,f89])).
% 6.67/1.49  
% 6.67/1.49  fof(f96,plain,(
% 6.67/1.49    ( ! [X0,X1] : (r1_tarski(k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))),X0)) )),
% 6.67/1.49    inference(definition_unfolding,[],[f59,f90])).
% 6.67/1.49  
% 6.67/1.49  fof(f11,axiom,(
% 6.67/1.49    ! [X0,X1,X2] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2)),
% 6.67/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.67/1.49  
% 6.67/1.49  fof(f63,plain,(
% 6.67/1.49    ( ! [X2,X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2)) )),
% 6.67/1.49    inference(cnf_transformation,[],[f11])).
% 6.67/1.49  
% 6.67/1.49  fof(f1,axiom,(
% 6.67/1.49    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)),
% 6.67/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.67/1.49  
% 6.67/1.49  fof(f48,plain,(
% 6.67/1.49    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)) )),
% 6.67/1.49    inference(cnf_transformation,[],[f1])).
% 6.67/1.49  
% 6.67/1.49  fof(f10,axiom,(
% 6.67/1.49    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 6.67/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.67/1.49  
% 6.67/1.49  fof(f62,plain,(
% 6.67/1.49    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 6.67/1.49    inference(cnf_transformation,[],[f10])).
% 6.67/1.49  
% 6.67/1.49  fof(f97,plain,(
% 6.67/1.49    ( ! [X0,X1] : (r1_tarski(X0,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) )),
% 6.67/1.49    inference(definition_unfolding,[],[f62,f89])).
% 6.67/1.49  
% 6.67/1.49  fof(f23,axiom,(
% 6.67/1.49    ! [X0,X1] : (r1_tarski(X0,k1_tarski(X1)) <=> (k1_tarski(X1) = X0 | k1_xboole_0 = X0))),
% 6.67/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.67/1.49  
% 6.67/1.49  fof(f44,plain,(
% 6.67/1.49    ! [X0,X1] : ((r1_tarski(X0,k1_tarski(X1)) | (k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & ((k1_tarski(X1) = X0 | k1_xboole_0 = X0) | ~r1_tarski(X0,k1_tarski(X1))))),
% 6.67/1.49    inference(nnf_transformation,[],[f23])).
% 6.67/1.49  
% 6.67/1.49  fof(f45,plain,(
% 6.67/1.49    ! [X0,X1] : ((r1_tarski(X0,k1_tarski(X1)) | (k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & (k1_tarski(X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k1_tarski(X1))))),
% 6.67/1.49    inference(flattening,[],[f44])).
% 6.67/1.49  
% 6.67/1.49  fof(f76,plain,(
% 6.67/1.49    ( ! [X0,X1] : (k1_tarski(X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k1_tarski(X1))) )),
% 6.67/1.49    inference(cnf_transformation,[],[f45])).
% 6.67/1.49  
% 6.67/1.49  fof(f103,plain,(
% 6.67/1.49    ( ! [X0,X1] : (k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))) )),
% 6.67/1.49    inference(definition_unfolding,[],[f76,f91,f91])).
% 6.67/1.49  
% 6.67/1.49  fof(f83,plain,(
% 6.67/1.49    k1_xboole_0 != sK4 | k1_tarski(sK2) != sK3),
% 6.67/1.49    inference(cnf_transformation,[],[f47])).
% 6.67/1.49  
% 6.67/1.49  fof(f104,plain,(
% 6.67/1.49    k1_xboole_0 != sK4 | k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) != sK3),
% 6.67/1.49    inference(definition_unfolding,[],[f83,f91])).
% 6.67/1.49  
% 6.67/1.49  fof(f81,plain,(
% 6.67/1.49    k1_tarski(sK2) != sK4 | k1_tarski(sK2) != sK3),
% 6.67/1.49    inference(cnf_transformation,[],[f47])).
% 6.67/1.49  
% 6.67/1.49  fof(f106,plain,(
% 6.67/1.49    k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) != sK4 | k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) != sK3),
% 6.67/1.49    inference(definition_unfolding,[],[f81,f91,f91])).
% 6.67/1.49  
% 6.67/1.49  fof(f82,plain,(
% 6.67/1.49    k1_tarski(sK2) != sK4 | k1_xboole_0 != sK3),
% 6.67/1.49    inference(cnf_transformation,[],[f47])).
% 6.67/1.49  
% 6.67/1.49  fof(f105,plain,(
% 6.67/1.49    k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) != sK4 | k1_xboole_0 != sK3),
% 6.67/1.49    inference(definition_unfolding,[],[f82,f91])).
% 6.67/1.49  
% 6.67/1.49  fof(f12,axiom,(
% 6.67/1.49    ! [X0] : k5_xboole_0(X0,X0) = k1_xboole_0),
% 6.67/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.67/1.49  
% 6.67/1.49  fof(f64,plain,(
% 6.67/1.49    ( ! [X0] : (k5_xboole_0(X0,X0) = k1_xboole_0) )),
% 6.67/1.49    inference(cnf_transformation,[],[f12])).
% 6.67/1.49  
% 6.67/1.49  fof(f9,axiom,(
% 6.67/1.49    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 6.67/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.67/1.49  
% 6.67/1.49  fof(f61,plain,(
% 6.67/1.49    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 6.67/1.49    inference(cnf_transformation,[],[f9])).
% 6.67/1.49  
% 6.67/1.49  fof(f8,axiom,(
% 6.67/1.49    ! [X0] : (r1_tarski(X0,k1_xboole_0) => k1_xboole_0 = X0)),
% 6.67/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.67/1.49  
% 6.67/1.49  fof(f32,plain,(
% 6.67/1.49    ! [X0] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k1_xboole_0))),
% 6.67/1.49    inference(ennf_transformation,[],[f8])).
% 6.67/1.49  
% 6.67/1.49  fof(f60,plain,(
% 6.67/1.49    ( ! [X0] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k1_xboole_0)) )),
% 6.67/1.49    inference(cnf_transformation,[],[f32])).
% 6.67/1.49  
% 6.67/1.49  cnf(c_26,negated_conjecture,
% 6.67/1.49      ( k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) = k3_tarski(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4)) ),
% 6.67/1.49      inference(cnf_transformation,[],[f107]) ).
% 6.67/1.49  
% 6.67/1.49  cnf(c_11,plain,
% 6.67/1.49      ( r1_tarski(k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))),X0) ),
% 6.67/1.49      inference(cnf_transformation,[],[f96]) ).
% 6.67/1.49  
% 6.67/1.49  cnf(c_15,plain,
% 6.67/1.49      ( k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
% 6.67/1.49      inference(cnf_transformation,[],[f63]) ).
% 6.67/1.49  
% 6.67/1.49  cnf(c_0,plain,
% 6.67/1.49      ( k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
% 6.67/1.49      inference(cnf_transformation,[],[f48]) ).
% 6.67/1.49  
% 6.67/1.49  cnf(c_457,plain,
% 6.67/1.49      ( r1_tarski(k5_xboole_0(X0,k5_xboole_0(X1,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))),X0) ),
% 6.67/1.49      inference(theory_normalisation,[status(thm)],[c_11,c_15,c_0]) ).
% 6.67/1.49  
% 6.67/1.49  cnf(c_896,plain,
% 6.67/1.49      ( r1_tarski(k5_xboole_0(X0,k5_xboole_0(X1,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))),X0) = iProver_top ),
% 6.67/1.49      inference(predicate_to_equality,[status(thm)],[c_457]) ).
% 6.67/1.49  
% 6.67/1.49  cnf(c_20223,plain,
% 6.67/1.49      ( r1_tarski(k5_xboole_0(sK3,k5_xboole_0(sK4,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))),sK3) = iProver_top ),
% 6.67/1.49      inference(superposition,[status(thm)],[c_26,c_896]) ).
% 6.67/1.49  
% 6.67/1.49  cnf(c_14,plain,
% 6.67/1.49      ( r1_tarski(X0,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) ),
% 6.67/1.49      inference(cnf_transformation,[],[f97]) ).
% 6.67/1.49  
% 6.67/1.49  cnf(c_894,plain,
% 6.67/1.49      ( r1_tarski(X0,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) = iProver_top ),
% 6.67/1.49      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 6.67/1.49  
% 6.67/1.49  cnf(c_16908,plain,
% 6.67/1.49      ( r1_tarski(sK3,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)) = iProver_top ),
% 6.67/1.49      inference(superposition,[status(thm)],[c_26,c_894]) ).
% 6.67/1.49  
% 6.67/1.49  cnf(c_22,plain,
% 6.67/1.49      ( ~ r1_tarski(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))
% 6.67/1.49      | k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) = X0
% 6.67/1.49      | k1_xboole_0 = X0 ),
% 6.67/1.49      inference(cnf_transformation,[],[f103]) ).
% 6.67/1.49  
% 6.67/1.49  cnf(c_888,plain,
% 6.67/1.49      ( k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) = X1
% 6.67/1.49      | k1_xboole_0 = X1
% 6.67/1.49      | r1_tarski(X1,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) != iProver_top ),
% 6.67/1.49      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 6.67/1.49  
% 6.67/1.49  cnf(c_19776,plain,
% 6.67/1.49      ( k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) = sK3
% 6.67/1.49      | sK3 = k1_xboole_0 ),
% 6.67/1.49      inference(superposition,[status(thm)],[c_16908,c_888]) ).
% 6.67/1.49  
% 6.67/1.49  cnf(c_19867,plain,
% 6.67/1.49      ( k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) = X0
% 6.67/1.49      | sK3 = k1_xboole_0
% 6.67/1.49      | k1_xboole_0 = X0
% 6.67/1.49      | r1_tarski(X0,sK3) != iProver_top ),
% 6.67/1.49      inference(superposition,[status(thm)],[c_19776,c_888]) ).
% 6.67/1.49  
% 6.67/1.49  cnf(c_24891,plain,
% 6.67/1.49      ( k5_xboole_0(sK3,k5_xboole_0(sK4,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))) = k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)
% 6.67/1.49      | k5_xboole_0(sK3,k5_xboole_0(sK4,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))) = k1_xboole_0
% 6.67/1.49      | sK3 = k1_xboole_0 ),
% 6.67/1.49      inference(superposition,[status(thm)],[c_20223,c_19867]) ).
% 6.67/1.49  
% 6.67/1.49  cnf(c_23,negated_conjecture,
% 6.67/1.49      ( k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) != sK3
% 6.67/1.49      | k1_xboole_0 != sK4 ),
% 6.67/1.49      inference(cnf_transformation,[],[f104]) ).
% 6.67/1.49  
% 6.67/1.49  cnf(c_19872,plain,
% 6.67/1.49      ( sK3 = k1_xboole_0 | sK4 != k1_xboole_0 ),
% 6.67/1.49      inference(superposition,[status(thm)],[c_19776,c_23]) ).
% 6.67/1.49  
% 6.67/1.49  cnf(c_25,negated_conjecture,
% 6.67/1.49      ( k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) != sK3
% 6.67/1.49      | k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) != sK4 ),
% 6.67/1.49      inference(cnf_transformation,[],[f106]) ).
% 6.67/1.49  
% 6.67/1.49  cnf(c_19870,plain,
% 6.67/1.49      ( k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) != sK4
% 6.67/1.49      | sK3 = k1_xboole_0 ),
% 6.67/1.49      inference(superposition,[status(thm)],[c_19776,c_25]) ).
% 6.67/1.49  
% 6.67/1.49  cnf(c_24,negated_conjecture,
% 6.67/1.49      ( k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) != sK4
% 6.67/1.49      | k1_xboole_0 != sK3 ),
% 6.67/1.49      inference(cnf_transformation,[],[f105]) ).
% 6.67/1.49  
% 6.67/1.49  cnf(c_1811,plain,
% 6.67/1.49      ( ~ r1_tarski(sK3,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))
% 6.67/1.49      | k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) = sK3
% 6.67/1.49      | k1_xboole_0 = sK3 ),
% 6.67/1.49      inference(instantiation,[status(thm)],[c_22]) ).
% 6.67/1.49  
% 6.67/1.49  cnf(c_1814,plain,
% 6.67/1.49      ( ~ r1_tarski(sK3,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))
% 6.67/1.49      | k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) = sK3
% 6.67/1.49      | k1_xboole_0 = sK3 ),
% 6.67/1.49      inference(instantiation,[status(thm)],[c_1811]) ).
% 6.67/1.49  
% 6.67/1.49  cnf(c_16914,plain,
% 6.67/1.49      ( r1_tarski(sK3,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)) ),
% 6.67/1.49      inference(predicate_to_equality_rev,[status(thm)],[c_16908]) ).
% 6.67/1.49  
% 6.67/1.49  cnf(c_20072,plain,
% 6.67/1.49      ( k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) != sK4 ),
% 6.67/1.49      inference(global_propositional_subsumption,
% 6.67/1.49                [status(thm)],
% 6.67/1.49                [c_19870,c_25,c_24,c_1814,c_16914]) ).
% 6.67/1.49  
% 6.67/1.49  cnf(c_22482,plain,
% 6.67/1.49      ( sK3 = k1_xboole_0
% 6.67/1.49      | r1_tarski(k5_xboole_0(sK3,k5_xboole_0(sK4,sK3)),sK3) = iProver_top ),
% 6.67/1.49      inference(superposition,[status(thm)],[c_19776,c_20223]) ).
% 6.67/1.49  
% 6.67/1.49  cnf(c_16,plain,
% 6.67/1.49      ( k5_xboole_0(X0,X0) = k1_xboole_0 ),
% 6.67/1.49      inference(cnf_transformation,[],[f64]) ).
% 6.67/1.49  
% 6.67/1.49  cnf(c_1218,plain,
% 6.67/1.49      ( k5_xboole_0(X0,k5_xboole_0(X0,X1)) = k5_xboole_0(k1_xboole_0,X1) ),
% 6.67/1.49      inference(superposition,[status(thm)],[c_16,c_15]) ).
% 6.67/1.49  
% 6.67/1.49  cnf(c_13,plain,
% 6.67/1.49      ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
% 6.67/1.49      inference(cnf_transformation,[],[f61]) ).
% 6.67/1.49  
% 6.67/1.49  cnf(c_1174,plain,
% 6.67/1.49      ( k5_xboole_0(k1_xboole_0,X0) = X0 ),
% 6.67/1.49      inference(superposition,[status(thm)],[c_13,c_0]) ).
% 6.67/1.49  
% 6.67/1.49  cnf(c_1353,plain,
% 6.67/1.49      ( k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1 ),
% 6.67/1.49      inference(demodulation,[status(thm)],[c_1218,c_1174]) ).
% 6.67/1.49  
% 6.67/1.49  cnf(c_1358,plain,
% 6.67/1.49      ( k5_xboole_0(X0,k5_xboole_0(X1,X0)) = X1 ),
% 6.67/1.49      inference(superposition,[status(thm)],[c_0,c_1353]) ).
% 6.67/1.49  
% 6.67/1.49  cnf(c_22485,plain,
% 6.67/1.49      ( sK3 = k1_xboole_0 | r1_tarski(sK4,sK3) = iProver_top ),
% 6.67/1.49      inference(demodulation,[status(thm)],[c_22482,c_1358]) ).
% 6.67/1.49  
% 6.67/1.49  cnf(c_24890,plain,
% 6.67/1.49      ( k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) = sK4
% 6.67/1.49      | sK3 = k1_xboole_0
% 6.67/1.49      | sK4 = k1_xboole_0 ),
% 6.67/1.49      inference(superposition,[status(thm)],[c_22485,c_19867]) ).
% 6.67/1.49  
% 6.67/1.49  cnf(c_24964,plain,
% 6.67/1.49      ( sK3 = k1_xboole_0 ),
% 6.67/1.49      inference(global_propositional_subsumption,
% 6.67/1.49                [status(thm)],
% 6.67/1.49                [c_24891,c_25,c_24,c_1814,c_16914,c_19872,c_24890]) ).
% 6.67/1.49  
% 6.67/1.49  cnf(c_24973,plain,
% 6.67/1.49      ( r1_tarski(k5_xboole_0(k1_xboole_0,k5_xboole_0(sK4,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))),k1_xboole_0) = iProver_top ),
% 6.67/1.49      inference(demodulation,[status(thm)],[c_24964,c_20223]) ).
% 6.67/1.49  
% 6.67/1.49  cnf(c_1003,plain,
% 6.67/1.49      ( k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(X2,k5_xboole_0(X1,X0)) ),
% 6.67/1.49      inference(superposition,[status(thm)],[c_15,c_0]) ).
% 6.67/1.49  
% 6.67/1.49  cnf(c_1722,plain,
% 6.67/1.49      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(X0,X1)) = k5_xboole_0(X1,X0) ),
% 6.67/1.49      inference(superposition,[status(thm)],[c_13,c_1003]) ).
% 6.67/1.49  
% 6.67/1.49  cnf(c_24989,plain,
% 6.67/1.49      ( r1_tarski(k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK4),k1_xboole_0) = iProver_top ),
% 6.67/1.49      inference(demodulation,[status(thm)],[c_24973,c_1722]) ).
% 6.67/1.49  
% 6.67/1.49  cnf(c_12,plain,
% 6.67/1.49      ( ~ r1_tarski(X0,k1_xboole_0) | k1_xboole_0 = X0 ),
% 6.67/1.49      inference(cnf_transformation,[],[f60]) ).
% 6.67/1.49  
% 6.67/1.49  cnf(c_895,plain,
% 6.67/1.49      ( k1_xboole_0 = X0 | r1_tarski(X0,k1_xboole_0) != iProver_top ),
% 6.67/1.49      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 6.67/1.49  
% 6.67/1.49  cnf(c_26989,plain,
% 6.67/1.49      ( k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK4) = k1_xboole_0 ),
% 6.67/1.49      inference(superposition,[status(thm)],[c_24989,c_895]) ).
% 6.67/1.49  
% 6.67/1.49  cnf(c_1002,plain,
% 6.67/1.49      ( k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(X1,k5_xboole_0(X0,X2)) ),
% 6.67/1.49      inference(superposition,[status(thm)],[c_15,c_0]) ).
% 6.67/1.49  
% 6.67/1.49  cnf(c_1608,plain,
% 6.67/1.49      ( k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X0,k5_xboole_0(X2,X1))) = X2 ),
% 6.67/1.49      inference(superposition,[status(thm)],[c_1002,c_1358]) ).
% 6.67/1.49  
% 6.67/1.49  cnf(c_27816,plain,
% 6.67/1.49      ( k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) = k5_xboole_0(k5_xboole_0(X0,sK4),k5_xboole_0(X0,k1_xboole_0)) ),
% 6.67/1.49      inference(superposition,[status(thm)],[c_26989,c_1608]) ).
% 6.67/1.49  
% 6.67/1.49  cnf(c_27826,plain,
% 6.67/1.49      ( k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) = k5_xboole_0(k5_xboole_0(X0,sK4),X0) ),
% 6.67/1.49      inference(light_normalisation,[status(thm)],[c_27816,c_13]) ).
% 6.67/1.49  
% 6.67/1.49  cnf(c_1391,plain,
% 6.67/1.49      ( k5_xboole_0(k5_xboole_0(X0,X1),X0) = X1 ),
% 6.67/1.49      inference(superposition,[status(thm)],[c_1358,c_1358]) ).
% 6.67/1.49  
% 6.67/1.49  cnf(c_27827,plain,
% 6.67/1.49      ( k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) = sK4 ),
% 6.67/1.49      inference(demodulation,[status(thm)],[c_27826,c_1391]) ).
% 6.67/1.49  
% 6.67/1.49  cnf(contradiction,plain,
% 6.67/1.49      ( $false ),
% 6.67/1.49      inference(minisat,[status(thm)],[c_27827,c_20072]) ).
% 6.67/1.49  
% 6.67/1.49  
% 6.67/1.49  % SZS output end CNFRefutation for theBenchmark.p
% 6.67/1.49  
% 6.67/1.49  ------                               Statistics
% 6.67/1.49  
% 6.67/1.49  ------ General
% 6.67/1.49  
% 6.67/1.49  abstr_ref_over_cycles:                  0
% 6.67/1.49  abstr_ref_under_cycles:                 0
% 6.67/1.49  gc_basic_clause_elim:                   0
% 6.67/1.49  forced_gc_time:                         0
% 6.67/1.49  parsing_time:                           0.01
% 6.67/1.49  unif_index_cands_time:                  0.
% 6.67/1.49  unif_index_add_time:                    0.
% 6.67/1.49  orderings_time:                         0.
% 6.67/1.49  out_proof_time:                         0.008
% 6.67/1.49  total_time:                             0.629
% 6.67/1.49  num_of_symbols:                         43
% 6.67/1.49  num_of_terms:                           25440
% 6.67/1.49  
% 6.67/1.49  ------ Preprocessing
% 6.67/1.49  
% 6.67/1.49  num_of_splits:                          0
% 6.67/1.49  num_of_split_atoms:                     0
% 6.67/1.49  num_of_reused_defs:                     0
% 6.67/1.49  num_eq_ax_congr_red:                    15
% 6.67/1.49  num_of_sem_filtered_clauses:            1
% 6.67/1.49  num_of_subtypes:                        0
% 6.67/1.49  monotx_restored_types:                  0
% 6.67/1.49  sat_num_of_epr_types:                   0
% 6.67/1.49  sat_num_of_non_cyclic_types:            0
% 6.67/1.49  sat_guarded_non_collapsed_types:        0
% 6.67/1.49  num_pure_diseq_elim:                    0
% 6.67/1.49  simp_replaced_by:                       0
% 6.67/1.49  res_preprocessed:                       121
% 6.67/1.49  prep_upred:                             0
% 6.67/1.49  prep_unflattend:                        4
% 6.67/1.49  smt_new_axioms:                         0
% 6.67/1.49  pred_elim_cands:                        3
% 6.67/1.49  pred_elim:                              0
% 6.67/1.49  pred_elim_cl:                           0
% 6.67/1.49  pred_elim_cycles:                       2
% 6.67/1.49  merged_defs:                            8
% 6.67/1.49  merged_defs_ncl:                        0
% 6.67/1.49  bin_hyper_res:                          8
% 6.67/1.49  prep_cycles:                            4
% 6.67/1.49  pred_elim_time:                         0.002
% 6.67/1.49  splitting_time:                         0.
% 6.67/1.49  sem_filter_time:                        0.
% 6.67/1.49  monotx_time:                            0.
% 6.67/1.49  subtype_inf_time:                       0.
% 6.67/1.49  
% 6.67/1.49  ------ Problem properties
% 6.67/1.49  
% 6.67/1.49  clauses:                                26
% 6.67/1.49  conjectures:                            4
% 6.67/1.49  epr:                                    4
% 6.67/1.49  horn:                                   22
% 6.67/1.49  ground:                                 4
% 6.67/1.49  unary:                                  12
% 6.67/1.49  binary:                                 11
% 6.67/1.49  lits:                                   43
% 6.67/1.49  lits_eq:                                17
% 6.67/1.49  fd_pure:                                0
% 6.67/1.49  fd_pseudo:                              0
% 6.67/1.49  fd_cond:                                1
% 6.67/1.49  fd_pseudo_cond:                         2
% 6.67/1.49  ac_symbols:                             1
% 6.67/1.49  
% 6.67/1.49  ------ Propositional Solver
% 6.67/1.49  
% 6.67/1.49  prop_solver_calls:                      29
% 6.67/1.49  prop_fast_solver_calls:                 648
% 6.67/1.49  smt_solver_calls:                       0
% 6.67/1.49  smt_fast_solver_calls:                  0
% 6.67/1.49  prop_num_of_clauses:                    5069
% 6.67/1.49  prop_preprocess_simplified:             8639
% 6.67/1.49  prop_fo_subsumed:                       8
% 6.67/1.49  prop_solver_time:                       0.
% 6.67/1.49  smt_solver_time:                        0.
% 6.67/1.49  smt_fast_solver_time:                   0.
% 6.67/1.49  prop_fast_solver_time:                  0.
% 6.67/1.49  prop_unsat_core_time:                   0.
% 6.67/1.49  
% 6.67/1.49  ------ QBF
% 6.67/1.49  
% 6.67/1.49  qbf_q_res:                              0
% 6.67/1.49  qbf_num_tautologies:                    0
% 6.67/1.49  qbf_prep_cycles:                        0
% 6.67/1.49  
% 6.67/1.49  ------ BMC1
% 6.67/1.49  
% 6.67/1.49  bmc1_current_bound:                     -1
% 6.67/1.49  bmc1_last_solved_bound:                 -1
% 6.67/1.49  bmc1_unsat_core_size:                   -1
% 6.67/1.49  bmc1_unsat_core_parents_size:           -1
% 6.67/1.49  bmc1_merge_next_fun:                    0
% 6.67/1.49  bmc1_unsat_core_clauses_time:           0.
% 6.67/1.49  
% 6.67/1.49  ------ Instantiation
% 6.67/1.49  
% 6.67/1.49  inst_num_of_clauses:                    1072
% 6.67/1.49  inst_num_in_passive:                    159
% 6.67/1.50  inst_num_in_active:                     420
% 6.67/1.50  inst_num_in_unprocessed:                494
% 6.67/1.50  inst_num_of_loops:                      570
% 6.67/1.50  inst_num_of_learning_restarts:          0
% 6.67/1.50  inst_num_moves_active_passive:          147
% 6.67/1.50  inst_lit_activity:                      0
% 6.67/1.50  inst_lit_activity_moves:                0
% 6.67/1.50  inst_num_tautologies:                   0
% 6.67/1.50  inst_num_prop_implied:                  0
% 6.67/1.50  inst_num_existing_simplified:           0
% 6.67/1.50  inst_num_eq_res_simplified:             0
% 6.67/1.50  inst_num_child_elim:                    0
% 6.67/1.50  inst_num_of_dismatching_blockings:      328
% 6.67/1.50  inst_num_of_non_proper_insts:           1046
% 6.67/1.50  inst_num_of_duplicates:                 0
% 6.67/1.50  inst_inst_num_from_inst_to_res:         0
% 6.67/1.50  inst_dismatching_checking_time:         0.
% 6.67/1.50  
% 6.67/1.50  ------ Resolution
% 6.67/1.50  
% 6.67/1.50  res_num_of_clauses:                     0
% 6.67/1.50  res_num_in_passive:                     0
% 6.67/1.50  res_num_in_active:                      0
% 6.67/1.50  res_num_of_loops:                       125
% 6.67/1.50  res_forward_subset_subsumed:            87
% 6.67/1.50  res_backward_subset_subsumed:           2
% 6.67/1.50  res_forward_subsumed:                   0
% 6.67/1.50  res_backward_subsumed:                  0
% 6.67/1.50  res_forward_subsumption_resolution:     0
% 6.67/1.50  res_backward_subsumption_resolution:    0
% 6.67/1.50  res_clause_to_clause_subsumption:       69576
% 6.67/1.50  res_orphan_elimination:                 0
% 6.67/1.50  res_tautology_del:                      85
% 6.67/1.50  res_num_eq_res_simplified:              0
% 6.67/1.50  res_num_sel_changes:                    0
% 6.67/1.50  res_moves_from_active_to_pass:          0
% 6.67/1.50  
% 6.67/1.50  ------ Superposition
% 6.67/1.50  
% 6.67/1.50  sup_time_total:                         0.
% 6.67/1.50  sup_time_generating:                    0.
% 6.67/1.50  sup_time_sim_full:                      0.
% 6.67/1.50  sup_time_sim_immed:                     0.
% 6.67/1.50  
% 6.67/1.50  sup_num_of_clauses:                     1748
% 6.67/1.50  sup_num_in_active:                      85
% 6.67/1.50  sup_num_in_passive:                     1663
% 6.67/1.50  sup_num_of_loops:                       112
% 6.67/1.50  sup_fw_superposition:                   6622
% 6.67/1.50  sup_bw_superposition:                   4655
% 6.67/1.50  sup_immediate_simplified:               3004
% 6.67/1.50  sup_given_eliminated:                   2
% 6.67/1.50  comparisons_done:                       0
% 6.67/1.50  comparisons_avoided:                    6
% 6.67/1.50  
% 6.67/1.50  ------ Simplifications
% 6.67/1.50  
% 6.67/1.50  
% 6.67/1.50  sim_fw_subset_subsumed:                 2
% 6.67/1.50  sim_bw_subset_subsumed:                 14
% 6.67/1.50  sim_fw_subsumed:                        162
% 6.67/1.50  sim_bw_subsumed:                        0
% 6.67/1.50  sim_fw_subsumption_res:                 0
% 6.67/1.50  sim_bw_subsumption_res:                 0
% 6.67/1.50  sim_tautology_del:                      5
% 6.67/1.50  sim_eq_tautology_del:                   417
% 6.67/1.50  sim_eq_res_simp:                        0
% 6.67/1.50  sim_fw_demodulated:                     1464
% 6.67/1.50  sim_bw_demodulated:                     112
% 6.67/1.50  sim_light_normalised:                   1191
% 6.67/1.50  sim_joinable_taut:                      274
% 6.67/1.50  sim_joinable_simp:                      0
% 6.67/1.50  sim_ac_normalised:                      0
% 6.67/1.50  sim_smt_subsumption:                    0
% 6.67/1.50  
%------------------------------------------------------------------------------
