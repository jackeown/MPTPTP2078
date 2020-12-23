%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:32:21 EST 2020

% Result     : Theorem 3.82s
% Output     : CNFRefutation 3.82s
% Verified   : 
% Statistics : Number of formulae       :  130 (1629 expanded)
%              Number of clauses        :   64 ( 191 expanded)
%              Number of leaves         :   22 ( 506 expanded)
%              Depth                    :   23
%              Number of atoms          :  255 (2500 expanded)
%              Number of equality atoms :  198 (2331 expanded)
%              Maximal formula depth    :   11 (   3 average)
%              Maximal clause size      :   14 (   2 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f21,conjecture,(
    ! [X0,X1,X2] :
      ~ ( ~ ( k1_xboole_0 = X2
            & k1_tarski(X0) = X1 )
        & ~ ( k1_tarski(X0) = X2
            & k1_xboole_0 = X1 )
        & ~ ( k1_tarski(X0) = X2
            & k1_tarski(X0) = X1 )
        & k2_xboole_0(X1,X2) = k1_tarski(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ~ ( ~ ( k1_xboole_0 = X2
              & k1_tarski(X0) = X1 )
          & ~ ( k1_tarski(X0) = X2
              & k1_xboole_0 = X1 )
          & ~ ( k1_tarski(X0) = X2
              & k1_tarski(X0) = X1 )
          & k2_xboole_0(X1,X2) = k1_tarski(X0) ) ),
    inference(negated_conjecture,[],[f21])).

fof(f28,plain,(
    ? [X0,X1,X2] :
      ( ( k1_xboole_0 != X2
        | k1_tarski(X0) != X1 )
      & ( k1_tarski(X0) != X2
        | k1_xboole_0 != X1 )
      & ( k1_tarski(X0) != X2
        | k1_tarski(X0) != X1 )
      & k2_xboole_0(X1,X2) = k1_tarski(X0) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f31,plain,
    ( ? [X0,X1,X2] :
        ( ( k1_xboole_0 != X2
          | k1_tarski(X0) != X1 )
        & ( k1_tarski(X0) != X2
          | k1_xboole_0 != X1 )
        & ( k1_tarski(X0) != X2
          | k1_tarski(X0) != X1 )
        & k2_xboole_0(X1,X2) = k1_tarski(X0) )
   => ( ( k1_xboole_0 != sK2
        | k1_tarski(sK0) != sK1 )
      & ( k1_tarski(sK0) != sK2
        | k1_xboole_0 != sK1 )
      & ( k1_tarski(sK0) != sK2
        | k1_tarski(sK0) != sK1 )
      & k2_xboole_0(sK1,sK2) = k1_tarski(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,
    ( ( k1_xboole_0 != sK2
      | k1_tarski(sK0) != sK1 )
    & ( k1_tarski(sK0) != sK2
      | k1_xboole_0 != sK1 )
    & ( k1_tarski(sK0) != sK2
      | k1_tarski(sK0) != sK1 )
    & k2_xboole_0(sK1,sK2) = k1_tarski(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f28,f31])).

fof(f56,plain,(
    k2_xboole_0(sK1,sK2) = k1_tarski(sK0) ),
    inference(cnf_transformation,[],[f32])).

fof(f20,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f55,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f20])).

fof(f65,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f55,f64])).

fof(f12,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f12])).

fof(f13,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f13])).

fof(f14,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f47,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f14])).

fof(f15,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f15])).

fof(f16,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f49,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f16])).

fof(f17,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f50,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f17])).

fof(f18,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f51,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f18])).

fof(f60,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f50,f51])).

fof(f61,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f49,f60])).

fof(f62,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f48,f61])).

fof(f63,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f47,f62])).

fof(f64,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f46,f63])).

fof(f67,plain,(
    ! [X0] : k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f45,f64])).

fof(f78,plain,(
    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)) ),
    inference(definition_unfolding,[],[f56,f65,f67])).

fof(f4,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f11,axiom,(
    ! [X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f11])).

fof(f66,plain,(
    ! [X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) = k3_xboole_0(X0,X1) ),
    inference(definition_unfolding,[],[f44,f65])).

fof(f70,plain,(
    ! [X0,X1] : r1_tarski(k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))),X0) ),
    inference(definition_unfolding,[],[f36,f66])).

fof(f9,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X2,X0,X1] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f9])).

fof(f1,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f8,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f71,plain,(
    ! [X0,X1] : r1_tarski(X0,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) ),
    inference(definition_unfolding,[],[f41,f65])).

fof(f19,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,k1_tarski(X1))
    <=> ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,k1_tarski(X1))
        | ( k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k1_tarski(X1)) ) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,k1_tarski(X1))
        | ( k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k1_tarski(X1)) ) ) ),
    inference(flattening,[],[f29])).

fof(f52,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = X0
      | k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_tarski(X1)) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f74,plain,(
    ! [X0,X1] :
      ( k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) = X0
      | k1_xboole_0 = X0
      | ~ r1_tarski(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)) ) ),
    inference(definition_unfolding,[],[f52,f67,f67])).

fof(f59,plain,
    ( k1_xboole_0 != sK2
    | k1_tarski(sK0) != sK1 ),
    inference(cnf_transformation,[],[f32])).

fof(f75,plain,
    ( k1_xboole_0 != sK2
    | k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) != sK1 ),
    inference(definition_unfolding,[],[f59,f67])).

fof(f57,plain,
    ( k1_tarski(sK0) != sK2
    | k1_tarski(sK0) != sK1 ),
    inference(cnf_transformation,[],[f32])).

fof(f77,plain,
    ( k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) != sK2
    | k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) != sK1 ),
    inference(definition_unfolding,[],[f57,f67,f67])).

fof(f58,plain,
    ( k1_tarski(sK0) != sK2
    | k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f32])).

fof(f76,plain,
    ( k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) != sK2
    | k1_xboole_0 != sK1 ),
    inference(definition_unfolding,[],[f58,f67])).

fof(f10,axiom,(
    ! [X0] : k5_xboole_0(X0,X0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X0] : k5_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f10])).

fof(f5,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f6,axiom,(
    ! [X0] :
      ( ~ ( r1_xboole_0(X0,X0)
          & k1_xboole_0 != X0 )
      & ~ ( k1_xboole_0 = X0
          & ~ r1_xboole_0(X0,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0] :
      ( ( ~ r1_xboole_0(X0,X0)
        | k1_xboole_0 = X0 )
      & ( k1_xboole_0 != X0
        | r1_xboole_0(X0,X0) ) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f38,plain,(
    ! [X0] :
      ( k1_xboole_0 != X0
      | r1_xboole_0(X0,X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f79,plain,(
    r1_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(equality_resolution,[],[f38])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X1,X2)
        & r1_tarski(X0,X2)
        & r1_tarski(X0,X1) )
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( k1_xboole_0 = X0
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( k1_xboole_0 = X0
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f26])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 = X0
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

cnf(c_17,negated_conjecture,
    ( k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_3,plain,
    ( r1_tarski(k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))),X0) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_9,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_0,plain,
    ( k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_289,plain,
    ( r1_tarski(k5_xboole_0(X0,k5_xboole_0(X1,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))),X0) ),
    inference(theory_normalisation,[status(thm)],[c_3,c_9,c_0])).

cnf(c_403,plain,
    ( r1_tarski(k5_xboole_0(X0,k5_xboole_0(X1,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_289])).

cnf(c_8494,plain,
    ( r1_tarski(k5_xboole_0(sK1,k5_xboole_0(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))),sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_17,c_403])).

cnf(c_8,plain,
    ( r1_tarski(X0,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_402,plain,
    ( r1_tarski(X0,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_7481,plain,
    ( r1_tarski(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_17,c_402])).

cnf(c_13,plain,
    ( ~ r1_tarski(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))
    | k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) = X0
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f74])).

cnf(c_399,plain,
    ( k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) = X1
    | k1_xboole_0 = X1
    | r1_tarski(X1,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_8251,plain,
    ( k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) = sK1
    | sK1 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_7481,c_399])).

cnf(c_8253,plain,
    ( k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) = X0
    | sK1 = k1_xboole_0
    | k1_xboole_0 = X0
    | r1_tarski(X0,sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_8251,c_399])).

cnf(c_10771,plain,
    ( k5_xboole_0(sK1,k5_xboole_0(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))) = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)
    | k5_xboole_0(sK1,k5_xboole_0(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))) = k1_xboole_0
    | sK1 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_8494,c_8253])).

cnf(c_14,negated_conjecture,
    ( k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) != sK1
    | k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f75])).

cnf(c_8259,plain,
    ( sK1 = k1_xboole_0
    | sK2 != k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_8251,c_14])).

cnf(c_16,negated_conjecture,
    ( k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) != sK1
    | k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) != sK2 ),
    inference(cnf_transformation,[],[f77])).

cnf(c_8257,plain,
    ( k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) != sK2
    | sK1 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_8251,c_16])).

cnf(c_15,negated_conjecture,
    ( k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) != sK2
    | k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f76])).

cnf(c_425,plain,
    ( ~ r1_tarski(sK1,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))
    | k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) = sK1
    | k1_xboole_0 = sK1 ),
    inference(instantiation,[status(thm)],[c_13])).

cnf(c_430,plain,
    ( ~ r1_tarski(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))
    | k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) = sK1
    | k1_xboole_0 = sK1 ),
    inference(instantiation,[status(thm)],[c_425])).

cnf(c_292,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_502,plain,
    ( sK1 = sK1 ),
    inference(instantiation,[status(thm)],[c_292])).

cnf(c_297,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_460,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(sK1,k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2))
    | k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2) != X1
    | sK1 != X0 ),
    inference(instantiation,[status(thm)],[c_297])).

cnf(c_494,plain,
    ( ~ r1_tarski(sK1,X0)
    | r1_tarski(sK1,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))
    | k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) != X0
    | sK1 != sK1 ),
    inference(instantiation,[status(thm)],[c_460])).

cnf(c_563,plain,
    ( r1_tarski(sK1,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))
    | ~ r1_tarski(sK1,k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,X1)))
    | k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) != k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,X1))
    | sK1 != sK1 ),
    inference(instantiation,[status(thm)],[c_494])).

cnf(c_1737,plain,
    ( r1_tarski(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))
    | ~ r1_tarski(sK1,k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)))
    | k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) != k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2))
    | sK1 != sK1 ),
    inference(instantiation,[status(thm)],[c_563])).

cnf(c_653,plain,
    ( r1_tarski(sK1,k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,X0))) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_2078,plain,
    ( r1_tarski(sK1,k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2))) ),
    inference(instantiation,[status(thm)],[c_653])).

cnf(c_8351,plain,
    ( k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) != sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_8257,c_17,c_16,c_15,c_430,c_502,c_1737,c_2078])).

cnf(c_10605,plain,
    ( sK1 = k1_xboole_0
    | r1_tarski(k5_xboole_0(sK1,k5_xboole_0(sK2,sK1)),sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_8251,c_8494])).

cnf(c_10,plain,
    ( k5_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f43])).

cnf(c_411,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(X1,k5_xboole_0(X0,X2)) ),
    inference(superposition,[status(thm)],[c_9,c_0])).

cnf(c_775,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,X0)) = k5_xboole_0(X1,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_10,c_411])).

cnf(c_4,plain,
    ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f37])).

cnf(c_792,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,X0)) = X1 ),
    inference(demodulation,[status(thm)],[c_775,c_4])).

cnf(c_10606,plain,
    ( sK1 = k1_xboole_0
    | r1_tarski(sK2,sK1) = iProver_top ),
    inference(demodulation,[status(thm)],[c_10605,c_792])).

cnf(c_10774,plain,
    ( k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) = sK2
    | sK1 = k1_xboole_0
    | sK2 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_10606,c_8253])).

cnf(c_10868,plain,
    ( sK1 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_10771,c_17,c_16,c_15,c_430,c_502,c_1737,c_2078,c_8259,c_10774])).

cnf(c_10873,plain,
    ( r1_tarski(k5_xboole_0(k1_xboole_0,k5_xboole_0(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))),k1_xboole_0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_10868,c_8494])).

cnf(c_412,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(X2,k5_xboole_0(X1,X0)) ),
    inference(superposition,[status(thm)],[c_9,c_0])).

cnf(c_1099,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(X0,X1)) = k5_xboole_0(X1,X0) ),
    inference(superposition,[status(thm)],[c_4,c_412])).

cnf(c_10880,plain,
    ( r1_tarski(k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK2),k1_xboole_0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_10873,c_1099])).

cnf(c_6,plain,
    ( r1_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_7,plain,
    ( ~ r1_xboole_0(X0,X1)
    | ~ r1_tarski(X2,X1)
    | ~ r1_tarski(X2,X0)
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f40])).

cnf(c_113,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X0,X2)
    | k1_xboole_0 != X2
    | k1_xboole_0 != X1
    | k1_xboole_0 = X0 ),
    inference(resolution_lifted,[status(thm)],[c_6,c_7])).

cnf(c_114,plain,
    ( ~ r1_tarski(X0,k1_xboole_0)
    | k1_xboole_0 = X0 ),
    inference(unflattening,[status(thm)],[c_113])).

cnf(c_398,plain,
    ( k1_xboole_0 = X0
    | r1_tarski(X0,k1_xboole_0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_114])).

cnf(c_14013,plain,
    ( k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK2) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_10880,c_398])).

cnf(c_632,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X0,X1)) = k5_xboole_0(k1_xboole_0,X1) ),
    inference(superposition,[status(thm)],[c_10,c_9])).

cnf(c_603,plain,
    ( k5_xboole_0(k1_xboole_0,X0) = X0 ),
    inference(superposition,[status(thm)],[c_4,c_0])).

cnf(c_639,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1 ),
    inference(demodulation,[status(thm)],[c_632,c_603])).

cnf(c_804,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X0,k5_xboole_0(X1,X2))) = X2 ),
    inference(superposition,[status(thm)],[c_9,c_639])).

cnf(c_1543,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,X2)),k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,X3)))) = X3 ),
    inference(superposition,[status(thm)],[c_9,c_804])).

cnf(c_14196,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))),k5_xboole_0(X0,k5_xboole_0(X1,k1_xboole_0))) = sK2 ),
    inference(superposition,[status(thm)],[c_14013,c_1543])).

cnf(c_949,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),X0) = X1 ),
    inference(superposition,[status(thm)],[c_792,c_792])).

cnf(c_1054,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,X2)),k5_xboole_0(X0,X1)) = X2 ),
    inference(superposition,[status(thm)],[c_9,c_949])).

cnf(c_945,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),X1) = X0 ),
    inference(superposition,[status(thm)],[c_639,c_792])).

cnf(c_980,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X1,X2)) = k5_xboole_0(X0,X2) ),
    inference(superposition,[status(thm)],[c_945,c_9])).

cnf(c_2837,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,X2)),k5_xboole_0(X0,k5_xboole_0(X1,X3))) = k5_xboole_0(X3,X2) ),
    inference(superposition,[status(thm)],[c_980,c_1054])).

cnf(c_14197,plain,
    ( k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) = sK2 ),
    inference(demodulation,[status(thm)],[c_14196,c_4,c_1054,c_2837])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_14197,c_8351])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.00/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n024.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 09:59:51 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 3.82/0.97  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.82/0.97  
% 3.82/0.97  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.82/0.97  
% 3.82/0.97  ------  iProver source info
% 3.82/0.97  
% 3.82/0.97  git: date: 2020-06-30 10:37:57 +0100
% 3.82/0.97  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.82/0.97  git: non_committed_changes: false
% 3.82/0.97  git: last_make_outside_of_git: false
% 3.82/0.97  
% 3.82/0.97  ------ 
% 3.82/0.97  
% 3.82/0.97  ------ Input Options
% 3.82/0.97  
% 3.82/0.97  --out_options                           all
% 3.82/0.97  --tptp_safe_out                         true
% 3.82/0.97  --problem_path                          ""
% 3.82/0.97  --include_path                          ""
% 3.82/0.97  --clausifier                            res/vclausify_rel
% 3.82/0.97  --clausifier_options                    ""
% 3.82/0.97  --stdin                                 false
% 3.82/0.97  --stats_out                             all
% 3.82/0.97  
% 3.82/0.97  ------ General Options
% 3.82/0.97  
% 3.82/0.97  --fof                                   false
% 3.82/0.97  --time_out_real                         305.
% 3.82/0.97  --time_out_virtual                      -1.
% 3.82/0.97  --symbol_type_check                     false
% 3.82/0.97  --clausify_out                          false
% 3.82/0.97  --sig_cnt_out                           false
% 3.82/0.97  --trig_cnt_out                          false
% 3.82/0.97  --trig_cnt_out_tolerance                1.
% 3.82/0.97  --trig_cnt_out_sk_spl                   false
% 3.82/0.97  --abstr_cl_out                          false
% 3.82/0.97  
% 3.82/0.97  ------ Global Options
% 3.82/0.97  
% 3.82/0.97  --schedule                              default
% 3.82/0.97  --add_important_lit                     false
% 3.82/0.97  --prop_solver_per_cl                    1000
% 3.82/0.97  --min_unsat_core                        false
% 3.82/0.97  --soft_assumptions                      false
% 3.82/0.97  --soft_lemma_size                       3
% 3.82/0.97  --prop_impl_unit_size                   0
% 3.82/0.97  --prop_impl_unit                        []
% 3.82/0.97  --share_sel_clauses                     true
% 3.82/0.97  --reset_solvers                         false
% 3.82/0.97  --bc_imp_inh                            [conj_cone]
% 3.82/0.97  --conj_cone_tolerance                   3.
% 3.82/0.97  --extra_neg_conj                        none
% 3.82/0.97  --large_theory_mode                     true
% 3.82/0.97  --prolific_symb_bound                   200
% 3.82/0.97  --lt_threshold                          2000
% 3.82/0.97  --clause_weak_htbl                      true
% 3.82/0.97  --gc_record_bc_elim                     false
% 3.82/0.97  
% 3.82/0.97  ------ Preprocessing Options
% 3.82/0.97  
% 3.82/0.97  --preprocessing_flag                    true
% 3.82/0.97  --time_out_prep_mult                    0.1
% 3.82/0.97  --splitting_mode                        input
% 3.82/0.97  --splitting_grd                         true
% 3.82/0.97  --splitting_cvd                         false
% 3.82/0.97  --splitting_cvd_svl                     false
% 3.82/0.97  --splitting_nvd                         32
% 3.82/0.97  --sub_typing                            true
% 3.82/0.97  --prep_gs_sim                           true
% 3.82/0.97  --prep_unflatten                        true
% 3.82/0.97  --prep_res_sim                          true
% 3.82/0.97  --prep_upred                            true
% 3.82/0.97  --prep_sem_filter                       exhaustive
% 3.82/0.97  --prep_sem_filter_out                   false
% 3.82/0.97  --pred_elim                             true
% 3.82/0.97  --res_sim_input                         true
% 3.82/0.97  --eq_ax_congr_red                       true
% 3.82/0.97  --pure_diseq_elim                       true
% 3.82/0.97  --brand_transform                       false
% 3.82/0.97  --non_eq_to_eq                          false
% 3.82/0.97  --prep_def_merge                        true
% 3.82/0.97  --prep_def_merge_prop_impl              false
% 3.82/0.97  --prep_def_merge_mbd                    true
% 3.82/0.97  --prep_def_merge_tr_red                 false
% 3.82/0.97  --prep_def_merge_tr_cl                  false
% 3.82/0.97  --smt_preprocessing                     true
% 3.82/0.97  --smt_ac_axioms                         fast
% 3.82/0.97  --preprocessed_out                      false
% 3.82/0.97  --preprocessed_stats                    false
% 3.82/0.97  
% 3.82/0.97  ------ Abstraction refinement Options
% 3.82/0.97  
% 3.82/0.97  --abstr_ref                             []
% 3.82/0.97  --abstr_ref_prep                        false
% 3.82/0.97  --abstr_ref_until_sat                   false
% 3.82/0.97  --abstr_ref_sig_restrict                funpre
% 3.82/0.97  --abstr_ref_af_restrict_to_split_sk     false
% 3.82/0.97  --abstr_ref_under                       []
% 3.82/0.97  
% 3.82/0.97  ------ SAT Options
% 3.82/0.97  
% 3.82/0.97  --sat_mode                              false
% 3.82/0.97  --sat_fm_restart_options                ""
% 3.82/0.97  --sat_gr_def                            false
% 3.82/0.97  --sat_epr_types                         true
% 3.82/0.97  --sat_non_cyclic_types                  false
% 3.82/0.97  --sat_finite_models                     false
% 3.82/0.97  --sat_fm_lemmas                         false
% 3.82/0.97  --sat_fm_prep                           false
% 3.82/0.97  --sat_fm_uc_incr                        true
% 3.82/0.97  --sat_out_model                         small
% 3.82/0.97  --sat_out_clauses                       false
% 3.82/0.97  
% 3.82/0.97  ------ QBF Options
% 3.82/0.97  
% 3.82/0.97  --qbf_mode                              false
% 3.82/0.97  --qbf_elim_univ                         false
% 3.82/0.97  --qbf_dom_inst                          none
% 3.82/0.97  --qbf_dom_pre_inst                      false
% 3.82/0.97  --qbf_sk_in                             false
% 3.82/0.97  --qbf_pred_elim                         true
% 3.82/0.97  --qbf_split                             512
% 3.82/0.97  
% 3.82/0.97  ------ BMC1 Options
% 3.82/0.97  
% 3.82/0.97  --bmc1_incremental                      false
% 3.82/0.97  --bmc1_axioms                           reachable_all
% 3.82/0.97  --bmc1_min_bound                        0
% 3.82/0.97  --bmc1_max_bound                        -1
% 3.82/0.97  --bmc1_max_bound_default                -1
% 3.82/0.97  --bmc1_symbol_reachability              true
% 3.82/0.97  --bmc1_property_lemmas                  false
% 3.82/0.97  --bmc1_k_induction                      false
% 3.82/0.97  --bmc1_non_equiv_states                 false
% 3.82/0.97  --bmc1_deadlock                         false
% 3.82/0.97  --bmc1_ucm                              false
% 3.82/0.97  --bmc1_add_unsat_core                   none
% 3.82/0.97  --bmc1_unsat_core_children              false
% 3.82/0.97  --bmc1_unsat_core_extrapolate_axioms    false
% 3.82/0.97  --bmc1_out_stat                         full
% 3.82/0.97  --bmc1_ground_init                      false
% 3.82/0.97  --bmc1_pre_inst_next_state              false
% 3.82/0.97  --bmc1_pre_inst_state                   false
% 3.82/0.97  --bmc1_pre_inst_reach_state             false
% 3.82/0.97  --bmc1_out_unsat_core                   false
% 3.82/0.97  --bmc1_aig_witness_out                  false
% 3.82/0.97  --bmc1_verbose                          false
% 3.82/0.97  --bmc1_dump_clauses_tptp                false
% 3.82/0.97  --bmc1_dump_unsat_core_tptp             false
% 3.82/0.97  --bmc1_dump_file                        -
% 3.82/0.97  --bmc1_ucm_expand_uc_limit              128
% 3.82/0.97  --bmc1_ucm_n_expand_iterations          6
% 3.82/0.97  --bmc1_ucm_extend_mode                  1
% 3.82/0.97  --bmc1_ucm_init_mode                    2
% 3.82/0.97  --bmc1_ucm_cone_mode                    none
% 3.82/0.97  --bmc1_ucm_reduced_relation_type        0
% 3.82/0.97  --bmc1_ucm_relax_model                  4
% 3.82/0.97  --bmc1_ucm_full_tr_after_sat            true
% 3.82/0.97  --bmc1_ucm_expand_neg_assumptions       false
% 3.82/0.97  --bmc1_ucm_layered_model                none
% 3.82/0.97  --bmc1_ucm_max_lemma_size               10
% 3.82/0.97  
% 3.82/0.97  ------ AIG Options
% 3.82/0.97  
% 3.82/0.97  --aig_mode                              false
% 3.82/0.97  
% 3.82/0.97  ------ Instantiation Options
% 3.82/0.97  
% 3.82/0.97  --instantiation_flag                    true
% 3.82/0.97  --inst_sos_flag                         true
% 3.82/0.97  --inst_sos_phase                        true
% 3.82/0.97  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.82/0.97  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.82/0.97  --inst_lit_sel_side                     num_symb
% 3.82/0.97  --inst_solver_per_active                1400
% 3.82/0.97  --inst_solver_calls_frac                1.
% 3.82/0.97  --inst_passive_queue_type               priority_queues
% 3.82/0.97  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.82/0.97  --inst_passive_queues_freq              [25;2]
% 3.82/0.97  --inst_dismatching                      true
% 3.82/0.97  --inst_eager_unprocessed_to_passive     true
% 3.82/0.97  --inst_prop_sim_given                   true
% 3.82/0.97  --inst_prop_sim_new                     false
% 3.82/0.97  --inst_subs_new                         false
% 3.82/0.97  --inst_eq_res_simp                      false
% 3.82/0.97  --inst_subs_given                       false
% 3.82/0.97  --inst_orphan_elimination               true
% 3.82/0.97  --inst_learning_loop_flag               true
% 3.82/0.97  --inst_learning_start                   3000
% 3.82/0.97  --inst_learning_factor                  2
% 3.82/0.97  --inst_start_prop_sim_after_learn       3
% 3.82/0.97  --inst_sel_renew                        solver
% 3.82/0.97  --inst_lit_activity_flag                true
% 3.82/0.97  --inst_restr_to_given                   false
% 3.82/0.97  --inst_activity_threshold               500
% 3.82/0.97  --inst_out_proof                        true
% 3.82/0.97  
% 3.82/0.97  ------ Resolution Options
% 3.82/0.97  
% 3.82/0.97  --resolution_flag                       true
% 3.82/0.97  --res_lit_sel                           adaptive
% 3.82/0.97  --res_lit_sel_side                      none
% 3.82/0.97  --res_ordering                          kbo
% 3.82/0.97  --res_to_prop_solver                    active
% 3.82/0.97  --res_prop_simpl_new                    false
% 3.82/0.97  --res_prop_simpl_given                  true
% 3.82/0.97  --res_passive_queue_type                priority_queues
% 3.82/0.97  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.82/0.97  --res_passive_queues_freq               [15;5]
% 3.82/0.97  --res_forward_subs                      full
% 3.82/0.97  --res_backward_subs                     full
% 3.82/0.97  --res_forward_subs_resolution           true
% 3.82/0.97  --res_backward_subs_resolution          true
% 3.82/0.97  --res_orphan_elimination                true
% 3.82/0.97  --res_time_limit                        2.
% 3.82/0.97  --res_out_proof                         true
% 3.82/0.97  
% 3.82/0.97  ------ Superposition Options
% 3.82/0.97  
% 3.82/0.97  --superposition_flag                    true
% 3.82/0.97  --sup_passive_queue_type                priority_queues
% 3.82/0.97  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.82/0.97  --sup_passive_queues_freq               [8;1;4]
% 3.82/0.97  --demod_completeness_check              fast
% 3.82/0.97  --demod_use_ground                      true
% 3.82/0.97  --sup_to_prop_solver                    passive
% 3.82/0.97  --sup_prop_simpl_new                    true
% 3.82/0.97  --sup_prop_simpl_given                  true
% 3.82/0.97  --sup_fun_splitting                     true
% 3.82/0.97  --sup_smt_interval                      50000
% 3.82/0.97  
% 3.82/0.97  ------ Superposition Simplification Setup
% 3.82/0.97  
% 3.82/0.97  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 3.82/0.97  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 3.82/0.97  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 3.82/0.97  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 3.82/0.97  --sup_full_triv                         [TrivRules;PropSubs]
% 3.82/0.97  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 3.82/0.97  --sup_full_bw                           [BwDemod;BwSubsumption]
% 3.82/0.97  --sup_immed_triv                        [TrivRules]
% 3.82/0.97  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.82/0.97  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.82/0.97  --sup_immed_bw_main                     []
% 3.82/0.97  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 3.82/0.97  --sup_input_triv                        [Unflattening;TrivRules]
% 3.82/0.97  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.82/0.97  --sup_input_bw                          []
% 3.82/0.97  
% 3.82/0.97  ------ Combination Options
% 3.82/0.97  
% 3.82/0.97  --comb_res_mult                         3
% 3.82/0.97  --comb_sup_mult                         2
% 3.82/0.97  --comb_inst_mult                        10
% 3.82/0.97  
% 3.82/0.97  ------ Debug Options
% 3.82/0.97  
% 3.82/0.97  --dbg_backtrace                         false
% 3.82/0.97  --dbg_dump_prop_clauses                 false
% 3.82/0.97  --dbg_dump_prop_clauses_file            -
% 3.82/0.97  --dbg_out_stat                          false
% 3.82/0.97  ------ Parsing...
% 3.82/0.97  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.82/0.97  
% 3.82/0.97  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 3.82/0.97  
% 3.82/0.97  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.82/0.97  
% 3.82/0.97  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.82/0.97  ------ Proving...
% 3.82/0.97  ------ Problem Properties 
% 3.82/0.97  
% 3.82/0.97  
% 3.82/0.97  clauses                                 16
% 3.82/0.97  conjectures                             4
% 3.82/0.97  EPR                                     1
% 3.82/0.97  Horn                                    15
% 3.82/0.97  unary                                   11
% 3.82/0.97  binary                                  4
% 3.82/0.97  lits                                    22
% 3.82/0.97  lits eq                                 16
% 3.82/0.97  fd_pure                                 0
% 3.82/0.97  fd_pseudo                               0
% 3.82/0.97  fd_cond                                 1
% 3.82/0.97  fd_pseudo_cond                          1
% 3.82/0.97  AC symbols                              1
% 3.82/0.97  
% 3.82/0.97  ------ Schedule dynamic 5 is on 
% 3.82/0.97  
% 3.82/0.97  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.82/0.97  
% 3.82/0.97  
% 3.82/0.97  ------ 
% 3.82/0.97  Current options:
% 3.82/0.97  ------ 
% 3.82/0.97  
% 3.82/0.97  ------ Input Options
% 3.82/0.97  
% 3.82/0.97  --out_options                           all
% 3.82/0.97  --tptp_safe_out                         true
% 3.82/0.97  --problem_path                          ""
% 3.82/0.97  --include_path                          ""
% 3.82/0.97  --clausifier                            res/vclausify_rel
% 3.82/0.97  --clausifier_options                    ""
% 3.82/0.97  --stdin                                 false
% 3.82/0.97  --stats_out                             all
% 3.82/0.97  
% 3.82/0.97  ------ General Options
% 3.82/0.97  
% 3.82/0.97  --fof                                   false
% 3.82/0.97  --time_out_real                         305.
% 3.82/0.97  --time_out_virtual                      -1.
% 3.82/0.97  --symbol_type_check                     false
% 3.82/0.97  --clausify_out                          false
% 3.82/0.97  --sig_cnt_out                           false
% 3.82/0.97  --trig_cnt_out                          false
% 3.82/0.97  --trig_cnt_out_tolerance                1.
% 3.82/0.97  --trig_cnt_out_sk_spl                   false
% 3.82/0.97  --abstr_cl_out                          false
% 3.82/0.97  
% 3.82/0.97  ------ Global Options
% 3.82/0.97  
% 3.82/0.97  --schedule                              default
% 3.82/0.97  --add_important_lit                     false
% 3.82/0.97  --prop_solver_per_cl                    1000
% 3.82/0.97  --min_unsat_core                        false
% 3.82/0.97  --soft_assumptions                      false
% 3.82/0.97  --soft_lemma_size                       3
% 3.82/0.97  --prop_impl_unit_size                   0
% 3.82/0.97  --prop_impl_unit                        []
% 3.82/0.97  --share_sel_clauses                     true
% 3.82/0.97  --reset_solvers                         false
% 3.82/0.97  --bc_imp_inh                            [conj_cone]
% 3.82/0.97  --conj_cone_tolerance                   3.
% 3.82/0.97  --extra_neg_conj                        none
% 3.82/0.97  --large_theory_mode                     true
% 3.82/0.97  --prolific_symb_bound                   200
% 3.82/0.97  --lt_threshold                          2000
% 3.82/0.97  --clause_weak_htbl                      true
% 3.82/0.97  --gc_record_bc_elim                     false
% 3.82/0.97  
% 3.82/0.97  ------ Preprocessing Options
% 3.82/0.97  
% 3.82/0.97  --preprocessing_flag                    true
% 3.82/0.97  --time_out_prep_mult                    0.1
% 3.82/0.97  --splitting_mode                        input
% 3.82/0.97  --splitting_grd                         true
% 3.82/0.97  --splitting_cvd                         false
% 3.82/0.97  --splitting_cvd_svl                     false
% 3.82/0.97  --splitting_nvd                         32
% 3.82/0.97  --sub_typing                            true
% 3.82/0.97  --prep_gs_sim                           true
% 3.82/0.97  --prep_unflatten                        true
% 3.82/0.97  --prep_res_sim                          true
% 3.82/0.97  --prep_upred                            true
% 3.82/0.97  --prep_sem_filter                       exhaustive
% 3.82/0.97  --prep_sem_filter_out                   false
% 3.82/0.97  --pred_elim                             true
% 3.82/0.97  --res_sim_input                         true
% 3.82/0.97  --eq_ax_congr_red                       true
% 3.82/0.97  --pure_diseq_elim                       true
% 3.82/0.97  --brand_transform                       false
% 3.82/0.97  --non_eq_to_eq                          false
% 3.82/0.97  --prep_def_merge                        true
% 3.82/0.97  --prep_def_merge_prop_impl              false
% 3.82/0.97  --prep_def_merge_mbd                    true
% 3.82/0.97  --prep_def_merge_tr_red                 false
% 3.82/0.97  --prep_def_merge_tr_cl                  false
% 3.82/0.97  --smt_preprocessing                     true
% 3.82/0.97  --smt_ac_axioms                         fast
% 3.82/0.97  --preprocessed_out                      false
% 3.82/0.97  --preprocessed_stats                    false
% 3.82/0.97  
% 3.82/0.97  ------ Abstraction refinement Options
% 3.82/0.97  
% 3.82/0.97  --abstr_ref                             []
% 3.82/0.97  --abstr_ref_prep                        false
% 3.82/0.97  --abstr_ref_until_sat                   false
% 3.82/0.97  --abstr_ref_sig_restrict                funpre
% 3.82/0.97  --abstr_ref_af_restrict_to_split_sk     false
% 3.82/0.97  --abstr_ref_under                       []
% 3.82/0.97  
% 3.82/0.97  ------ SAT Options
% 3.82/0.97  
% 3.82/0.97  --sat_mode                              false
% 3.82/0.97  --sat_fm_restart_options                ""
% 3.82/0.97  --sat_gr_def                            false
% 3.82/0.97  --sat_epr_types                         true
% 3.82/0.97  --sat_non_cyclic_types                  false
% 3.82/0.97  --sat_finite_models                     false
% 3.82/0.97  --sat_fm_lemmas                         false
% 3.82/0.97  --sat_fm_prep                           false
% 3.82/0.97  --sat_fm_uc_incr                        true
% 3.82/0.97  --sat_out_model                         small
% 3.82/0.97  --sat_out_clauses                       false
% 3.82/0.97  
% 3.82/0.97  ------ QBF Options
% 3.82/0.97  
% 3.82/0.97  --qbf_mode                              false
% 3.82/0.97  --qbf_elim_univ                         false
% 3.82/0.97  --qbf_dom_inst                          none
% 3.82/0.97  --qbf_dom_pre_inst                      false
% 3.82/0.97  --qbf_sk_in                             false
% 3.82/0.97  --qbf_pred_elim                         true
% 3.82/0.97  --qbf_split                             512
% 3.82/0.97  
% 3.82/0.97  ------ BMC1 Options
% 3.82/0.97  
% 3.82/0.97  --bmc1_incremental                      false
% 3.82/0.97  --bmc1_axioms                           reachable_all
% 3.82/0.97  --bmc1_min_bound                        0
% 3.82/0.97  --bmc1_max_bound                        -1
% 3.82/0.97  --bmc1_max_bound_default                -1
% 3.82/0.97  --bmc1_symbol_reachability              true
% 3.82/0.97  --bmc1_property_lemmas                  false
% 3.82/0.97  --bmc1_k_induction                      false
% 3.82/0.97  --bmc1_non_equiv_states                 false
% 3.82/0.97  --bmc1_deadlock                         false
% 3.82/0.97  --bmc1_ucm                              false
% 3.82/0.97  --bmc1_add_unsat_core                   none
% 3.82/0.97  --bmc1_unsat_core_children              false
% 3.82/0.97  --bmc1_unsat_core_extrapolate_axioms    false
% 3.82/0.97  --bmc1_out_stat                         full
% 3.82/0.97  --bmc1_ground_init                      false
% 3.82/0.97  --bmc1_pre_inst_next_state              false
% 3.82/0.97  --bmc1_pre_inst_state                   false
% 3.82/0.97  --bmc1_pre_inst_reach_state             false
% 3.82/0.97  --bmc1_out_unsat_core                   false
% 3.82/0.97  --bmc1_aig_witness_out                  false
% 3.82/0.97  --bmc1_verbose                          false
% 3.82/0.97  --bmc1_dump_clauses_tptp                false
% 3.82/0.97  --bmc1_dump_unsat_core_tptp             false
% 3.82/0.97  --bmc1_dump_file                        -
% 3.82/0.97  --bmc1_ucm_expand_uc_limit              128
% 3.82/0.97  --bmc1_ucm_n_expand_iterations          6
% 3.82/0.97  --bmc1_ucm_extend_mode                  1
% 3.82/0.97  --bmc1_ucm_init_mode                    2
% 3.82/0.97  --bmc1_ucm_cone_mode                    none
% 3.82/0.97  --bmc1_ucm_reduced_relation_type        0
% 3.82/0.97  --bmc1_ucm_relax_model                  4
% 3.82/0.97  --bmc1_ucm_full_tr_after_sat            true
% 3.82/0.97  --bmc1_ucm_expand_neg_assumptions       false
% 3.82/0.97  --bmc1_ucm_layered_model                none
% 3.82/0.97  --bmc1_ucm_max_lemma_size               10
% 3.82/0.97  
% 3.82/0.97  ------ AIG Options
% 3.82/0.97  
% 3.82/0.97  --aig_mode                              false
% 3.82/0.97  
% 3.82/0.97  ------ Instantiation Options
% 3.82/0.97  
% 3.82/0.97  --instantiation_flag                    true
% 3.82/0.97  --inst_sos_flag                         true
% 3.82/0.97  --inst_sos_phase                        true
% 3.82/0.97  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.82/0.97  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.82/0.97  --inst_lit_sel_side                     none
% 3.82/0.97  --inst_solver_per_active                1400
% 3.82/0.97  --inst_solver_calls_frac                1.
% 3.82/0.97  --inst_passive_queue_type               priority_queues
% 3.82/0.97  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.82/0.97  --inst_passive_queues_freq              [25;2]
% 3.82/0.97  --inst_dismatching                      true
% 3.82/0.97  --inst_eager_unprocessed_to_passive     true
% 3.82/0.97  --inst_prop_sim_given                   true
% 3.82/0.97  --inst_prop_sim_new                     false
% 3.82/0.97  --inst_subs_new                         false
% 3.82/0.97  --inst_eq_res_simp                      false
% 3.82/0.97  --inst_subs_given                       false
% 3.82/0.97  --inst_orphan_elimination               true
% 3.82/0.97  --inst_learning_loop_flag               true
% 3.82/0.97  --inst_learning_start                   3000
% 3.82/0.97  --inst_learning_factor                  2
% 3.82/0.97  --inst_start_prop_sim_after_learn       3
% 3.82/0.97  --inst_sel_renew                        solver
% 3.82/0.97  --inst_lit_activity_flag                true
% 3.82/0.97  --inst_restr_to_given                   false
% 3.82/0.97  --inst_activity_threshold               500
% 3.82/0.97  --inst_out_proof                        true
% 3.82/0.97  
% 3.82/0.97  ------ Resolution Options
% 3.82/0.97  
% 3.82/0.97  --resolution_flag                       false
% 3.82/0.97  --res_lit_sel                           adaptive
% 3.82/0.97  --res_lit_sel_side                      none
% 3.82/0.97  --res_ordering                          kbo
% 3.82/0.97  --res_to_prop_solver                    active
% 3.82/0.97  --res_prop_simpl_new                    false
% 3.82/0.97  --res_prop_simpl_given                  true
% 3.82/0.97  --res_passive_queue_type                priority_queues
% 3.82/0.97  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.82/0.97  --res_passive_queues_freq               [15;5]
% 3.82/0.97  --res_forward_subs                      full
% 3.82/0.97  --res_backward_subs                     full
% 3.82/0.97  --res_forward_subs_resolution           true
% 3.82/0.97  --res_backward_subs_resolution          true
% 3.82/0.97  --res_orphan_elimination                true
% 3.82/0.97  --res_time_limit                        2.
% 3.82/0.97  --res_out_proof                         true
% 3.82/0.97  
% 3.82/0.97  ------ Superposition Options
% 3.82/0.97  
% 3.82/0.97  --superposition_flag                    true
% 3.82/0.97  --sup_passive_queue_type                priority_queues
% 3.82/0.97  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.82/0.97  --sup_passive_queues_freq               [8;1;4]
% 3.82/0.97  --demod_completeness_check              fast
% 3.82/0.97  --demod_use_ground                      true
% 3.82/0.97  --sup_to_prop_solver                    passive
% 3.82/0.97  --sup_prop_simpl_new                    true
% 3.82/0.97  --sup_prop_simpl_given                  true
% 3.82/0.97  --sup_fun_splitting                     true
% 3.82/0.97  --sup_smt_interval                      50000
% 3.82/0.97  
% 3.82/0.97  ------ Superposition Simplification Setup
% 3.82/0.97  
% 3.82/0.97  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 3.82/0.97  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 3.82/0.97  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 3.82/0.97  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 3.82/0.97  --sup_full_triv                         [TrivRules;PropSubs]
% 3.82/0.97  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 3.82/0.97  --sup_full_bw                           [BwDemod;BwSubsumption]
% 3.82/0.97  --sup_immed_triv                        [TrivRules]
% 3.82/0.97  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.82/0.97  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.82/0.97  --sup_immed_bw_main                     []
% 3.82/0.97  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 3.82/0.97  --sup_input_triv                        [Unflattening;TrivRules]
% 3.82/0.97  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.82/0.97  --sup_input_bw                          []
% 3.82/0.97  
% 3.82/0.97  ------ Combination Options
% 3.82/0.97  
% 3.82/0.97  --comb_res_mult                         3
% 3.82/0.97  --comb_sup_mult                         2
% 3.82/0.97  --comb_inst_mult                        10
% 3.82/0.97  
% 3.82/0.97  ------ Debug Options
% 3.82/0.97  
% 3.82/0.97  --dbg_backtrace                         false
% 3.82/0.97  --dbg_dump_prop_clauses                 false
% 3.82/0.97  --dbg_dump_prop_clauses_file            -
% 3.82/0.97  --dbg_out_stat                          false
% 3.82/0.97  
% 3.82/0.97  
% 3.82/0.97  
% 3.82/0.97  
% 3.82/0.97  ------ Proving...
% 3.82/0.97  
% 3.82/0.97  
% 3.82/0.97  % SZS status Theorem for theBenchmark.p
% 3.82/0.97  
% 3.82/0.97  % SZS output start CNFRefutation for theBenchmark.p
% 3.82/0.97  
% 3.82/0.97  fof(f21,conjecture,(
% 3.82/0.97    ! [X0,X1,X2] : ~(~(k1_xboole_0 = X2 & k1_tarski(X0) = X1) & ~(k1_tarski(X0) = X2 & k1_xboole_0 = X1) & ~(k1_tarski(X0) = X2 & k1_tarski(X0) = X1) & k2_xboole_0(X1,X2) = k1_tarski(X0))),
% 3.82/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.82/0.97  
% 3.82/0.97  fof(f22,negated_conjecture,(
% 3.82/0.97    ~! [X0,X1,X2] : ~(~(k1_xboole_0 = X2 & k1_tarski(X0) = X1) & ~(k1_tarski(X0) = X2 & k1_xboole_0 = X1) & ~(k1_tarski(X0) = X2 & k1_tarski(X0) = X1) & k2_xboole_0(X1,X2) = k1_tarski(X0))),
% 3.82/0.97    inference(negated_conjecture,[],[f21])).
% 3.82/0.97  
% 3.82/0.97  fof(f28,plain,(
% 3.82/0.97    ? [X0,X1,X2] : ((k1_xboole_0 != X2 | k1_tarski(X0) != X1) & (k1_tarski(X0) != X2 | k1_xboole_0 != X1) & (k1_tarski(X0) != X2 | k1_tarski(X0) != X1) & k2_xboole_0(X1,X2) = k1_tarski(X0))),
% 3.82/0.97    inference(ennf_transformation,[],[f22])).
% 3.82/0.97  
% 3.82/0.97  fof(f31,plain,(
% 3.82/0.97    ? [X0,X1,X2] : ((k1_xboole_0 != X2 | k1_tarski(X0) != X1) & (k1_tarski(X0) != X2 | k1_xboole_0 != X1) & (k1_tarski(X0) != X2 | k1_tarski(X0) != X1) & k2_xboole_0(X1,X2) = k1_tarski(X0)) => ((k1_xboole_0 != sK2 | k1_tarski(sK0) != sK1) & (k1_tarski(sK0) != sK2 | k1_xboole_0 != sK1) & (k1_tarski(sK0) != sK2 | k1_tarski(sK0) != sK1) & k2_xboole_0(sK1,sK2) = k1_tarski(sK0))),
% 3.82/0.97    introduced(choice_axiom,[])).
% 3.82/0.97  
% 3.82/0.97  fof(f32,plain,(
% 3.82/0.97    (k1_xboole_0 != sK2 | k1_tarski(sK0) != sK1) & (k1_tarski(sK0) != sK2 | k1_xboole_0 != sK1) & (k1_tarski(sK0) != sK2 | k1_tarski(sK0) != sK1) & k2_xboole_0(sK1,sK2) = k1_tarski(sK0)),
% 3.82/0.97    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f28,f31])).
% 3.82/0.97  
% 3.82/0.97  fof(f56,plain,(
% 3.82/0.97    k2_xboole_0(sK1,sK2) = k1_tarski(sK0)),
% 3.82/0.97    inference(cnf_transformation,[],[f32])).
% 3.82/0.97  
% 3.82/0.97  fof(f20,axiom,(
% 3.82/0.97    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 3.82/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.82/0.97  
% 3.82/0.97  fof(f55,plain,(
% 3.82/0.97    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 3.82/0.97    inference(cnf_transformation,[],[f20])).
% 3.82/0.97  
% 3.82/0.97  fof(f65,plain,(
% 3.82/0.97    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) )),
% 3.82/0.97    inference(definition_unfolding,[],[f55,f64])).
% 3.82/0.97  
% 3.82/0.97  fof(f12,axiom,(
% 3.82/0.97    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 3.82/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.82/0.97  
% 3.82/0.97  fof(f45,plain,(
% 3.82/0.97    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 3.82/0.97    inference(cnf_transformation,[],[f12])).
% 3.82/0.97  
% 3.82/0.97  fof(f13,axiom,(
% 3.82/0.97    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 3.82/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.82/0.97  
% 3.82/0.97  fof(f46,plain,(
% 3.82/0.97    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 3.82/0.97    inference(cnf_transformation,[],[f13])).
% 3.82/0.97  
% 3.82/0.97  fof(f14,axiom,(
% 3.82/0.97    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 3.82/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.82/0.97  
% 3.82/0.97  fof(f47,plain,(
% 3.82/0.97    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 3.82/0.97    inference(cnf_transformation,[],[f14])).
% 3.82/0.97  
% 3.82/0.97  fof(f15,axiom,(
% 3.82/0.97    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 3.82/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.82/0.97  
% 3.82/0.97  fof(f48,plain,(
% 3.82/0.97    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 3.82/0.97    inference(cnf_transformation,[],[f15])).
% 3.82/0.97  
% 3.82/0.97  fof(f16,axiom,(
% 3.82/0.97    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)),
% 3.82/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.82/0.97  
% 3.82/0.97  fof(f49,plain,(
% 3.82/0.97    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)) )),
% 3.82/0.97    inference(cnf_transformation,[],[f16])).
% 3.82/0.97  
% 3.82/0.97  fof(f17,axiom,(
% 3.82/0.97    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)),
% 3.82/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.82/0.97  
% 3.82/0.97  fof(f50,plain,(
% 3.82/0.97    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)) )),
% 3.82/0.97    inference(cnf_transformation,[],[f17])).
% 3.82/0.97  
% 3.82/0.97  fof(f18,axiom,(
% 3.82/0.97    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)),
% 3.82/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.82/0.97  
% 3.82/0.97  fof(f51,plain,(
% 3.82/0.97    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)) )),
% 3.82/0.97    inference(cnf_transformation,[],[f18])).
% 3.82/0.97  
% 3.82/0.97  fof(f60,plain,(
% 3.82/0.97    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 3.82/0.97    inference(definition_unfolding,[],[f50,f51])).
% 3.82/0.97  
% 3.82/0.97  fof(f61,plain,(
% 3.82/0.97    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 3.82/0.97    inference(definition_unfolding,[],[f49,f60])).
% 3.82/0.97  
% 3.82/0.97  fof(f62,plain,(
% 3.82/0.97    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 3.82/0.97    inference(definition_unfolding,[],[f48,f61])).
% 3.82/0.97  
% 3.82/0.97  fof(f63,plain,(
% 3.82/0.97    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 3.82/0.97    inference(definition_unfolding,[],[f47,f62])).
% 3.82/0.97  
% 3.82/0.97  fof(f64,plain,(
% 3.82/0.97    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 3.82/0.97    inference(definition_unfolding,[],[f46,f63])).
% 3.82/0.97  
% 3.82/0.97  fof(f67,plain,(
% 3.82/0.97    ( ! [X0] : (k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) )),
% 3.82/0.97    inference(definition_unfolding,[],[f45,f64])).
% 3.82/0.97  
% 3.82/0.97  fof(f78,plain,(
% 3.82/0.97    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2))),
% 3.82/0.97    inference(definition_unfolding,[],[f56,f65,f67])).
% 3.82/0.97  
% 3.82/0.97  fof(f4,axiom,(
% 3.82/0.97    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 3.82/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.82/0.97  
% 3.82/0.97  fof(f36,plain,(
% 3.82/0.97    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 3.82/0.97    inference(cnf_transformation,[],[f4])).
% 3.82/0.97  
% 3.82/0.97  fof(f11,axiom,(
% 3.82/0.97    ! [X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)),
% 3.82/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.82/0.97  
% 3.82/0.97  fof(f44,plain,(
% 3.82/0.97    ( ! [X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)) )),
% 3.82/0.97    inference(cnf_transformation,[],[f11])).
% 3.82/0.97  
% 3.82/0.97  fof(f66,plain,(
% 3.82/0.97    ( ! [X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) = k3_xboole_0(X0,X1)) )),
% 3.82/0.97    inference(definition_unfolding,[],[f44,f65])).
% 3.82/0.97  
% 3.82/0.97  fof(f70,plain,(
% 3.82/0.97    ( ! [X0,X1] : (r1_tarski(k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))),X0)) )),
% 3.82/0.97    inference(definition_unfolding,[],[f36,f66])).
% 3.82/0.97  
% 3.82/0.97  fof(f9,axiom,(
% 3.82/0.97    ! [X0,X1,X2] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2)),
% 3.82/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.82/0.97  
% 3.82/0.97  fof(f42,plain,(
% 3.82/0.97    ( ! [X2,X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2)) )),
% 3.82/0.97    inference(cnf_transformation,[],[f9])).
% 3.82/0.97  
% 3.82/0.97  fof(f1,axiom,(
% 3.82/0.97    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)),
% 3.82/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.82/0.97  
% 3.82/0.97  fof(f33,plain,(
% 3.82/0.97    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)) )),
% 3.82/0.97    inference(cnf_transformation,[],[f1])).
% 3.82/0.97  
% 3.82/0.97  fof(f8,axiom,(
% 3.82/0.97    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 3.82/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.82/0.97  
% 3.82/0.97  fof(f41,plain,(
% 3.82/0.97    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 3.82/0.97    inference(cnf_transformation,[],[f8])).
% 3.82/0.97  
% 3.82/0.97  fof(f71,plain,(
% 3.82/0.97    ( ! [X0,X1] : (r1_tarski(X0,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) )),
% 3.82/0.97    inference(definition_unfolding,[],[f41,f65])).
% 3.82/0.97  
% 3.82/0.97  fof(f19,axiom,(
% 3.82/0.97    ! [X0,X1] : (r1_tarski(X0,k1_tarski(X1)) <=> (k1_tarski(X1) = X0 | k1_xboole_0 = X0))),
% 3.82/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.82/0.97  
% 3.82/0.97  fof(f29,plain,(
% 3.82/0.97    ! [X0,X1] : ((r1_tarski(X0,k1_tarski(X1)) | (k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & ((k1_tarski(X1) = X0 | k1_xboole_0 = X0) | ~r1_tarski(X0,k1_tarski(X1))))),
% 3.82/0.97    inference(nnf_transformation,[],[f19])).
% 3.82/0.97  
% 3.82/0.97  fof(f30,plain,(
% 3.82/0.97    ! [X0,X1] : ((r1_tarski(X0,k1_tarski(X1)) | (k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & (k1_tarski(X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k1_tarski(X1))))),
% 3.82/0.97    inference(flattening,[],[f29])).
% 3.82/0.97  
% 3.82/0.97  fof(f52,plain,(
% 3.82/0.97    ( ! [X0,X1] : (k1_tarski(X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k1_tarski(X1))) )),
% 3.82/0.97    inference(cnf_transformation,[],[f30])).
% 3.82/0.97  
% 3.82/0.97  fof(f74,plain,(
% 3.82/0.97    ( ! [X0,X1] : (k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))) )),
% 3.82/0.97    inference(definition_unfolding,[],[f52,f67,f67])).
% 3.82/0.97  
% 3.82/0.97  fof(f59,plain,(
% 3.82/0.97    k1_xboole_0 != sK2 | k1_tarski(sK0) != sK1),
% 3.82/0.97    inference(cnf_transformation,[],[f32])).
% 3.82/0.97  
% 3.82/0.97  fof(f75,plain,(
% 3.82/0.97    k1_xboole_0 != sK2 | k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) != sK1),
% 3.82/0.97    inference(definition_unfolding,[],[f59,f67])).
% 3.82/0.97  
% 3.82/0.97  fof(f57,plain,(
% 3.82/0.97    k1_tarski(sK0) != sK2 | k1_tarski(sK0) != sK1),
% 3.82/0.97    inference(cnf_transformation,[],[f32])).
% 3.82/0.97  
% 3.82/0.97  fof(f77,plain,(
% 3.82/0.97    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) != sK2 | k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) != sK1),
% 3.82/0.97    inference(definition_unfolding,[],[f57,f67,f67])).
% 3.82/0.97  
% 3.82/0.97  fof(f58,plain,(
% 3.82/0.97    k1_tarski(sK0) != sK2 | k1_xboole_0 != sK1),
% 3.82/0.97    inference(cnf_transformation,[],[f32])).
% 3.82/0.97  
% 3.82/0.97  fof(f76,plain,(
% 3.82/0.97    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) != sK2 | k1_xboole_0 != sK1),
% 3.82/0.97    inference(definition_unfolding,[],[f58,f67])).
% 3.82/0.97  
% 3.82/0.97  fof(f10,axiom,(
% 3.82/0.97    ! [X0] : k5_xboole_0(X0,X0) = k1_xboole_0),
% 3.82/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.82/0.97  
% 3.82/0.97  fof(f43,plain,(
% 3.82/0.97    ( ! [X0] : (k5_xboole_0(X0,X0) = k1_xboole_0) )),
% 3.82/0.97    inference(cnf_transformation,[],[f10])).
% 3.82/0.97  
% 3.82/0.97  fof(f5,axiom,(
% 3.82/0.97    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 3.82/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.82/0.97  
% 3.82/0.97  fof(f37,plain,(
% 3.82/0.97    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 3.82/0.97    inference(cnf_transformation,[],[f5])).
% 3.82/0.97  
% 3.82/0.97  fof(f6,axiom,(
% 3.82/0.97    ! [X0] : (~(r1_xboole_0(X0,X0) & k1_xboole_0 != X0) & ~(k1_xboole_0 = X0 & ~r1_xboole_0(X0,X0)))),
% 3.82/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.82/0.97  
% 3.82/0.97  fof(f25,plain,(
% 3.82/0.97    ! [X0] : ((~r1_xboole_0(X0,X0) | k1_xboole_0 = X0) & (k1_xboole_0 != X0 | r1_xboole_0(X0,X0)))),
% 3.82/0.97    inference(ennf_transformation,[],[f6])).
% 3.82/0.97  
% 3.82/0.97  fof(f38,plain,(
% 3.82/0.97    ( ! [X0] : (k1_xboole_0 != X0 | r1_xboole_0(X0,X0)) )),
% 3.82/0.97    inference(cnf_transformation,[],[f25])).
% 3.82/0.97  
% 3.82/0.97  fof(f79,plain,(
% 3.82/0.97    r1_xboole_0(k1_xboole_0,k1_xboole_0)),
% 3.82/0.97    inference(equality_resolution,[],[f38])).
% 3.82/0.97  
% 3.82/0.97  fof(f7,axiom,(
% 3.82/0.97    ! [X0,X1,X2] : ((r1_xboole_0(X1,X2) & r1_tarski(X0,X2) & r1_tarski(X0,X1)) => k1_xboole_0 = X0)),
% 3.82/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.82/0.97  
% 3.82/0.97  fof(f26,plain,(
% 3.82/0.97    ! [X0,X1,X2] : (k1_xboole_0 = X0 | (~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)))),
% 3.82/0.97    inference(ennf_transformation,[],[f7])).
% 3.82/0.97  
% 3.82/0.97  fof(f27,plain,(
% 3.82/0.97    ! [X0,X1,X2] : (k1_xboole_0 = X0 | ~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1))),
% 3.82/0.97    inference(flattening,[],[f26])).
% 3.82/0.97  
% 3.82/0.97  fof(f40,plain,(
% 3.82/0.97    ( ! [X2,X0,X1] : (k1_xboole_0 = X0 | ~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)) )),
% 3.82/0.97    inference(cnf_transformation,[],[f27])).
% 3.82/0.97  
% 3.82/0.97  cnf(c_17,negated_conjecture,
% 3.82/0.97      ( k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)) ),
% 3.82/0.97      inference(cnf_transformation,[],[f78]) ).
% 3.82/0.97  
% 3.82/0.97  cnf(c_3,plain,
% 3.82/0.97      ( r1_tarski(k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))),X0) ),
% 3.82/0.97      inference(cnf_transformation,[],[f70]) ).
% 3.82/0.97  
% 3.82/0.97  cnf(c_9,plain,
% 3.82/0.97      ( k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
% 3.82/0.97      inference(cnf_transformation,[],[f42]) ).
% 3.82/0.97  
% 3.82/0.97  cnf(c_0,plain,
% 3.82/0.97      ( k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
% 3.82/0.97      inference(cnf_transformation,[],[f33]) ).
% 3.82/0.97  
% 3.82/0.97  cnf(c_289,plain,
% 3.82/0.97      ( r1_tarski(k5_xboole_0(X0,k5_xboole_0(X1,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))),X0) ),
% 3.82/0.97      inference(theory_normalisation,[status(thm)],[c_3,c_9,c_0]) ).
% 3.82/0.97  
% 3.82/0.97  cnf(c_403,plain,
% 3.82/0.97      ( r1_tarski(k5_xboole_0(X0,k5_xboole_0(X1,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))),X0) = iProver_top ),
% 3.82/0.97      inference(predicate_to_equality,[status(thm)],[c_289]) ).
% 3.82/0.97  
% 3.82/0.97  cnf(c_8494,plain,
% 3.82/0.97      ( r1_tarski(k5_xboole_0(sK1,k5_xboole_0(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))),sK1) = iProver_top ),
% 3.82/0.97      inference(superposition,[status(thm)],[c_17,c_403]) ).
% 3.82/0.97  
% 3.82/0.97  cnf(c_8,plain,
% 3.82/0.97      ( r1_tarski(X0,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) ),
% 3.82/0.97      inference(cnf_transformation,[],[f71]) ).
% 3.82/0.97  
% 3.82/0.97  cnf(c_402,plain,
% 3.82/0.97      ( r1_tarski(X0,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) = iProver_top ),
% 3.82/0.97      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 3.82/0.97  
% 3.82/0.97  cnf(c_7481,plain,
% 3.82/0.97      ( r1_tarski(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)) = iProver_top ),
% 3.82/0.97      inference(superposition,[status(thm)],[c_17,c_402]) ).
% 3.82/0.97  
% 3.82/0.97  cnf(c_13,plain,
% 3.82/0.97      ( ~ r1_tarski(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))
% 3.82/0.97      | k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) = X0
% 3.82/0.97      | k1_xboole_0 = X0 ),
% 3.82/0.97      inference(cnf_transformation,[],[f74]) ).
% 3.82/0.97  
% 3.82/0.97  cnf(c_399,plain,
% 3.82/0.97      ( k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) = X1
% 3.82/0.97      | k1_xboole_0 = X1
% 3.82/0.97      | r1_tarski(X1,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) != iProver_top ),
% 3.82/0.97      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 3.82/0.97  
% 3.82/0.97  cnf(c_8251,plain,
% 3.82/0.97      ( k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) = sK1
% 3.82/0.97      | sK1 = k1_xboole_0 ),
% 3.82/0.97      inference(superposition,[status(thm)],[c_7481,c_399]) ).
% 3.82/0.97  
% 3.82/0.97  cnf(c_8253,plain,
% 3.82/0.97      ( k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) = X0
% 3.82/0.97      | sK1 = k1_xboole_0
% 3.82/0.97      | k1_xboole_0 = X0
% 3.82/0.97      | r1_tarski(X0,sK1) != iProver_top ),
% 3.82/0.97      inference(superposition,[status(thm)],[c_8251,c_399]) ).
% 3.82/0.97  
% 3.82/0.97  cnf(c_10771,plain,
% 3.82/0.97      ( k5_xboole_0(sK1,k5_xboole_0(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))) = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)
% 3.82/0.97      | k5_xboole_0(sK1,k5_xboole_0(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))) = k1_xboole_0
% 3.82/0.97      | sK1 = k1_xboole_0 ),
% 3.82/0.97      inference(superposition,[status(thm)],[c_8494,c_8253]) ).
% 3.82/0.97  
% 3.82/0.97  cnf(c_14,negated_conjecture,
% 3.82/0.97      ( k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) != sK1
% 3.82/0.97      | k1_xboole_0 != sK2 ),
% 3.82/0.97      inference(cnf_transformation,[],[f75]) ).
% 3.82/0.97  
% 3.82/0.97  cnf(c_8259,plain,
% 3.82/0.97      ( sK1 = k1_xboole_0 | sK2 != k1_xboole_0 ),
% 3.82/0.97      inference(superposition,[status(thm)],[c_8251,c_14]) ).
% 3.82/0.97  
% 3.82/0.97  cnf(c_16,negated_conjecture,
% 3.82/0.97      ( k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) != sK1
% 3.82/0.97      | k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) != sK2 ),
% 3.82/0.97      inference(cnf_transformation,[],[f77]) ).
% 3.82/0.97  
% 3.82/0.97  cnf(c_8257,plain,
% 3.82/0.97      ( k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) != sK2
% 3.82/0.97      | sK1 = k1_xboole_0 ),
% 3.82/0.97      inference(superposition,[status(thm)],[c_8251,c_16]) ).
% 3.82/0.97  
% 3.82/0.97  cnf(c_15,negated_conjecture,
% 3.82/0.97      ( k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) != sK2
% 3.82/0.97      | k1_xboole_0 != sK1 ),
% 3.82/0.97      inference(cnf_transformation,[],[f76]) ).
% 3.82/0.97  
% 3.82/0.97  cnf(c_425,plain,
% 3.82/0.97      ( ~ r1_tarski(sK1,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))
% 3.82/0.97      | k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) = sK1
% 3.82/0.97      | k1_xboole_0 = sK1 ),
% 3.82/0.97      inference(instantiation,[status(thm)],[c_13]) ).
% 3.82/0.97  
% 3.82/0.97  cnf(c_430,plain,
% 3.82/0.97      ( ~ r1_tarski(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))
% 3.82/0.97      | k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) = sK1
% 3.82/0.97      | k1_xboole_0 = sK1 ),
% 3.82/0.97      inference(instantiation,[status(thm)],[c_425]) ).
% 3.82/0.97  
% 3.82/0.97  cnf(c_292,plain,( X0 = X0 ),theory(equality) ).
% 3.82/0.97  
% 3.82/0.97  cnf(c_502,plain,
% 3.82/0.97      ( sK1 = sK1 ),
% 3.82/0.97      inference(instantiation,[status(thm)],[c_292]) ).
% 3.82/0.97  
% 3.82/0.97  cnf(c_297,plain,
% 3.82/0.97      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,X3) | X2 != X0 | X3 != X1 ),
% 3.82/0.97      theory(equality) ).
% 3.82/0.97  
% 3.82/0.97  cnf(c_460,plain,
% 3.82/0.97      ( ~ r1_tarski(X0,X1)
% 3.82/0.97      | r1_tarski(sK1,k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2))
% 3.82/0.97      | k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2) != X1
% 3.82/0.97      | sK1 != X0 ),
% 3.82/0.97      inference(instantiation,[status(thm)],[c_297]) ).
% 3.82/0.97  
% 3.82/0.97  cnf(c_494,plain,
% 3.82/0.97      ( ~ r1_tarski(sK1,X0)
% 3.82/0.97      | r1_tarski(sK1,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))
% 3.82/0.97      | k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) != X0
% 3.82/0.97      | sK1 != sK1 ),
% 3.82/0.97      inference(instantiation,[status(thm)],[c_460]) ).
% 3.82/0.97  
% 3.82/0.97  cnf(c_563,plain,
% 3.82/0.97      ( r1_tarski(sK1,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))
% 3.82/0.97      | ~ r1_tarski(sK1,k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,X1)))
% 3.82/0.97      | k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) != k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,X1))
% 3.82/0.98      | sK1 != sK1 ),
% 3.82/0.98      inference(instantiation,[status(thm)],[c_494]) ).
% 3.82/0.98  
% 3.82/0.98  cnf(c_1737,plain,
% 3.82/0.98      ( r1_tarski(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))
% 3.82/0.98      | ~ r1_tarski(sK1,k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)))
% 3.82/0.98      | k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) != k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2))
% 3.82/0.98      | sK1 != sK1 ),
% 3.82/0.98      inference(instantiation,[status(thm)],[c_563]) ).
% 3.82/0.98  
% 3.82/0.98  cnf(c_653,plain,
% 3.82/0.98      ( r1_tarski(sK1,k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,X0))) ),
% 3.82/0.98      inference(instantiation,[status(thm)],[c_8]) ).
% 3.82/0.98  
% 3.82/0.98  cnf(c_2078,plain,
% 3.82/0.98      ( r1_tarski(sK1,k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2))) ),
% 3.82/0.98      inference(instantiation,[status(thm)],[c_653]) ).
% 3.82/0.98  
% 3.82/0.98  cnf(c_8351,plain,
% 3.82/0.98      ( k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) != sK2 ),
% 3.82/0.98      inference(global_propositional_subsumption,
% 3.82/0.98                [status(thm)],
% 3.82/0.98                [c_8257,c_17,c_16,c_15,c_430,c_502,c_1737,c_2078]) ).
% 3.82/0.98  
% 3.82/0.98  cnf(c_10605,plain,
% 3.82/0.98      ( sK1 = k1_xboole_0
% 3.82/0.98      | r1_tarski(k5_xboole_0(sK1,k5_xboole_0(sK2,sK1)),sK1) = iProver_top ),
% 3.82/0.98      inference(superposition,[status(thm)],[c_8251,c_8494]) ).
% 3.82/0.98  
% 3.82/0.98  cnf(c_10,plain,
% 3.82/0.98      ( k5_xboole_0(X0,X0) = k1_xboole_0 ),
% 3.82/0.98      inference(cnf_transformation,[],[f43]) ).
% 3.82/0.98  
% 3.82/0.98  cnf(c_411,plain,
% 3.82/0.98      ( k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(X1,k5_xboole_0(X0,X2)) ),
% 3.82/0.98      inference(superposition,[status(thm)],[c_9,c_0]) ).
% 3.82/0.98  
% 3.82/0.98  cnf(c_775,plain,
% 3.82/0.98      ( k5_xboole_0(X0,k5_xboole_0(X1,X0)) = k5_xboole_0(X1,k1_xboole_0) ),
% 3.82/0.98      inference(superposition,[status(thm)],[c_10,c_411]) ).
% 3.82/0.98  
% 3.82/0.98  cnf(c_4,plain,
% 3.82/0.98      ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
% 3.82/0.98      inference(cnf_transformation,[],[f37]) ).
% 3.82/0.98  
% 3.82/0.98  cnf(c_792,plain,
% 3.82/0.98      ( k5_xboole_0(X0,k5_xboole_0(X1,X0)) = X1 ),
% 3.82/0.98      inference(demodulation,[status(thm)],[c_775,c_4]) ).
% 3.82/0.98  
% 3.82/0.98  cnf(c_10606,plain,
% 3.82/0.98      ( sK1 = k1_xboole_0 | r1_tarski(sK2,sK1) = iProver_top ),
% 3.82/0.98      inference(demodulation,[status(thm)],[c_10605,c_792]) ).
% 3.82/0.98  
% 3.82/0.98  cnf(c_10774,plain,
% 3.82/0.98      ( k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) = sK2
% 3.82/0.98      | sK1 = k1_xboole_0
% 3.82/0.98      | sK2 = k1_xboole_0 ),
% 3.82/0.98      inference(superposition,[status(thm)],[c_10606,c_8253]) ).
% 3.82/0.98  
% 3.82/0.98  cnf(c_10868,plain,
% 3.82/0.98      ( sK1 = k1_xboole_0 ),
% 3.82/0.98      inference(global_propositional_subsumption,
% 3.82/0.98                [status(thm)],
% 3.82/0.98                [c_10771,c_17,c_16,c_15,c_430,c_502,c_1737,c_2078,c_8259,
% 3.82/0.98                 c_10774]) ).
% 3.82/0.98  
% 3.82/0.98  cnf(c_10873,plain,
% 3.82/0.98      ( r1_tarski(k5_xboole_0(k1_xboole_0,k5_xboole_0(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))),k1_xboole_0) = iProver_top ),
% 3.82/0.98      inference(demodulation,[status(thm)],[c_10868,c_8494]) ).
% 3.82/0.98  
% 3.82/0.98  cnf(c_412,plain,
% 3.82/0.98      ( k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(X2,k5_xboole_0(X1,X0)) ),
% 3.82/0.98      inference(superposition,[status(thm)],[c_9,c_0]) ).
% 3.82/0.98  
% 3.82/0.98  cnf(c_1099,plain,
% 3.82/0.98      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(X0,X1)) = k5_xboole_0(X1,X0) ),
% 3.82/0.98      inference(superposition,[status(thm)],[c_4,c_412]) ).
% 3.82/0.98  
% 3.82/0.98  cnf(c_10880,plain,
% 3.82/0.98      ( r1_tarski(k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK2),k1_xboole_0) = iProver_top ),
% 3.82/0.98      inference(demodulation,[status(thm)],[c_10873,c_1099]) ).
% 3.82/0.98  
% 3.82/0.98  cnf(c_6,plain,
% 3.82/0.98      ( r1_xboole_0(k1_xboole_0,k1_xboole_0) ),
% 3.82/0.98      inference(cnf_transformation,[],[f79]) ).
% 3.82/0.98  
% 3.82/0.98  cnf(c_7,plain,
% 3.82/0.98      ( ~ r1_xboole_0(X0,X1)
% 3.82/0.98      | ~ r1_tarski(X2,X1)
% 3.82/0.98      | ~ r1_tarski(X2,X0)
% 3.82/0.98      | k1_xboole_0 = X2 ),
% 3.82/0.98      inference(cnf_transformation,[],[f40]) ).
% 3.82/0.98  
% 3.82/0.98  cnf(c_113,plain,
% 3.82/0.98      ( ~ r1_tarski(X0,X1)
% 3.82/0.98      | ~ r1_tarski(X0,X2)
% 3.82/0.98      | k1_xboole_0 != X2
% 3.82/0.98      | k1_xboole_0 != X1
% 3.82/0.98      | k1_xboole_0 = X0 ),
% 3.82/0.98      inference(resolution_lifted,[status(thm)],[c_6,c_7]) ).
% 3.82/0.98  
% 3.82/0.98  cnf(c_114,plain,
% 3.82/0.98      ( ~ r1_tarski(X0,k1_xboole_0) | k1_xboole_0 = X0 ),
% 3.82/0.98      inference(unflattening,[status(thm)],[c_113]) ).
% 3.82/0.98  
% 3.82/0.98  cnf(c_398,plain,
% 3.82/0.98      ( k1_xboole_0 = X0 | r1_tarski(X0,k1_xboole_0) != iProver_top ),
% 3.82/0.98      inference(predicate_to_equality,[status(thm)],[c_114]) ).
% 3.82/0.98  
% 3.82/0.98  cnf(c_14013,plain,
% 3.82/0.98      ( k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK2) = k1_xboole_0 ),
% 3.82/0.98      inference(superposition,[status(thm)],[c_10880,c_398]) ).
% 3.82/0.98  
% 3.82/0.98  cnf(c_632,plain,
% 3.82/0.98      ( k5_xboole_0(X0,k5_xboole_0(X0,X1)) = k5_xboole_0(k1_xboole_0,X1) ),
% 3.82/0.98      inference(superposition,[status(thm)],[c_10,c_9]) ).
% 3.82/0.98  
% 3.82/0.98  cnf(c_603,plain,
% 3.82/0.98      ( k5_xboole_0(k1_xboole_0,X0) = X0 ),
% 3.82/0.98      inference(superposition,[status(thm)],[c_4,c_0]) ).
% 3.82/0.98  
% 3.82/0.98  cnf(c_639,plain,
% 3.82/0.98      ( k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1 ),
% 3.82/0.98      inference(demodulation,[status(thm)],[c_632,c_603]) ).
% 3.82/0.98  
% 3.82/0.98  cnf(c_804,plain,
% 3.82/0.98      ( k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X0,k5_xboole_0(X1,X2))) = X2 ),
% 3.82/0.98      inference(superposition,[status(thm)],[c_9,c_639]) ).
% 3.82/0.98  
% 3.82/0.98  cnf(c_1543,plain,
% 3.82/0.98      ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,X2)),k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,X3)))) = X3 ),
% 3.82/0.98      inference(superposition,[status(thm)],[c_9,c_804]) ).
% 3.82/0.98  
% 3.82/0.98  cnf(c_14196,plain,
% 3.82/0.98      ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))),k5_xboole_0(X0,k5_xboole_0(X1,k1_xboole_0))) = sK2 ),
% 3.82/0.98      inference(superposition,[status(thm)],[c_14013,c_1543]) ).
% 3.82/0.98  
% 3.82/0.98  cnf(c_949,plain,
% 3.82/0.98      ( k5_xboole_0(k5_xboole_0(X0,X1),X0) = X1 ),
% 3.82/0.98      inference(superposition,[status(thm)],[c_792,c_792]) ).
% 3.82/0.98  
% 3.82/0.98  cnf(c_1054,plain,
% 3.82/0.98      ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,X2)),k5_xboole_0(X0,X1)) = X2 ),
% 3.82/0.98      inference(superposition,[status(thm)],[c_9,c_949]) ).
% 3.82/0.98  
% 3.82/0.98  cnf(c_945,plain,
% 3.82/0.98      ( k5_xboole_0(k5_xboole_0(X0,X1),X1) = X0 ),
% 3.82/0.98      inference(superposition,[status(thm)],[c_639,c_792]) ).
% 3.82/0.98  
% 3.82/0.98  cnf(c_980,plain,
% 3.82/0.98      ( k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X1,X2)) = k5_xboole_0(X0,X2) ),
% 3.82/0.98      inference(superposition,[status(thm)],[c_945,c_9]) ).
% 3.82/0.98  
% 3.82/0.98  cnf(c_2837,plain,
% 3.82/0.98      ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,X2)),k5_xboole_0(X0,k5_xboole_0(X1,X3))) = k5_xboole_0(X3,X2) ),
% 3.82/0.98      inference(superposition,[status(thm)],[c_980,c_1054]) ).
% 3.82/0.98  
% 3.82/0.98  cnf(c_14197,plain,
% 3.82/0.98      ( k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) = sK2 ),
% 3.82/0.98      inference(demodulation,[status(thm)],[c_14196,c_4,c_1054,c_2837]) ).
% 3.82/0.98  
% 3.82/0.98  cnf(contradiction,plain,
% 3.82/0.98      ( $false ),
% 3.82/0.98      inference(minisat,[status(thm)],[c_14197,c_8351]) ).
% 3.82/0.98  
% 3.82/0.98  
% 3.82/0.98  % SZS output end CNFRefutation for theBenchmark.p
% 3.82/0.98  
% 3.82/0.98  ------                               Statistics
% 3.82/0.98  
% 3.82/0.98  ------ General
% 3.82/0.98  
% 3.82/0.98  abstr_ref_over_cycles:                  0
% 3.82/0.98  abstr_ref_under_cycles:                 0
% 3.82/0.98  gc_basic_clause_elim:                   0
% 3.82/0.98  forced_gc_time:                         0
% 3.82/0.98  parsing_time:                           0.022
% 3.82/0.98  unif_index_cands_time:                  0.
% 3.82/0.98  unif_index_add_time:                    0.
% 3.82/0.98  orderings_time:                         0.
% 3.82/0.98  out_proof_time:                         0.012
% 3.82/0.98  total_time:                             0.477
% 3.82/0.98  num_of_symbols:                         40
% 3.82/0.98  num_of_terms:                           22652
% 3.82/0.98  
% 3.82/0.98  ------ Preprocessing
% 3.82/0.98  
% 3.82/0.98  num_of_splits:                          0
% 3.82/0.98  num_of_split_atoms:                     0
% 3.82/0.98  num_of_reused_defs:                     0
% 3.82/0.98  num_eq_ax_congr_red:                    0
% 3.82/0.98  num_of_sem_filtered_clauses:            1
% 3.82/0.98  num_of_subtypes:                        0
% 3.82/0.98  monotx_restored_types:                  0
% 3.82/0.98  sat_num_of_epr_types:                   0
% 3.82/0.98  sat_num_of_non_cyclic_types:            0
% 3.82/0.98  sat_guarded_non_collapsed_types:        0
% 3.82/0.98  num_pure_diseq_elim:                    0
% 3.82/0.98  simp_replaced_by:                       0
% 3.82/0.98  res_preprocessed:                       79
% 3.82/0.98  prep_upred:                             0
% 3.82/0.98  prep_unflattend:                        23
% 3.82/0.98  smt_new_axioms:                         0
% 3.82/0.98  pred_elim_cands:                        1
% 3.82/0.98  pred_elim:                              1
% 3.82/0.98  pred_elim_cl:                           2
% 3.82/0.98  pred_elim_cycles:                       3
% 3.82/0.98  merged_defs:                            0
% 3.82/0.98  merged_defs_ncl:                        0
% 3.82/0.98  bin_hyper_res:                          0
% 3.82/0.98  prep_cycles:                            4
% 3.82/0.98  pred_elim_time:                         0.002
% 3.82/0.98  splitting_time:                         0.
% 3.82/0.98  sem_filter_time:                        0.
% 3.82/0.98  monotx_time:                            0.
% 3.82/0.98  subtype_inf_time:                       0.
% 3.82/0.98  
% 3.82/0.98  ------ Problem properties
% 3.82/0.98  
% 3.82/0.98  clauses:                                16
% 3.82/0.98  conjectures:                            4
% 3.82/0.98  epr:                                    1
% 3.82/0.98  horn:                                   15
% 3.82/0.98  ground:                                 4
% 3.82/0.98  unary:                                  11
% 3.82/0.98  binary:                                 4
% 3.82/0.98  lits:                                   22
% 3.82/0.98  lits_eq:                                16
% 3.82/0.98  fd_pure:                                0
% 3.82/0.98  fd_pseudo:                              0
% 3.82/0.98  fd_cond:                                1
% 3.82/0.98  fd_pseudo_cond:                         1
% 3.82/0.98  ac_symbols:                             1
% 3.82/0.98  
% 3.82/0.98  ------ Propositional Solver
% 3.82/0.98  
% 3.82/0.98  prop_solver_calls:                      31
% 3.82/0.98  prop_fast_solver_calls:                 421
% 3.82/0.98  smt_solver_calls:                       0
% 3.82/0.98  smt_fast_solver_calls:                  0
% 3.82/0.98  prop_num_of_clauses:                    2360
% 3.82/0.98  prop_preprocess_simplified:             4562
% 3.82/0.98  prop_fo_subsumed:                       7
% 3.82/0.98  prop_solver_time:                       0.
% 3.82/0.98  smt_solver_time:                        0.
% 3.82/0.98  smt_fast_solver_time:                   0.
% 3.82/0.98  prop_fast_solver_time:                  0.
% 3.82/0.98  prop_unsat_core_time:                   0.
% 3.82/0.98  
% 3.82/0.98  ------ QBF
% 3.82/0.98  
% 3.82/0.98  qbf_q_res:                              0
% 3.82/0.98  qbf_num_tautologies:                    0
% 3.82/0.98  qbf_prep_cycles:                        0
% 3.82/0.98  
% 3.82/0.98  ------ BMC1
% 3.82/0.98  
% 3.82/0.98  bmc1_current_bound:                     -1
% 3.82/0.98  bmc1_last_solved_bound:                 -1
% 3.82/0.98  bmc1_unsat_core_size:                   -1
% 3.82/0.98  bmc1_unsat_core_parents_size:           -1
% 3.82/0.98  bmc1_merge_next_fun:                    0
% 3.82/0.98  bmc1_unsat_core_clauses_time:           0.
% 3.82/0.98  
% 3.82/0.98  ------ Instantiation
% 3.82/0.98  
% 3.82/0.98  inst_num_of_clauses:                    787
% 3.82/0.98  inst_num_in_passive:                    89
% 3.82/0.98  inst_num_in_active:                     342
% 3.82/0.98  inst_num_in_unprocessed:                361
% 3.82/0.98  inst_num_of_loops:                      410
% 3.82/0.98  inst_num_of_learning_restarts:          0
% 3.82/0.98  inst_num_moves_active_passive:          63
% 3.82/0.98  inst_lit_activity:                      0
% 3.82/0.98  inst_lit_activity_moves:                0
% 3.82/0.98  inst_num_tautologies:                   0
% 3.82/0.98  inst_num_prop_implied:                  0
% 3.82/0.98  inst_num_existing_simplified:           0
% 3.82/0.98  inst_num_eq_res_simplified:             0
% 3.82/0.98  inst_num_child_elim:                    0
% 3.82/0.98  inst_num_of_dismatching_blockings:      123
% 3.82/0.98  inst_num_of_non_proper_insts:           721
% 3.82/0.98  inst_num_of_duplicates:                 0
% 3.82/0.98  inst_inst_num_from_inst_to_res:         0
% 3.82/0.98  inst_dismatching_checking_time:         0.
% 3.82/0.98  
% 3.82/0.98  ------ Resolution
% 3.82/0.98  
% 3.82/0.98  res_num_of_clauses:                     0
% 3.82/0.98  res_num_in_passive:                     0
% 3.82/0.98  res_num_in_active:                      0
% 3.82/0.98  res_num_of_loops:                       83
% 3.82/0.98  res_forward_subset_subsumed:            167
% 3.82/0.98  res_backward_subset_subsumed:           10
% 3.82/0.98  res_forward_subsumed:                   0
% 3.82/0.98  res_backward_subsumed:                  0
% 3.82/0.98  res_forward_subsumption_resolution:     0
% 3.82/0.98  res_backward_subsumption_resolution:    0
% 3.82/0.98  res_clause_to_clause_subsumption:       20853
% 3.82/0.98  res_orphan_elimination:                 0
% 3.82/0.98  res_tautology_del:                      60
% 3.82/0.98  res_num_eq_res_simplified:              0
% 3.82/0.98  res_num_sel_changes:                    0
% 3.82/0.98  res_moves_from_active_to_pass:          0
% 3.82/0.98  
% 3.82/0.98  ------ Superposition
% 3.82/0.98  
% 3.82/0.98  sup_time_total:                         0.
% 3.82/0.98  sup_time_generating:                    0.
% 3.82/0.98  sup_time_sim_full:                      0.
% 3.82/0.98  sup_time_sim_immed:                     0.
% 3.82/0.98  
% 3.82/0.98  sup_num_of_clauses:                     504
% 3.82/0.98  sup_num_in_active:                      62
% 3.82/0.98  sup_num_in_passive:                     442
% 3.82/0.98  sup_num_of_loops:                       80
% 3.82/0.98  sup_fw_superposition:                   4296
% 3.82/0.98  sup_bw_superposition:                   2740
% 3.82/0.98  sup_immediate_simplified:               2924
% 3.82/0.98  sup_given_eliminated:                   2
% 3.82/0.98  comparisons_done:                       0
% 3.82/0.98  comparisons_avoided:                    6
% 3.82/0.98  
% 3.82/0.98  ------ Simplifications
% 3.82/0.98  
% 3.82/0.98  
% 3.82/0.98  sim_fw_subset_subsumed:                 0
% 3.82/0.98  sim_bw_subset_subsumed:                 7
% 3.82/0.98  sim_fw_subsumed:                        125
% 3.82/0.98  sim_bw_subsumed:                        2
% 3.82/0.98  sim_fw_subsumption_res:                 0
% 3.82/0.98  sim_bw_subsumption_res:                 0
% 3.82/0.98  sim_tautology_del:                      1
% 3.82/0.98  sim_eq_tautology_del:                   700
% 3.82/0.98  sim_eq_res_simp:                        0
% 3.82/0.98  sim_fw_demodulated:                     2640
% 3.82/0.98  sim_bw_demodulated:                     19
% 3.82/0.98  sim_light_normalised:                   853
% 3.82/0.98  sim_joinable_taut:                      178
% 3.82/0.98  sim_joinable_simp:                      0
% 3.82/0.98  sim_ac_normalised:                      0
% 3.82/0.98  sim_smt_subsumption:                    0
% 3.82/0.98  
%------------------------------------------------------------------------------
