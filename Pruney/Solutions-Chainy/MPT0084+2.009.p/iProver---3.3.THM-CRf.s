%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:24:13 EST 2020

% Result     : Theorem 12.00s
% Output     : CNFRefutation 12.00s
% Verified   : 
% Statistics : Number of formulae       :   97 ( 486 expanded)
%              Number of clauses        :   59 ( 167 expanded)
%              Number of leaves         :   12 ( 127 expanded)
%              Depth                    :   15
%              Number of atoms          :  183 ( 758 expanded)
%              Number of equality atoms :   99 ( 482 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal clause size      :    6 (   2 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f6,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f6])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f7,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f39,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(definition_unfolding,[],[f25,f33,f33])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k3_xboole_0(X0,X1) != k1_xboole_0 )
      & ( k3_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f27,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k3_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f20])).

fof(f40,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k1_xboole_0 != k4_xboole_0(X0,k4_xboole_0(X0,X1)) ) ),
    inference(definition_unfolding,[],[f27,f33])).

fof(f4,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f44,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0) ),
    inference(definition_unfolding,[],[f30,f33])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_xboole_0(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f16])).

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f9,axiom,(
    ! [X0,X1] :
      ~ ( r1_xboole_0(k3_xboole_0(X0,X1),X1)
        & ~ r1_xboole_0(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(k3_xboole_0(X0,X1),X1)
      | r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(k3_xboole_0(X0,X1),X1)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1)
      | r1_xboole_0(X0,X1) ) ),
    inference(definition_unfolding,[],[f35,f33])).

fof(f26,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f41,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,X1))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(definition_unfolding,[],[f26,f33])).

fof(f10,conjecture,(
    ! [X0,X1,X2] :
      ~ ( r1_xboole_0(X0,k3_xboole_0(X1,X2))
        & r1_tarski(X0,X2)
        & ~ r1_xboole_0(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f11,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ~ ( r1_xboole_0(X0,k3_xboole_0(X1,X2))
          & r1_tarski(X0,X2)
          & ~ r1_xboole_0(X0,X1) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f19,plain,(
    ? [X0,X1,X2] :
      ( r1_xboole_0(X0,k3_xboole_0(X1,X2))
      & r1_tarski(X0,X2)
      & ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f23,plain,
    ( ? [X0,X1,X2] :
        ( r1_xboole_0(X0,k3_xboole_0(X1,X2))
        & r1_tarski(X0,X2)
        & ~ r1_xboole_0(X0,X1) )
   => ( r1_xboole_0(sK1,k3_xboole_0(sK2,sK3))
      & r1_tarski(sK1,sK3)
      & ~ r1_xboole_0(sK1,sK2) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,
    ( r1_xboole_0(sK1,k3_xboole_0(sK2,sK3))
    & r1_tarski(sK1,sK3)
    & ~ r1_xboole_0(sK1,sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f19,f23])).

fof(f38,plain,(
    r1_xboole_0(sK1,k3_xboole_0(sK2,sK3)) ),
    inference(cnf_transformation,[],[f24])).

fof(f47,plain,(
    r1_xboole_0(sK1,k4_xboole_0(sK2,k4_xboole_0(sK2,sK3))) ),
    inference(definition_unfolding,[],[f38,f33])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( r1_tarski(X2,X3)
        & r1_tarski(X0,X1) )
     => r1_tarski(k3_xboole_0(X0,X2),k3_xboole_0(X1,X3)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1,X2,X3] :
      ( r1_tarski(k3_xboole_0(X0,X2),k3_xboole_0(X1,X3))
      | ~ r1_tarski(X2,X3)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f15,plain,(
    ! [X0,X1,X2,X3] :
      ( r1_tarski(k3_xboole_0(X0,X2),k3_xboole_0(X1,X3))
      | ~ r1_tarski(X2,X3)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f14])).

fof(f31,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_tarski(k3_xboole_0(X0,X2),k3_xboole_0(X1,X3))
      | ~ r1_tarski(X2,X3)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f45,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_tarski(k4_xboole_0(X0,k4_xboole_0(X0,X2)),k4_xboole_0(X1,k4_xboole_0(X1,X3)))
      | ~ r1_tarski(X2,X3)
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f31,f33,f33])).

fof(f37,plain,(
    r1_tarski(sK1,sK3) ),
    inference(cnf_transformation,[],[f24])).

fof(f36,plain,(
    ~ r1_xboole_0(sK1,sK2) ),
    inference(cnf_transformation,[],[f24])).

cnf(c_7,plain,
    ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f32])).

cnf(c_0,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_756,plain,
    ( k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0)) = k4_xboole_0(X0,X0) ),
    inference(superposition,[status(thm)],[c_7,c_0])).

cnf(c_1,plain,
    ( r1_xboole_0(X0,X1)
    | k4_xboole_0(X0,k4_xboole_0(X0,X1)) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f40])).

cnf(c_457,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) != k1_xboole_0
    | r1_xboole_0(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_1293,plain,
    ( k4_xboole_0(X0,X0) != k1_xboole_0
    | r1_xboole_0(X0,k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_7,c_457])).

cnf(c_1782,plain,
    ( k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0)) != k1_xboole_0
    | r1_xboole_0(X0,k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_756,c_1293])).

cnf(c_20,plain,
    ( k4_xboole_0(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_1290,plain,
    ( k4_xboole_0(X0,X0) != k1_xboole_0
    | r1_xboole_0(k1_xboole_0,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_756,c_457])).

cnf(c_1300,plain,
    ( k4_xboole_0(k1_xboole_0,k1_xboole_0) != k1_xboole_0
    | r1_xboole_0(k1_xboole_0,k1_xboole_0) = iProver_top ),
    inference(instantiation,[status(thm)],[c_1290])).

cnf(c_5,plain,
    ( r1_tarski(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_453,plain,
    ( r1_tarski(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_825,plain,
    ( r1_tarski(k4_xboole_0(X0,X0),k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_756,c_453])).

cnf(c_8,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_xboole_0(X1,X2)
    | r1_xboole_0(X0,X2) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_451,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_xboole_0(X1,X2) != iProver_top
    | r1_xboole_0(X0,X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_1148,plain,
    ( r1_xboole_0(k4_xboole_0(X0,X0),X1) = iProver_top
    | r1_xboole_0(k1_xboole_0,X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_825,c_451])).

cnf(c_9,plain,
    ( r1_xboole_0(X0,X1)
    | ~ r1_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_450,plain,
    ( r1_xboole_0(X0,X1) = iProver_top
    | r1_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_811,plain,
    ( r1_xboole_0(X0,k1_xboole_0) = iProver_top
    | r1_xboole_0(k4_xboole_0(X0,X0),k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_7,c_450])).

cnf(c_15476,plain,
    ( r1_xboole_0(X0,k1_xboole_0) = iProver_top
    | r1_xboole_0(k1_xboole_0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1148,c_811])).

cnf(c_39559,plain,
    ( r1_xboole_0(X0,k1_xboole_0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1782,c_20,c_1300,c_15476])).

cnf(c_2,plain,
    ( ~ r1_xboole_0(X0,X1)
    | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f41])).

cnf(c_456,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_xboole_0
    | r1_xboole_0(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_39563,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_39559,c_456])).

cnf(c_39584,plain,
    ( k4_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_39563,c_7])).

cnf(c_761,plain,
    ( r1_tarski(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_0,c_453])).

cnf(c_872,plain,
    ( r1_tarski(k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0))),k4_xboole_0(X0,X1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_0,c_761])).

cnf(c_934,plain,
    ( r1_tarski(k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X0,X1),X0))),k4_xboole_0(X1,k4_xboole_0(X1,X0))) = iProver_top ),
    inference(superposition,[status(thm)],[c_0,c_872])).

cnf(c_39866,plain,
    ( r1_tarski(k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(X0,X0),k4_xboole_0(k4_xboole_0(X0,X0),X0))),k4_xboole_0(X0,k1_xboole_0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_39584,c_934])).

cnf(c_40120,plain,
    ( r1_tarski(k4_xboole_0(X0,k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0))),k4_xboole_0(X0,k1_xboole_0)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_39866,c_39584])).

cnf(c_39636,plain,
    ( k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0)) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_39584,c_756])).

cnf(c_40121,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_40120,c_7,c_39636])).

cnf(c_10,negated_conjecture,
    ( r1_xboole_0(sK1,k4_xboole_0(sK2,k4_xboole_0(sK2,sK3))) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_449,plain,
    ( r1_xboole_0(sK1,k4_xboole_0(sK2,k4_xboole_0(sK2,sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_1072,plain,
    ( k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_449,c_456])).

cnf(c_1287,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) != k1_xboole_0
    | r1_xboole_0(X1,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_0,c_457])).

cnf(c_2279,plain,
    ( r1_xboole_0(k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)),sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_1072,c_1287])).

cnf(c_6,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X2,X3)
    | r1_tarski(k4_xboole_0(X2,k4_xboole_0(X2,X0)),k4_xboole_0(X3,k4_xboole_0(X3,X1))) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_452,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X2,X3) != iProver_top
    | r1_tarski(k4_xboole_0(X2,k4_xboole_0(X2,X0)),k4_xboole_0(X3,k4_xboole_0(X3,X1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_1693,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X2,X3) != iProver_top
    | r1_xboole_0(k4_xboole_0(X3,k4_xboole_0(X3,X1)),X4) != iProver_top
    | r1_xboole_0(k4_xboole_0(X2,k4_xboole_0(X2,X0)),X4) = iProver_top ),
    inference(superposition,[status(thm)],[c_452,c_451])).

cnf(c_36852,plain,
    ( r1_tarski(X0,sK3) != iProver_top
    | r1_tarski(X1,sK2) != iProver_top
    | r1_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_2279,c_1693])).

cnf(c_37641,plain,
    ( r1_tarski(X0,sK2) != iProver_top
    | r1_tarski(sK1,sK3) != iProver_top
    | r1_xboole_0(X0,sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_36852,c_450])).

cnf(c_11,negated_conjecture,
    ( r1_tarski(sK1,sK3) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_14,plain,
    ( r1_tarski(sK1,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_40947,plain,
    ( r1_tarski(X0,sK2) != iProver_top
    | r1_xboole_0(X0,sK1) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_37641,c_14])).

cnf(c_40954,plain,
    ( r1_xboole_0(sK2,sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_40121,c_40947])).

cnf(c_1247,plain,
    ( ~ r1_xboole_0(sK2,sK1)
    | k4_xboole_0(sK2,k4_xboole_0(sK2,sK1)) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_1248,plain,
    ( k4_xboole_0(sK2,k4_xboole_0(sK2,sK1)) = k1_xboole_0
    | r1_xboole_0(sK2,sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1247])).

cnf(c_976,plain,
    ( k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)) = k4_xboole_0(sK2,k4_xboole_0(sK2,sK1)) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_171,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_697,plain,
    ( k4_xboole_0(sK2,k4_xboole_0(sK2,sK1)) != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = k4_xboole_0(sK2,k4_xboole_0(sK2,sK1)) ),
    inference(instantiation,[status(thm)],[c_171])).

cnf(c_698,plain,
    ( k4_xboole_0(sK2,k4_xboole_0(sK2,sK1)) != k1_xboole_0
    | k1_xboole_0 = k4_xboole_0(sK2,k4_xboole_0(sK2,sK1))
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_697])).

cnf(c_499,plain,
    ( k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)) != X0
    | k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)) = k1_xboole_0
    | k1_xboole_0 != X0 ),
    inference(instantiation,[status(thm)],[c_171])).

cnf(c_587,plain,
    ( k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)) != k4_xboole_0(sK2,k4_xboole_0(sK2,sK1))
    | k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)) = k1_xboole_0
    | k1_xboole_0 != k4_xboole_0(sK2,k4_xboole_0(sK2,sK1)) ),
    inference(instantiation,[status(thm)],[c_499])).

cnf(c_477,plain,
    ( r1_xboole_0(sK1,sK2)
    | k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)) != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_170,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_181,plain,
    ( k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_170])).

cnf(c_12,negated_conjecture,
    ( ~ r1_xboole_0(sK1,sK2) ),
    inference(cnf_transformation,[],[f36])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_40954,c_1248,c_976,c_698,c_587,c_477,c_181,c_12])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 19:36:19 EST 2020
% 0.20/0.34  % CPUTime    : 
% 0.20/0.34  % Running in FOF mode
% 12.00/2.00  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 12.00/2.00  
% 12.00/2.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 12.00/2.00  
% 12.00/2.00  ------  iProver source info
% 12.00/2.00  
% 12.00/2.00  git: date: 2020-06-30 10:37:57 +0100
% 12.00/2.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 12.00/2.00  git: non_committed_changes: false
% 12.00/2.00  git: last_make_outside_of_git: false
% 12.00/2.00  
% 12.00/2.00  ------ 
% 12.00/2.00  
% 12.00/2.00  ------ Input Options
% 12.00/2.00  
% 12.00/2.00  --out_options                           all
% 12.00/2.00  --tptp_safe_out                         true
% 12.00/2.00  --problem_path                          ""
% 12.00/2.00  --include_path                          ""
% 12.00/2.00  --clausifier                            res/vclausify_rel
% 12.00/2.00  --clausifier_options                    ""
% 12.00/2.00  --stdin                                 false
% 12.00/2.00  --stats_out                             all
% 12.00/2.00  
% 12.00/2.00  ------ General Options
% 12.00/2.00  
% 12.00/2.00  --fof                                   false
% 12.00/2.00  --time_out_real                         305.
% 12.00/2.00  --time_out_virtual                      -1.
% 12.00/2.00  --symbol_type_check                     false
% 12.00/2.00  --clausify_out                          false
% 12.00/2.00  --sig_cnt_out                           false
% 12.00/2.00  --trig_cnt_out                          false
% 12.00/2.00  --trig_cnt_out_tolerance                1.
% 12.00/2.00  --trig_cnt_out_sk_spl                   false
% 12.00/2.00  --abstr_cl_out                          false
% 12.00/2.00  
% 12.00/2.00  ------ Global Options
% 12.00/2.00  
% 12.00/2.00  --schedule                              default
% 12.00/2.00  --add_important_lit                     false
% 12.00/2.00  --prop_solver_per_cl                    1000
% 12.00/2.00  --min_unsat_core                        false
% 12.00/2.00  --soft_assumptions                      false
% 12.00/2.00  --soft_lemma_size                       3
% 12.00/2.00  --prop_impl_unit_size                   0
% 12.00/2.00  --prop_impl_unit                        []
% 12.00/2.00  --share_sel_clauses                     true
% 12.00/2.00  --reset_solvers                         false
% 12.00/2.00  --bc_imp_inh                            [conj_cone]
% 12.00/2.00  --conj_cone_tolerance                   3.
% 12.00/2.00  --extra_neg_conj                        none
% 12.00/2.00  --large_theory_mode                     true
% 12.00/2.00  --prolific_symb_bound                   200
% 12.00/2.00  --lt_threshold                          2000
% 12.00/2.00  --clause_weak_htbl                      true
% 12.00/2.00  --gc_record_bc_elim                     false
% 12.00/2.00  
% 12.00/2.00  ------ Preprocessing Options
% 12.00/2.00  
% 12.00/2.00  --preprocessing_flag                    true
% 12.00/2.00  --time_out_prep_mult                    0.1
% 12.00/2.00  --splitting_mode                        input
% 12.00/2.00  --splitting_grd                         true
% 12.00/2.00  --splitting_cvd                         false
% 12.00/2.00  --splitting_cvd_svl                     false
% 12.00/2.00  --splitting_nvd                         32
% 12.00/2.00  --sub_typing                            true
% 12.00/2.00  --prep_gs_sim                           true
% 12.00/2.00  --prep_unflatten                        true
% 12.00/2.00  --prep_res_sim                          true
% 12.00/2.00  --prep_upred                            true
% 12.00/2.00  --prep_sem_filter                       exhaustive
% 12.00/2.00  --prep_sem_filter_out                   false
% 12.00/2.00  --pred_elim                             true
% 12.00/2.00  --res_sim_input                         true
% 12.00/2.00  --eq_ax_congr_red                       true
% 12.00/2.00  --pure_diseq_elim                       true
% 12.00/2.00  --brand_transform                       false
% 12.00/2.00  --non_eq_to_eq                          false
% 12.00/2.00  --prep_def_merge                        true
% 12.00/2.00  --prep_def_merge_prop_impl              false
% 12.00/2.00  --prep_def_merge_mbd                    true
% 12.00/2.00  --prep_def_merge_tr_red                 false
% 12.00/2.00  --prep_def_merge_tr_cl                  false
% 12.00/2.00  --smt_preprocessing                     true
% 12.00/2.00  --smt_ac_axioms                         fast
% 12.00/2.00  --preprocessed_out                      false
% 12.00/2.00  --preprocessed_stats                    false
% 12.00/2.00  
% 12.00/2.00  ------ Abstraction refinement Options
% 12.00/2.00  
% 12.00/2.00  --abstr_ref                             []
% 12.00/2.00  --abstr_ref_prep                        false
% 12.00/2.00  --abstr_ref_until_sat                   false
% 12.00/2.00  --abstr_ref_sig_restrict                funpre
% 12.00/2.00  --abstr_ref_af_restrict_to_split_sk     false
% 12.00/2.00  --abstr_ref_under                       []
% 12.00/2.00  
% 12.00/2.00  ------ SAT Options
% 12.00/2.00  
% 12.00/2.00  --sat_mode                              false
% 12.00/2.00  --sat_fm_restart_options                ""
% 12.00/2.00  --sat_gr_def                            false
% 12.00/2.00  --sat_epr_types                         true
% 12.00/2.00  --sat_non_cyclic_types                  false
% 12.00/2.00  --sat_finite_models                     false
% 12.00/2.00  --sat_fm_lemmas                         false
% 12.00/2.00  --sat_fm_prep                           false
% 12.00/2.00  --sat_fm_uc_incr                        true
% 12.00/2.00  --sat_out_model                         small
% 12.00/2.00  --sat_out_clauses                       false
% 12.00/2.00  
% 12.00/2.00  ------ QBF Options
% 12.00/2.00  
% 12.00/2.00  --qbf_mode                              false
% 12.00/2.00  --qbf_elim_univ                         false
% 12.00/2.00  --qbf_dom_inst                          none
% 12.00/2.00  --qbf_dom_pre_inst                      false
% 12.00/2.00  --qbf_sk_in                             false
% 12.00/2.00  --qbf_pred_elim                         true
% 12.00/2.00  --qbf_split                             512
% 12.00/2.00  
% 12.00/2.00  ------ BMC1 Options
% 12.00/2.00  
% 12.00/2.00  --bmc1_incremental                      false
% 12.00/2.00  --bmc1_axioms                           reachable_all
% 12.00/2.00  --bmc1_min_bound                        0
% 12.00/2.00  --bmc1_max_bound                        -1
% 12.00/2.00  --bmc1_max_bound_default                -1
% 12.00/2.00  --bmc1_symbol_reachability              true
% 12.00/2.00  --bmc1_property_lemmas                  false
% 12.00/2.00  --bmc1_k_induction                      false
% 12.00/2.00  --bmc1_non_equiv_states                 false
% 12.00/2.00  --bmc1_deadlock                         false
% 12.00/2.00  --bmc1_ucm                              false
% 12.00/2.00  --bmc1_add_unsat_core                   none
% 12.00/2.00  --bmc1_unsat_core_children              false
% 12.00/2.00  --bmc1_unsat_core_extrapolate_axioms    false
% 12.00/2.00  --bmc1_out_stat                         full
% 12.00/2.00  --bmc1_ground_init                      false
% 12.00/2.00  --bmc1_pre_inst_next_state              false
% 12.00/2.00  --bmc1_pre_inst_state                   false
% 12.00/2.00  --bmc1_pre_inst_reach_state             false
% 12.00/2.00  --bmc1_out_unsat_core                   false
% 12.00/2.00  --bmc1_aig_witness_out                  false
% 12.00/2.00  --bmc1_verbose                          false
% 12.00/2.00  --bmc1_dump_clauses_tptp                false
% 12.00/2.00  --bmc1_dump_unsat_core_tptp             false
% 12.00/2.00  --bmc1_dump_file                        -
% 12.00/2.00  --bmc1_ucm_expand_uc_limit              128
% 12.00/2.00  --bmc1_ucm_n_expand_iterations          6
% 12.00/2.00  --bmc1_ucm_extend_mode                  1
% 12.00/2.00  --bmc1_ucm_init_mode                    2
% 12.00/2.00  --bmc1_ucm_cone_mode                    none
% 12.00/2.00  --bmc1_ucm_reduced_relation_type        0
% 12.00/2.00  --bmc1_ucm_relax_model                  4
% 12.00/2.00  --bmc1_ucm_full_tr_after_sat            true
% 12.00/2.00  --bmc1_ucm_expand_neg_assumptions       false
% 12.00/2.00  --bmc1_ucm_layered_model                none
% 12.00/2.00  --bmc1_ucm_max_lemma_size               10
% 12.00/2.00  
% 12.00/2.00  ------ AIG Options
% 12.00/2.00  
% 12.00/2.00  --aig_mode                              false
% 12.00/2.00  
% 12.00/2.00  ------ Instantiation Options
% 12.00/2.00  
% 12.00/2.00  --instantiation_flag                    true
% 12.00/2.00  --inst_sos_flag                         true
% 12.00/2.00  --inst_sos_phase                        true
% 12.00/2.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 12.00/2.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 12.00/2.00  --inst_lit_sel_side                     num_symb
% 12.00/2.00  --inst_solver_per_active                1400
% 12.00/2.00  --inst_solver_calls_frac                1.
% 12.00/2.00  --inst_passive_queue_type               priority_queues
% 12.00/2.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 12.00/2.00  --inst_passive_queues_freq              [25;2]
% 12.00/2.00  --inst_dismatching                      true
% 12.00/2.00  --inst_eager_unprocessed_to_passive     true
% 12.00/2.00  --inst_prop_sim_given                   true
% 12.00/2.00  --inst_prop_sim_new                     false
% 12.00/2.00  --inst_subs_new                         false
% 12.00/2.00  --inst_eq_res_simp                      false
% 12.00/2.00  --inst_subs_given                       false
% 12.00/2.00  --inst_orphan_elimination               true
% 12.00/2.00  --inst_learning_loop_flag               true
% 12.00/2.00  --inst_learning_start                   3000
% 12.00/2.00  --inst_learning_factor                  2
% 12.00/2.00  --inst_start_prop_sim_after_learn       3
% 12.00/2.00  --inst_sel_renew                        solver
% 12.00/2.00  --inst_lit_activity_flag                true
% 12.00/2.00  --inst_restr_to_given                   false
% 12.00/2.00  --inst_activity_threshold               500
% 12.00/2.00  --inst_out_proof                        true
% 12.00/2.00  
% 12.00/2.00  ------ Resolution Options
% 12.00/2.00  
% 12.00/2.00  --resolution_flag                       true
% 12.00/2.00  --res_lit_sel                           adaptive
% 12.00/2.00  --res_lit_sel_side                      none
% 12.00/2.00  --res_ordering                          kbo
% 12.00/2.00  --res_to_prop_solver                    active
% 12.00/2.00  --res_prop_simpl_new                    false
% 12.00/2.00  --res_prop_simpl_given                  true
% 12.00/2.00  --res_passive_queue_type                priority_queues
% 12.00/2.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 12.00/2.00  --res_passive_queues_freq               [15;5]
% 12.00/2.00  --res_forward_subs                      full
% 12.00/2.00  --res_backward_subs                     full
% 12.00/2.00  --res_forward_subs_resolution           true
% 12.00/2.00  --res_backward_subs_resolution          true
% 12.00/2.00  --res_orphan_elimination                true
% 12.00/2.00  --res_time_limit                        2.
% 12.00/2.00  --res_out_proof                         true
% 12.00/2.00  
% 12.00/2.00  ------ Superposition Options
% 12.00/2.00  
% 12.00/2.00  --superposition_flag                    true
% 12.00/2.00  --sup_passive_queue_type                priority_queues
% 12.00/2.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 12.00/2.00  --sup_passive_queues_freq               [8;1;4]
% 12.00/2.00  --demod_completeness_check              fast
% 12.00/2.00  --demod_use_ground                      true
% 12.00/2.00  --sup_to_prop_solver                    passive
% 12.00/2.00  --sup_prop_simpl_new                    true
% 12.00/2.00  --sup_prop_simpl_given                  true
% 12.00/2.00  --sup_fun_splitting                     true
% 12.00/2.00  --sup_smt_interval                      50000
% 12.00/2.00  
% 12.00/2.00  ------ Superposition Simplification Setup
% 12.00/2.00  
% 12.00/2.00  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 12.00/2.00  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 12.00/2.00  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 12.00/2.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 12.00/2.00  --sup_full_triv                         [TrivRules;PropSubs]
% 12.00/2.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 12.00/2.00  --sup_full_bw                           [BwDemod;BwSubsumption]
% 12.00/2.00  --sup_immed_triv                        [TrivRules]
% 12.00/2.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 12.00/2.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 12.00/2.00  --sup_immed_bw_main                     []
% 12.00/2.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 12.00/2.00  --sup_input_triv                        [Unflattening;TrivRules]
% 12.00/2.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 12.00/2.00  --sup_input_bw                          []
% 12.00/2.00  
% 12.00/2.00  ------ Combination Options
% 12.00/2.00  
% 12.00/2.00  --comb_res_mult                         3
% 12.00/2.00  --comb_sup_mult                         2
% 12.00/2.00  --comb_inst_mult                        10
% 12.00/2.00  
% 12.00/2.00  ------ Debug Options
% 12.00/2.00  
% 12.00/2.00  --dbg_backtrace                         false
% 12.00/2.00  --dbg_dump_prop_clauses                 false
% 12.00/2.00  --dbg_dump_prop_clauses_file            -
% 12.00/2.00  --dbg_out_stat                          false
% 12.00/2.00  ------ Parsing...
% 12.00/2.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 12.00/2.00  
% 12.00/2.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 12.00/2.00  
% 12.00/2.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 12.00/2.00  
% 12.00/2.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 12.00/2.00  ------ Proving...
% 12.00/2.00  ------ Problem Properties 
% 12.00/2.00  
% 12.00/2.00  
% 12.00/2.00  clauses                                 13
% 12.00/2.00  conjectures                             3
% 12.00/2.00  EPR                                     3
% 12.00/2.00  Horn                                    12
% 12.00/2.00  unary                                   6
% 12.00/2.00  binary                                  5
% 12.00/2.00  lits                                    22
% 12.00/2.00  lits eq                                 4
% 12.00/2.00  fd_pure                                 0
% 12.00/2.00  fd_pseudo                               0
% 12.00/2.00  fd_cond                                 0
% 12.00/2.00  fd_pseudo_cond                          0
% 12.00/2.00  AC symbols                              0
% 12.00/2.00  
% 12.00/2.00  ------ Schedule dynamic 5 is on 
% 12.00/2.00  
% 12.00/2.00  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 12.00/2.00  
% 12.00/2.00  
% 12.00/2.00  ------ 
% 12.00/2.00  Current options:
% 12.00/2.00  ------ 
% 12.00/2.00  
% 12.00/2.00  ------ Input Options
% 12.00/2.00  
% 12.00/2.00  --out_options                           all
% 12.00/2.00  --tptp_safe_out                         true
% 12.00/2.00  --problem_path                          ""
% 12.00/2.00  --include_path                          ""
% 12.00/2.00  --clausifier                            res/vclausify_rel
% 12.00/2.00  --clausifier_options                    ""
% 12.00/2.00  --stdin                                 false
% 12.00/2.00  --stats_out                             all
% 12.00/2.00  
% 12.00/2.00  ------ General Options
% 12.00/2.00  
% 12.00/2.00  --fof                                   false
% 12.00/2.00  --time_out_real                         305.
% 12.00/2.00  --time_out_virtual                      -1.
% 12.00/2.00  --symbol_type_check                     false
% 12.00/2.00  --clausify_out                          false
% 12.00/2.00  --sig_cnt_out                           false
% 12.00/2.00  --trig_cnt_out                          false
% 12.00/2.00  --trig_cnt_out_tolerance                1.
% 12.00/2.00  --trig_cnt_out_sk_spl                   false
% 12.00/2.00  --abstr_cl_out                          false
% 12.00/2.00  
% 12.00/2.00  ------ Global Options
% 12.00/2.00  
% 12.00/2.00  --schedule                              default
% 12.00/2.00  --add_important_lit                     false
% 12.00/2.00  --prop_solver_per_cl                    1000
% 12.00/2.00  --min_unsat_core                        false
% 12.00/2.00  --soft_assumptions                      false
% 12.00/2.00  --soft_lemma_size                       3
% 12.00/2.00  --prop_impl_unit_size                   0
% 12.00/2.00  --prop_impl_unit                        []
% 12.00/2.00  --share_sel_clauses                     true
% 12.00/2.00  --reset_solvers                         false
% 12.00/2.00  --bc_imp_inh                            [conj_cone]
% 12.00/2.00  --conj_cone_tolerance                   3.
% 12.00/2.00  --extra_neg_conj                        none
% 12.00/2.00  --large_theory_mode                     true
% 12.00/2.00  --prolific_symb_bound                   200
% 12.00/2.00  --lt_threshold                          2000
% 12.00/2.00  --clause_weak_htbl                      true
% 12.00/2.00  --gc_record_bc_elim                     false
% 12.00/2.00  
% 12.00/2.00  ------ Preprocessing Options
% 12.00/2.00  
% 12.00/2.00  --preprocessing_flag                    true
% 12.00/2.00  --time_out_prep_mult                    0.1
% 12.00/2.00  --splitting_mode                        input
% 12.00/2.00  --splitting_grd                         true
% 12.00/2.00  --splitting_cvd                         false
% 12.00/2.00  --splitting_cvd_svl                     false
% 12.00/2.00  --splitting_nvd                         32
% 12.00/2.00  --sub_typing                            true
% 12.00/2.00  --prep_gs_sim                           true
% 12.00/2.00  --prep_unflatten                        true
% 12.00/2.00  --prep_res_sim                          true
% 12.00/2.00  --prep_upred                            true
% 12.00/2.00  --prep_sem_filter                       exhaustive
% 12.00/2.00  --prep_sem_filter_out                   false
% 12.00/2.00  --pred_elim                             true
% 12.00/2.00  --res_sim_input                         true
% 12.00/2.00  --eq_ax_congr_red                       true
% 12.00/2.00  --pure_diseq_elim                       true
% 12.00/2.00  --brand_transform                       false
% 12.00/2.00  --non_eq_to_eq                          false
% 12.00/2.00  --prep_def_merge                        true
% 12.00/2.00  --prep_def_merge_prop_impl              false
% 12.00/2.00  --prep_def_merge_mbd                    true
% 12.00/2.00  --prep_def_merge_tr_red                 false
% 12.00/2.00  --prep_def_merge_tr_cl                  false
% 12.00/2.00  --smt_preprocessing                     true
% 12.00/2.00  --smt_ac_axioms                         fast
% 12.00/2.00  --preprocessed_out                      false
% 12.00/2.00  --preprocessed_stats                    false
% 12.00/2.00  
% 12.00/2.00  ------ Abstraction refinement Options
% 12.00/2.00  
% 12.00/2.00  --abstr_ref                             []
% 12.00/2.00  --abstr_ref_prep                        false
% 12.00/2.00  --abstr_ref_until_sat                   false
% 12.00/2.00  --abstr_ref_sig_restrict                funpre
% 12.00/2.00  --abstr_ref_af_restrict_to_split_sk     false
% 12.00/2.00  --abstr_ref_under                       []
% 12.00/2.00  
% 12.00/2.00  ------ SAT Options
% 12.00/2.00  
% 12.00/2.00  --sat_mode                              false
% 12.00/2.00  --sat_fm_restart_options                ""
% 12.00/2.00  --sat_gr_def                            false
% 12.00/2.00  --sat_epr_types                         true
% 12.00/2.00  --sat_non_cyclic_types                  false
% 12.00/2.00  --sat_finite_models                     false
% 12.00/2.00  --sat_fm_lemmas                         false
% 12.00/2.00  --sat_fm_prep                           false
% 12.00/2.00  --sat_fm_uc_incr                        true
% 12.00/2.00  --sat_out_model                         small
% 12.00/2.00  --sat_out_clauses                       false
% 12.00/2.00  
% 12.00/2.00  ------ QBF Options
% 12.00/2.00  
% 12.00/2.00  --qbf_mode                              false
% 12.00/2.00  --qbf_elim_univ                         false
% 12.00/2.00  --qbf_dom_inst                          none
% 12.00/2.00  --qbf_dom_pre_inst                      false
% 12.00/2.00  --qbf_sk_in                             false
% 12.00/2.00  --qbf_pred_elim                         true
% 12.00/2.00  --qbf_split                             512
% 12.00/2.00  
% 12.00/2.00  ------ BMC1 Options
% 12.00/2.00  
% 12.00/2.00  --bmc1_incremental                      false
% 12.00/2.00  --bmc1_axioms                           reachable_all
% 12.00/2.00  --bmc1_min_bound                        0
% 12.00/2.00  --bmc1_max_bound                        -1
% 12.00/2.00  --bmc1_max_bound_default                -1
% 12.00/2.00  --bmc1_symbol_reachability              true
% 12.00/2.00  --bmc1_property_lemmas                  false
% 12.00/2.00  --bmc1_k_induction                      false
% 12.00/2.00  --bmc1_non_equiv_states                 false
% 12.00/2.00  --bmc1_deadlock                         false
% 12.00/2.00  --bmc1_ucm                              false
% 12.00/2.00  --bmc1_add_unsat_core                   none
% 12.00/2.00  --bmc1_unsat_core_children              false
% 12.00/2.00  --bmc1_unsat_core_extrapolate_axioms    false
% 12.00/2.00  --bmc1_out_stat                         full
% 12.00/2.00  --bmc1_ground_init                      false
% 12.00/2.00  --bmc1_pre_inst_next_state              false
% 12.00/2.00  --bmc1_pre_inst_state                   false
% 12.00/2.00  --bmc1_pre_inst_reach_state             false
% 12.00/2.00  --bmc1_out_unsat_core                   false
% 12.00/2.00  --bmc1_aig_witness_out                  false
% 12.00/2.00  --bmc1_verbose                          false
% 12.00/2.00  --bmc1_dump_clauses_tptp                false
% 12.00/2.00  --bmc1_dump_unsat_core_tptp             false
% 12.00/2.00  --bmc1_dump_file                        -
% 12.00/2.00  --bmc1_ucm_expand_uc_limit              128
% 12.00/2.00  --bmc1_ucm_n_expand_iterations          6
% 12.00/2.00  --bmc1_ucm_extend_mode                  1
% 12.00/2.00  --bmc1_ucm_init_mode                    2
% 12.00/2.00  --bmc1_ucm_cone_mode                    none
% 12.00/2.00  --bmc1_ucm_reduced_relation_type        0
% 12.00/2.00  --bmc1_ucm_relax_model                  4
% 12.00/2.00  --bmc1_ucm_full_tr_after_sat            true
% 12.00/2.00  --bmc1_ucm_expand_neg_assumptions       false
% 12.00/2.00  --bmc1_ucm_layered_model                none
% 12.00/2.00  --bmc1_ucm_max_lemma_size               10
% 12.00/2.00  
% 12.00/2.00  ------ AIG Options
% 12.00/2.00  
% 12.00/2.00  --aig_mode                              false
% 12.00/2.00  
% 12.00/2.00  ------ Instantiation Options
% 12.00/2.00  
% 12.00/2.00  --instantiation_flag                    true
% 12.00/2.00  --inst_sos_flag                         true
% 12.00/2.00  --inst_sos_phase                        true
% 12.00/2.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 12.00/2.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 12.00/2.00  --inst_lit_sel_side                     none
% 12.00/2.00  --inst_solver_per_active                1400
% 12.00/2.00  --inst_solver_calls_frac                1.
% 12.00/2.00  --inst_passive_queue_type               priority_queues
% 12.00/2.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 12.00/2.00  --inst_passive_queues_freq              [25;2]
% 12.00/2.00  --inst_dismatching                      true
% 12.00/2.00  --inst_eager_unprocessed_to_passive     true
% 12.00/2.00  --inst_prop_sim_given                   true
% 12.00/2.00  --inst_prop_sim_new                     false
% 12.00/2.00  --inst_subs_new                         false
% 12.00/2.00  --inst_eq_res_simp                      false
% 12.00/2.00  --inst_subs_given                       false
% 12.00/2.00  --inst_orphan_elimination               true
% 12.00/2.00  --inst_learning_loop_flag               true
% 12.00/2.00  --inst_learning_start                   3000
% 12.00/2.00  --inst_learning_factor                  2
% 12.00/2.00  --inst_start_prop_sim_after_learn       3
% 12.00/2.00  --inst_sel_renew                        solver
% 12.00/2.00  --inst_lit_activity_flag                true
% 12.00/2.00  --inst_restr_to_given                   false
% 12.00/2.00  --inst_activity_threshold               500
% 12.00/2.00  --inst_out_proof                        true
% 12.00/2.00  
% 12.00/2.00  ------ Resolution Options
% 12.00/2.00  
% 12.00/2.00  --resolution_flag                       false
% 12.00/2.00  --res_lit_sel                           adaptive
% 12.00/2.00  --res_lit_sel_side                      none
% 12.00/2.00  --res_ordering                          kbo
% 12.00/2.00  --res_to_prop_solver                    active
% 12.00/2.00  --res_prop_simpl_new                    false
% 12.00/2.00  --res_prop_simpl_given                  true
% 12.00/2.00  --res_passive_queue_type                priority_queues
% 12.00/2.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 12.00/2.00  --res_passive_queues_freq               [15;5]
% 12.00/2.00  --res_forward_subs                      full
% 12.00/2.00  --res_backward_subs                     full
% 12.00/2.00  --res_forward_subs_resolution           true
% 12.00/2.00  --res_backward_subs_resolution          true
% 12.00/2.00  --res_orphan_elimination                true
% 12.00/2.00  --res_time_limit                        2.
% 12.00/2.00  --res_out_proof                         true
% 12.00/2.00  
% 12.00/2.00  ------ Superposition Options
% 12.00/2.00  
% 12.00/2.00  --superposition_flag                    true
% 12.00/2.00  --sup_passive_queue_type                priority_queues
% 12.00/2.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 12.00/2.00  --sup_passive_queues_freq               [8;1;4]
% 12.00/2.00  --demod_completeness_check              fast
% 12.00/2.00  --demod_use_ground                      true
% 12.00/2.00  --sup_to_prop_solver                    passive
% 12.00/2.00  --sup_prop_simpl_new                    true
% 12.00/2.00  --sup_prop_simpl_given                  true
% 12.00/2.00  --sup_fun_splitting                     true
% 12.00/2.00  --sup_smt_interval                      50000
% 12.00/2.00  
% 12.00/2.00  ------ Superposition Simplification Setup
% 12.00/2.00  
% 12.00/2.00  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 12.00/2.00  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 12.00/2.00  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 12.00/2.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 12.00/2.00  --sup_full_triv                         [TrivRules;PropSubs]
% 12.00/2.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 12.00/2.00  --sup_full_bw                           [BwDemod;BwSubsumption]
% 12.00/2.00  --sup_immed_triv                        [TrivRules]
% 12.00/2.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 12.00/2.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 12.00/2.00  --sup_immed_bw_main                     []
% 12.00/2.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 12.00/2.00  --sup_input_triv                        [Unflattening;TrivRules]
% 12.00/2.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 12.00/2.00  --sup_input_bw                          []
% 12.00/2.00  
% 12.00/2.00  ------ Combination Options
% 12.00/2.00  
% 12.00/2.00  --comb_res_mult                         3
% 12.00/2.00  --comb_sup_mult                         2
% 12.00/2.00  --comb_inst_mult                        10
% 12.00/2.00  
% 12.00/2.00  ------ Debug Options
% 12.00/2.00  
% 12.00/2.00  --dbg_backtrace                         false
% 12.00/2.00  --dbg_dump_prop_clauses                 false
% 12.00/2.00  --dbg_dump_prop_clauses_file            -
% 12.00/2.00  --dbg_out_stat                          false
% 12.00/2.00  
% 12.00/2.00  
% 12.00/2.00  
% 12.00/2.00  
% 12.00/2.00  ------ Proving...
% 12.00/2.00  
% 12.00/2.00  
% 12.00/2.00  % SZS status Theorem for theBenchmark.p
% 12.00/2.00  
% 12.00/2.00  % SZS output start CNFRefutation for theBenchmark.p
% 12.00/2.00  
% 12.00/2.00  fof(f6,axiom,(
% 12.00/2.00    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 12.00/2.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 12.00/2.00  
% 12.00/2.00  fof(f32,plain,(
% 12.00/2.00    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 12.00/2.00    inference(cnf_transformation,[],[f6])).
% 12.00/2.00  
% 12.00/2.00  fof(f1,axiom,(
% 12.00/2.00    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 12.00/2.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 12.00/2.00  
% 12.00/2.00  fof(f25,plain,(
% 12.00/2.00    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 12.00/2.00    inference(cnf_transformation,[],[f1])).
% 12.00/2.00  
% 12.00/2.00  fof(f7,axiom,(
% 12.00/2.00    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 12.00/2.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 12.00/2.00  
% 12.00/2.00  fof(f33,plain,(
% 12.00/2.00    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 12.00/2.00    inference(cnf_transformation,[],[f7])).
% 12.00/2.00  
% 12.00/2.00  fof(f39,plain,(
% 12.00/2.00    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0))) )),
% 12.00/2.00    inference(definition_unfolding,[],[f25,f33,f33])).
% 12.00/2.00  
% 12.00/2.00  fof(f2,axiom,(
% 12.00/2.00    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 12.00/2.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 12.00/2.00  
% 12.00/2.00  fof(f20,plain,(
% 12.00/2.00    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) & (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)))),
% 12.00/2.00    inference(nnf_transformation,[],[f2])).
% 12.00/2.00  
% 12.00/2.00  fof(f27,plain,(
% 12.00/2.00    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) )),
% 12.00/2.00    inference(cnf_transformation,[],[f20])).
% 12.00/2.00  
% 12.00/2.00  fof(f40,plain,(
% 12.00/2.00    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k1_xboole_0 != k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 12.00/2.00    inference(definition_unfolding,[],[f27,f33])).
% 12.00/2.00  
% 12.00/2.00  fof(f4,axiom,(
% 12.00/2.00    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 12.00/2.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 12.00/2.00  
% 12.00/2.00  fof(f30,plain,(
% 12.00/2.00    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 12.00/2.00    inference(cnf_transformation,[],[f4])).
% 12.00/2.00  
% 12.00/2.00  fof(f44,plain,(
% 12.00/2.00    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0)) )),
% 12.00/2.00    inference(definition_unfolding,[],[f30,f33])).
% 12.00/2.00  
% 12.00/2.00  fof(f8,axiom,(
% 12.00/2.00    ! [X0,X1,X2] : ((r1_xboole_0(X1,X2) & r1_tarski(X0,X1)) => r1_xboole_0(X0,X2))),
% 12.00/2.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 12.00/2.00  
% 12.00/2.00  fof(f16,plain,(
% 12.00/2.00    ! [X0,X1,X2] : (r1_xboole_0(X0,X2) | (~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X1)))),
% 12.00/2.00    inference(ennf_transformation,[],[f8])).
% 12.00/2.00  
% 12.00/2.00  fof(f17,plain,(
% 12.00/2.00    ! [X0,X1,X2] : (r1_xboole_0(X0,X2) | ~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X1))),
% 12.00/2.00    inference(flattening,[],[f16])).
% 12.00/2.00  
% 12.00/2.00  fof(f34,plain,(
% 12.00/2.00    ( ! [X2,X0,X1] : (r1_xboole_0(X0,X2) | ~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X1)) )),
% 12.00/2.00    inference(cnf_transformation,[],[f17])).
% 12.00/2.00  
% 12.00/2.00  fof(f9,axiom,(
% 12.00/2.00    ! [X0,X1] : ~(r1_xboole_0(k3_xboole_0(X0,X1),X1) & ~r1_xboole_0(X0,X1))),
% 12.00/2.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 12.00/2.00  
% 12.00/2.00  fof(f18,plain,(
% 12.00/2.00    ! [X0,X1] : (~r1_xboole_0(k3_xboole_0(X0,X1),X1) | r1_xboole_0(X0,X1))),
% 12.00/2.00    inference(ennf_transformation,[],[f9])).
% 12.00/2.00  
% 12.00/2.00  fof(f35,plain,(
% 12.00/2.00    ( ! [X0,X1] : (~r1_xboole_0(k3_xboole_0(X0,X1),X1) | r1_xboole_0(X0,X1)) )),
% 12.00/2.00    inference(cnf_transformation,[],[f18])).
% 12.00/2.00  
% 12.00/2.00  fof(f46,plain,(
% 12.00/2.00    ( ! [X0,X1] : (~r1_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1) | r1_xboole_0(X0,X1)) )),
% 12.00/2.00    inference(definition_unfolding,[],[f35,f33])).
% 12.00/2.00  
% 12.00/2.00  fof(f26,plain,(
% 12.00/2.00    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)) )),
% 12.00/2.00    inference(cnf_transformation,[],[f20])).
% 12.00/2.00  
% 12.00/2.00  fof(f41,plain,(
% 12.00/2.00    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,X1)) | ~r1_xboole_0(X0,X1)) )),
% 12.00/2.00    inference(definition_unfolding,[],[f26,f33])).
% 12.00/2.00  
% 12.00/2.00  fof(f10,conjecture,(
% 12.00/2.00    ! [X0,X1,X2] : ~(r1_xboole_0(X0,k3_xboole_0(X1,X2)) & r1_tarski(X0,X2) & ~r1_xboole_0(X0,X1))),
% 12.00/2.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 12.00/2.00  
% 12.00/2.00  fof(f11,negated_conjecture,(
% 12.00/2.00    ~! [X0,X1,X2] : ~(r1_xboole_0(X0,k3_xboole_0(X1,X2)) & r1_tarski(X0,X2) & ~r1_xboole_0(X0,X1))),
% 12.00/2.00    inference(negated_conjecture,[],[f10])).
% 12.00/2.00  
% 12.00/2.00  fof(f19,plain,(
% 12.00/2.00    ? [X0,X1,X2] : (r1_xboole_0(X0,k3_xboole_0(X1,X2)) & r1_tarski(X0,X2) & ~r1_xboole_0(X0,X1))),
% 12.00/2.00    inference(ennf_transformation,[],[f11])).
% 12.00/2.00  
% 12.00/2.00  fof(f23,plain,(
% 12.00/2.00    ? [X0,X1,X2] : (r1_xboole_0(X0,k3_xboole_0(X1,X2)) & r1_tarski(X0,X2) & ~r1_xboole_0(X0,X1)) => (r1_xboole_0(sK1,k3_xboole_0(sK2,sK3)) & r1_tarski(sK1,sK3) & ~r1_xboole_0(sK1,sK2))),
% 12.00/2.00    introduced(choice_axiom,[])).
% 12.00/2.00  
% 12.00/2.00  fof(f24,plain,(
% 12.00/2.00    r1_xboole_0(sK1,k3_xboole_0(sK2,sK3)) & r1_tarski(sK1,sK3) & ~r1_xboole_0(sK1,sK2)),
% 12.00/2.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f19,f23])).
% 12.00/2.00  
% 12.00/2.00  fof(f38,plain,(
% 12.00/2.00    r1_xboole_0(sK1,k3_xboole_0(sK2,sK3))),
% 12.00/2.00    inference(cnf_transformation,[],[f24])).
% 12.00/2.00  
% 12.00/2.00  fof(f47,plain,(
% 12.00/2.00    r1_xboole_0(sK1,k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)))),
% 12.00/2.00    inference(definition_unfolding,[],[f38,f33])).
% 12.00/2.00  
% 12.00/2.00  fof(f5,axiom,(
% 12.00/2.00    ! [X0,X1,X2,X3] : ((r1_tarski(X2,X3) & r1_tarski(X0,X1)) => r1_tarski(k3_xboole_0(X0,X2),k3_xboole_0(X1,X3)))),
% 12.00/2.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 12.00/2.00  
% 12.00/2.00  fof(f14,plain,(
% 12.00/2.00    ! [X0,X1,X2,X3] : (r1_tarski(k3_xboole_0(X0,X2),k3_xboole_0(X1,X3)) | (~r1_tarski(X2,X3) | ~r1_tarski(X0,X1)))),
% 12.00/2.00    inference(ennf_transformation,[],[f5])).
% 12.00/2.00  
% 12.00/2.00  fof(f15,plain,(
% 12.00/2.00    ! [X0,X1,X2,X3] : (r1_tarski(k3_xboole_0(X0,X2),k3_xboole_0(X1,X3)) | ~r1_tarski(X2,X3) | ~r1_tarski(X0,X1))),
% 12.00/2.00    inference(flattening,[],[f14])).
% 12.00/2.00  
% 12.00/2.00  fof(f31,plain,(
% 12.00/2.00    ( ! [X2,X0,X3,X1] : (r1_tarski(k3_xboole_0(X0,X2),k3_xboole_0(X1,X3)) | ~r1_tarski(X2,X3) | ~r1_tarski(X0,X1)) )),
% 12.00/2.00    inference(cnf_transformation,[],[f15])).
% 12.00/2.00  
% 12.00/2.00  fof(f45,plain,(
% 12.00/2.00    ( ! [X2,X0,X3,X1] : (r1_tarski(k4_xboole_0(X0,k4_xboole_0(X0,X2)),k4_xboole_0(X1,k4_xboole_0(X1,X3))) | ~r1_tarski(X2,X3) | ~r1_tarski(X0,X1)) )),
% 12.00/2.00    inference(definition_unfolding,[],[f31,f33,f33])).
% 12.00/2.00  
% 12.00/2.00  fof(f37,plain,(
% 12.00/2.00    r1_tarski(sK1,sK3)),
% 12.00/2.00    inference(cnf_transformation,[],[f24])).
% 12.00/2.00  
% 12.00/2.00  fof(f36,plain,(
% 12.00/2.00    ~r1_xboole_0(sK1,sK2)),
% 12.00/2.00    inference(cnf_transformation,[],[f24])).
% 12.00/2.00  
% 12.00/2.00  cnf(c_7,plain,
% 12.00/2.00      ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
% 12.00/2.00      inference(cnf_transformation,[],[f32]) ).
% 12.00/2.00  
% 12.00/2.00  cnf(c_0,plain,
% 12.00/2.00      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
% 12.00/2.00      inference(cnf_transformation,[],[f39]) ).
% 12.00/2.00  
% 12.00/2.00  cnf(c_756,plain,
% 12.00/2.00      ( k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0)) = k4_xboole_0(X0,X0) ),
% 12.00/2.00      inference(superposition,[status(thm)],[c_7,c_0]) ).
% 12.00/2.00  
% 12.00/2.00  cnf(c_1,plain,
% 12.00/2.00      ( r1_xboole_0(X0,X1)
% 12.00/2.00      | k4_xboole_0(X0,k4_xboole_0(X0,X1)) != k1_xboole_0 ),
% 12.00/2.00      inference(cnf_transformation,[],[f40]) ).
% 12.00/2.00  
% 12.00/2.00  cnf(c_457,plain,
% 12.00/2.00      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) != k1_xboole_0
% 12.00/2.00      | r1_xboole_0(X0,X1) = iProver_top ),
% 12.00/2.00      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 12.00/2.00  
% 12.00/2.00  cnf(c_1293,plain,
% 12.00/2.00      ( k4_xboole_0(X0,X0) != k1_xboole_0
% 12.00/2.00      | r1_xboole_0(X0,k1_xboole_0) = iProver_top ),
% 12.00/2.00      inference(superposition,[status(thm)],[c_7,c_457]) ).
% 12.00/2.00  
% 12.00/2.00  cnf(c_1782,plain,
% 12.00/2.00      ( k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0)) != k1_xboole_0
% 12.00/2.00      | r1_xboole_0(X0,k1_xboole_0) = iProver_top ),
% 12.00/2.00      inference(superposition,[status(thm)],[c_756,c_1293]) ).
% 12.00/2.00  
% 12.00/2.00  cnf(c_20,plain,
% 12.00/2.00      ( k4_xboole_0(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
% 12.00/2.00      inference(instantiation,[status(thm)],[c_7]) ).
% 12.00/2.00  
% 12.00/2.00  cnf(c_1290,plain,
% 12.00/2.00      ( k4_xboole_0(X0,X0) != k1_xboole_0
% 12.00/2.00      | r1_xboole_0(k1_xboole_0,X0) = iProver_top ),
% 12.00/2.00      inference(superposition,[status(thm)],[c_756,c_457]) ).
% 12.00/2.00  
% 12.00/2.00  cnf(c_1300,plain,
% 12.00/2.00      ( k4_xboole_0(k1_xboole_0,k1_xboole_0) != k1_xboole_0
% 12.00/2.00      | r1_xboole_0(k1_xboole_0,k1_xboole_0) = iProver_top ),
% 12.00/2.00      inference(instantiation,[status(thm)],[c_1290]) ).
% 12.00/2.00  
% 12.00/2.00  cnf(c_5,plain,
% 12.00/2.00      ( r1_tarski(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0) ),
% 12.00/2.00      inference(cnf_transformation,[],[f44]) ).
% 12.00/2.00  
% 12.00/2.00  cnf(c_453,plain,
% 12.00/2.00      ( r1_tarski(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0) = iProver_top ),
% 12.00/2.00      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 12.00/2.00  
% 12.00/2.00  cnf(c_825,plain,
% 12.00/2.00      ( r1_tarski(k4_xboole_0(X0,X0),k1_xboole_0) = iProver_top ),
% 12.00/2.00      inference(superposition,[status(thm)],[c_756,c_453]) ).
% 12.00/2.00  
% 12.00/2.00  cnf(c_8,plain,
% 12.00/2.00      ( ~ r1_tarski(X0,X1) | ~ r1_xboole_0(X1,X2) | r1_xboole_0(X0,X2) ),
% 12.00/2.00      inference(cnf_transformation,[],[f34]) ).
% 12.00/2.00  
% 12.00/2.00  cnf(c_451,plain,
% 12.00/2.00      ( r1_tarski(X0,X1) != iProver_top
% 12.00/2.00      | r1_xboole_0(X1,X2) != iProver_top
% 12.00/2.00      | r1_xboole_0(X0,X2) = iProver_top ),
% 12.00/2.00      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 12.00/2.00  
% 12.00/2.00  cnf(c_1148,plain,
% 12.00/2.00      ( r1_xboole_0(k4_xboole_0(X0,X0),X1) = iProver_top
% 12.00/2.00      | r1_xboole_0(k1_xboole_0,X1) != iProver_top ),
% 12.00/2.00      inference(superposition,[status(thm)],[c_825,c_451]) ).
% 12.00/2.00  
% 12.00/2.00  cnf(c_9,plain,
% 12.00/2.00      ( r1_xboole_0(X0,X1)
% 12.00/2.00      | ~ r1_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1) ),
% 12.00/2.00      inference(cnf_transformation,[],[f46]) ).
% 12.00/2.00  
% 12.00/2.00  cnf(c_450,plain,
% 12.00/2.00      ( r1_xboole_0(X0,X1) = iProver_top
% 12.00/2.00      | r1_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1) != iProver_top ),
% 12.00/2.00      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 12.00/2.00  
% 12.00/2.00  cnf(c_811,plain,
% 12.00/2.00      ( r1_xboole_0(X0,k1_xboole_0) = iProver_top
% 12.00/2.00      | r1_xboole_0(k4_xboole_0(X0,X0),k1_xboole_0) != iProver_top ),
% 12.00/2.00      inference(superposition,[status(thm)],[c_7,c_450]) ).
% 12.00/2.00  
% 12.00/2.00  cnf(c_15476,plain,
% 12.00/2.00      ( r1_xboole_0(X0,k1_xboole_0) = iProver_top
% 12.00/2.00      | r1_xboole_0(k1_xboole_0,k1_xboole_0) != iProver_top ),
% 12.00/2.00      inference(superposition,[status(thm)],[c_1148,c_811]) ).
% 12.00/2.00  
% 12.00/2.00  cnf(c_39559,plain,
% 12.00/2.00      ( r1_xboole_0(X0,k1_xboole_0) = iProver_top ),
% 12.00/2.00      inference(global_propositional_subsumption,
% 12.00/2.00                [status(thm)],
% 12.00/2.00                [c_1782,c_20,c_1300,c_15476]) ).
% 12.00/2.00  
% 12.00/2.00  cnf(c_2,plain,
% 12.00/2.00      ( ~ r1_xboole_0(X0,X1)
% 12.00/2.00      | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_xboole_0 ),
% 12.00/2.00      inference(cnf_transformation,[],[f41]) ).
% 12.00/2.00  
% 12.00/2.00  cnf(c_456,plain,
% 12.00/2.00      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_xboole_0
% 12.00/2.00      | r1_xboole_0(X0,X1) != iProver_top ),
% 12.00/2.00      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 12.00/2.00  
% 12.00/2.00  cnf(c_39563,plain,
% 12.00/2.00      ( k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) = k1_xboole_0 ),
% 12.00/2.00      inference(superposition,[status(thm)],[c_39559,c_456]) ).
% 12.00/2.00  
% 12.00/2.00  cnf(c_39584,plain,
% 12.00/2.00      ( k4_xboole_0(X0,X0) = k1_xboole_0 ),
% 12.00/2.00      inference(light_normalisation,[status(thm)],[c_39563,c_7]) ).
% 12.00/2.00  
% 12.00/2.00  cnf(c_761,plain,
% 12.00/2.00      ( r1_tarski(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1) = iProver_top ),
% 12.00/2.00      inference(superposition,[status(thm)],[c_0,c_453]) ).
% 12.00/2.00  
% 12.00/2.00  cnf(c_872,plain,
% 12.00/2.00      ( r1_tarski(k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0))),k4_xboole_0(X0,X1)) = iProver_top ),
% 12.00/2.00      inference(superposition,[status(thm)],[c_0,c_761]) ).
% 12.00/2.00  
% 12.00/2.00  cnf(c_934,plain,
% 12.00/2.00      ( r1_tarski(k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X0,X1),X0))),k4_xboole_0(X1,k4_xboole_0(X1,X0))) = iProver_top ),
% 12.00/2.00      inference(superposition,[status(thm)],[c_0,c_872]) ).
% 12.00/2.00  
% 12.00/2.00  cnf(c_39866,plain,
% 12.00/2.00      ( r1_tarski(k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(X0,X0),k4_xboole_0(k4_xboole_0(X0,X0),X0))),k4_xboole_0(X0,k1_xboole_0)) = iProver_top ),
% 12.00/2.00      inference(superposition,[status(thm)],[c_39584,c_934]) ).
% 12.00/2.00  
% 12.00/2.00  cnf(c_40120,plain,
% 12.00/2.00      ( r1_tarski(k4_xboole_0(X0,k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0))),k4_xboole_0(X0,k1_xboole_0)) = iProver_top ),
% 12.00/2.00      inference(demodulation,[status(thm)],[c_39866,c_39584]) ).
% 12.00/2.00  
% 12.00/2.00  cnf(c_39636,plain,
% 12.00/2.00      ( k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0)) = k1_xboole_0 ),
% 12.00/2.00      inference(demodulation,[status(thm)],[c_39584,c_756]) ).
% 12.00/2.00  
% 12.00/2.00  cnf(c_40121,plain,
% 12.00/2.00      ( r1_tarski(X0,X0) = iProver_top ),
% 12.00/2.00      inference(light_normalisation,[status(thm)],[c_40120,c_7,c_39636]) ).
% 12.00/2.00  
% 12.00/2.00  cnf(c_10,negated_conjecture,
% 12.00/2.00      ( r1_xboole_0(sK1,k4_xboole_0(sK2,k4_xboole_0(sK2,sK3))) ),
% 12.00/2.00      inference(cnf_transformation,[],[f47]) ).
% 12.00/2.00  
% 12.00/2.00  cnf(c_449,plain,
% 12.00/2.00      ( r1_xboole_0(sK1,k4_xboole_0(sK2,k4_xboole_0(sK2,sK3))) = iProver_top ),
% 12.00/2.00      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 12.00/2.00  
% 12.00/2.00  cnf(c_1072,plain,
% 12.00/2.00      ( k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)))) = k1_xboole_0 ),
% 12.00/2.00      inference(superposition,[status(thm)],[c_449,c_456]) ).
% 12.00/2.00  
% 12.00/2.00  cnf(c_1287,plain,
% 12.00/2.00      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) != k1_xboole_0
% 12.00/2.01      | r1_xboole_0(X1,X0) = iProver_top ),
% 12.00/2.01      inference(superposition,[status(thm)],[c_0,c_457]) ).
% 12.00/2.01  
% 12.00/2.01  cnf(c_2279,plain,
% 12.00/2.01      ( r1_xboole_0(k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)),sK1) = iProver_top ),
% 12.00/2.01      inference(superposition,[status(thm)],[c_1072,c_1287]) ).
% 12.00/2.01  
% 12.00/2.01  cnf(c_6,plain,
% 12.00/2.01      ( ~ r1_tarski(X0,X1)
% 12.00/2.01      | ~ r1_tarski(X2,X3)
% 12.00/2.01      | r1_tarski(k4_xboole_0(X2,k4_xboole_0(X2,X0)),k4_xboole_0(X3,k4_xboole_0(X3,X1))) ),
% 12.00/2.01      inference(cnf_transformation,[],[f45]) ).
% 12.00/2.01  
% 12.00/2.01  cnf(c_452,plain,
% 12.00/2.01      ( r1_tarski(X0,X1) != iProver_top
% 12.00/2.01      | r1_tarski(X2,X3) != iProver_top
% 12.00/2.01      | r1_tarski(k4_xboole_0(X2,k4_xboole_0(X2,X0)),k4_xboole_0(X3,k4_xboole_0(X3,X1))) = iProver_top ),
% 12.00/2.01      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 12.00/2.01  
% 12.00/2.01  cnf(c_1693,plain,
% 12.00/2.01      ( r1_tarski(X0,X1) != iProver_top
% 12.00/2.01      | r1_tarski(X2,X3) != iProver_top
% 12.00/2.01      | r1_xboole_0(k4_xboole_0(X3,k4_xboole_0(X3,X1)),X4) != iProver_top
% 12.00/2.01      | r1_xboole_0(k4_xboole_0(X2,k4_xboole_0(X2,X0)),X4) = iProver_top ),
% 12.00/2.01      inference(superposition,[status(thm)],[c_452,c_451]) ).
% 12.00/2.01  
% 12.00/2.01  cnf(c_36852,plain,
% 12.00/2.01      ( r1_tarski(X0,sK3) != iProver_top
% 12.00/2.01      | r1_tarski(X1,sK2) != iProver_top
% 12.00/2.01      | r1_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),sK1) = iProver_top ),
% 12.00/2.01      inference(superposition,[status(thm)],[c_2279,c_1693]) ).
% 12.00/2.01  
% 12.00/2.01  cnf(c_37641,plain,
% 12.00/2.01      ( r1_tarski(X0,sK2) != iProver_top
% 12.00/2.01      | r1_tarski(sK1,sK3) != iProver_top
% 12.00/2.01      | r1_xboole_0(X0,sK1) = iProver_top ),
% 12.00/2.01      inference(superposition,[status(thm)],[c_36852,c_450]) ).
% 12.00/2.01  
% 12.00/2.01  cnf(c_11,negated_conjecture,
% 12.00/2.01      ( r1_tarski(sK1,sK3) ),
% 12.00/2.01      inference(cnf_transformation,[],[f37]) ).
% 12.00/2.01  
% 12.00/2.01  cnf(c_14,plain,
% 12.00/2.01      ( r1_tarski(sK1,sK3) = iProver_top ),
% 12.00/2.01      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 12.00/2.01  
% 12.00/2.01  cnf(c_40947,plain,
% 12.00/2.01      ( r1_tarski(X0,sK2) != iProver_top
% 12.00/2.01      | r1_xboole_0(X0,sK1) = iProver_top ),
% 12.00/2.01      inference(global_propositional_subsumption,
% 12.00/2.01                [status(thm)],
% 12.00/2.01                [c_37641,c_14]) ).
% 12.00/2.01  
% 12.00/2.01  cnf(c_40954,plain,
% 12.00/2.01      ( r1_xboole_0(sK2,sK1) = iProver_top ),
% 12.00/2.01      inference(superposition,[status(thm)],[c_40121,c_40947]) ).
% 12.00/2.01  
% 12.00/2.01  cnf(c_1247,plain,
% 12.00/2.01      ( ~ r1_xboole_0(sK2,sK1)
% 12.00/2.01      | k4_xboole_0(sK2,k4_xboole_0(sK2,sK1)) = k1_xboole_0 ),
% 12.00/2.01      inference(instantiation,[status(thm)],[c_2]) ).
% 12.00/2.01  
% 12.00/2.01  cnf(c_1248,plain,
% 12.00/2.01      ( k4_xboole_0(sK2,k4_xboole_0(sK2,sK1)) = k1_xboole_0
% 12.00/2.01      | r1_xboole_0(sK2,sK1) != iProver_top ),
% 12.00/2.01      inference(predicate_to_equality,[status(thm)],[c_1247]) ).
% 12.00/2.01  
% 12.00/2.01  cnf(c_976,plain,
% 12.00/2.01      ( k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)) = k4_xboole_0(sK2,k4_xboole_0(sK2,sK1)) ),
% 12.00/2.01      inference(instantiation,[status(thm)],[c_0]) ).
% 12.00/2.01  
% 12.00/2.01  cnf(c_171,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 12.00/2.01  
% 12.00/2.01  cnf(c_697,plain,
% 12.00/2.01      ( k4_xboole_0(sK2,k4_xboole_0(sK2,sK1)) != X0
% 12.00/2.01      | k1_xboole_0 != X0
% 12.00/2.01      | k1_xboole_0 = k4_xboole_0(sK2,k4_xboole_0(sK2,sK1)) ),
% 12.00/2.01      inference(instantiation,[status(thm)],[c_171]) ).
% 12.00/2.01  
% 12.00/2.01  cnf(c_698,plain,
% 12.00/2.01      ( k4_xboole_0(sK2,k4_xboole_0(sK2,sK1)) != k1_xboole_0
% 12.00/2.01      | k1_xboole_0 = k4_xboole_0(sK2,k4_xboole_0(sK2,sK1))
% 12.00/2.01      | k1_xboole_0 != k1_xboole_0 ),
% 12.00/2.01      inference(instantiation,[status(thm)],[c_697]) ).
% 12.00/2.01  
% 12.00/2.01  cnf(c_499,plain,
% 12.00/2.01      ( k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)) != X0
% 12.00/2.01      | k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)) = k1_xboole_0
% 12.00/2.01      | k1_xboole_0 != X0 ),
% 12.00/2.01      inference(instantiation,[status(thm)],[c_171]) ).
% 12.00/2.01  
% 12.00/2.01  cnf(c_587,plain,
% 12.00/2.01      ( k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)) != k4_xboole_0(sK2,k4_xboole_0(sK2,sK1))
% 12.00/2.01      | k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)) = k1_xboole_0
% 12.00/2.01      | k1_xboole_0 != k4_xboole_0(sK2,k4_xboole_0(sK2,sK1)) ),
% 12.00/2.01      inference(instantiation,[status(thm)],[c_499]) ).
% 12.00/2.01  
% 12.00/2.01  cnf(c_477,plain,
% 12.00/2.01      ( r1_xboole_0(sK1,sK2)
% 12.00/2.01      | k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)) != k1_xboole_0 ),
% 12.00/2.01      inference(instantiation,[status(thm)],[c_1]) ).
% 12.00/2.01  
% 12.00/2.01  cnf(c_170,plain,( X0 = X0 ),theory(equality) ).
% 12.00/2.01  
% 12.00/2.01  cnf(c_181,plain,
% 12.00/2.01      ( k1_xboole_0 = k1_xboole_0 ),
% 12.00/2.01      inference(instantiation,[status(thm)],[c_170]) ).
% 12.00/2.01  
% 12.00/2.01  cnf(c_12,negated_conjecture,
% 12.00/2.01      ( ~ r1_xboole_0(sK1,sK2) ),
% 12.00/2.01      inference(cnf_transformation,[],[f36]) ).
% 12.00/2.01  
% 12.00/2.01  cnf(contradiction,plain,
% 12.00/2.01      ( $false ),
% 12.00/2.01      inference(minisat,
% 12.00/2.01                [status(thm)],
% 12.00/2.01                [c_40954,c_1248,c_976,c_698,c_587,c_477,c_181,c_12]) ).
% 12.00/2.01  
% 12.00/2.01  
% 12.00/2.01  % SZS output end CNFRefutation for theBenchmark.p
% 12.00/2.01  
% 12.00/2.01  ------                               Statistics
% 12.00/2.01  
% 12.00/2.01  ------ General
% 12.00/2.01  
% 12.00/2.01  abstr_ref_over_cycles:                  0
% 12.00/2.01  abstr_ref_under_cycles:                 0
% 12.00/2.01  gc_basic_clause_elim:                   0
% 12.00/2.01  forced_gc_time:                         0
% 12.00/2.01  parsing_time:                           0.008
% 12.00/2.01  unif_index_cands_time:                  0.
% 12.00/2.01  unif_index_add_time:                    0.
% 12.00/2.01  orderings_time:                         0.
% 12.00/2.01  out_proof_time:                         0.011
% 12.00/2.01  total_time:                             1.335
% 12.00/2.01  num_of_symbols:                         40
% 12.00/2.01  num_of_terms:                           28452
% 12.00/2.01  
% 12.00/2.01  ------ Preprocessing
% 12.00/2.01  
% 12.00/2.01  num_of_splits:                          0
% 12.00/2.01  num_of_split_atoms:                     0
% 12.00/2.01  num_of_reused_defs:                     0
% 12.00/2.01  num_eq_ax_congr_red:                    4
% 12.00/2.01  num_of_sem_filtered_clauses:            1
% 12.00/2.01  num_of_subtypes:                        0
% 12.00/2.01  monotx_restored_types:                  0
% 12.00/2.01  sat_num_of_epr_types:                   0
% 12.00/2.01  sat_num_of_non_cyclic_types:            0
% 12.00/2.01  sat_guarded_non_collapsed_types:        0
% 12.00/2.01  num_pure_diseq_elim:                    0
% 12.00/2.01  simp_replaced_by:                       0
% 12.00/2.01  res_preprocessed:                       52
% 12.00/2.01  prep_upred:                             0
% 12.00/2.01  prep_unflattend:                        1
% 12.00/2.01  smt_new_axioms:                         0
% 12.00/2.01  pred_elim_cands:                        3
% 12.00/2.01  pred_elim:                              0
% 12.00/2.01  pred_elim_cl:                           0
% 12.00/2.01  pred_elim_cycles:                       1
% 12.00/2.01  merged_defs:                            6
% 12.00/2.01  merged_defs_ncl:                        0
% 12.00/2.01  bin_hyper_res:                          6
% 12.00/2.01  prep_cycles:                            3
% 12.00/2.01  pred_elim_time:                         0.
% 12.00/2.01  splitting_time:                         0.
% 12.00/2.01  sem_filter_time:                        0.
% 12.00/2.01  monotx_time:                            0.001
% 12.00/2.01  subtype_inf_time:                       0.
% 12.00/2.01  
% 12.00/2.01  ------ Problem properties
% 12.00/2.01  
% 12.00/2.01  clauses:                                13
% 12.00/2.01  conjectures:                            3
% 12.00/2.01  epr:                                    3
% 12.00/2.01  horn:                                   12
% 12.00/2.01  ground:                                 3
% 12.00/2.01  unary:                                  6
% 12.00/2.01  binary:                                 5
% 12.00/2.01  lits:                                   22
% 12.00/2.01  lits_eq:                                4
% 12.00/2.01  fd_pure:                                0
% 12.00/2.01  fd_pseudo:                              0
% 12.00/2.01  fd_cond:                                0
% 12.00/2.01  fd_pseudo_cond:                         0
% 12.00/2.01  ac_symbols:                             0
% 12.00/2.01  
% 12.00/2.01  ------ Propositional Solver
% 12.00/2.01  
% 12.00/2.01  prop_solver_calls:                      32
% 12.00/2.01  prop_fast_solver_calls:                 1243
% 12.00/2.01  smt_solver_calls:                       0
% 12.00/2.01  smt_fast_solver_calls:                  0
% 12.00/2.01  prop_num_of_clauses:                    13755
% 12.00/2.01  prop_preprocess_simplified:             20475
% 12.00/2.01  prop_fo_subsumed:                       37
% 12.00/2.01  prop_solver_time:                       0.
% 12.00/2.01  smt_solver_time:                        0.
% 12.00/2.01  smt_fast_solver_time:                   0.
% 12.00/2.01  prop_fast_solver_time:                  0.
% 12.00/2.01  prop_unsat_core_time:                   0.001
% 12.00/2.01  
% 12.00/2.01  ------ QBF
% 12.00/2.01  
% 12.00/2.01  qbf_q_res:                              0
% 12.00/2.01  qbf_num_tautologies:                    0
% 12.00/2.01  qbf_prep_cycles:                        0
% 12.00/2.01  
% 12.00/2.01  ------ BMC1
% 12.00/2.01  
% 12.00/2.01  bmc1_current_bound:                     -1
% 12.00/2.01  bmc1_last_solved_bound:                 -1
% 12.00/2.01  bmc1_unsat_core_size:                   -1
% 12.00/2.01  bmc1_unsat_core_parents_size:           -1
% 12.00/2.01  bmc1_merge_next_fun:                    0
% 12.00/2.01  bmc1_unsat_core_clauses_time:           0.
% 12.00/2.01  
% 12.00/2.01  ------ Instantiation
% 12.00/2.01  
% 12.00/2.01  inst_num_of_clauses:                    4912
% 12.00/2.01  inst_num_in_passive:                    845
% 12.00/2.01  inst_num_in_active:                     1993
% 12.00/2.01  inst_num_in_unprocessed:                2074
% 12.00/2.01  inst_num_of_loops:                      2190
% 12.00/2.01  inst_num_of_learning_restarts:          0
% 12.00/2.01  inst_num_moves_active_passive:          191
% 12.00/2.01  inst_lit_activity:                      0
% 12.00/2.01  inst_lit_activity_moves:                0
% 12.00/2.01  inst_num_tautologies:                   0
% 12.00/2.01  inst_num_prop_implied:                  0
% 12.00/2.01  inst_num_existing_simplified:           0
% 12.00/2.01  inst_num_eq_res_simplified:             0
% 12.00/2.01  inst_num_child_elim:                    0
% 12.00/2.01  inst_num_of_dismatching_blockings:      5750
% 12.00/2.01  inst_num_of_non_proper_insts:           6623
% 12.00/2.01  inst_num_of_duplicates:                 0
% 12.00/2.01  inst_inst_num_from_inst_to_res:         0
% 12.00/2.01  inst_dismatching_checking_time:         0.
% 12.00/2.01  
% 12.00/2.01  ------ Resolution
% 12.00/2.01  
% 12.00/2.01  res_num_of_clauses:                     0
% 12.00/2.01  res_num_in_passive:                     0
% 12.00/2.01  res_num_in_active:                      0
% 12.00/2.01  res_num_of_loops:                       55
% 12.00/2.01  res_forward_subset_subsumed:            735
% 12.00/2.01  res_backward_subset_subsumed:           4
% 12.00/2.01  res_forward_subsumed:                   0
% 12.00/2.01  res_backward_subsumed:                  0
% 12.00/2.01  res_forward_subsumption_resolution:     0
% 12.00/2.01  res_backward_subsumption_resolution:    0
% 12.00/2.01  res_clause_to_clause_subsumption:       18881
% 12.00/2.01  res_orphan_elimination:                 0
% 12.00/2.01  res_tautology_del:                      605
% 12.00/2.01  res_num_eq_res_simplified:              0
% 12.00/2.01  res_num_sel_changes:                    0
% 12.00/2.01  res_moves_from_active_to_pass:          0
% 12.00/2.01  
% 12.00/2.01  ------ Superposition
% 12.00/2.01  
% 12.00/2.01  sup_time_total:                         0.
% 12.00/2.01  sup_time_generating:                    0.
% 12.00/2.01  sup_time_sim_full:                      0.
% 12.00/2.01  sup_time_sim_immed:                     0.
% 12.00/2.01  
% 12.00/2.01  sup_num_of_clauses:                     1268
% 12.00/2.01  sup_num_in_active:                      323
% 12.00/2.01  sup_num_in_passive:                     945
% 12.00/2.01  sup_num_of_loops:                       436
% 12.00/2.01  sup_fw_superposition:                   4063
% 12.00/2.01  sup_bw_superposition:                   958
% 12.00/2.01  sup_immediate_simplified:               1964
% 12.00/2.01  sup_given_eliminated:                   0
% 12.00/2.01  comparisons_done:                       0
% 12.00/2.01  comparisons_avoided:                    0
% 12.00/2.01  
% 12.00/2.01  ------ Simplifications
% 12.00/2.01  
% 12.00/2.01  
% 12.00/2.01  sim_fw_subset_subsumed:                 180
% 12.00/2.01  sim_bw_subset_subsumed:                 17
% 12.00/2.01  sim_fw_subsumed:                        562
% 12.00/2.01  sim_bw_subsumed:                        37
% 12.00/2.01  sim_fw_subsumption_res:                 0
% 12.00/2.01  sim_bw_subsumption_res:                 0
% 12.00/2.01  sim_tautology_del:                      250
% 12.00/2.01  sim_eq_tautology_del:                   2
% 12.00/2.01  sim_eq_res_simp:                        35
% 12.00/2.01  sim_fw_demodulated:                     1254
% 12.00/2.01  sim_bw_demodulated:                     91
% 12.00/2.01  sim_light_normalised:                   592
% 12.00/2.01  sim_joinable_taut:                      0
% 12.00/2.01  sim_joinable_simp:                      0
% 12.00/2.01  sim_ac_normalised:                      0
% 12.00/2.01  sim_smt_subsumption:                    0
% 12.00/2.01  
%------------------------------------------------------------------------------
