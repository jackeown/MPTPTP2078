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
% DateTime   : Thu Dec  3 11:36:22 EST 2020

% Result     : Theorem 3.55s
% Output     : CNFRefutation 3.55s
% Verified   : 
% Statistics : Number of formulae       :  105 ( 556 expanded)
%              Number of clauses        :   50 ( 117 expanded)
%              Number of leaves         :   15 ( 147 expanded)
%              Depth                    :   16
%              Number of atoms          :  226 (1465 expanded)
%              Number of equality atoms :   88 ( 605 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal clause size      :   12 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f14,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f54,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f14])).

fof(f15,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f55,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1) ),
    inference(cnf_transformation,[],[f15])).

fof(f71,plain,(
    ! [X0,X1] : k3_enumset1(X0,X0,X0,X0,X1) = k3_enumset1(X1,X1,X1,X1,X0) ),
    inference(definition_unfolding,[],[f54,f55,f55])).

fof(f21,conjecture,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(k2_tarski(X0,X1),X2) = k2_tarski(X0,X1)
    <=> ( ~ r2_hidden(X1,X2)
        & ~ r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( k4_xboole_0(k2_tarski(X0,X1),X2) = k2_tarski(X0,X1)
      <=> ( ~ r2_hidden(X1,X2)
          & ~ r2_hidden(X0,X2) ) ) ),
    inference(negated_conjecture,[],[f21])).

fof(f28,plain,(
    ? [X0,X1,X2] :
      ( k4_xboole_0(k2_tarski(X0,X1),X2) = k2_tarski(X0,X1)
    <~> ( ~ r2_hidden(X1,X2)
        & ~ r2_hidden(X0,X2) ) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f33,plain,(
    ? [X0,X1,X2] :
      ( ( r2_hidden(X1,X2)
        | r2_hidden(X0,X2)
        | k4_xboole_0(k2_tarski(X0,X1),X2) != k2_tarski(X0,X1) )
      & ( ( ~ r2_hidden(X1,X2)
          & ~ r2_hidden(X0,X2) )
        | k4_xboole_0(k2_tarski(X0,X1),X2) = k2_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f28])).

fof(f34,plain,(
    ? [X0,X1,X2] :
      ( ( r2_hidden(X1,X2)
        | r2_hidden(X0,X2)
        | k4_xboole_0(k2_tarski(X0,X1),X2) != k2_tarski(X0,X1) )
      & ( ( ~ r2_hidden(X1,X2)
          & ~ r2_hidden(X0,X2) )
        | k4_xboole_0(k2_tarski(X0,X1),X2) = k2_tarski(X0,X1) ) ) ),
    inference(flattening,[],[f33])).

fof(f35,plain,
    ( ? [X0,X1,X2] :
        ( ( r2_hidden(X1,X2)
          | r2_hidden(X0,X2)
          | k4_xboole_0(k2_tarski(X0,X1),X2) != k2_tarski(X0,X1) )
        & ( ( ~ r2_hidden(X1,X2)
            & ~ r2_hidden(X0,X2) )
          | k4_xboole_0(k2_tarski(X0,X1),X2) = k2_tarski(X0,X1) ) )
   => ( ( r2_hidden(sK1,sK2)
        | r2_hidden(sK0,sK2)
        | k4_xboole_0(k2_tarski(sK0,sK1),sK2) != k2_tarski(sK0,sK1) )
      & ( ( ~ r2_hidden(sK1,sK2)
          & ~ r2_hidden(sK0,sK2) )
        | k4_xboole_0(k2_tarski(sK0,sK1),sK2) = k2_tarski(sK0,sK1) ) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,
    ( ( r2_hidden(sK1,sK2)
      | r2_hidden(sK0,sK2)
      | k4_xboole_0(k2_tarski(sK0,sK1),sK2) != k2_tarski(sK0,sK1) )
    & ( ( ~ r2_hidden(sK1,sK2)
        & ~ r2_hidden(sK0,sK2) )
      | k4_xboole_0(k2_tarski(sK0,sK1),sK2) = k2_tarski(sK0,sK1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f34,f35])).

fof(f63,plain,
    ( ~ r2_hidden(sK0,sK2)
    | k4_xboole_0(k2_tarski(sK0,sK1),sK2) = k2_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f36])).

fof(f80,plain,
    ( ~ r2_hidden(sK0,sK2)
    | k4_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK1),sK2) = k3_enumset1(sK0,sK0,sK0,sK0,sK1) ),
    inference(definition_unfolding,[],[f63,f55,f55])).

fof(f64,plain,
    ( ~ r2_hidden(sK1,sK2)
    | k4_xboole_0(k2_tarski(sK0,sK1),sK2) = k2_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f36])).

fof(f79,plain,
    ( ~ r2_hidden(sK1,sK2)
    | k4_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK1),sK2) = k3_enumset1(sK0,sK0,sK0,sK0,sK1) ),
    inference(definition_unfolding,[],[f64,f55,f55])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k4_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k4_xboole_0(X0,X1) != X0 )
      & ( k4_xboole_0(X0,X1) = X0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f8])).

fof(f47,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = X0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f20,axiom,(
    ! [X0,X1,X2] :
      ~ ( ~ r1_xboole_0(k2_tarski(X0,X2),X1)
        & ~ r2_hidden(X2,X1)
        & ~ r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(k2_tarski(X0,X2),X1)
      | r2_hidden(X2,X1)
      | r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( r1_xboole_0(k2_tarski(X0,X2),X1)
      | r2_hidden(X2,X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f77,plain,(
    ! [X2,X0,X1] :
      ( r1_xboole_0(k3_enumset1(X0,X0,X0,X0,X2),X1)
      | r2_hidden(X2,X1)
      | r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f62,f55])).

fof(f12,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),k5_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f52,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),k5_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f12])).

fof(f19,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_tarski(X0,X1),X2)
    <=> ( r2_hidden(X1,X2)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(k2_tarski(X0,X1),X2)
        | ~ r2_hidden(X1,X2)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) )
        | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(k2_tarski(X0,X1),X2)
        | ~ r2_hidden(X1,X2)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) )
        | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ) ),
    inference(flattening,[],[f31])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X1,X2)
      | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X1,X2)
      | ~ r1_tarski(k3_enumset1(X0,X0,X0,X0,X1),X2) ) ),
    inference(definition_unfolding,[],[f60,f55])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k5_xboole_0(X1,X2))
    <=> ~ ( r2_hidden(X0,X1)
        <=> r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k5_xboole_0(X1,X2))
    <=> ( r2_hidden(X0,X1)
      <~> r2_hidden(X0,X2) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k5_xboole_0(X1,X2))
        | ( ( r2_hidden(X0,X1)
            | ~ r2_hidden(X0,X2) )
          & ( r2_hidden(X0,X2)
            | ~ r2_hidden(X0,X1) ) ) )
      & ( ( ( ~ r2_hidden(X0,X2)
            | ~ r2_hidden(X0,X1) )
          & ( r2_hidden(X0,X2)
            | r2_hidden(X0,X1) ) )
        | ~ r2_hidden(X0,k5_xboole_0(X1,X2)) ) ) ),
    inference(nnf_transformation,[],[f23])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X2)
      | ~ r2_hidden(X0,X1)
      | ~ r2_hidden(X0,k5_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f17,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f57,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f17])).

fof(f13,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f53,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f13])).

fof(f72,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f57,f53,f55])).

fof(f5,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f69,plain,(
    ! [X0,X1] : r1_tarski(X0,k5_xboole_0(X0,k4_xboole_0(X1,X0))) ),
    inference(definition_unfolding,[],[f44,f53])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,X2)
      | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,X2)
      | ~ r1_tarski(k3_enumset1(X0,X0,X0,X0,X1),X2) ) ),
    inference(definition_unfolding,[],[f59,f55])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X1,X2))
     => r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k4_xboole_0(X0,X1),X2)
      | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k4_xboole_0(X0,X1),X2)
      | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k4_xboole_0(X0,X1),X2)
      | ~ r1_tarski(X0,k5_xboole_0(X1,k4_xboole_0(X2,X1))) ) ),
    inference(definition_unfolding,[],[f42,f53])).

fof(f18,axiom,(
    ! [X0,X1] : r1_tarski(k1_tarski(X0),k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f58,plain,(
    ! [X0,X1] : r1_tarski(k1_tarski(X0),k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f18])).

fof(f16,axiom,(
    ! [X0] : k3_enumset1(X0,X0,X0,X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f56,plain,(
    ! [X0] : k3_enumset1(X0,X0,X0,X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f16])).

fof(f73,plain,(
    ! [X0,X1] : r1_tarski(k3_enumset1(X0,X0,X0,X0,X0),k3_enumset1(X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f58,f56,f55])).

fof(f65,plain,
    ( r2_hidden(sK1,sK2)
    | r2_hidden(sK0,sK2)
    | k4_xboole_0(k2_tarski(sK0,sK1),sK2) != k2_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f36])).

fof(f78,plain,
    ( r2_hidden(sK1,sK2)
    | r2_hidden(sK0,sK2)
    | k4_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK1),sK2) != k3_enumset1(sK0,sK0,sK0,sK0,sK1) ),
    inference(definition_unfolding,[],[f65,f55,f55])).

cnf(c_15,plain,
    ( k3_enumset1(X0,X0,X0,X0,X1) = k3_enumset1(X1,X1,X1,X1,X0) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_24,negated_conjecture,
    ( ~ r2_hidden(sK0,sK2)
    | k4_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK1),sK2) = k3_enumset1(sK0,sK0,sK0,sK0,sK1) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_758,plain,
    ( k4_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK1),sK2) = k3_enumset1(sK0,sK0,sK0,sK0,sK1)
    | r2_hidden(sK0,sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_23,negated_conjecture,
    ( ~ r2_hidden(sK1,sK2)
    | k4_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK1),sK2) = k3_enumset1(sK0,sK0,sK0,sK0,sK1) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_11,plain,
    ( ~ r1_xboole_0(X0,X1)
    | k4_xboole_0(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f47])).

cnf(c_803,plain,
    ( ~ r1_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK1),sK2)
    | k4_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK1),sK2) = k3_enumset1(sK0,sK0,sK0,sK0,sK1) ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_21,plain,
    ( r1_xboole_0(k3_enumset1(X0,X0,X0,X0,X1),X2)
    | r2_hidden(X0,X2)
    | r2_hidden(X1,X2) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_876,plain,
    ( r1_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK1),sK2)
    | r2_hidden(sK0,sK2)
    | r2_hidden(sK1,sK2) ),
    inference(instantiation,[status(thm)],[c_21])).

cnf(c_933,plain,
    ( k4_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK1),sK2) = k3_enumset1(sK0,sK0,sK0,sK0,sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_758,c_24,c_23,c_803,c_876])).

cnf(c_14,plain,
    ( r1_tarski(k4_xboole_0(X0,X1),k5_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_766,plain,
    ( r1_tarski(k4_xboole_0(X0,X1),k5_xboole_0(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_989,plain,
    ( r1_tarski(k3_enumset1(sK0,sK0,sK0,sK0,sK1),k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK1),sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_933,c_766])).

cnf(c_1218,plain,
    ( r1_tarski(k3_enumset1(sK1,sK1,sK1,sK1,sK0),k5_xboole_0(k3_enumset1(sK1,sK1,sK1,sK1,sK0),sK2)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_15,c_989])).

cnf(c_19,plain,
    ( ~ r1_tarski(k3_enumset1(X0,X0,X0,X0,X1),X2)
    | r2_hidden(X1,X2) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_763,plain,
    ( r1_tarski(k3_enumset1(X0,X0,X0,X0,X1),X2) != iProver_top
    | r2_hidden(X1,X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_2531,plain,
    ( r2_hidden(sK0,k5_xboole_0(k3_enumset1(sK1,sK1,sK1,sK1,sK0),sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1218,c_763])).

cnf(c_2,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X0,X2)
    | ~ r2_hidden(X0,k5_xboole_0(X2,X1)) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_776,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,X2) != iProver_top
    | r2_hidden(X0,k5_xboole_0(X1,X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_11402,plain,
    ( r2_hidden(sK0,k3_enumset1(sK1,sK1,sK1,sK1,sK0)) != iProver_top
    | r2_hidden(sK0,sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_2531,c_776])).

cnf(c_1219,plain,
    ( k4_xboole_0(k3_enumset1(sK1,sK1,sK1,sK1,sK0),sK2) = k3_enumset1(sK1,sK1,sK1,sK1,sK0) ),
    inference(demodulation,[status(thm)],[c_15,c_933])).

cnf(c_16,plain,
    ( k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_1256,plain,
    ( k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)) = k5_xboole_0(X1,k4_xboole_0(X0,X1)) ),
    inference(superposition,[status(thm)],[c_15,c_16])).

cnf(c_7,plain,
    ( r1_tarski(X0,k5_xboole_0(X0,k4_xboole_0(X1,X0))) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_772,plain,
    ( r1_tarski(X0,k5_xboole_0(X0,k4_xboole_0(X1,X0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_2816,plain,
    ( r1_tarski(X0,k3_tarski(k3_enumset1(X1,X1,X1,X1,X0))) = iProver_top ),
    inference(superposition,[status(thm)],[c_1256,c_772])).

cnf(c_2820,plain,
    ( r1_tarski(X0,k5_xboole_0(X1,k4_xboole_0(X0,X1))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_2816,c_16])).

cnf(c_3035,plain,
    ( r1_tarski(k3_enumset1(sK1,sK1,sK1,sK1,sK0),k5_xboole_0(sK2,k3_enumset1(sK1,sK1,sK1,sK1,sK0))) = iProver_top ),
    inference(superposition,[status(thm)],[c_1219,c_2820])).

cnf(c_20,plain,
    ( ~ r1_tarski(k3_enumset1(X0,X0,X0,X0,X1),X2)
    | r2_hidden(X0,X2) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_762,plain,
    ( r1_tarski(k3_enumset1(X0,X0,X0,X0,X1),X2) != iProver_top
    | r2_hidden(X0,X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_3238,plain,
    ( r2_hidden(sK1,k5_xboole_0(sK2,k3_enumset1(sK1,sK1,sK1,sK1,sK0))) = iProver_top ),
    inference(superposition,[status(thm)],[c_3035,c_762])).

cnf(c_11404,plain,
    ( r2_hidden(sK1,k3_enumset1(sK1,sK1,sK1,sK1,sK0)) != iProver_top
    | r2_hidden(sK1,sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_3238,c_776])).

cnf(c_5,plain,
    ( ~ r1_tarski(X0,k5_xboole_0(X1,k4_xboole_0(X2,X1)))
    | r1_tarski(k4_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_773,plain,
    ( r1_tarski(X0,k5_xboole_0(X1,k4_xboole_0(X2,X1))) != iProver_top
    | r1_tarski(k4_xboole_0(X0,X1),X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_5973,plain,
    ( r1_tarski(X0,k5_xboole_0(sK2,k3_enumset1(sK1,sK1,sK1,sK1,sK0))) != iProver_top
    | r1_tarski(k4_xboole_0(X0,sK2),k3_enumset1(sK1,sK1,sK1,sK1,sK0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1219,c_773])).

cnf(c_6951,plain,
    ( r1_tarski(k4_xboole_0(k3_enumset1(sK1,sK1,sK1,sK1,sK0),sK2),k3_enumset1(sK1,sK1,sK1,sK1,sK0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_3035,c_5973])).

cnf(c_6952,plain,
    ( r1_tarski(k3_enumset1(sK1,sK1,sK1,sK1,sK0),k3_enumset1(sK1,sK1,sK1,sK1,sK0)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_6951,c_1219])).

cnf(c_6960,plain,
    ( r2_hidden(sK0,k3_enumset1(sK1,sK1,sK1,sK1,sK0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_6952,c_763])).

cnf(c_17,plain,
    ( r1_tarski(k3_enumset1(X0,X0,X0,X0,X0),k3_enumset1(X0,X0,X0,X0,X1)) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_1915,plain,
    ( r1_tarski(k3_enumset1(sK1,sK1,sK1,sK1,sK1),k3_enumset1(sK1,sK1,sK1,sK1,X0)) ),
    inference(instantiation,[status(thm)],[c_17])).

cnf(c_1916,plain,
    ( r1_tarski(k3_enumset1(sK1,sK1,sK1,sK1,sK1),k3_enumset1(sK1,sK1,sK1,sK1,X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1915])).

cnf(c_1918,plain,
    ( r1_tarski(k3_enumset1(sK1,sK1,sK1,sK1,sK1),k3_enumset1(sK1,sK1,sK1,sK1,sK0)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_1916])).

cnf(c_1048,plain,
    ( ~ r1_tarski(k3_enumset1(sK1,sK1,sK1,sK1,X0),X1)
    | r2_hidden(sK1,X1) ),
    inference(instantiation,[status(thm)],[c_20])).

cnf(c_1195,plain,
    ( ~ r1_tarski(k3_enumset1(sK1,sK1,sK1,sK1,sK1),k3_enumset1(sK1,sK1,sK1,sK1,X0))
    | r2_hidden(sK1,k3_enumset1(sK1,sK1,sK1,sK1,X0)) ),
    inference(instantiation,[status(thm)],[c_1048])).

cnf(c_1196,plain,
    ( r1_tarski(k3_enumset1(sK1,sK1,sK1,sK1,sK1),k3_enumset1(sK1,sK1,sK1,sK1,X0)) != iProver_top
    | r2_hidden(sK1,k3_enumset1(sK1,sK1,sK1,sK1,X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1195])).

cnf(c_1198,plain,
    ( r1_tarski(k3_enumset1(sK1,sK1,sK1,sK1,sK1),k3_enumset1(sK1,sK1,sK1,sK1,sK0)) != iProver_top
    | r2_hidden(sK1,k3_enumset1(sK1,sK1,sK1,sK1,sK0)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_1196])).

cnf(c_22,negated_conjecture,
    ( r2_hidden(sK0,sK2)
    | r2_hidden(sK1,sK2)
    | k4_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK1),sK2) != k3_enumset1(sK0,sK0,sK0,sK0,sK1) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_760,plain,
    ( k4_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK1),sK2) != k3_enumset1(sK0,sK0,sK0,sK0,sK1)
    | r2_hidden(sK0,sK2) = iProver_top
    | r2_hidden(sK1,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_27,plain,
    ( k4_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK1),sK2) != k3_enumset1(sK0,sK0,sK0,sK0,sK1)
    | r2_hidden(sK0,sK2) = iProver_top
    | r2_hidden(sK1,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_936,plain,
    ( r2_hidden(sK0,sK2) = iProver_top
    | r2_hidden(sK1,sK2) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_760,c_24,c_23,c_27,c_803,c_876])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_11402,c_11404,c_6960,c_1918,c_1198,c_936])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.14/0.34  % Computer   : n018.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 12:53:12 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running in FOF mode
% 3.55/0.99  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.55/0.99  
% 3.55/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.55/0.99  
% 3.55/0.99  ------  iProver source info
% 3.55/0.99  
% 3.55/0.99  git: date: 2020-06-30 10:37:57 +0100
% 3.55/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.55/0.99  git: non_committed_changes: false
% 3.55/0.99  git: last_make_outside_of_git: false
% 3.55/0.99  
% 3.55/0.99  ------ 
% 3.55/0.99  
% 3.55/0.99  ------ Input Options
% 3.55/0.99  
% 3.55/0.99  --out_options                           all
% 3.55/0.99  --tptp_safe_out                         true
% 3.55/0.99  --problem_path                          ""
% 3.55/0.99  --include_path                          ""
% 3.55/0.99  --clausifier                            res/vclausify_rel
% 3.55/0.99  --clausifier_options                    ""
% 3.55/0.99  --stdin                                 false
% 3.55/0.99  --stats_out                             all
% 3.55/0.99  
% 3.55/0.99  ------ General Options
% 3.55/0.99  
% 3.55/0.99  --fof                                   false
% 3.55/0.99  --time_out_real                         305.
% 3.55/0.99  --time_out_virtual                      -1.
% 3.55/0.99  --symbol_type_check                     false
% 3.55/0.99  --clausify_out                          false
% 3.55/0.99  --sig_cnt_out                           false
% 3.55/0.99  --trig_cnt_out                          false
% 3.55/0.99  --trig_cnt_out_tolerance                1.
% 3.55/0.99  --trig_cnt_out_sk_spl                   false
% 3.55/0.99  --abstr_cl_out                          false
% 3.55/0.99  
% 3.55/0.99  ------ Global Options
% 3.55/0.99  
% 3.55/0.99  --schedule                              default
% 3.55/0.99  --add_important_lit                     false
% 3.55/0.99  --prop_solver_per_cl                    1000
% 3.55/0.99  --min_unsat_core                        false
% 3.55/0.99  --soft_assumptions                      false
% 3.55/0.99  --soft_lemma_size                       3
% 3.55/0.99  --prop_impl_unit_size                   0
% 3.55/0.99  --prop_impl_unit                        []
% 3.55/0.99  --share_sel_clauses                     true
% 3.55/0.99  --reset_solvers                         false
% 3.55/0.99  --bc_imp_inh                            [conj_cone]
% 3.55/0.99  --conj_cone_tolerance                   3.
% 3.55/0.99  --extra_neg_conj                        none
% 3.55/0.99  --large_theory_mode                     true
% 3.55/0.99  --prolific_symb_bound                   200
% 3.55/0.99  --lt_threshold                          2000
% 3.55/0.99  --clause_weak_htbl                      true
% 3.55/0.99  --gc_record_bc_elim                     false
% 3.55/0.99  
% 3.55/0.99  ------ Preprocessing Options
% 3.55/0.99  
% 3.55/0.99  --preprocessing_flag                    true
% 3.55/0.99  --time_out_prep_mult                    0.1
% 3.55/0.99  --splitting_mode                        input
% 3.55/0.99  --splitting_grd                         true
% 3.55/0.99  --splitting_cvd                         false
% 3.55/0.99  --splitting_cvd_svl                     false
% 3.55/0.99  --splitting_nvd                         32
% 3.55/0.99  --sub_typing                            true
% 3.55/0.99  --prep_gs_sim                           true
% 3.55/0.99  --prep_unflatten                        true
% 3.55/0.99  --prep_res_sim                          true
% 3.55/0.99  --prep_upred                            true
% 3.55/0.99  --prep_sem_filter                       exhaustive
% 3.55/0.99  --prep_sem_filter_out                   false
% 3.55/0.99  --pred_elim                             true
% 3.55/0.99  --res_sim_input                         true
% 3.55/0.99  --eq_ax_congr_red                       true
% 3.55/0.99  --pure_diseq_elim                       true
% 3.55/0.99  --brand_transform                       false
% 3.55/0.99  --non_eq_to_eq                          false
% 3.55/0.99  --prep_def_merge                        true
% 3.55/0.99  --prep_def_merge_prop_impl              false
% 3.55/0.99  --prep_def_merge_mbd                    true
% 3.55/0.99  --prep_def_merge_tr_red                 false
% 3.55/0.99  --prep_def_merge_tr_cl                  false
% 3.55/0.99  --smt_preprocessing                     true
% 3.55/0.99  --smt_ac_axioms                         fast
% 3.55/0.99  --preprocessed_out                      false
% 3.55/0.99  --preprocessed_stats                    false
% 3.55/0.99  
% 3.55/0.99  ------ Abstraction refinement Options
% 3.55/0.99  
% 3.55/0.99  --abstr_ref                             []
% 3.55/0.99  --abstr_ref_prep                        false
% 3.55/0.99  --abstr_ref_until_sat                   false
% 3.55/0.99  --abstr_ref_sig_restrict                funpre
% 3.55/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 3.55/0.99  --abstr_ref_under                       []
% 3.55/0.99  
% 3.55/0.99  ------ SAT Options
% 3.55/0.99  
% 3.55/0.99  --sat_mode                              false
% 3.55/0.99  --sat_fm_restart_options                ""
% 3.55/0.99  --sat_gr_def                            false
% 3.55/0.99  --sat_epr_types                         true
% 3.55/0.99  --sat_non_cyclic_types                  false
% 3.55/0.99  --sat_finite_models                     false
% 3.55/0.99  --sat_fm_lemmas                         false
% 3.55/0.99  --sat_fm_prep                           false
% 3.55/0.99  --sat_fm_uc_incr                        true
% 3.55/0.99  --sat_out_model                         small
% 3.55/0.99  --sat_out_clauses                       false
% 3.55/0.99  
% 3.55/0.99  ------ QBF Options
% 3.55/0.99  
% 3.55/0.99  --qbf_mode                              false
% 3.55/0.99  --qbf_elim_univ                         false
% 3.55/0.99  --qbf_dom_inst                          none
% 3.55/0.99  --qbf_dom_pre_inst                      false
% 3.55/0.99  --qbf_sk_in                             false
% 3.55/0.99  --qbf_pred_elim                         true
% 3.55/0.99  --qbf_split                             512
% 3.55/0.99  
% 3.55/0.99  ------ BMC1 Options
% 3.55/0.99  
% 3.55/0.99  --bmc1_incremental                      false
% 3.55/0.99  --bmc1_axioms                           reachable_all
% 3.55/0.99  --bmc1_min_bound                        0
% 3.55/0.99  --bmc1_max_bound                        -1
% 3.55/0.99  --bmc1_max_bound_default                -1
% 3.55/0.99  --bmc1_symbol_reachability              true
% 3.55/0.99  --bmc1_property_lemmas                  false
% 3.55/0.99  --bmc1_k_induction                      false
% 3.55/0.99  --bmc1_non_equiv_states                 false
% 3.55/0.99  --bmc1_deadlock                         false
% 3.55/0.99  --bmc1_ucm                              false
% 3.55/0.99  --bmc1_add_unsat_core                   none
% 3.55/0.99  --bmc1_unsat_core_children              false
% 3.55/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 3.55/0.99  --bmc1_out_stat                         full
% 3.55/0.99  --bmc1_ground_init                      false
% 3.55/0.99  --bmc1_pre_inst_next_state              false
% 3.55/0.99  --bmc1_pre_inst_state                   false
% 3.55/0.99  --bmc1_pre_inst_reach_state             false
% 3.55/0.99  --bmc1_out_unsat_core                   false
% 3.55/0.99  --bmc1_aig_witness_out                  false
% 3.55/0.99  --bmc1_verbose                          false
% 3.55/0.99  --bmc1_dump_clauses_tptp                false
% 3.55/0.99  --bmc1_dump_unsat_core_tptp             false
% 3.55/0.99  --bmc1_dump_file                        -
% 3.55/0.99  --bmc1_ucm_expand_uc_limit              128
% 3.55/0.99  --bmc1_ucm_n_expand_iterations          6
% 3.55/0.99  --bmc1_ucm_extend_mode                  1
% 3.55/0.99  --bmc1_ucm_init_mode                    2
% 3.55/0.99  --bmc1_ucm_cone_mode                    none
% 3.55/0.99  --bmc1_ucm_reduced_relation_type        0
% 3.55/0.99  --bmc1_ucm_relax_model                  4
% 3.55/0.99  --bmc1_ucm_full_tr_after_sat            true
% 3.55/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 3.55/0.99  --bmc1_ucm_layered_model                none
% 3.55/0.99  --bmc1_ucm_max_lemma_size               10
% 3.55/0.99  
% 3.55/0.99  ------ AIG Options
% 3.55/0.99  
% 3.55/0.99  --aig_mode                              false
% 3.55/0.99  
% 3.55/0.99  ------ Instantiation Options
% 3.55/0.99  
% 3.55/0.99  --instantiation_flag                    true
% 3.55/0.99  --inst_sos_flag                         true
% 3.55/0.99  --inst_sos_phase                        true
% 3.55/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.55/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.55/0.99  --inst_lit_sel_side                     num_symb
% 3.55/0.99  --inst_solver_per_active                1400
% 3.55/0.99  --inst_solver_calls_frac                1.
% 3.55/0.99  --inst_passive_queue_type               priority_queues
% 3.55/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.55/0.99  --inst_passive_queues_freq              [25;2]
% 3.55/0.99  --inst_dismatching                      true
% 3.55/0.99  --inst_eager_unprocessed_to_passive     true
% 3.55/0.99  --inst_prop_sim_given                   true
% 3.55/0.99  --inst_prop_sim_new                     false
% 3.55/0.99  --inst_subs_new                         false
% 3.55/0.99  --inst_eq_res_simp                      false
% 3.55/0.99  --inst_subs_given                       false
% 3.55/0.99  --inst_orphan_elimination               true
% 3.55/0.99  --inst_learning_loop_flag               true
% 3.55/0.99  --inst_learning_start                   3000
% 3.55/0.99  --inst_learning_factor                  2
% 3.55/0.99  --inst_start_prop_sim_after_learn       3
% 3.55/0.99  --inst_sel_renew                        solver
% 3.55/0.99  --inst_lit_activity_flag                true
% 3.55/0.99  --inst_restr_to_given                   false
% 3.55/0.99  --inst_activity_threshold               500
% 3.55/0.99  --inst_out_proof                        true
% 3.55/0.99  
% 3.55/0.99  ------ Resolution Options
% 3.55/0.99  
% 3.55/0.99  --resolution_flag                       true
% 3.55/0.99  --res_lit_sel                           adaptive
% 3.55/0.99  --res_lit_sel_side                      none
% 3.55/0.99  --res_ordering                          kbo
% 3.55/0.99  --res_to_prop_solver                    active
% 3.55/0.99  --res_prop_simpl_new                    false
% 3.55/0.99  --res_prop_simpl_given                  true
% 3.55/0.99  --res_passive_queue_type                priority_queues
% 3.55/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.55/0.99  --res_passive_queues_freq               [15;5]
% 3.55/0.99  --res_forward_subs                      full
% 3.55/0.99  --res_backward_subs                     full
% 3.55/0.99  --res_forward_subs_resolution           true
% 3.55/0.99  --res_backward_subs_resolution          true
% 3.55/0.99  --res_orphan_elimination                true
% 3.55/0.99  --res_time_limit                        2.
% 3.55/0.99  --res_out_proof                         true
% 3.55/0.99  
% 3.55/0.99  ------ Superposition Options
% 3.55/0.99  
% 3.55/0.99  --superposition_flag                    true
% 3.55/0.99  --sup_passive_queue_type                priority_queues
% 3.55/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.55/0.99  --sup_passive_queues_freq               [8;1;4]
% 3.55/0.99  --demod_completeness_check              fast
% 3.55/0.99  --demod_use_ground                      true
% 3.55/0.99  --sup_to_prop_solver                    passive
% 3.55/0.99  --sup_prop_simpl_new                    true
% 3.55/0.99  --sup_prop_simpl_given                  true
% 3.55/0.99  --sup_fun_splitting                     true
% 3.55/0.99  --sup_smt_interval                      50000
% 3.55/0.99  
% 3.55/0.99  ------ Superposition Simplification Setup
% 3.55/0.99  
% 3.55/0.99  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 3.55/0.99  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 3.55/0.99  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 3.55/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 3.55/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 3.55/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 3.55/0.99  --sup_full_bw                           [BwDemod;BwSubsumption]
% 3.55/0.99  --sup_immed_triv                        [TrivRules]
% 3.55/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.55/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.55/0.99  --sup_immed_bw_main                     []
% 3.55/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 3.55/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 3.55/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.55/0.99  --sup_input_bw                          []
% 3.55/0.99  
% 3.55/0.99  ------ Combination Options
% 3.55/0.99  
% 3.55/0.99  --comb_res_mult                         3
% 3.55/0.99  --comb_sup_mult                         2
% 3.55/0.99  --comb_inst_mult                        10
% 3.55/0.99  
% 3.55/0.99  ------ Debug Options
% 3.55/0.99  
% 3.55/0.99  --dbg_backtrace                         false
% 3.55/0.99  --dbg_dump_prop_clauses                 false
% 3.55/0.99  --dbg_dump_prop_clauses_file            -
% 3.55/0.99  --dbg_out_stat                          false
% 3.55/0.99  ------ Parsing...
% 3.55/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.55/0.99  
% 3.55/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 3.55/0.99  
% 3.55/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.55/0.99  
% 3.55/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.55/0.99  ------ Proving...
% 3.55/0.99  ------ Problem Properties 
% 3.55/0.99  
% 3.55/0.99  
% 3.55/0.99  clauses                                 25
% 3.55/0.99  conjectures                             3
% 3.55/0.99  EPR                                     0
% 3.55/0.99  Horn                                    20
% 3.55/0.99  unary                                   9
% 3.55/0.99  binary                                  9
% 3.55/0.99  lits                                    48
% 3.55/0.99  lits eq                                 10
% 3.55/0.99  fd_pure                                 0
% 3.55/0.99  fd_pseudo                               0
% 3.55/0.99  fd_cond                                 1
% 3.55/0.99  fd_pseudo_cond                          0
% 3.55/0.99  AC symbols                              0
% 3.55/0.99  
% 3.55/0.99  ------ Schedule dynamic 5 is on 
% 3.55/0.99  
% 3.55/0.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.55/0.99  
% 3.55/0.99  
% 3.55/0.99  ------ 
% 3.55/0.99  Current options:
% 3.55/0.99  ------ 
% 3.55/0.99  
% 3.55/0.99  ------ Input Options
% 3.55/0.99  
% 3.55/0.99  --out_options                           all
% 3.55/0.99  --tptp_safe_out                         true
% 3.55/0.99  --problem_path                          ""
% 3.55/0.99  --include_path                          ""
% 3.55/0.99  --clausifier                            res/vclausify_rel
% 3.55/0.99  --clausifier_options                    ""
% 3.55/0.99  --stdin                                 false
% 3.55/0.99  --stats_out                             all
% 3.55/0.99  
% 3.55/0.99  ------ General Options
% 3.55/0.99  
% 3.55/0.99  --fof                                   false
% 3.55/0.99  --time_out_real                         305.
% 3.55/0.99  --time_out_virtual                      -1.
% 3.55/0.99  --symbol_type_check                     false
% 3.55/0.99  --clausify_out                          false
% 3.55/0.99  --sig_cnt_out                           false
% 3.55/0.99  --trig_cnt_out                          false
% 3.55/0.99  --trig_cnt_out_tolerance                1.
% 3.55/0.99  --trig_cnt_out_sk_spl                   false
% 3.55/0.99  --abstr_cl_out                          false
% 3.55/0.99  
% 3.55/0.99  ------ Global Options
% 3.55/0.99  
% 3.55/0.99  --schedule                              default
% 3.55/0.99  --add_important_lit                     false
% 3.55/0.99  --prop_solver_per_cl                    1000
% 3.55/0.99  --min_unsat_core                        false
% 3.55/0.99  --soft_assumptions                      false
% 3.55/0.99  --soft_lemma_size                       3
% 3.55/0.99  --prop_impl_unit_size                   0
% 3.55/0.99  --prop_impl_unit                        []
% 3.55/0.99  --share_sel_clauses                     true
% 3.55/0.99  --reset_solvers                         false
% 3.55/0.99  --bc_imp_inh                            [conj_cone]
% 3.55/0.99  --conj_cone_tolerance                   3.
% 3.55/0.99  --extra_neg_conj                        none
% 3.55/0.99  --large_theory_mode                     true
% 3.55/0.99  --prolific_symb_bound                   200
% 3.55/0.99  --lt_threshold                          2000
% 3.55/0.99  --clause_weak_htbl                      true
% 3.55/0.99  --gc_record_bc_elim                     false
% 3.55/0.99  
% 3.55/0.99  ------ Preprocessing Options
% 3.55/0.99  
% 3.55/0.99  --preprocessing_flag                    true
% 3.55/0.99  --time_out_prep_mult                    0.1
% 3.55/0.99  --splitting_mode                        input
% 3.55/0.99  --splitting_grd                         true
% 3.55/0.99  --splitting_cvd                         false
% 3.55/0.99  --splitting_cvd_svl                     false
% 3.55/0.99  --splitting_nvd                         32
% 3.55/0.99  --sub_typing                            true
% 3.55/0.99  --prep_gs_sim                           true
% 3.55/0.99  --prep_unflatten                        true
% 3.55/0.99  --prep_res_sim                          true
% 3.55/0.99  --prep_upred                            true
% 3.55/0.99  --prep_sem_filter                       exhaustive
% 3.55/0.99  --prep_sem_filter_out                   false
% 3.55/0.99  --pred_elim                             true
% 3.55/0.99  --res_sim_input                         true
% 3.55/0.99  --eq_ax_congr_red                       true
% 3.55/0.99  --pure_diseq_elim                       true
% 3.55/0.99  --brand_transform                       false
% 3.55/0.99  --non_eq_to_eq                          false
% 3.55/0.99  --prep_def_merge                        true
% 3.55/0.99  --prep_def_merge_prop_impl              false
% 3.55/0.99  --prep_def_merge_mbd                    true
% 3.55/0.99  --prep_def_merge_tr_red                 false
% 3.55/0.99  --prep_def_merge_tr_cl                  false
% 3.55/0.99  --smt_preprocessing                     true
% 3.55/0.99  --smt_ac_axioms                         fast
% 3.55/0.99  --preprocessed_out                      false
% 3.55/0.99  --preprocessed_stats                    false
% 3.55/0.99  
% 3.55/0.99  ------ Abstraction refinement Options
% 3.55/0.99  
% 3.55/0.99  --abstr_ref                             []
% 3.55/0.99  --abstr_ref_prep                        false
% 3.55/0.99  --abstr_ref_until_sat                   false
% 3.55/0.99  --abstr_ref_sig_restrict                funpre
% 3.55/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 3.55/0.99  --abstr_ref_under                       []
% 3.55/0.99  
% 3.55/0.99  ------ SAT Options
% 3.55/0.99  
% 3.55/0.99  --sat_mode                              false
% 3.55/0.99  --sat_fm_restart_options                ""
% 3.55/0.99  --sat_gr_def                            false
% 3.55/0.99  --sat_epr_types                         true
% 3.55/0.99  --sat_non_cyclic_types                  false
% 3.55/0.99  --sat_finite_models                     false
% 3.55/0.99  --sat_fm_lemmas                         false
% 3.55/0.99  --sat_fm_prep                           false
% 3.55/0.99  --sat_fm_uc_incr                        true
% 3.55/0.99  --sat_out_model                         small
% 3.55/0.99  --sat_out_clauses                       false
% 3.55/0.99  
% 3.55/0.99  ------ QBF Options
% 3.55/0.99  
% 3.55/0.99  --qbf_mode                              false
% 3.55/0.99  --qbf_elim_univ                         false
% 3.55/0.99  --qbf_dom_inst                          none
% 3.55/0.99  --qbf_dom_pre_inst                      false
% 3.55/0.99  --qbf_sk_in                             false
% 3.55/0.99  --qbf_pred_elim                         true
% 3.55/0.99  --qbf_split                             512
% 3.55/0.99  
% 3.55/0.99  ------ BMC1 Options
% 3.55/0.99  
% 3.55/0.99  --bmc1_incremental                      false
% 3.55/0.99  --bmc1_axioms                           reachable_all
% 3.55/0.99  --bmc1_min_bound                        0
% 3.55/0.99  --bmc1_max_bound                        -1
% 3.55/0.99  --bmc1_max_bound_default                -1
% 3.55/0.99  --bmc1_symbol_reachability              true
% 3.55/0.99  --bmc1_property_lemmas                  false
% 3.55/0.99  --bmc1_k_induction                      false
% 3.55/0.99  --bmc1_non_equiv_states                 false
% 3.55/0.99  --bmc1_deadlock                         false
% 3.55/0.99  --bmc1_ucm                              false
% 3.55/0.99  --bmc1_add_unsat_core                   none
% 3.55/0.99  --bmc1_unsat_core_children              false
% 3.55/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 3.55/0.99  --bmc1_out_stat                         full
% 3.55/0.99  --bmc1_ground_init                      false
% 3.55/0.99  --bmc1_pre_inst_next_state              false
% 3.55/0.99  --bmc1_pre_inst_state                   false
% 3.55/0.99  --bmc1_pre_inst_reach_state             false
% 3.55/0.99  --bmc1_out_unsat_core                   false
% 3.55/0.99  --bmc1_aig_witness_out                  false
% 3.55/0.99  --bmc1_verbose                          false
% 3.55/0.99  --bmc1_dump_clauses_tptp                false
% 3.55/0.99  --bmc1_dump_unsat_core_tptp             false
% 3.55/0.99  --bmc1_dump_file                        -
% 3.55/0.99  --bmc1_ucm_expand_uc_limit              128
% 3.55/0.99  --bmc1_ucm_n_expand_iterations          6
% 3.55/0.99  --bmc1_ucm_extend_mode                  1
% 3.55/0.99  --bmc1_ucm_init_mode                    2
% 3.55/0.99  --bmc1_ucm_cone_mode                    none
% 3.55/0.99  --bmc1_ucm_reduced_relation_type        0
% 3.55/0.99  --bmc1_ucm_relax_model                  4
% 3.55/0.99  --bmc1_ucm_full_tr_after_sat            true
% 3.55/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 3.55/0.99  --bmc1_ucm_layered_model                none
% 3.55/0.99  --bmc1_ucm_max_lemma_size               10
% 3.55/0.99  
% 3.55/0.99  ------ AIG Options
% 3.55/0.99  
% 3.55/0.99  --aig_mode                              false
% 3.55/0.99  
% 3.55/0.99  ------ Instantiation Options
% 3.55/0.99  
% 3.55/0.99  --instantiation_flag                    true
% 3.55/0.99  --inst_sos_flag                         true
% 3.55/0.99  --inst_sos_phase                        true
% 3.55/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.55/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.55/0.99  --inst_lit_sel_side                     none
% 3.55/0.99  --inst_solver_per_active                1400
% 3.55/0.99  --inst_solver_calls_frac                1.
% 3.55/0.99  --inst_passive_queue_type               priority_queues
% 3.55/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.55/0.99  --inst_passive_queues_freq              [25;2]
% 3.55/0.99  --inst_dismatching                      true
% 3.55/0.99  --inst_eager_unprocessed_to_passive     true
% 3.55/0.99  --inst_prop_sim_given                   true
% 3.55/0.99  --inst_prop_sim_new                     false
% 3.55/0.99  --inst_subs_new                         false
% 3.55/0.99  --inst_eq_res_simp                      false
% 3.55/0.99  --inst_subs_given                       false
% 3.55/0.99  --inst_orphan_elimination               true
% 3.55/0.99  --inst_learning_loop_flag               true
% 3.55/0.99  --inst_learning_start                   3000
% 3.55/0.99  --inst_learning_factor                  2
% 3.55/0.99  --inst_start_prop_sim_after_learn       3
% 3.55/0.99  --inst_sel_renew                        solver
% 3.55/0.99  --inst_lit_activity_flag                true
% 3.55/0.99  --inst_restr_to_given                   false
% 3.55/0.99  --inst_activity_threshold               500
% 3.55/0.99  --inst_out_proof                        true
% 3.55/0.99  
% 3.55/0.99  ------ Resolution Options
% 3.55/0.99  
% 3.55/0.99  --resolution_flag                       false
% 3.55/0.99  --res_lit_sel                           adaptive
% 3.55/0.99  --res_lit_sel_side                      none
% 3.55/0.99  --res_ordering                          kbo
% 3.55/0.99  --res_to_prop_solver                    active
% 3.55/0.99  --res_prop_simpl_new                    false
% 3.55/0.99  --res_prop_simpl_given                  true
% 3.55/0.99  --res_passive_queue_type                priority_queues
% 3.55/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.55/0.99  --res_passive_queues_freq               [15;5]
% 3.55/0.99  --res_forward_subs                      full
% 3.55/0.99  --res_backward_subs                     full
% 3.55/0.99  --res_forward_subs_resolution           true
% 3.55/0.99  --res_backward_subs_resolution          true
% 3.55/0.99  --res_orphan_elimination                true
% 3.55/0.99  --res_time_limit                        2.
% 3.55/0.99  --res_out_proof                         true
% 3.55/0.99  
% 3.55/0.99  ------ Superposition Options
% 3.55/0.99  
% 3.55/0.99  --superposition_flag                    true
% 3.55/0.99  --sup_passive_queue_type                priority_queues
% 3.55/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.55/0.99  --sup_passive_queues_freq               [8;1;4]
% 3.55/0.99  --demod_completeness_check              fast
% 3.55/0.99  --demod_use_ground                      true
% 3.55/0.99  --sup_to_prop_solver                    passive
% 3.55/0.99  --sup_prop_simpl_new                    true
% 3.55/0.99  --sup_prop_simpl_given                  true
% 3.55/0.99  --sup_fun_splitting                     true
% 3.55/0.99  --sup_smt_interval                      50000
% 3.55/0.99  
% 3.55/0.99  ------ Superposition Simplification Setup
% 3.55/0.99  
% 3.55/0.99  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 3.55/0.99  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 3.55/0.99  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 3.55/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 3.55/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 3.55/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 3.55/0.99  --sup_full_bw                           [BwDemod;BwSubsumption]
% 3.55/0.99  --sup_immed_triv                        [TrivRules]
% 3.55/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.55/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.55/0.99  --sup_immed_bw_main                     []
% 3.55/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 3.55/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 3.55/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.55/0.99  --sup_input_bw                          []
% 3.55/0.99  
% 3.55/0.99  ------ Combination Options
% 3.55/0.99  
% 3.55/0.99  --comb_res_mult                         3
% 3.55/0.99  --comb_sup_mult                         2
% 3.55/0.99  --comb_inst_mult                        10
% 3.55/0.99  
% 3.55/0.99  ------ Debug Options
% 3.55/0.99  
% 3.55/0.99  --dbg_backtrace                         false
% 3.55/0.99  --dbg_dump_prop_clauses                 false
% 3.55/0.99  --dbg_dump_prop_clauses_file            -
% 3.55/0.99  --dbg_out_stat                          false
% 3.55/0.99  
% 3.55/0.99  
% 3.55/0.99  
% 3.55/0.99  
% 3.55/0.99  ------ Proving...
% 3.55/0.99  
% 3.55/0.99  
% 3.55/0.99  % SZS status Theorem for theBenchmark.p
% 3.55/0.99  
% 3.55/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 3.55/0.99  
% 3.55/0.99  fof(f14,axiom,(
% 3.55/0.99    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 3.55/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.55/0.99  
% 3.55/0.99  fof(f54,plain,(
% 3.55/0.99    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 3.55/0.99    inference(cnf_transformation,[],[f14])).
% 3.55/0.99  
% 3.55/0.99  fof(f15,axiom,(
% 3.55/0.99    ! [X0,X1] : k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1)),
% 3.55/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.55/0.99  
% 3.55/0.99  fof(f55,plain,(
% 3.55/0.99    ( ! [X0,X1] : (k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1)) )),
% 3.55/0.99    inference(cnf_transformation,[],[f15])).
% 3.55/0.99  
% 3.55/0.99  fof(f71,plain,(
% 3.55/0.99    ( ! [X0,X1] : (k3_enumset1(X0,X0,X0,X0,X1) = k3_enumset1(X1,X1,X1,X1,X0)) )),
% 3.55/0.99    inference(definition_unfolding,[],[f54,f55,f55])).
% 3.55/0.99  
% 3.55/0.99  fof(f21,conjecture,(
% 3.55/0.99    ! [X0,X1,X2] : (k4_xboole_0(k2_tarski(X0,X1),X2) = k2_tarski(X0,X1) <=> (~r2_hidden(X1,X2) & ~r2_hidden(X0,X2)))),
% 3.55/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.55/0.99  
% 3.55/0.99  fof(f22,negated_conjecture,(
% 3.55/0.99    ~! [X0,X1,X2] : (k4_xboole_0(k2_tarski(X0,X1),X2) = k2_tarski(X0,X1) <=> (~r2_hidden(X1,X2) & ~r2_hidden(X0,X2)))),
% 3.55/0.99    inference(negated_conjecture,[],[f21])).
% 3.55/0.99  
% 3.55/0.99  fof(f28,plain,(
% 3.55/0.99    ? [X0,X1,X2] : (k4_xboole_0(k2_tarski(X0,X1),X2) = k2_tarski(X0,X1) <~> (~r2_hidden(X1,X2) & ~r2_hidden(X0,X2)))),
% 3.55/0.99    inference(ennf_transformation,[],[f22])).
% 3.55/0.99  
% 3.55/0.99  fof(f33,plain,(
% 3.55/0.99    ? [X0,X1,X2] : (((r2_hidden(X1,X2) | r2_hidden(X0,X2)) | k4_xboole_0(k2_tarski(X0,X1),X2) != k2_tarski(X0,X1)) & ((~r2_hidden(X1,X2) & ~r2_hidden(X0,X2)) | k4_xboole_0(k2_tarski(X0,X1),X2) = k2_tarski(X0,X1)))),
% 3.55/0.99    inference(nnf_transformation,[],[f28])).
% 3.55/0.99  
% 3.55/0.99  fof(f34,plain,(
% 3.55/0.99    ? [X0,X1,X2] : ((r2_hidden(X1,X2) | r2_hidden(X0,X2) | k4_xboole_0(k2_tarski(X0,X1),X2) != k2_tarski(X0,X1)) & ((~r2_hidden(X1,X2) & ~r2_hidden(X0,X2)) | k4_xboole_0(k2_tarski(X0,X1),X2) = k2_tarski(X0,X1)))),
% 3.55/0.99    inference(flattening,[],[f33])).
% 3.55/0.99  
% 3.55/0.99  fof(f35,plain,(
% 3.55/0.99    ? [X0,X1,X2] : ((r2_hidden(X1,X2) | r2_hidden(X0,X2) | k4_xboole_0(k2_tarski(X0,X1),X2) != k2_tarski(X0,X1)) & ((~r2_hidden(X1,X2) & ~r2_hidden(X0,X2)) | k4_xboole_0(k2_tarski(X0,X1),X2) = k2_tarski(X0,X1))) => ((r2_hidden(sK1,sK2) | r2_hidden(sK0,sK2) | k4_xboole_0(k2_tarski(sK0,sK1),sK2) != k2_tarski(sK0,sK1)) & ((~r2_hidden(sK1,sK2) & ~r2_hidden(sK0,sK2)) | k4_xboole_0(k2_tarski(sK0,sK1),sK2) = k2_tarski(sK0,sK1)))),
% 3.55/0.99    introduced(choice_axiom,[])).
% 3.55/0.99  
% 3.55/0.99  fof(f36,plain,(
% 3.55/0.99    (r2_hidden(sK1,sK2) | r2_hidden(sK0,sK2) | k4_xboole_0(k2_tarski(sK0,sK1),sK2) != k2_tarski(sK0,sK1)) & ((~r2_hidden(sK1,sK2) & ~r2_hidden(sK0,sK2)) | k4_xboole_0(k2_tarski(sK0,sK1),sK2) = k2_tarski(sK0,sK1))),
% 3.55/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f34,f35])).
% 3.55/0.99  
% 3.55/0.99  fof(f63,plain,(
% 3.55/0.99    ~r2_hidden(sK0,sK2) | k4_xboole_0(k2_tarski(sK0,sK1),sK2) = k2_tarski(sK0,sK1)),
% 3.55/0.99    inference(cnf_transformation,[],[f36])).
% 3.55/0.99  
% 3.55/0.99  fof(f80,plain,(
% 3.55/0.99    ~r2_hidden(sK0,sK2) | k4_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK1),sK2) = k3_enumset1(sK0,sK0,sK0,sK0,sK1)),
% 3.55/0.99    inference(definition_unfolding,[],[f63,f55,f55])).
% 3.55/0.99  
% 3.55/0.99  fof(f64,plain,(
% 3.55/0.99    ~r2_hidden(sK1,sK2) | k4_xboole_0(k2_tarski(sK0,sK1),sK2) = k2_tarski(sK0,sK1)),
% 3.55/0.99    inference(cnf_transformation,[],[f36])).
% 3.55/0.99  
% 3.55/0.99  fof(f79,plain,(
% 3.55/0.99    ~r2_hidden(sK1,sK2) | k4_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK1),sK2) = k3_enumset1(sK0,sK0,sK0,sK0,sK1)),
% 3.55/0.99    inference(definition_unfolding,[],[f64,f55,f55])).
% 3.55/0.99  
% 3.55/0.99  fof(f8,axiom,(
% 3.55/0.99    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k4_xboole_0(X0,X1) = X0)),
% 3.55/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.55/0.99  
% 3.55/0.99  fof(f30,plain,(
% 3.55/0.99    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) != X0) & (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)))),
% 3.55/0.99    inference(nnf_transformation,[],[f8])).
% 3.55/0.99  
% 3.55/0.99  fof(f47,plain,(
% 3.55/0.99    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)) )),
% 3.55/0.99    inference(cnf_transformation,[],[f30])).
% 3.55/0.99  
% 3.55/0.99  fof(f20,axiom,(
% 3.55/0.99    ! [X0,X1,X2] : ~(~r1_xboole_0(k2_tarski(X0,X2),X1) & ~r2_hidden(X2,X1) & ~r2_hidden(X0,X1))),
% 3.55/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.55/0.99  
% 3.55/0.99  fof(f27,plain,(
% 3.55/0.99    ! [X0,X1,X2] : (r1_xboole_0(k2_tarski(X0,X2),X1) | r2_hidden(X2,X1) | r2_hidden(X0,X1))),
% 3.55/0.99    inference(ennf_transformation,[],[f20])).
% 3.55/0.99  
% 3.55/0.99  fof(f62,plain,(
% 3.55/0.99    ( ! [X2,X0,X1] : (r1_xboole_0(k2_tarski(X0,X2),X1) | r2_hidden(X2,X1) | r2_hidden(X0,X1)) )),
% 3.55/0.99    inference(cnf_transformation,[],[f27])).
% 3.55/0.99  
% 3.55/0.99  fof(f77,plain,(
% 3.55/0.99    ( ! [X2,X0,X1] : (r1_xboole_0(k3_enumset1(X0,X0,X0,X0,X2),X1) | r2_hidden(X2,X1) | r2_hidden(X0,X1)) )),
% 3.55/0.99    inference(definition_unfolding,[],[f62,f55])).
% 3.55/0.99  
% 3.55/0.99  fof(f12,axiom,(
% 3.55/0.99    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),k5_xboole_0(X0,X1))),
% 3.55/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.55/0.99  
% 3.55/0.99  fof(f52,plain,(
% 3.55/0.99    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),k5_xboole_0(X0,X1))) )),
% 3.55/0.99    inference(cnf_transformation,[],[f12])).
% 3.55/0.99  
% 3.55/0.99  fof(f19,axiom,(
% 3.55/0.99    ! [X0,X1,X2] : (r1_tarski(k2_tarski(X0,X1),X2) <=> (r2_hidden(X1,X2) & r2_hidden(X0,X2)))),
% 3.55/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.55/0.99  
% 3.55/0.99  fof(f31,plain,(
% 3.55/0.99    ! [X0,X1,X2] : ((r1_tarski(k2_tarski(X0,X1),X2) | (~r2_hidden(X1,X2) | ~r2_hidden(X0,X2))) & ((r2_hidden(X1,X2) & r2_hidden(X0,X2)) | ~r1_tarski(k2_tarski(X0,X1),X2)))),
% 3.55/0.99    inference(nnf_transformation,[],[f19])).
% 3.55/0.99  
% 3.55/0.99  fof(f32,plain,(
% 3.55/0.99    ! [X0,X1,X2] : ((r1_tarski(k2_tarski(X0,X1),X2) | ~r2_hidden(X1,X2) | ~r2_hidden(X0,X2)) & ((r2_hidden(X1,X2) & r2_hidden(X0,X2)) | ~r1_tarski(k2_tarski(X0,X1),X2)))),
% 3.55/0.99    inference(flattening,[],[f31])).
% 3.55/0.99  
% 3.55/0.99  fof(f60,plain,(
% 3.55/0.99    ( ! [X2,X0,X1] : (r2_hidden(X1,X2) | ~r1_tarski(k2_tarski(X0,X1),X2)) )),
% 3.55/0.99    inference(cnf_transformation,[],[f32])).
% 3.55/0.99  
% 3.55/0.99  fof(f75,plain,(
% 3.55/0.99    ( ! [X2,X0,X1] : (r2_hidden(X1,X2) | ~r1_tarski(k3_enumset1(X0,X0,X0,X0,X1),X2)) )),
% 3.55/0.99    inference(definition_unfolding,[],[f60,f55])).
% 3.55/0.99  
% 3.55/0.99  fof(f1,axiom,(
% 3.55/0.99    ! [X0,X1,X2] : (r2_hidden(X0,k5_xboole_0(X1,X2)) <=> ~(r2_hidden(X0,X1) <=> r2_hidden(X0,X2)))),
% 3.55/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.55/0.99  
% 3.55/0.99  fof(f23,plain,(
% 3.55/0.99    ! [X0,X1,X2] : (r2_hidden(X0,k5_xboole_0(X1,X2)) <=> (r2_hidden(X0,X1) <~> r2_hidden(X0,X2)))),
% 3.55/0.99    inference(ennf_transformation,[],[f1])).
% 3.55/0.99  
% 3.55/0.99  fof(f29,plain,(
% 3.55/0.99    ! [X0,X1,X2] : ((r2_hidden(X0,k5_xboole_0(X1,X2)) | ((r2_hidden(X0,X1) | ~r2_hidden(X0,X2)) & (r2_hidden(X0,X2) | ~r2_hidden(X0,X1)))) & (((~r2_hidden(X0,X2) | ~r2_hidden(X0,X1)) & (r2_hidden(X0,X2) | r2_hidden(X0,X1))) | ~r2_hidden(X0,k5_xboole_0(X1,X2))))),
% 3.55/0.99    inference(nnf_transformation,[],[f23])).
% 3.55/0.99  
% 3.55/0.99  fof(f38,plain,(
% 3.55/0.99    ( ! [X2,X0,X1] : (~r2_hidden(X0,X2) | ~r2_hidden(X0,X1) | ~r2_hidden(X0,k5_xboole_0(X1,X2))) )),
% 3.55/0.99    inference(cnf_transformation,[],[f29])).
% 3.55/0.99  
% 3.55/0.99  fof(f17,axiom,(
% 3.55/0.99    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 3.55/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.55/0.99  
% 3.55/0.99  fof(f57,plain,(
% 3.55/0.99    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 3.55/0.99    inference(cnf_transformation,[],[f17])).
% 3.55/0.99  
% 3.55/0.99  fof(f13,axiom,(
% 3.55/0.99    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)),
% 3.55/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.55/0.99  
% 3.55/0.99  fof(f53,plain,(
% 3.55/0.99    ( ! [X0,X1] : (k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)) )),
% 3.55/0.99    inference(cnf_transformation,[],[f13])).
% 3.55/0.99  
% 3.55/0.99  fof(f72,plain,(
% 3.55/0.99    ( ! [X0,X1] : (k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k3_tarski(k3_enumset1(X0,X0,X0,X0,X1))) )),
% 3.55/0.99    inference(definition_unfolding,[],[f57,f53,f55])).
% 3.55/0.99  
% 3.55/0.99  fof(f5,axiom,(
% 3.55/0.99    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 3.55/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.55/0.99  
% 3.55/0.99  fof(f44,plain,(
% 3.55/0.99    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 3.55/0.99    inference(cnf_transformation,[],[f5])).
% 3.55/0.99  
% 3.55/0.99  fof(f69,plain,(
% 3.55/0.99    ( ! [X0,X1] : (r1_tarski(X0,k5_xboole_0(X0,k4_xboole_0(X1,X0)))) )),
% 3.55/0.99    inference(definition_unfolding,[],[f44,f53])).
% 3.55/0.99  
% 3.55/0.99  fof(f59,plain,(
% 3.55/0.99    ( ! [X2,X0,X1] : (r2_hidden(X0,X2) | ~r1_tarski(k2_tarski(X0,X1),X2)) )),
% 3.55/0.99    inference(cnf_transformation,[],[f32])).
% 3.55/0.99  
% 3.55/0.99  fof(f76,plain,(
% 3.55/0.99    ( ! [X2,X0,X1] : (r2_hidden(X0,X2) | ~r1_tarski(k3_enumset1(X0,X0,X0,X0,X1),X2)) )),
% 3.55/0.99    inference(definition_unfolding,[],[f59,f55])).
% 3.55/0.99  
% 3.55/0.99  fof(f3,axiom,(
% 3.55/0.99    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X1,X2)) => r1_tarski(k4_xboole_0(X0,X1),X2))),
% 3.55/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.55/0.99  
% 3.55/0.99  fof(f25,plain,(
% 3.55/0.99    ! [X0,X1,X2] : (r1_tarski(k4_xboole_0(X0,X1),X2) | ~r1_tarski(X0,k2_xboole_0(X1,X2)))),
% 3.55/0.99    inference(ennf_transformation,[],[f3])).
% 3.55/0.99  
% 3.55/0.99  fof(f42,plain,(
% 3.55/0.99    ( ! [X2,X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X2) | ~r1_tarski(X0,k2_xboole_0(X1,X2))) )),
% 3.55/0.99    inference(cnf_transformation,[],[f25])).
% 3.55/0.99  
% 3.55/0.99  fof(f67,plain,(
% 3.55/0.99    ( ! [X2,X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X2) | ~r1_tarski(X0,k5_xboole_0(X1,k4_xboole_0(X2,X1)))) )),
% 3.55/0.99    inference(definition_unfolding,[],[f42,f53])).
% 3.55/0.99  
% 3.55/0.99  fof(f18,axiom,(
% 3.55/0.99    ! [X0,X1] : r1_tarski(k1_tarski(X0),k2_tarski(X0,X1))),
% 3.55/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.55/0.99  
% 3.55/0.99  fof(f58,plain,(
% 3.55/0.99    ( ! [X0,X1] : (r1_tarski(k1_tarski(X0),k2_tarski(X0,X1))) )),
% 3.55/0.99    inference(cnf_transformation,[],[f18])).
% 3.55/0.99  
% 3.55/0.99  fof(f16,axiom,(
% 3.55/0.99    ! [X0] : k3_enumset1(X0,X0,X0,X0,X0) = k1_tarski(X0)),
% 3.55/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.55/0.99  
% 3.55/0.99  fof(f56,plain,(
% 3.55/0.99    ( ! [X0] : (k3_enumset1(X0,X0,X0,X0,X0) = k1_tarski(X0)) )),
% 3.55/0.99    inference(cnf_transformation,[],[f16])).
% 3.55/0.99  
% 3.55/0.99  fof(f73,plain,(
% 3.55/0.99    ( ! [X0,X1] : (r1_tarski(k3_enumset1(X0,X0,X0,X0,X0),k3_enumset1(X0,X0,X0,X0,X1))) )),
% 3.55/0.99    inference(definition_unfolding,[],[f58,f56,f55])).
% 3.55/0.99  
% 3.55/0.99  fof(f65,plain,(
% 3.55/0.99    r2_hidden(sK1,sK2) | r2_hidden(sK0,sK2) | k4_xboole_0(k2_tarski(sK0,sK1),sK2) != k2_tarski(sK0,sK1)),
% 3.55/0.99    inference(cnf_transformation,[],[f36])).
% 3.55/0.99  
% 3.55/0.99  fof(f78,plain,(
% 3.55/0.99    r2_hidden(sK1,sK2) | r2_hidden(sK0,sK2) | k4_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK1),sK2) != k3_enumset1(sK0,sK0,sK0,sK0,sK1)),
% 3.55/0.99    inference(definition_unfolding,[],[f65,f55,f55])).
% 3.55/0.99  
% 3.55/0.99  cnf(c_15,plain,
% 3.55/0.99      ( k3_enumset1(X0,X0,X0,X0,X1) = k3_enumset1(X1,X1,X1,X1,X0) ),
% 3.55/0.99      inference(cnf_transformation,[],[f71]) ).
% 3.55/0.99  
% 3.55/0.99  cnf(c_24,negated_conjecture,
% 3.55/0.99      ( ~ r2_hidden(sK0,sK2)
% 3.55/0.99      | k4_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK1),sK2) = k3_enumset1(sK0,sK0,sK0,sK0,sK1) ),
% 3.55/0.99      inference(cnf_transformation,[],[f80]) ).
% 3.55/0.99  
% 3.55/0.99  cnf(c_758,plain,
% 3.55/0.99      ( k4_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK1),sK2) = k3_enumset1(sK0,sK0,sK0,sK0,sK1)
% 3.55/0.99      | r2_hidden(sK0,sK2) != iProver_top ),
% 3.55/0.99      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 3.55/0.99  
% 3.55/0.99  cnf(c_23,negated_conjecture,
% 3.55/0.99      ( ~ r2_hidden(sK1,sK2)
% 3.55/0.99      | k4_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK1),sK2) = k3_enumset1(sK0,sK0,sK0,sK0,sK1) ),
% 3.55/0.99      inference(cnf_transformation,[],[f79]) ).
% 3.55/0.99  
% 3.55/0.99  cnf(c_11,plain,
% 3.55/0.99      ( ~ r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) = X0 ),
% 3.55/0.99      inference(cnf_transformation,[],[f47]) ).
% 3.55/0.99  
% 3.55/0.99  cnf(c_803,plain,
% 3.55/0.99      ( ~ r1_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK1),sK2)
% 3.55/0.99      | k4_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK1),sK2) = k3_enumset1(sK0,sK0,sK0,sK0,sK1) ),
% 3.55/0.99      inference(instantiation,[status(thm)],[c_11]) ).
% 3.55/0.99  
% 3.55/0.99  cnf(c_21,plain,
% 3.55/0.99      ( r1_xboole_0(k3_enumset1(X0,X0,X0,X0,X1),X2)
% 3.55/0.99      | r2_hidden(X0,X2)
% 3.55/0.99      | r2_hidden(X1,X2) ),
% 3.55/0.99      inference(cnf_transformation,[],[f77]) ).
% 3.55/0.99  
% 3.55/0.99  cnf(c_876,plain,
% 3.55/0.99      ( r1_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK1),sK2)
% 3.55/0.99      | r2_hidden(sK0,sK2)
% 3.55/0.99      | r2_hidden(sK1,sK2) ),
% 3.55/0.99      inference(instantiation,[status(thm)],[c_21]) ).
% 3.55/0.99  
% 3.55/0.99  cnf(c_933,plain,
% 3.55/0.99      ( k4_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK1),sK2) = k3_enumset1(sK0,sK0,sK0,sK0,sK1) ),
% 3.55/0.99      inference(global_propositional_subsumption,
% 3.55/0.99                [status(thm)],
% 3.55/0.99                [c_758,c_24,c_23,c_803,c_876]) ).
% 3.55/0.99  
% 3.55/0.99  cnf(c_14,plain,
% 3.55/0.99      ( r1_tarski(k4_xboole_0(X0,X1),k5_xboole_0(X0,X1)) ),
% 3.55/0.99      inference(cnf_transformation,[],[f52]) ).
% 3.55/0.99  
% 3.55/0.99  cnf(c_766,plain,
% 3.55/0.99      ( r1_tarski(k4_xboole_0(X0,X1),k5_xboole_0(X0,X1)) = iProver_top ),
% 3.55/0.99      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 3.55/0.99  
% 3.55/0.99  cnf(c_989,plain,
% 3.55/0.99      ( r1_tarski(k3_enumset1(sK0,sK0,sK0,sK0,sK1),k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK1),sK2)) = iProver_top ),
% 3.55/0.99      inference(superposition,[status(thm)],[c_933,c_766]) ).
% 3.55/0.99  
% 3.55/0.99  cnf(c_1218,plain,
% 3.55/0.99      ( r1_tarski(k3_enumset1(sK1,sK1,sK1,sK1,sK0),k5_xboole_0(k3_enumset1(sK1,sK1,sK1,sK1,sK0),sK2)) = iProver_top ),
% 3.55/0.99      inference(demodulation,[status(thm)],[c_15,c_989]) ).
% 3.55/0.99  
% 3.55/0.99  cnf(c_19,plain,
% 3.55/0.99      ( ~ r1_tarski(k3_enumset1(X0,X0,X0,X0,X1),X2) | r2_hidden(X1,X2) ),
% 3.55/0.99      inference(cnf_transformation,[],[f75]) ).
% 3.55/0.99  
% 3.55/0.99  cnf(c_763,plain,
% 3.55/0.99      ( r1_tarski(k3_enumset1(X0,X0,X0,X0,X1),X2) != iProver_top
% 3.55/0.99      | r2_hidden(X1,X2) = iProver_top ),
% 3.55/0.99      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 3.55/0.99  
% 3.55/0.99  cnf(c_2531,plain,
% 3.55/0.99      ( r2_hidden(sK0,k5_xboole_0(k3_enumset1(sK1,sK1,sK1,sK1,sK0),sK2)) = iProver_top ),
% 3.55/0.99      inference(superposition,[status(thm)],[c_1218,c_763]) ).
% 3.55/0.99  
% 3.55/0.99  cnf(c_2,plain,
% 3.55/0.99      ( ~ r2_hidden(X0,X1)
% 3.55/0.99      | ~ r2_hidden(X0,X2)
% 3.55/0.99      | ~ r2_hidden(X0,k5_xboole_0(X2,X1)) ),
% 3.55/0.99      inference(cnf_transformation,[],[f38]) ).
% 3.55/0.99  
% 3.55/0.99  cnf(c_776,plain,
% 3.55/0.99      ( r2_hidden(X0,X1) != iProver_top
% 3.55/0.99      | r2_hidden(X0,X2) != iProver_top
% 3.55/0.99      | r2_hidden(X0,k5_xboole_0(X1,X2)) != iProver_top ),
% 3.55/1.00      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 3.55/1.00  
% 3.55/1.00  cnf(c_11402,plain,
% 3.55/1.00      ( r2_hidden(sK0,k3_enumset1(sK1,sK1,sK1,sK1,sK0)) != iProver_top
% 3.55/1.00      | r2_hidden(sK0,sK2) != iProver_top ),
% 3.55/1.00      inference(superposition,[status(thm)],[c_2531,c_776]) ).
% 3.55/1.00  
% 3.55/1.00  cnf(c_1219,plain,
% 3.55/1.00      ( k4_xboole_0(k3_enumset1(sK1,sK1,sK1,sK1,sK0),sK2) = k3_enumset1(sK1,sK1,sK1,sK1,sK0) ),
% 3.55/1.00      inference(demodulation,[status(thm)],[c_15,c_933]) ).
% 3.55/1.00  
% 3.55/1.00  cnf(c_16,plain,
% 3.55/1.00      ( k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
% 3.55/1.00      inference(cnf_transformation,[],[f72]) ).
% 3.55/1.00  
% 3.55/1.00  cnf(c_1256,plain,
% 3.55/1.00      ( k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)) = k5_xboole_0(X1,k4_xboole_0(X0,X1)) ),
% 3.55/1.00      inference(superposition,[status(thm)],[c_15,c_16]) ).
% 3.55/1.00  
% 3.55/1.00  cnf(c_7,plain,
% 3.55/1.00      ( r1_tarski(X0,k5_xboole_0(X0,k4_xboole_0(X1,X0))) ),
% 3.55/1.00      inference(cnf_transformation,[],[f69]) ).
% 3.55/1.00  
% 3.55/1.00  cnf(c_772,plain,
% 3.55/1.00      ( r1_tarski(X0,k5_xboole_0(X0,k4_xboole_0(X1,X0))) = iProver_top ),
% 3.55/1.00      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 3.55/1.00  
% 3.55/1.00  cnf(c_2816,plain,
% 3.55/1.00      ( r1_tarski(X0,k3_tarski(k3_enumset1(X1,X1,X1,X1,X0))) = iProver_top ),
% 3.55/1.00      inference(superposition,[status(thm)],[c_1256,c_772]) ).
% 3.55/1.00  
% 3.55/1.00  cnf(c_2820,plain,
% 3.55/1.00      ( r1_tarski(X0,k5_xboole_0(X1,k4_xboole_0(X0,X1))) = iProver_top ),
% 3.55/1.00      inference(demodulation,[status(thm)],[c_2816,c_16]) ).
% 3.55/1.00  
% 3.55/1.00  cnf(c_3035,plain,
% 3.55/1.00      ( r1_tarski(k3_enumset1(sK1,sK1,sK1,sK1,sK0),k5_xboole_0(sK2,k3_enumset1(sK1,sK1,sK1,sK1,sK0))) = iProver_top ),
% 3.55/1.00      inference(superposition,[status(thm)],[c_1219,c_2820]) ).
% 3.55/1.00  
% 3.55/1.00  cnf(c_20,plain,
% 3.55/1.00      ( ~ r1_tarski(k3_enumset1(X0,X0,X0,X0,X1),X2) | r2_hidden(X0,X2) ),
% 3.55/1.00      inference(cnf_transformation,[],[f76]) ).
% 3.55/1.00  
% 3.55/1.00  cnf(c_762,plain,
% 3.55/1.00      ( r1_tarski(k3_enumset1(X0,X0,X0,X0,X1),X2) != iProver_top
% 3.55/1.00      | r2_hidden(X0,X2) = iProver_top ),
% 3.55/1.00      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 3.55/1.00  
% 3.55/1.00  cnf(c_3238,plain,
% 3.55/1.00      ( r2_hidden(sK1,k5_xboole_0(sK2,k3_enumset1(sK1,sK1,sK1,sK1,sK0))) = iProver_top ),
% 3.55/1.00      inference(superposition,[status(thm)],[c_3035,c_762]) ).
% 3.55/1.00  
% 3.55/1.00  cnf(c_11404,plain,
% 3.55/1.00      ( r2_hidden(sK1,k3_enumset1(sK1,sK1,sK1,sK1,sK0)) != iProver_top
% 3.55/1.00      | r2_hidden(sK1,sK2) != iProver_top ),
% 3.55/1.00      inference(superposition,[status(thm)],[c_3238,c_776]) ).
% 3.55/1.00  
% 3.55/1.00  cnf(c_5,plain,
% 3.55/1.00      ( ~ r1_tarski(X0,k5_xboole_0(X1,k4_xboole_0(X2,X1)))
% 3.55/1.00      | r1_tarski(k4_xboole_0(X0,X1),X2) ),
% 3.55/1.00      inference(cnf_transformation,[],[f67]) ).
% 3.55/1.00  
% 3.55/1.00  cnf(c_773,plain,
% 3.55/1.00      ( r1_tarski(X0,k5_xboole_0(X1,k4_xboole_0(X2,X1))) != iProver_top
% 3.55/1.00      | r1_tarski(k4_xboole_0(X0,X1),X2) = iProver_top ),
% 3.55/1.00      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 3.55/1.00  
% 3.55/1.00  cnf(c_5973,plain,
% 3.55/1.00      ( r1_tarski(X0,k5_xboole_0(sK2,k3_enumset1(sK1,sK1,sK1,sK1,sK0))) != iProver_top
% 3.55/1.00      | r1_tarski(k4_xboole_0(X0,sK2),k3_enumset1(sK1,sK1,sK1,sK1,sK0)) = iProver_top ),
% 3.55/1.00      inference(superposition,[status(thm)],[c_1219,c_773]) ).
% 3.55/1.00  
% 3.55/1.00  cnf(c_6951,plain,
% 3.55/1.00      ( r1_tarski(k4_xboole_0(k3_enumset1(sK1,sK1,sK1,sK1,sK0),sK2),k3_enumset1(sK1,sK1,sK1,sK1,sK0)) = iProver_top ),
% 3.55/1.00      inference(superposition,[status(thm)],[c_3035,c_5973]) ).
% 3.55/1.00  
% 3.55/1.00  cnf(c_6952,plain,
% 3.55/1.00      ( r1_tarski(k3_enumset1(sK1,sK1,sK1,sK1,sK0),k3_enumset1(sK1,sK1,sK1,sK1,sK0)) = iProver_top ),
% 3.55/1.00      inference(light_normalisation,[status(thm)],[c_6951,c_1219]) ).
% 3.55/1.00  
% 3.55/1.00  cnf(c_6960,plain,
% 3.55/1.00      ( r2_hidden(sK0,k3_enumset1(sK1,sK1,sK1,sK1,sK0)) = iProver_top ),
% 3.55/1.00      inference(superposition,[status(thm)],[c_6952,c_763]) ).
% 3.55/1.00  
% 3.55/1.00  cnf(c_17,plain,
% 3.55/1.00      ( r1_tarski(k3_enumset1(X0,X0,X0,X0,X0),k3_enumset1(X0,X0,X0,X0,X1)) ),
% 3.55/1.00      inference(cnf_transformation,[],[f73]) ).
% 3.55/1.00  
% 3.55/1.00  cnf(c_1915,plain,
% 3.55/1.00      ( r1_tarski(k3_enumset1(sK1,sK1,sK1,sK1,sK1),k3_enumset1(sK1,sK1,sK1,sK1,X0)) ),
% 3.55/1.00      inference(instantiation,[status(thm)],[c_17]) ).
% 3.55/1.00  
% 3.55/1.00  cnf(c_1916,plain,
% 3.55/1.00      ( r1_tarski(k3_enumset1(sK1,sK1,sK1,sK1,sK1),k3_enumset1(sK1,sK1,sK1,sK1,X0)) = iProver_top ),
% 3.55/1.00      inference(predicate_to_equality,[status(thm)],[c_1915]) ).
% 3.55/1.00  
% 3.55/1.00  cnf(c_1918,plain,
% 3.55/1.00      ( r1_tarski(k3_enumset1(sK1,sK1,sK1,sK1,sK1),k3_enumset1(sK1,sK1,sK1,sK1,sK0)) = iProver_top ),
% 3.55/1.00      inference(instantiation,[status(thm)],[c_1916]) ).
% 3.55/1.00  
% 3.55/1.00  cnf(c_1048,plain,
% 3.55/1.00      ( ~ r1_tarski(k3_enumset1(sK1,sK1,sK1,sK1,X0),X1)
% 3.55/1.00      | r2_hidden(sK1,X1) ),
% 3.55/1.00      inference(instantiation,[status(thm)],[c_20]) ).
% 3.55/1.00  
% 3.55/1.00  cnf(c_1195,plain,
% 3.55/1.00      ( ~ r1_tarski(k3_enumset1(sK1,sK1,sK1,sK1,sK1),k3_enumset1(sK1,sK1,sK1,sK1,X0))
% 3.55/1.00      | r2_hidden(sK1,k3_enumset1(sK1,sK1,sK1,sK1,X0)) ),
% 3.55/1.00      inference(instantiation,[status(thm)],[c_1048]) ).
% 3.55/1.00  
% 3.55/1.00  cnf(c_1196,plain,
% 3.55/1.00      ( r1_tarski(k3_enumset1(sK1,sK1,sK1,sK1,sK1),k3_enumset1(sK1,sK1,sK1,sK1,X0)) != iProver_top
% 3.55/1.00      | r2_hidden(sK1,k3_enumset1(sK1,sK1,sK1,sK1,X0)) = iProver_top ),
% 3.55/1.00      inference(predicate_to_equality,[status(thm)],[c_1195]) ).
% 3.55/1.00  
% 3.55/1.00  cnf(c_1198,plain,
% 3.55/1.00      ( r1_tarski(k3_enumset1(sK1,sK1,sK1,sK1,sK1),k3_enumset1(sK1,sK1,sK1,sK1,sK0)) != iProver_top
% 3.55/1.00      | r2_hidden(sK1,k3_enumset1(sK1,sK1,sK1,sK1,sK0)) = iProver_top ),
% 3.55/1.00      inference(instantiation,[status(thm)],[c_1196]) ).
% 3.55/1.00  
% 3.55/1.00  cnf(c_22,negated_conjecture,
% 3.55/1.00      ( r2_hidden(sK0,sK2)
% 3.55/1.00      | r2_hidden(sK1,sK2)
% 3.55/1.00      | k4_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK1),sK2) != k3_enumset1(sK0,sK0,sK0,sK0,sK1) ),
% 3.55/1.00      inference(cnf_transformation,[],[f78]) ).
% 3.55/1.00  
% 3.55/1.00  cnf(c_760,plain,
% 3.55/1.00      ( k4_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK1),sK2) != k3_enumset1(sK0,sK0,sK0,sK0,sK1)
% 3.55/1.00      | r2_hidden(sK0,sK2) = iProver_top
% 3.55/1.00      | r2_hidden(sK1,sK2) = iProver_top ),
% 3.55/1.00      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 3.55/1.00  
% 3.55/1.00  cnf(c_27,plain,
% 3.55/1.00      ( k4_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK1),sK2) != k3_enumset1(sK0,sK0,sK0,sK0,sK1)
% 3.55/1.00      | r2_hidden(sK0,sK2) = iProver_top
% 3.55/1.00      | r2_hidden(sK1,sK2) = iProver_top ),
% 3.55/1.00      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 3.55/1.00  
% 3.55/1.00  cnf(c_936,plain,
% 3.55/1.00      ( r2_hidden(sK0,sK2) = iProver_top
% 3.55/1.00      | r2_hidden(sK1,sK2) = iProver_top ),
% 3.55/1.00      inference(global_propositional_subsumption,
% 3.55/1.00                [status(thm)],
% 3.55/1.00                [c_760,c_24,c_23,c_27,c_803,c_876]) ).
% 3.55/1.00  
% 3.55/1.00  cnf(contradiction,plain,
% 3.55/1.00      ( $false ),
% 3.55/1.00      inference(minisat,
% 3.55/1.00                [status(thm)],
% 3.55/1.00                [c_11402,c_11404,c_6960,c_1918,c_1198,c_936]) ).
% 3.55/1.00  
% 3.55/1.00  
% 3.55/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 3.55/1.00  
% 3.55/1.00  ------                               Statistics
% 3.55/1.00  
% 3.55/1.00  ------ General
% 3.55/1.00  
% 3.55/1.00  abstr_ref_over_cycles:                  0
% 3.55/1.00  abstr_ref_under_cycles:                 0
% 3.55/1.00  gc_basic_clause_elim:                   0
% 3.55/1.00  forced_gc_time:                         0
% 3.55/1.00  parsing_time:                           0.007
% 3.55/1.00  unif_index_cands_time:                  0.
% 3.55/1.00  unif_index_add_time:                    0.
% 3.55/1.00  orderings_time:                         0.
% 3.55/1.00  out_proof_time:                         0.008
% 3.55/1.00  total_time:                             0.33
% 3.55/1.00  num_of_symbols:                         42
% 3.55/1.00  num_of_terms:                           15353
% 3.55/1.00  
% 3.55/1.00  ------ Preprocessing
% 3.55/1.00  
% 3.55/1.00  num_of_splits:                          0
% 3.55/1.00  num_of_split_atoms:                     0
% 3.55/1.00  num_of_reused_defs:                     0
% 3.55/1.00  num_eq_ax_congr_red:                    0
% 3.55/1.00  num_of_sem_filtered_clauses:            1
% 3.55/1.00  num_of_subtypes:                        0
% 3.55/1.00  monotx_restored_types:                  0
% 3.55/1.00  sat_num_of_epr_types:                   0
% 3.55/1.00  sat_num_of_non_cyclic_types:            0
% 3.55/1.00  sat_guarded_non_collapsed_types:        0
% 3.55/1.00  num_pure_diseq_elim:                    0
% 3.55/1.00  simp_replaced_by:                       0
% 3.55/1.00  res_preprocessed:                       94
% 3.55/1.00  prep_upred:                             0
% 3.55/1.00  prep_unflattend:                        0
% 3.55/1.00  smt_new_axioms:                         0
% 3.55/1.00  pred_elim_cands:                        3
% 3.55/1.00  pred_elim:                              0
% 3.55/1.00  pred_elim_cl:                           0
% 3.55/1.00  pred_elim_cycles:                       1
% 3.55/1.00  merged_defs:                            6
% 3.55/1.00  merged_defs_ncl:                        0
% 3.55/1.00  bin_hyper_res:                          6
% 3.55/1.00  prep_cycles:                            3
% 3.55/1.00  pred_elim_time:                         0.
% 3.55/1.00  splitting_time:                         0.
% 3.55/1.00  sem_filter_time:                        0.
% 3.55/1.00  monotx_time:                            0.
% 3.55/1.00  subtype_inf_time:                       0.
% 3.55/1.00  
% 3.55/1.00  ------ Problem properties
% 3.55/1.00  
% 3.55/1.00  clauses:                                25
% 3.55/1.00  conjectures:                            3
% 3.55/1.00  epr:                                    0
% 3.55/1.00  horn:                                   20
% 3.55/1.00  ground:                                 3
% 3.55/1.00  unary:                                  9
% 3.55/1.00  binary:                                 9
% 3.55/1.00  lits:                                   48
% 3.55/1.00  lits_eq:                                10
% 3.55/1.00  fd_pure:                                0
% 3.55/1.00  fd_pseudo:                              0
% 3.55/1.00  fd_cond:                                1
% 3.55/1.00  fd_pseudo_cond:                         0
% 3.55/1.00  ac_symbols:                             0
% 3.55/1.00  
% 3.55/1.00  ------ Propositional Solver
% 3.55/1.00  
% 3.55/1.00  prop_solver_calls:                      27
% 3.55/1.00  prop_fast_solver_calls:                 540
% 3.55/1.00  smt_solver_calls:                       0
% 3.55/1.00  smt_fast_solver_calls:                  0
% 3.55/1.00  prop_num_of_clauses:                    4297
% 3.55/1.00  prop_preprocess_simplified:             6587
% 3.55/1.00  prop_fo_subsumed:                       2
% 3.55/1.00  prop_solver_time:                       0.
% 3.55/1.00  smt_solver_time:                        0.
% 3.55/1.00  smt_fast_solver_time:                   0.
% 3.55/1.00  prop_fast_solver_time:                  0.
% 3.55/1.00  prop_unsat_core_time:                   0.
% 3.55/1.00  
% 3.55/1.00  ------ QBF
% 3.55/1.00  
% 3.55/1.00  qbf_q_res:                              0
% 3.55/1.00  qbf_num_tautologies:                    0
% 3.55/1.00  qbf_prep_cycles:                        0
% 3.55/1.00  
% 3.55/1.00  ------ BMC1
% 3.55/1.00  
% 3.55/1.00  bmc1_current_bound:                     -1
% 3.55/1.00  bmc1_last_solved_bound:                 -1
% 3.55/1.00  bmc1_unsat_core_size:                   -1
% 3.55/1.00  bmc1_unsat_core_parents_size:           -1
% 3.55/1.00  bmc1_merge_next_fun:                    0
% 3.55/1.00  bmc1_unsat_core_clauses_time:           0.
% 3.55/1.00  
% 3.55/1.00  ------ Instantiation
% 3.55/1.00  
% 3.55/1.00  inst_num_of_clauses:                    843
% 3.55/1.00  inst_num_in_passive:                    77
% 3.55/1.00  inst_num_in_active:                     397
% 3.55/1.00  inst_num_in_unprocessed:                369
% 3.55/1.00  inst_num_of_loops:                      480
% 3.55/1.00  inst_num_of_learning_restarts:          0
% 3.55/1.00  inst_num_moves_active_passive:          77
% 3.55/1.00  inst_lit_activity:                      0
% 3.55/1.00  inst_lit_activity_moves:                0
% 3.55/1.00  inst_num_tautologies:                   0
% 3.55/1.00  inst_num_prop_implied:                  0
% 3.55/1.00  inst_num_existing_simplified:           0
% 3.55/1.00  inst_num_eq_res_simplified:             0
% 3.55/1.00  inst_num_child_elim:                    0
% 3.55/1.00  inst_num_of_dismatching_blockings:      2012
% 3.55/1.00  inst_num_of_non_proper_insts:           1660
% 3.55/1.00  inst_num_of_duplicates:                 0
% 3.55/1.00  inst_inst_num_from_inst_to_res:         0
% 3.55/1.00  inst_dismatching_checking_time:         0.
% 3.55/1.00  
% 3.55/1.00  ------ Resolution
% 3.55/1.00  
% 3.55/1.00  res_num_of_clauses:                     0
% 3.55/1.00  res_num_in_passive:                     0
% 3.55/1.00  res_num_in_active:                      0
% 3.55/1.00  res_num_of_loops:                       97
% 3.55/1.00  res_forward_subset_subsumed:            49
% 3.55/1.00  res_backward_subset_subsumed:           12
% 3.55/1.00  res_forward_subsumed:                   0
% 3.55/1.00  res_backward_subsumed:                  0
% 3.55/1.00  res_forward_subsumption_resolution:     0
% 3.55/1.00  res_backward_subsumption_resolution:    0
% 3.55/1.00  res_clause_to_clause_subsumption:       2477
% 3.55/1.00  res_orphan_elimination:                 0
% 3.55/1.00  res_tautology_del:                      92
% 3.55/1.00  res_num_eq_res_simplified:              0
% 3.55/1.00  res_num_sel_changes:                    0
% 3.55/1.00  res_moves_from_active_to_pass:          0
% 3.55/1.00  
% 3.55/1.00  ------ Superposition
% 3.55/1.00  
% 3.55/1.00  sup_time_total:                         0.
% 3.55/1.00  sup_time_generating:                    0.
% 3.55/1.00  sup_time_sim_full:                      0.
% 3.55/1.00  sup_time_sim_immed:                     0.
% 3.55/1.00  
% 3.55/1.00  sup_num_of_clauses:                     606
% 3.55/1.00  sup_num_in_active:                      82
% 3.55/1.00  sup_num_in_passive:                     524
% 3.55/1.00  sup_num_of_loops:                       95
% 3.55/1.00  sup_fw_superposition:                   607
% 3.55/1.00  sup_bw_superposition:                   456
% 3.55/1.00  sup_immediate_simplified:               382
% 3.55/1.00  sup_given_eliminated:                   1
% 3.55/1.00  comparisons_done:                       0
% 3.55/1.00  comparisons_avoided:                    0
% 3.55/1.00  
% 3.55/1.00  ------ Simplifications
% 3.55/1.00  
% 3.55/1.00  
% 3.55/1.00  sim_fw_subset_subsumed:                 2
% 3.55/1.00  sim_bw_subset_subsumed:                 1
% 3.55/1.00  sim_fw_subsumed:                        34
% 3.55/1.00  sim_bw_subsumed:                        6
% 3.55/1.00  sim_fw_subsumption_res:                 0
% 3.55/1.00  sim_bw_subsumption_res:                 0
% 3.55/1.00  sim_tautology_del:                      4
% 3.55/1.00  sim_eq_tautology_del:                   25
% 3.55/1.00  sim_eq_res_simp:                        0
% 3.55/1.00  sim_fw_demodulated:                     263
% 3.55/1.00  sim_bw_demodulated:                     56
% 3.55/1.00  sim_light_normalised:                   166
% 3.55/1.00  sim_joinable_taut:                      0
% 3.55/1.00  sim_joinable_simp:                      0
% 3.55/1.00  sim_ac_normalised:                      0
% 3.55/1.00  sim_smt_subsumption:                    0
% 3.55/1.00  
%------------------------------------------------------------------------------
