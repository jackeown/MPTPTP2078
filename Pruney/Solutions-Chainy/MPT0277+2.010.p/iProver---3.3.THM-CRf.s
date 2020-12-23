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
% DateTime   : Thu Dec  3 11:36:30 EST 2020

% Result     : Theorem 2.89s
% Output     : CNFRefutation 2.89s
% Verified   : 
% Statistics : Number of formulae       :   74 ( 789 expanded)
%              Number of clauses        :   37 ( 199 expanded)
%              Number of leaves         :    7 ( 172 expanded)
%              Depth                    :   23
%              Number of atoms          :  240 (3583 expanded)
%              Number of equality atoms :  216 (3240 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal clause size      :   20 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f13,conjecture,(
    ! [X0,X1,X2] :
      ( k1_xboole_0 = k4_xboole_0(X0,k2_tarski(X1,X2))
    <=> ~ ( k2_tarski(X1,X2) != X0
          & k1_tarski(X2) != X0
          & k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( k1_xboole_0 = k4_xboole_0(X0,k2_tarski(X1,X2))
      <=> ~ ( k2_tarski(X1,X2) != X0
            & k1_tarski(X2) != X0
            & k1_tarski(X1) != X0
            & k1_xboole_0 != X0 ) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f19,plain,(
    ? [X0,X1,X2] :
      ( k1_xboole_0 = k4_xboole_0(X0,k2_tarski(X1,X2))
    <~> ( k2_tarski(X1,X2) = X0
        | k1_tarski(X2) = X0
        | k1_tarski(X1) = X0
        | k1_xboole_0 = X0 ) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f29,plain,(
    ? [X0,X1,X2] :
      ( ( ( k2_tarski(X1,X2) != X0
          & k1_tarski(X2) != X0
          & k1_tarski(X1) != X0
          & k1_xboole_0 != X0 )
        | k1_xboole_0 != k4_xboole_0(X0,k2_tarski(X1,X2)) )
      & ( k2_tarski(X1,X2) = X0
        | k1_tarski(X2) = X0
        | k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | k1_xboole_0 = k4_xboole_0(X0,k2_tarski(X1,X2)) ) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f30,plain,(
    ? [X0,X1,X2] :
      ( ( ( k2_tarski(X1,X2) != X0
          & k1_tarski(X2) != X0
          & k1_tarski(X1) != X0
          & k1_xboole_0 != X0 )
        | k1_xboole_0 != k4_xboole_0(X0,k2_tarski(X1,X2)) )
      & ( k2_tarski(X1,X2) = X0
        | k1_tarski(X2) = X0
        | k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | k1_xboole_0 = k4_xboole_0(X0,k2_tarski(X1,X2)) ) ) ),
    inference(flattening,[],[f29])).

fof(f31,plain,
    ( ? [X0,X1,X2] :
        ( ( ( k2_tarski(X1,X2) != X0
            & k1_tarski(X2) != X0
            & k1_tarski(X1) != X0
            & k1_xboole_0 != X0 )
          | k1_xboole_0 != k4_xboole_0(X0,k2_tarski(X1,X2)) )
        & ( k2_tarski(X1,X2) = X0
          | k1_tarski(X2) = X0
          | k1_tarski(X1) = X0
          | k1_xboole_0 = X0
          | k1_xboole_0 = k4_xboole_0(X0,k2_tarski(X1,X2)) ) )
   => ( ( ( k2_tarski(sK2,sK3) != sK1
          & k1_tarski(sK3) != sK1
          & k1_tarski(sK2) != sK1
          & k1_xboole_0 != sK1 )
        | k1_xboole_0 != k4_xboole_0(sK1,k2_tarski(sK2,sK3)) )
      & ( k2_tarski(sK2,sK3) = sK1
        | k1_tarski(sK3) = sK1
        | k1_tarski(sK2) = sK1
        | k1_xboole_0 = sK1
        | k1_xboole_0 = k4_xboole_0(sK1,k2_tarski(sK2,sK3)) ) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,
    ( ( ( k2_tarski(sK2,sK3) != sK1
        & k1_tarski(sK3) != sK1
        & k1_tarski(sK2) != sK1
        & k1_xboole_0 != sK1 )
      | k1_xboole_0 != k4_xboole_0(sK1,k2_tarski(sK2,sK3)) )
    & ( k2_tarski(sK2,sK3) = sK1
      | k1_tarski(sK3) = sK1
      | k1_tarski(sK2) = sK1
      | k1_xboole_0 = sK1
      | k1_xboole_0 = k4_xboole_0(sK1,k2_tarski(sK2,sK3)) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f30,f31])).

fof(f56,plain,
    ( k2_tarski(sK2,sK3) = sK1
    | k1_tarski(sK3) = sK1
    | k1_tarski(sK2) = sK1
    | k1_xboole_0 = sK1
    | k1_xboole_0 = k4_xboole_0(sK1,k2_tarski(sK2,sK3)) ),
    inference(cnf_transformation,[],[f32])).

fof(f8,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f8])).

fof(f70,plain,
    ( k2_tarski(sK2,sK3) = sK1
    | k2_tarski(sK3,sK3) = sK1
    | k2_tarski(sK2,sK2) = sK1
    | k1_xboole_0 = sK1
    | k1_xboole_0 = k4_xboole_0(sK1,k2_tarski(sK2,sK3)) ),
    inference(definition_unfolding,[],[f56,f46,f46])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,X1)
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k4_xboole_0(X0,X1)
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k1_xboole_0 != k4_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f35,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | k1_xboole_0 != k4_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_tarski(X1,X2))
    <=> ~ ( k2_tarski(X1,X2) != X0
          & k1_tarski(X2) != X0
          & k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_tarski(X1,X2))
    <=> ( k2_tarski(X1,X2) = X0
        | k1_tarski(X2) = X0
        | k1_tarski(X1) = X0
        | k1_xboole_0 = X0 ) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X0,k2_tarski(X1,X2))
        | ( k2_tarski(X1,X2) != X0
          & k1_tarski(X2) != X0
          & k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k2_tarski(X1,X2) = X0
        | k1_tarski(X2) = X0
        | k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k2_tarski(X1,X2)) ) ) ),
    inference(nnf_transformation,[],[f18])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X0,k2_tarski(X1,X2))
        | ( k2_tarski(X1,X2) != X0
          & k1_tarski(X2) != X0
          & k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k2_tarski(X1,X2) = X0
        | k1_tarski(X2) = X0
        | k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k2_tarski(X1,X2)) ) ) ),
    inference(flattening,[],[f26])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( k2_tarski(X1,X2) = X0
      | k1_tarski(X2) = X0
      | k1_tarski(X1) = X0
      | k1_xboole_0 = X0
      | ~ r1_tarski(X0,k2_tarski(X1,X2)) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( k2_tarski(X1,X2) = X0
      | k2_tarski(X2,X2) = X0
      | k2_tarski(X1,X1) = X0
      | k1_xboole_0 = X0
      | ~ r1_tarski(X0,k2_tarski(X1,X2)) ) ),
    inference(definition_unfolding,[],[f48,f46,f46])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k2_tarski(X1,X2))
      | k1_tarski(X2) != X0 ) ),
    inference(cnf_transformation,[],[f27])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k2_tarski(X1,X2))
      | k2_tarski(X2,X2) != X0 ) ),
    inference(definition_unfolding,[],[f51,f46])).

fof(f77,plain,(
    ! [X2,X1] : r1_tarski(k2_tarski(X2,X2),k2_tarski(X1,X2)) ),
    inference(equality_resolution,[],[f62])).

fof(f36,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f59,plain,
    ( k1_tarski(sK3) != sK1
    | k1_xboole_0 != k4_xboole_0(sK1,k2_tarski(sK2,sK3)) ),
    inference(cnf_transformation,[],[f32])).

fof(f68,plain,
    ( k2_tarski(sK3,sK3) != sK1
    | k1_xboole_0 != k4_xboole_0(sK1,k2_tarski(sK2,sK3)) ),
    inference(definition_unfolding,[],[f59,f46])).

fof(f11,axiom,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(k1_tarski(X0),k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f53,plain,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(k1_tarski(X0),k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f11])).

fof(f65,plain,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(k2_tarski(X0,X0),k2_tarski(X0,X1)) ),
    inference(definition_unfolding,[],[f53,f46])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k2_tarski(X1,X2))
      | k2_tarski(X1,X2) != X0 ) ),
    inference(cnf_transformation,[],[f27])).

fof(f76,plain,(
    ! [X2,X1] : r1_tarski(k2_tarski(X1,X2),k2_tarski(X1,X2)) ),
    inference(equality_resolution,[],[f52])).

fof(f60,plain,
    ( k2_tarski(sK2,sK3) != sK1
    | k1_xboole_0 != k4_xboole_0(sK1,k2_tarski(sK2,sK3)) ),
    inference(cnf_transformation,[],[f32])).

fof(f58,plain,
    ( k1_tarski(sK2) != sK1
    | k1_xboole_0 != k4_xboole_0(sK1,k2_tarski(sK2,sK3)) ),
    inference(cnf_transformation,[],[f32])).

fof(f69,plain,
    ( k2_tarski(sK2,sK2) != sK1
    | k1_xboole_0 != k4_xboole_0(sK1,k2_tarski(sK2,sK3)) ),
    inference(definition_unfolding,[],[f58,f46])).

fof(f57,plain,
    ( k1_xboole_0 != sK1
    | k1_xboole_0 != k4_xboole_0(sK1,k2_tarski(sK2,sK3)) ),
    inference(cnf_transformation,[],[f32])).

fof(f6,axiom,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f6])).

cnf(c_26,negated_conjecture,
    ( k2_tarski(sK3,sK3) = sK1
    | k2_tarski(sK2,sK3) = sK1
    | k2_tarski(sK2,sK2) = sK1
    | k1_xboole_0 = k4_xboole_0(sK1,k2_tarski(sK2,sK3))
    | k1_xboole_0 = sK1 ),
    inference(cnf_transformation,[],[f70])).

cnf(c_3,plain,
    ( r1_tarski(X0,X1)
    | k4_xboole_0(X0,X1) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f35])).

cnf(c_963,plain,
    ( k4_xboole_0(X0,X1) != k1_xboole_0
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_1564,plain,
    ( k2_tarski(sK3,sK3) = sK1
    | k2_tarski(sK2,sK3) = sK1
    | k2_tarski(sK2,sK2) = sK1
    | sK1 = k1_xboole_0
    | r1_tarski(sK1,k2_tarski(sK2,sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_26,c_963])).

cnf(c_18,plain,
    ( ~ r1_tarski(X0,k2_tarski(X1,X2))
    | k2_tarski(X1,X2) = X0
    | k2_tarski(X2,X2) = X0
    | k2_tarski(X1,X1) = X0
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f64])).

cnf(c_950,plain,
    ( k2_tarski(X0,X1) = X2
    | k2_tarski(X1,X1) = X2
    | k2_tarski(X0,X0) = X2
    | k1_xboole_0 = X2
    | r1_tarski(X2,k2_tarski(X0,X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_3004,plain,
    ( k2_tarski(sK3,sK3) = sK1
    | k2_tarski(sK2,sK3) = sK1
    | k2_tarski(sK2,sK2) = sK1
    | sK1 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1564,c_950])).

cnf(c_15,plain,
    ( r1_tarski(k2_tarski(X0,X0),k2_tarski(X1,X0)) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_953,plain,
    ( r1_tarski(k2_tarski(X0,X0),k2_tarski(X1,X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_2,plain,
    ( ~ r1_tarski(X0,X1)
    | k4_xboole_0(X0,X1) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f36])).

cnf(c_964,plain,
    ( k4_xboole_0(X0,X1) = k1_xboole_0
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_1684,plain,
    ( k4_xboole_0(k2_tarski(X0,X0),k2_tarski(X1,X0)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_953,c_964])).

cnf(c_3536,plain,
    ( k2_tarski(sK2,sK3) = sK1
    | k2_tarski(sK2,sK2) = sK1
    | k4_xboole_0(sK1,k2_tarski(X0,sK3)) = k1_xboole_0
    | sK1 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_3004,c_1684])).

cnf(c_23,negated_conjecture,
    ( k2_tarski(sK3,sK3) != sK1
    | k1_xboole_0 != k4_xboole_0(sK1,k2_tarski(sK2,sK3)) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_4395,plain,
    ( k2_tarski(sK3,sK3) != sK1
    | k2_tarski(sK2,sK3) = sK1
    | k2_tarski(sK2,sK2) = sK1
    | sK1 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_3536,c_23])).

cnf(c_4662,plain,
    ( k2_tarski(sK2,sK3) = sK1
    | k2_tarski(sK2,sK2) = sK1
    | sK1 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_4395,c_3004])).

cnf(c_19,plain,
    ( k4_xboole_0(k2_tarski(X0,X0),k2_tarski(X0,X1)) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f65])).

cnf(c_4675,plain,
    ( k2_tarski(sK2,sK2) = sK1
    | k4_xboole_0(k2_tarski(sK2,sK2),sK1) = k1_xboole_0
    | sK1 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_4662,c_19])).

cnf(c_14,plain,
    ( r1_tarski(k2_tarski(X0,X1),k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_954,plain,
    ( r1_tarski(k2_tarski(X0,X1),k2_tarski(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_1683,plain,
    ( k4_xboole_0(k2_tarski(X0,X1),k2_tarski(X0,X1)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_954,c_964])).

cnf(c_3522,plain,
    ( k2_tarski(sK2,sK3) = sK1
    | k2_tarski(sK2,sK2) = sK1
    | k4_xboole_0(sK1,sK1) = k1_xboole_0
    | sK1 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_3004,c_1683])).

cnf(c_3839,plain,
    ( k2_tarski(sK2,sK2) = sK1
    | k4_xboole_0(sK1,sK1) = k1_xboole_0
    | sK1 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_3522,c_1683])).

cnf(c_22,negated_conjecture,
    ( k2_tarski(sK2,sK3) != sK1
    | k1_xboole_0 != k4_xboole_0(sK1,k2_tarski(sK2,sK3)) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_4685,plain,
    ( k2_tarski(sK2,sK3) != sK1
    | k2_tarski(sK2,sK2) = sK1
    | k4_xboole_0(sK1,sK1) != k1_xboole_0
    | sK1 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_4662,c_22])).

cnf(c_4692,plain,
    ( k2_tarski(sK2,sK2) = sK1
    | k4_xboole_0(sK1,sK1) != k1_xboole_0
    | sK1 = k1_xboole_0 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_4685,c_4662])).

cnf(c_5040,plain,
    ( k2_tarski(sK2,sK2) = sK1
    | sK1 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_4675,c_3839,c_4692])).

cnf(c_5063,plain,
    ( k4_xboole_0(sK1,k2_tarski(sK2,X0)) = k1_xboole_0
    | sK1 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_5040,c_19])).

cnf(c_24,negated_conjecture,
    ( k2_tarski(sK2,sK2) != sK1
    | k1_xboole_0 != k4_xboole_0(sK1,k2_tarski(sK2,sK3)) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_5256,plain,
    ( k2_tarski(sK2,sK2) != sK1
    | sK1 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_5063,c_24])).

cnf(c_5295,plain,
    ( sK1 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_5256,c_5040])).

cnf(c_25,negated_conjecture,
    ( k1_xboole_0 != k4_xboole_0(sK1,k2_tarski(sK2,sK3))
    | k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f57])).

cnf(c_5309,plain,
    ( k4_xboole_0(k1_xboole_0,k2_tarski(sK2,sK3)) != k1_xboole_0
    | k1_xboole_0 != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_5295,c_25])).

cnf(c_5310,plain,
    ( k4_xboole_0(k1_xboole_0,k2_tarski(sK2,sK3)) != k1_xboole_0 ),
    inference(equality_resolution_simp,[status(thm)],[c_5309])).

cnf(c_6,plain,
    ( k4_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f39])).

cnf(c_5312,plain,
    ( k1_xboole_0 != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_5310,c_6])).

cnf(c_5313,plain,
    ( $false ),
    inference(equality_resolution_simp,[status(thm)],[c_5312])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.11  % Command    : iproveropt_run.sh %d %s
% 0.11/0.32  % Computer   : n010.cluster.edu
% 0.11/0.32  % Model      : x86_64 x86_64
% 0.11/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.32  % Memory     : 8042.1875MB
% 0.11/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.32  % CPULimit   : 60
% 0.11/0.32  % WCLimit    : 600
% 0.11/0.32  % DateTime   : Tue Dec  1 12:35:59 EST 2020
% 0.11/0.32  % CPUTime    : 
% 0.11/0.32  % Running in FOF mode
% 2.89/0.98  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.89/0.98  
% 2.89/0.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.89/0.98  
% 2.89/0.98  ------  iProver source info
% 2.89/0.98  
% 2.89/0.98  git: date: 2020-06-30 10:37:57 +0100
% 2.89/0.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.89/0.98  git: non_committed_changes: false
% 2.89/0.98  git: last_make_outside_of_git: false
% 2.89/0.98  
% 2.89/0.98  ------ 
% 2.89/0.98  
% 2.89/0.98  ------ Input Options
% 2.89/0.98  
% 2.89/0.98  --out_options                           all
% 2.89/0.98  --tptp_safe_out                         true
% 2.89/0.98  --problem_path                          ""
% 2.89/0.98  --include_path                          ""
% 2.89/0.98  --clausifier                            res/vclausify_rel
% 2.89/0.98  --clausifier_options                    --mode clausify
% 2.89/0.98  --stdin                                 false
% 2.89/0.98  --stats_out                             all
% 2.89/0.98  
% 2.89/0.98  ------ General Options
% 2.89/0.98  
% 2.89/0.98  --fof                                   false
% 2.89/0.98  --time_out_real                         305.
% 2.89/0.98  --time_out_virtual                      -1.
% 2.89/0.98  --symbol_type_check                     false
% 2.89/0.98  --clausify_out                          false
% 2.89/0.98  --sig_cnt_out                           false
% 2.89/0.98  --trig_cnt_out                          false
% 2.89/0.98  --trig_cnt_out_tolerance                1.
% 2.89/0.98  --trig_cnt_out_sk_spl                   false
% 2.89/0.98  --abstr_cl_out                          false
% 2.89/0.98  
% 2.89/0.98  ------ Global Options
% 2.89/0.98  
% 2.89/0.98  --schedule                              default
% 2.89/0.98  --add_important_lit                     false
% 2.89/0.98  --prop_solver_per_cl                    1000
% 2.89/0.98  --min_unsat_core                        false
% 2.89/0.98  --soft_assumptions                      false
% 2.89/0.98  --soft_lemma_size                       3
% 2.89/0.98  --prop_impl_unit_size                   0
% 2.89/0.98  --prop_impl_unit                        []
% 2.89/0.98  --share_sel_clauses                     true
% 2.89/0.98  --reset_solvers                         false
% 2.89/0.98  --bc_imp_inh                            [conj_cone]
% 2.89/0.98  --conj_cone_tolerance                   3.
% 2.89/0.98  --extra_neg_conj                        none
% 2.89/0.98  --large_theory_mode                     true
% 2.89/0.98  --prolific_symb_bound                   200
% 2.89/0.98  --lt_threshold                          2000
% 2.89/0.98  --clause_weak_htbl                      true
% 2.89/0.98  --gc_record_bc_elim                     false
% 2.89/0.98  
% 2.89/0.98  ------ Preprocessing Options
% 2.89/0.98  
% 2.89/0.98  --preprocessing_flag                    true
% 2.89/0.98  --time_out_prep_mult                    0.1
% 2.89/0.98  --splitting_mode                        input
% 2.89/0.98  --splitting_grd                         true
% 2.89/0.98  --splitting_cvd                         false
% 2.89/0.98  --splitting_cvd_svl                     false
% 2.89/0.98  --splitting_nvd                         32
% 2.89/0.98  --sub_typing                            true
% 2.89/0.98  --prep_gs_sim                           true
% 2.89/0.98  --prep_unflatten                        true
% 2.89/0.98  --prep_res_sim                          true
% 2.89/0.98  --prep_upred                            true
% 2.89/0.98  --prep_sem_filter                       exhaustive
% 2.89/0.98  --prep_sem_filter_out                   false
% 2.89/0.98  --pred_elim                             true
% 2.89/0.98  --res_sim_input                         true
% 2.89/0.98  --eq_ax_congr_red                       true
% 2.89/0.98  --pure_diseq_elim                       true
% 2.89/0.98  --brand_transform                       false
% 2.89/0.98  --non_eq_to_eq                          false
% 2.89/0.98  --prep_def_merge                        true
% 2.89/0.98  --prep_def_merge_prop_impl              false
% 2.89/0.98  --prep_def_merge_mbd                    true
% 2.89/0.98  --prep_def_merge_tr_red                 false
% 2.89/0.98  --prep_def_merge_tr_cl                  false
% 2.89/0.98  --smt_preprocessing                     true
% 2.89/0.98  --smt_ac_axioms                         fast
% 2.89/0.98  --preprocessed_out                      false
% 2.89/0.98  --preprocessed_stats                    false
% 2.89/0.98  
% 2.89/0.98  ------ Abstraction refinement Options
% 2.89/0.98  
% 2.89/0.98  --abstr_ref                             []
% 2.89/0.98  --abstr_ref_prep                        false
% 2.89/0.98  --abstr_ref_until_sat                   false
% 2.89/0.98  --abstr_ref_sig_restrict                funpre
% 2.89/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 2.89/0.98  --abstr_ref_under                       []
% 2.89/0.98  
% 2.89/0.98  ------ SAT Options
% 2.89/0.98  
% 2.89/0.98  --sat_mode                              false
% 2.89/0.98  --sat_fm_restart_options                ""
% 2.89/0.98  --sat_gr_def                            false
% 2.89/0.98  --sat_epr_types                         true
% 2.89/0.98  --sat_non_cyclic_types                  false
% 2.89/0.98  --sat_finite_models                     false
% 2.89/0.98  --sat_fm_lemmas                         false
% 2.89/0.98  --sat_fm_prep                           false
% 2.89/0.98  --sat_fm_uc_incr                        true
% 2.89/0.98  --sat_out_model                         small
% 2.89/0.98  --sat_out_clauses                       false
% 2.89/0.98  
% 2.89/0.98  ------ QBF Options
% 2.89/0.98  
% 2.89/0.98  --qbf_mode                              false
% 2.89/0.98  --qbf_elim_univ                         false
% 2.89/0.98  --qbf_dom_inst                          none
% 2.89/0.98  --qbf_dom_pre_inst                      false
% 2.89/0.98  --qbf_sk_in                             false
% 2.89/0.98  --qbf_pred_elim                         true
% 2.89/0.98  --qbf_split                             512
% 2.89/0.98  
% 2.89/0.98  ------ BMC1 Options
% 2.89/0.98  
% 2.89/0.98  --bmc1_incremental                      false
% 2.89/0.98  --bmc1_axioms                           reachable_all
% 2.89/0.98  --bmc1_min_bound                        0
% 2.89/0.98  --bmc1_max_bound                        -1
% 2.89/0.98  --bmc1_max_bound_default                -1
% 2.89/0.98  --bmc1_symbol_reachability              true
% 2.89/0.98  --bmc1_property_lemmas                  false
% 2.89/0.98  --bmc1_k_induction                      false
% 2.89/0.98  --bmc1_non_equiv_states                 false
% 2.89/0.98  --bmc1_deadlock                         false
% 2.89/0.98  --bmc1_ucm                              false
% 2.89/0.98  --bmc1_add_unsat_core                   none
% 2.89/0.98  --bmc1_unsat_core_children              false
% 2.89/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 2.89/0.98  --bmc1_out_stat                         full
% 2.89/0.98  --bmc1_ground_init                      false
% 2.89/0.98  --bmc1_pre_inst_next_state              false
% 2.89/0.98  --bmc1_pre_inst_state                   false
% 2.89/0.98  --bmc1_pre_inst_reach_state             false
% 2.89/0.98  --bmc1_out_unsat_core                   false
% 2.89/0.98  --bmc1_aig_witness_out                  false
% 2.89/0.98  --bmc1_verbose                          false
% 2.89/0.98  --bmc1_dump_clauses_tptp                false
% 2.89/0.98  --bmc1_dump_unsat_core_tptp             false
% 2.89/0.98  --bmc1_dump_file                        -
% 2.89/0.98  --bmc1_ucm_expand_uc_limit              128
% 2.89/0.98  --bmc1_ucm_n_expand_iterations          6
% 2.89/0.98  --bmc1_ucm_extend_mode                  1
% 2.89/0.98  --bmc1_ucm_init_mode                    2
% 2.89/0.98  --bmc1_ucm_cone_mode                    none
% 2.89/0.98  --bmc1_ucm_reduced_relation_type        0
% 2.89/0.98  --bmc1_ucm_relax_model                  4
% 2.89/0.98  --bmc1_ucm_full_tr_after_sat            true
% 2.89/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 2.89/0.98  --bmc1_ucm_layered_model                none
% 2.89/0.98  --bmc1_ucm_max_lemma_size               10
% 2.89/0.98  
% 2.89/0.98  ------ AIG Options
% 2.89/0.98  
% 2.89/0.98  --aig_mode                              false
% 2.89/0.98  
% 2.89/0.98  ------ Instantiation Options
% 2.89/0.98  
% 2.89/0.98  --instantiation_flag                    true
% 2.89/0.98  --inst_sos_flag                         false
% 2.89/0.98  --inst_sos_phase                        true
% 2.89/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.89/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.89/0.98  --inst_lit_sel_side                     num_symb
% 2.89/0.98  --inst_solver_per_active                1400
% 2.89/0.98  --inst_solver_calls_frac                1.
% 2.89/0.98  --inst_passive_queue_type               priority_queues
% 2.89/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.89/0.98  --inst_passive_queues_freq              [25;2]
% 2.89/0.98  --inst_dismatching                      true
% 2.89/0.98  --inst_eager_unprocessed_to_passive     true
% 2.89/0.98  --inst_prop_sim_given                   true
% 2.89/0.98  --inst_prop_sim_new                     false
% 2.89/0.98  --inst_subs_new                         false
% 2.89/0.98  --inst_eq_res_simp                      false
% 2.89/0.98  --inst_subs_given                       false
% 2.89/0.98  --inst_orphan_elimination               true
% 2.89/0.98  --inst_learning_loop_flag               true
% 2.89/0.98  --inst_learning_start                   3000
% 2.89/0.98  --inst_learning_factor                  2
% 2.89/0.98  --inst_start_prop_sim_after_learn       3
% 2.89/0.98  --inst_sel_renew                        solver
% 2.89/0.98  --inst_lit_activity_flag                true
% 2.89/0.98  --inst_restr_to_given                   false
% 2.89/0.98  --inst_activity_threshold               500
% 2.89/0.98  --inst_out_proof                        true
% 2.89/0.98  
% 2.89/0.98  ------ Resolution Options
% 2.89/0.98  
% 2.89/0.98  --resolution_flag                       true
% 2.89/0.98  --res_lit_sel                           adaptive
% 2.89/0.98  --res_lit_sel_side                      none
% 2.89/0.98  --res_ordering                          kbo
% 2.89/0.98  --res_to_prop_solver                    active
% 2.89/0.98  --res_prop_simpl_new                    false
% 2.89/0.98  --res_prop_simpl_given                  true
% 2.89/0.98  --res_passive_queue_type                priority_queues
% 2.89/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.89/0.98  --res_passive_queues_freq               [15;5]
% 2.89/0.98  --res_forward_subs                      full
% 2.89/0.98  --res_backward_subs                     full
% 2.89/0.98  --res_forward_subs_resolution           true
% 2.89/0.98  --res_backward_subs_resolution          true
% 2.89/0.98  --res_orphan_elimination                true
% 2.89/0.98  --res_time_limit                        2.
% 2.89/0.98  --res_out_proof                         true
% 2.89/0.98  
% 2.89/0.98  ------ Superposition Options
% 2.89/0.98  
% 2.89/0.98  --superposition_flag                    true
% 2.89/0.98  --sup_passive_queue_type                priority_queues
% 2.89/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.89/0.98  --sup_passive_queues_freq               [8;1;4]
% 2.89/0.98  --demod_completeness_check              fast
% 2.89/0.98  --demod_use_ground                      true
% 2.89/0.98  --sup_to_prop_solver                    passive
% 2.89/0.98  --sup_prop_simpl_new                    true
% 2.89/0.98  --sup_prop_simpl_given                  true
% 2.89/0.98  --sup_fun_splitting                     false
% 2.89/0.98  --sup_smt_interval                      50000
% 2.89/0.98  
% 2.89/0.98  ------ Superposition Simplification Setup
% 2.89/0.98  
% 2.89/0.98  --sup_indices_passive                   []
% 2.89/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.89/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.89/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.89/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 2.89/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.89/0.98  --sup_full_bw                           [BwDemod]
% 2.89/0.98  --sup_immed_triv                        [TrivRules]
% 2.89/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.89/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.89/0.98  --sup_immed_bw_main                     []
% 2.89/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.89/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 2.89/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.89/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.89/0.98  
% 2.89/0.98  ------ Combination Options
% 2.89/0.98  
% 2.89/0.98  --comb_res_mult                         3
% 2.89/0.98  --comb_sup_mult                         2
% 2.89/0.98  --comb_inst_mult                        10
% 2.89/0.98  
% 2.89/0.98  ------ Debug Options
% 2.89/0.98  
% 2.89/0.98  --dbg_backtrace                         false
% 2.89/0.98  --dbg_dump_prop_clauses                 false
% 2.89/0.98  --dbg_dump_prop_clauses_file            -
% 2.89/0.98  --dbg_out_stat                          false
% 2.89/0.98  ------ Parsing...
% 2.89/0.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.89/0.98  
% 2.89/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 2.89/0.98  
% 2.89/0.98  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.89/0.98  
% 2.89/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.89/0.98  ------ Proving...
% 2.89/0.98  ------ Problem Properties 
% 2.89/0.98  
% 2.89/0.98  
% 2.89/0.98  clauses                                 27
% 2.89/0.98  conjectures                             5
% 2.89/0.98  EPR                                     1
% 2.89/0.98  Horn                                    23
% 2.89/0.98  unary                                   11
% 2.89/0.98  binary                                  10
% 2.89/0.98  lits                                    54
% 2.89/0.98  lits eq                                 35
% 2.89/0.98  fd_pure                                 0
% 2.89/0.98  fd_pseudo                               0
% 2.89/0.98  fd_cond                                 0
% 2.89/0.98  fd_pseudo_cond                          4
% 2.89/0.98  AC symbols                              0
% 2.89/0.98  
% 2.89/0.98  ------ Schedule dynamic 5 is on 
% 2.89/0.98  
% 2.89/0.98  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.89/0.98  
% 2.89/0.98  
% 2.89/0.98  ------ 
% 2.89/0.98  Current options:
% 2.89/0.98  ------ 
% 2.89/0.98  
% 2.89/0.98  ------ Input Options
% 2.89/0.98  
% 2.89/0.98  --out_options                           all
% 2.89/0.98  --tptp_safe_out                         true
% 2.89/0.98  --problem_path                          ""
% 2.89/0.98  --include_path                          ""
% 2.89/0.98  --clausifier                            res/vclausify_rel
% 2.89/0.98  --clausifier_options                    --mode clausify
% 2.89/0.98  --stdin                                 false
% 2.89/0.98  --stats_out                             all
% 2.89/0.98  
% 2.89/0.98  ------ General Options
% 2.89/0.98  
% 2.89/0.98  --fof                                   false
% 2.89/0.98  --time_out_real                         305.
% 2.89/0.98  --time_out_virtual                      -1.
% 2.89/0.98  --symbol_type_check                     false
% 2.89/0.98  --clausify_out                          false
% 2.89/0.98  --sig_cnt_out                           false
% 2.89/0.98  --trig_cnt_out                          false
% 2.89/0.98  --trig_cnt_out_tolerance                1.
% 2.89/0.98  --trig_cnt_out_sk_spl                   false
% 2.89/0.98  --abstr_cl_out                          false
% 2.89/0.98  
% 2.89/0.98  ------ Global Options
% 2.89/0.98  
% 2.89/0.98  --schedule                              default
% 2.89/0.98  --add_important_lit                     false
% 2.89/0.98  --prop_solver_per_cl                    1000
% 2.89/0.98  --min_unsat_core                        false
% 2.89/0.98  --soft_assumptions                      false
% 2.89/0.98  --soft_lemma_size                       3
% 2.89/0.98  --prop_impl_unit_size                   0
% 2.89/0.98  --prop_impl_unit                        []
% 2.89/0.98  --share_sel_clauses                     true
% 2.89/0.98  --reset_solvers                         false
% 2.89/0.98  --bc_imp_inh                            [conj_cone]
% 2.89/0.98  --conj_cone_tolerance                   3.
% 2.89/0.98  --extra_neg_conj                        none
% 2.89/0.98  --large_theory_mode                     true
% 2.89/0.98  --prolific_symb_bound                   200
% 2.89/0.98  --lt_threshold                          2000
% 2.89/0.98  --clause_weak_htbl                      true
% 2.89/0.98  --gc_record_bc_elim                     false
% 2.89/0.98  
% 2.89/0.98  ------ Preprocessing Options
% 2.89/0.98  
% 2.89/0.98  --preprocessing_flag                    true
% 2.89/0.98  --time_out_prep_mult                    0.1
% 2.89/0.98  --splitting_mode                        input
% 2.89/0.98  --splitting_grd                         true
% 2.89/0.98  --splitting_cvd                         false
% 2.89/0.98  --splitting_cvd_svl                     false
% 2.89/0.98  --splitting_nvd                         32
% 2.89/0.98  --sub_typing                            true
% 2.89/0.98  --prep_gs_sim                           true
% 2.89/0.98  --prep_unflatten                        true
% 2.89/0.98  --prep_res_sim                          true
% 2.89/0.98  --prep_upred                            true
% 2.89/0.98  --prep_sem_filter                       exhaustive
% 2.89/0.98  --prep_sem_filter_out                   false
% 2.89/0.98  --pred_elim                             true
% 2.89/0.98  --res_sim_input                         true
% 2.89/0.98  --eq_ax_congr_red                       true
% 2.89/0.98  --pure_diseq_elim                       true
% 2.89/0.98  --brand_transform                       false
% 2.89/0.98  --non_eq_to_eq                          false
% 2.89/0.98  --prep_def_merge                        true
% 2.89/0.98  --prep_def_merge_prop_impl              false
% 2.89/0.98  --prep_def_merge_mbd                    true
% 2.89/0.98  --prep_def_merge_tr_red                 false
% 2.89/0.98  --prep_def_merge_tr_cl                  false
% 2.89/0.98  --smt_preprocessing                     true
% 2.89/0.98  --smt_ac_axioms                         fast
% 2.89/0.98  --preprocessed_out                      false
% 2.89/0.98  --preprocessed_stats                    false
% 2.89/0.98  
% 2.89/0.98  ------ Abstraction refinement Options
% 2.89/0.98  
% 2.89/0.98  --abstr_ref                             []
% 2.89/0.98  --abstr_ref_prep                        false
% 2.89/0.98  --abstr_ref_until_sat                   false
% 2.89/0.98  --abstr_ref_sig_restrict                funpre
% 2.89/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 2.89/0.98  --abstr_ref_under                       []
% 2.89/0.98  
% 2.89/0.98  ------ SAT Options
% 2.89/0.98  
% 2.89/0.98  --sat_mode                              false
% 2.89/0.98  --sat_fm_restart_options                ""
% 2.89/0.98  --sat_gr_def                            false
% 2.89/0.98  --sat_epr_types                         true
% 2.89/0.98  --sat_non_cyclic_types                  false
% 2.89/0.98  --sat_finite_models                     false
% 2.89/0.98  --sat_fm_lemmas                         false
% 2.89/0.98  --sat_fm_prep                           false
% 2.89/0.98  --sat_fm_uc_incr                        true
% 2.89/0.98  --sat_out_model                         small
% 2.89/0.98  --sat_out_clauses                       false
% 2.89/0.98  
% 2.89/0.98  ------ QBF Options
% 2.89/0.98  
% 2.89/0.98  --qbf_mode                              false
% 2.89/0.98  --qbf_elim_univ                         false
% 2.89/0.98  --qbf_dom_inst                          none
% 2.89/0.98  --qbf_dom_pre_inst                      false
% 2.89/0.98  --qbf_sk_in                             false
% 2.89/0.98  --qbf_pred_elim                         true
% 2.89/0.98  --qbf_split                             512
% 2.89/0.98  
% 2.89/0.98  ------ BMC1 Options
% 2.89/0.98  
% 2.89/0.98  --bmc1_incremental                      false
% 2.89/0.98  --bmc1_axioms                           reachable_all
% 2.89/0.98  --bmc1_min_bound                        0
% 2.89/0.98  --bmc1_max_bound                        -1
% 2.89/0.98  --bmc1_max_bound_default                -1
% 2.89/0.98  --bmc1_symbol_reachability              true
% 2.89/0.98  --bmc1_property_lemmas                  false
% 2.89/0.98  --bmc1_k_induction                      false
% 2.89/0.98  --bmc1_non_equiv_states                 false
% 2.89/0.98  --bmc1_deadlock                         false
% 2.89/0.98  --bmc1_ucm                              false
% 2.89/0.98  --bmc1_add_unsat_core                   none
% 2.89/0.98  --bmc1_unsat_core_children              false
% 2.89/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 2.89/0.98  --bmc1_out_stat                         full
% 2.89/0.98  --bmc1_ground_init                      false
% 2.89/0.98  --bmc1_pre_inst_next_state              false
% 2.89/0.98  --bmc1_pre_inst_state                   false
% 2.89/0.98  --bmc1_pre_inst_reach_state             false
% 2.89/0.98  --bmc1_out_unsat_core                   false
% 2.89/0.98  --bmc1_aig_witness_out                  false
% 2.89/0.98  --bmc1_verbose                          false
% 2.89/0.98  --bmc1_dump_clauses_tptp                false
% 2.89/0.98  --bmc1_dump_unsat_core_tptp             false
% 2.89/0.98  --bmc1_dump_file                        -
% 2.89/0.98  --bmc1_ucm_expand_uc_limit              128
% 2.89/0.98  --bmc1_ucm_n_expand_iterations          6
% 2.89/0.98  --bmc1_ucm_extend_mode                  1
% 2.89/0.98  --bmc1_ucm_init_mode                    2
% 2.89/0.98  --bmc1_ucm_cone_mode                    none
% 2.89/0.98  --bmc1_ucm_reduced_relation_type        0
% 2.89/0.98  --bmc1_ucm_relax_model                  4
% 2.89/0.98  --bmc1_ucm_full_tr_after_sat            true
% 2.89/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 2.89/0.98  --bmc1_ucm_layered_model                none
% 2.89/0.98  --bmc1_ucm_max_lemma_size               10
% 2.89/0.98  
% 2.89/0.98  ------ AIG Options
% 2.89/0.98  
% 2.89/0.98  --aig_mode                              false
% 2.89/0.98  
% 2.89/0.98  ------ Instantiation Options
% 2.89/0.98  
% 2.89/0.98  --instantiation_flag                    true
% 2.89/0.98  --inst_sos_flag                         false
% 2.89/0.98  --inst_sos_phase                        true
% 2.89/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.89/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.89/0.98  --inst_lit_sel_side                     none
% 2.89/0.98  --inst_solver_per_active                1400
% 2.89/0.98  --inst_solver_calls_frac                1.
% 2.89/0.98  --inst_passive_queue_type               priority_queues
% 2.89/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.89/0.98  --inst_passive_queues_freq              [25;2]
% 2.89/0.98  --inst_dismatching                      true
% 2.89/0.98  --inst_eager_unprocessed_to_passive     true
% 2.89/0.98  --inst_prop_sim_given                   true
% 2.89/0.98  --inst_prop_sim_new                     false
% 2.89/0.98  --inst_subs_new                         false
% 2.89/0.98  --inst_eq_res_simp                      false
% 2.89/0.98  --inst_subs_given                       false
% 2.89/0.98  --inst_orphan_elimination               true
% 2.89/0.98  --inst_learning_loop_flag               true
% 2.89/0.98  --inst_learning_start                   3000
% 2.89/0.98  --inst_learning_factor                  2
% 2.89/0.98  --inst_start_prop_sim_after_learn       3
% 2.89/0.98  --inst_sel_renew                        solver
% 2.89/0.98  --inst_lit_activity_flag                true
% 2.89/0.98  --inst_restr_to_given                   false
% 2.89/0.98  --inst_activity_threshold               500
% 2.89/0.98  --inst_out_proof                        true
% 2.89/0.98  
% 2.89/0.98  ------ Resolution Options
% 2.89/0.98  
% 2.89/0.98  --resolution_flag                       false
% 2.89/0.98  --res_lit_sel                           adaptive
% 2.89/0.98  --res_lit_sel_side                      none
% 2.89/0.98  --res_ordering                          kbo
% 2.89/0.98  --res_to_prop_solver                    active
% 2.89/0.98  --res_prop_simpl_new                    false
% 2.89/0.98  --res_prop_simpl_given                  true
% 2.89/0.98  --res_passive_queue_type                priority_queues
% 2.89/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.89/0.98  --res_passive_queues_freq               [15;5]
% 2.89/0.98  --res_forward_subs                      full
% 2.89/0.98  --res_backward_subs                     full
% 2.89/0.98  --res_forward_subs_resolution           true
% 2.89/0.98  --res_backward_subs_resolution          true
% 2.89/0.98  --res_orphan_elimination                true
% 2.89/0.98  --res_time_limit                        2.
% 2.89/0.98  --res_out_proof                         true
% 2.89/0.98  
% 2.89/0.98  ------ Superposition Options
% 2.89/0.98  
% 2.89/0.98  --superposition_flag                    true
% 2.89/0.98  --sup_passive_queue_type                priority_queues
% 2.89/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.89/0.98  --sup_passive_queues_freq               [8;1;4]
% 2.89/0.98  --demod_completeness_check              fast
% 2.89/0.98  --demod_use_ground                      true
% 2.89/0.98  --sup_to_prop_solver                    passive
% 2.89/0.98  --sup_prop_simpl_new                    true
% 2.89/0.98  --sup_prop_simpl_given                  true
% 2.89/0.98  --sup_fun_splitting                     false
% 2.89/0.98  --sup_smt_interval                      50000
% 2.89/0.98  
% 2.89/0.98  ------ Superposition Simplification Setup
% 2.89/0.98  
% 2.89/0.98  --sup_indices_passive                   []
% 2.89/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.89/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.89/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.89/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 2.89/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.89/0.98  --sup_full_bw                           [BwDemod]
% 2.89/0.98  --sup_immed_triv                        [TrivRules]
% 2.89/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.89/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.89/0.98  --sup_immed_bw_main                     []
% 2.89/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.89/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 2.89/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.89/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.89/0.98  
% 2.89/0.98  ------ Combination Options
% 2.89/0.98  
% 2.89/0.98  --comb_res_mult                         3
% 2.89/0.98  --comb_sup_mult                         2
% 2.89/0.98  --comb_inst_mult                        10
% 2.89/0.98  
% 2.89/0.98  ------ Debug Options
% 2.89/0.98  
% 2.89/0.98  --dbg_backtrace                         false
% 2.89/0.98  --dbg_dump_prop_clauses                 false
% 2.89/0.98  --dbg_dump_prop_clauses_file            -
% 2.89/0.98  --dbg_out_stat                          false
% 2.89/0.98  
% 2.89/0.98  
% 2.89/0.98  
% 2.89/0.98  
% 2.89/0.98  ------ Proving...
% 2.89/0.98  
% 2.89/0.98  
% 2.89/0.98  % SZS status Theorem for theBenchmark.p
% 2.89/0.98  
% 2.89/0.98   Resolution empty clause
% 2.89/0.98  
% 2.89/0.98  % SZS output start CNFRefutation for theBenchmark.p
% 2.89/0.98  
% 2.89/0.98  fof(f13,conjecture,(
% 2.89/0.98    ! [X0,X1,X2] : (k1_xboole_0 = k4_xboole_0(X0,k2_tarski(X1,X2)) <=> ~(k2_tarski(X1,X2) != X0 & k1_tarski(X2) != X0 & k1_tarski(X1) != X0 & k1_xboole_0 != X0))),
% 2.89/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.89/0.98  
% 2.89/0.98  fof(f14,negated_conjecture,(
% 2.89/0.98    ~! [X0,X1,X2] : (k1_xboole_0 = k4_xboole_0(X0,k2_tarski(X1,X2)) <=> ~(k2_tarski(X1,X2) != X0 & k1_tarski(X2) != X0 & k1_tarski(X1) != X0 & k1_xboole_0 != X0))),
% 2.89/0.98    inference(negated_conjecture,[],[f13])).
% 2.89/0.98  
% 2.89/0.98  fof(f19,plain,(
% 2.89/0.98    ? [X0,X1,X2] : (k1_xboole_0 = k4_xboole_0(X0,k2_tarski(X1,X2)) <~> (k2_tarski(X1,X2) = X0 | k1_tarski(X2) = X0 | k1_tarski(X1) = X0 | k1_xboole_0 = X0))),
% 2.89/0.98    inference(ennf_transformation,[],[f14])).
% 2.89/0.98  
% 2.89/0.98  fof(f29,plain,(
% 2.89/0.98    ? [X0,X1,X2] : (((k2_tarski(X1,X2) != X0 & k1_tarski(X2) != X0 & k1_tarski(X1) != X0 & k1_xboole_0 != X0) | k1_xboole_0 != k4_xboole_0(X0,k2_tarski(X1,X2))) & ((k2_tarski(X1,X2) = X0 | k1_tarski(X2) = X0 | k1_tarski(X1) = X0 | k1_xboole_0 = X0) | k1_xboole_0 = k4_xboole_0(X0,k2_tarski(X1,X2))))),
% 2.89/0.98    inference(nnf_transformation,[],[f19])).
% 2.89/0.98  
% 2.89/0.98  fof(f30,plain,(
% 2.89/0.98    ? [X0,X1,X2] : (((k2_tarski(X1,X2) != X0 & k1_tarski(X2) != X0 & k1_tarski(X1) != X0 & k1_xboole_0 != X0) | k1_xboole_0 != k4_xboole_0(X0,k2_tarski(X1,X2))) & (k2_tarski(X1,X2) = X0 | k1_tarski(X2) = X0 | k1_tarski(X1) = X0 | k1_xboole_0 = X0 | k1_xboole_0 = k4_xboole_0(X0,k2_tarski(X1,X2))))),
% 2.89/0.98    inference(flattening,[],[f29])).
% 2.89/0.98  
% 2.89/0.98  fof(f31,plain,(
% 2.89/0.98    ? [X0,X1,X2] : (((k2_tarski(X1,X2) != X0 & k1_tarski(X2) != X0 & k1_tarski(X1) != X0 & k1_xboole_0 != X0) | k1_xboole_0 != k4_xboole_0(X0,k2_tarski(X1,X2))) & (k2_tarski(X1,X2) = X0 | k1_tarski(X2) = X0 | k1_tarski(X1) = X0 | k1_xboole_0 = X0 | k1_xboole_0 = k4_xboole_0(X0,k2_tarski(X1,X2)))) => (((k2_tarski(sK2,sK3) != sK1 & k1_tarski(sK3) != sK1 & k1_tarski(sK2) != sK1 & k1_xboole_0 != sK1) | k1_xboole_0 != k4_xboole_0(sK1,k2_tarski(sK2,sK3))) & (k2_tarski(sK2,sK3) = sK1 | k1_tarski(sK3) = sK1 | k1_tarski(sK2) = sK1 | k1_xboole_0 = sK1 | k1_xboole_0 = k4_xboole_0(sK1,k2_tarski(sK2,sK3))))),
% 2.89/0.98    introduced(choice_axiom,[])).
% 2.89/0.98  
% 2.89/0.98  fof(f32,plain,(
% 2.89/0.98    ((k2_tarski(sK2,sK3) != sK1 & k1_tarski(sK3) != sK1 & k1_tarski(sK2) != sK1 & k1_xboole_0 != sK1) | k1_xboole_0 != k4_xboole_0(sK1,k2_tarski(sK2,sK3))) & (k2_tarski(sK2,sK3) = sK1 | k1_tarski(sK3) = sK1 | k1_tarski(sK2) = sK1 | k1_xboole_0 = sK1 | k1_xboole_0 = k4_xboole_0(sK1,k2_tarski(sK2,sK3)))),
% 2.89/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f30,f31])).
% 2.89/0.98  
% 2.89/0.98  fof(f56,plain,(
% 2.89/0.98    k2_tarski(sK2,sK3) = sK1 | k1_tarski(sK3) = sK1 | k1_tarski(sK2) = sK1 | k1_xboole_0 = sK1 | k1_xboole_0 = k4_xboole_0(sK1,k2_tarski(sK2,sK3))),
% 2.89/0.98    inference(cnf_transformation,[],[f32])).
% 2.89/0.98  
% 2.89/0.98  fof(f8,axiom,(
% 2.89/0.98    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 2.89/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.89/0.98  
% 2.89/0.98  fof(f46,plain,(
% 2.89/0.98    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 2.89/0.98    inference(cnf_transformation,[],[f8])).
% 2.89/0.98  
% 2.89/0.98  fof(f70,plain,(
% 2.89/0.98    k2_tarski(sK2,sK3) = sK1 | k2_tarski(sK3,sK3) = sK1 | k2_tarski(sK2,sK2) = sK1 | k1_xboole_0 = sK1 | k1_xboole_0 = k4_xboole_0(sK1,k2_tarski(sK2,sK3))),
% 2.89/0.98    inference(definition_unfolding,[],[f56,f46,f46])).
% 2.89/0.98  
% 2.89/0.98  fof(f3,axiom,(
% 2.89/0.98    ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,X1) <=> r1_tarski(X0,X1))),
% 2.89/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.89/0.98  
% 2.89/0.98  fof(f20,plain,(
% 2.89/0.98    ! [X0,X1] : ((k1_xboole_0 = k4_xboole_0(X0,X1) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k1_xboole_0 != k4_xboole_0(X0,X1)))),
% 2.89/0.98    inference(nnf_transformation,[],[f3])).
% 2.89/0.98  
% 2.89/0.98  fof(f35,plain,(
% 2.89/0.98    ( ! [X0,X1] : (r1_tarski(X0,X1) | k1_xboole_0 != k4_xboole_0(X0,X1)) )),
% 2.89/0.98    inference(cnf_transformation,[],[f20])).
% 2.89/0.98  
% 2.89/0.98  fof(f10,axiom,(
% 2.89/0.98    ! [X0,X1,X2] : (r1_tarski(X0,k2_tarski(X1,X2)) <=> ~(k2_tarski(X1,X2) != X0 & k1_tarski(X2) != X0 & k1_tarski(X1) != X0 & k1_xboole_0 != X0))),
% 2.89/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.89/0.98  
% 2.89/0.98  fof(f18,plain,(
% 2.89/0.98    ! [X0,X1,X2] : (r1_tarski(X0,k2_tarski(X1,X2)) <=> (k2_tarski(X1,X2) = X0 | k1_tarski(X2) = X0 | k1_tarski(X1) = X0 | k1_xboole_0 = X0))),
% 2.89/0.98    inference(ennf_transformation,[],[f10])).
% 2.89/0.98  
% 2.89/0.98  fof(f26,plain,(
% 2.89/0.98    ! [X0,X1,X2] : ((r1_tarski(X0,k2_tarski(X1,X2)) | (k2_tarski(X1,X2) != X0 & k1_tarski(X2) != X0 & k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & ((k2_tarski(X1,X2) = X0 | k1_tarski(X2) = X0 | k1_tarski(X1) = X0 | k1_xboole_0 = X0) | ~r1_tarski(X0,k2_tarski(X1,X2))))),
% 2.89/0.98    inference(nnf_transformation,[],[f18])).
% 2.89/0.98  
% 2.89/0.98  fof(f27,plain,(
% 2.89/0.98    ! [X0,X1,X2] : ((r1_tarski(X0,k2_tarski(X1,X2)) | (k2_tarski(X1,X2) != X0 & k1_tarski(X2) != X0 & k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & (k2_tarski(X1,X2) = X0 | k1_tarski(X2) = X0 | k1_tarski(X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k2_tarski(X1,X2))))),
% 2.89/0.98    inference(flattening,[],[f26])).
% 2.89/0.98  
% 2.89/0.98  fof(f48,plain,(
% 2.89/0.98    ( ! [X2,X0,X1] : (k2_tarski(X1,X2) = X0 | k1_tarski(X2) = X0 | k1_tarski(X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k2_tarski(X1,X2))) )),
% 2.89/0.98    inference(cnf_transformation,[],[f27])).
% 2.89/0.98  
% 2.89/0.98  fof(f64,plain,(
% 2.89/0.98    ( ! [X2,X0,X1] : (k2_tarski(X1,X2) = X0 | k2_tarski(X2,X2) = X0 | k2_tarski(X1,X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k2_tarski(X1,X2))) )),
% 2.89/0.98    inference(definition_unfolding,[],[f48,f46,f46])).
% 2.89/0.98  
% 2.89/0.98  fof(f51,plain,(
% 2.89/0.98    ( ! [X2,X0,X1] : (r1_tarski(X0,k2_tarski(X1,X2)) | k1_tarski(X2) != X0) )),
% 2.89/0.98    inference(cnf_transformation,[],[f27])).
% 2.89/0.98  
% 2.89/0.98  fof(f62,plain,(
% 2.89/0.98    ( ! [X2,X0,X1] : (r1_tarski(X0,k2_tarski(X1,X2)) | k2_tarski(X2,X2) != X0) )),
% 2.89/0.98    inference(definition_unfolding,[],[f51,f46])).
% 2.89/0.98  
% 2.89/0.98  fof(f77,plain,(
% 2.89/0.98    ( ! [X2,X1] : (r1_tarski(k2_tarski(X2,X2),k2_tarski(X1,X2))) )),
% 2.89/0.98    inference(equality_resolution,[],[f62])).
% 2.89/0.98  
% 2.89/0.98  fof(f36,plain,(
% 2.89/0.98    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,X1) | ~r1_tarski(X0,X1)) )),
% 2.89/0.98    inference(cnf_transformation,[],[f20])).
% 2.89/0.98  
% 2.89/0.98  fof(f59,plain,(
% 2.89/0.98    k1_tarski(sK3) != sK1 | k1_xboole_0 != k4_xboole_0(sK1,k2_tarski(sK2,sK3))),
% 2.89/0.98    inference(cnf_transformation,[],[f32])).
% 2.89/0.98  
% 2.89/0.98  fof(f68,plain,(
% 2.89/0.98    k2_tarski(sK3,sK3) != sK1 | k1_xboole_0 != k4_xboole_0(sK1,k2_tarski(sK2,sK3))),
% 2.89/0.98    inference(definition_unfolding,[],[f59,f46])).
% 2.89/0.98  
% 2.89/0.98  fof(f11,axiom,(
% 2.89/0.98    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(k1_tarski(X0),k2_tarski(X0,X1))),
% 2.89/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.89/0.98  
% 2.89/0.98  fof(f53,plain,(
% 2.89/0.98    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(k1_tarski(X0),k2_tarski(X0,X1))) )),
% 2.89/0.98    inference(cnf_transformation,[],[f11])).
% 2.89/0.98  
% 2.89/0.98  fof(f65,plain,(
% 2.89/0.98    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(k2_tarski(X0,X0),k2_tarski(X0,X1))) )),
% 2.89/0.98    inference(definition_unfolding,[],[f53,f46])).
% 2.89/0.98  
% 2.89/0.98  fof(f52,plain,(
% 2.89/0.98    ( ! [X2,X0,X1] : (r1_tarski(X0,k2_tarski(X1,X2)) | k2_tarski(X1,X2) != X0) )),
% 2.89/0.98    inference(cnf_transformation,[],[f27])).
% 2.89/0.98  
% 2.89/0.98  fof(f76,plain,(
% 2.89/0.98    ( ! [X2,X1] : (r1_tarski(k2_tarski(X1,X2),k2_tarski(X1,X2))) )),
% 2.89/0.98    inference(equality_resolution,[],[f52])).
% 2.89/0.98  
% 2.89/0.98  fof(f60,plain,(
% 2.89/0.98    k2_tarski(sK2,sK3) != sK1 | k1_xboole_0 != k4_xboole_0(sK1,k2_tarski(sK2,sK3))),
% 2.89/0.98    inference(cnf_transformation,[],[f32])).
% 2.89/0.98  
% 2.89/0.98  fof(f58,plain,(
% 2.89/0.98    k1_tarski(sK2) != sK1 | k1_xboole_0 != k4_xboole_0(sK1,k2_tarski(sK2,sK3))),
% 2.89/0.98    inference(cnf_transformation,[],[f32])).
% 2.89/0.98  
% 2.89/0.98  fof(f69,plain,(
% 2.89/0.98    k2_tarski(sK2,sK2) != sK1 | k1_xboole_0 != k4_xboole_0(sK1,k2_tarski(sK2,sK3))),
% 2.89/0.98    inference(definition_unfolding,[],[f58,f46])).
% 2.89/0.98  
% 2.89/0.98  fof(f57,plain,(
% 2.89/0.98    k1_xboole_0 != sK1 | k1_xboole_0 != k4_xboole_0(sK1,k2_tarski(sK2,sK3))),
% 2.89/0.98    inference(cnf_transformation,[],[f32])).
% 2.89/0.98  
% 2.89/0.98  fof(f6,axiom,(
% 2.89/0.98    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)),
% 2.89/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.89/0.98  
% 2.89/0.98  fof(f39,plain,(
% 2.89/0.98    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)) )),
% 2.89/0.98    inference(cnf_transformation,[],[f6])).
% 2.89/0.98  
% 2.89/0.98  cnf(c_26,negated_conjecture,
% 2.89/0.98      ( k2_tarski(sK3,sK3) = sK1
% 2.89/0.98      | k2_tarski(sK2,sK3) = sK1
% 2.89/0.98      | k2_tarski(sK2,sK2) = sK1
% 2.89/0.98      | k1_xboole_0 = k4_xboole_0(sK1,k2_tarski(sK2,sK3))
% 2.89/0.98      | k1_xboole_0 = sK1 ),
% 2.89/0.98      inference(cnf_transformation,[],[f70]) ).
% 2.89/0.98  
% 2.89/0.98  cnf(c_3,plain,
% 2.89/0.98      ( r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0 ),
% 2.89/0.98      inference(cnf_transformation,[],[f35]) ).
% 2.89/0.98  
% 2.89/0.98  cnf(c_963,plain,
% 2.89/0.98      ( k4_xboole_0(X0,X1) != k1_xboole_0 | r1_tarski(X0,X1) = iProver_top ),
% 2.89/0.98      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 2.89/0.98  
% 2.89/0.98  cnf(c_1564,plain,
% 2.89/0.98      ( k2_tarski(sK3,sK3) = sK1
% 2.89/0.98      | k2_tarski(sK2,sK3) = sK1
% 2.89/0.98      | k2_tarski(sK2,sK2) = sK1
% 2.89/0.98      | sK1 = k1_xboole_0
% 2.89/0.98      | r1_tarski(sK1,k2_tarski(sK2,sK3)) = iProver_top ),
% 2.89/0.98      inference(superposition,[status(thm)],[c_26,c_963]) ).
% 2.89/0.98  
% 2.89/0.98  cnf(c_18,plain,
% 2.89/0.98      ( ~ r1_tarski(X0,k2_tarski(X1,X2))
% 2.89/0.98      | k2_tarski(X1,X2) = X0
% 2.89/0.98      | k2_tarski(X2,X2) = X0
% 2.89/0.98      | k2_tarski(X1,X1) = X0
% 2.89/0.98      | k1_xboole_0 = X0 ),
% 2.89/0.98      inference(cnf_transformation,[],[f64]) ).
% 2.89/0.98  
% 2.89/0.98  cnf(c_950,plain,
% 2.89/0.98      ( k2_tarski(X0,X1) = X2
% 2.89/0.98      | k2_tarski(X1,X1) = X2
% 2.89/0.98      | k2_tarski(X0,X0) = X2
% 2.89/0.98      | k1_xboole_0 = X2
% 2.89/0.98      | r1_tarski(X2,k2_tarski(X0,X1)) != iProver_top ),
% 2.89/0.98      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 2.89/0.98  
% 2.89/0.98  cnf(c_3004,plain,
% 2.89/0.98      ( k2_tarski(sK3,sK3) = sK1
% 2.89/0.98      | k2_tarski(sK2,sK3) = sK1
% 2.89/0.98      | k2_tarski(sK2,sK2) = sK1
% 2.89/0.98      | sK1 = k1_xboole_0 ),
% 2.89/0.98      inference(superposition,[status(thm)],[c_1564,c_950]) ).
% 2.89/0.98  
% 2.89/0.98  cnf(c_15,plain,
% 2.89/0.98      ( r1_tarski(k2_tarski(X0,X0),k2_tarski(X1,X0)) ),
% 2.89/0.98      inference(cnf_transformation,[],[f77]) ).
% 2.89/0.98  
% 2.89/0.98  cnf(c_953,plain,
% 2.89/0.98      ( r1_tarski(k2_tarski(X0,X0),k2_tarski(X1,X0)) = iProver_top ),
% 2.89/0.98      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 2.89/0.98  
% 2.89/0.98  cnf(c_2,plain,
% 2.89/0.98      ( ~ r1_tarski(X0,X1) | k4_xboole_0(X0,X1) = k1_xboole_0 ),
% 2.89/0.98      inference(cnf_transformation,[],[f36]) ).
% 2.89/0.98  
% 2.89/0.98  cnf(c_964,plain,
% 2.89/0.98      ( k4_xboole_0(X0,X1) = k1_xboole_0 | r1_tarski(X0,X1) != iProver_top ),
% 2.89/0.98      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 2.89/0.98  
% 2.89/0.98  cnf(c_1684,plain,
% 2.89/0.98      ( k4_xboole_0(k2_tarski(X0,X0),k2_tarski(X1,X0)) = k1_xboole_0 ),
% 2.89/0.98      inference(superposition,[status(thm)],[c_953,c_964]) ).
% 2.89/0.98  
% 2.89/0.98  cnf(c_3536,plain,
% 2.89/0.98      ( k2_tarski(sK2,sK3) = sK1
% 2.89/0.98      | k2_tarski(sK2,sK2) = sK1
% 2.89/0.98      | k4_xboole_0(sK1,k2_tarski(X0,sK3)) = k1_xboole_0
% 2.89/0.98      | sK1 = k1_xboole_0 ),
% 2.89/0.98      inference(superposition,[status(thm)],[c_3004,c_1684]) ).
% 2.89/0.98  
% 2.89/0.98  cnf(c_23,negated_conjecture,
% 2.89/0.98      ( k2_tarski(sK3,sK3) != sK1
% 2.89/0.98      | k1_xboole_0 != k4_xboole_0(sK1,k2_tarski(sK2,sK3)) ),
% 2.89/0.98      inference(cnf_transformation,[],[f68]) ).
% 2.89/0.98  
% 2.89/0.98  cnf(c_4395,plain,
% 2.89/0.98      ( k2_tarski(sK3,sK3) != sK1
% 2.89/0.98      | k2_tarski(sK2,sK3) = sK1
% 2.89/0.98      | k2_tarski(sK2,sK2) = sK1
% 2.89/0.98      | sK1 = k1_xboole_0 ),
% 2.89/0.98      inference(superposition,[status(thm)],[c_3536,c_23]) ).
% 2.89/0.98  
% 2.89/0.98  cnf(c_4662,plain,
% 2.89/0.98      ( k2_tarski(sK2,sK3) = sK1
% 2.89/0.98      | k2_tarski(sK2,sK2) = sK1
% 2.89/0.98      | sK1 = k1_xboole_0 ),
% 2.89/0.98      inference(global_propositional_subsumption,[status(thm)],[c_4395,c_3004]) ).
% 2.89/0.98  
% 2.89/0.98  cnf(c_19,plain,
% 2.89/0.98      ( k4_xboole_0(k2_tarski(X0,X0),k2_tarski(X0,X1)) = k1_xboole_0 ),
% 2.89/0.98      inference(cnf_transformation,[],[f65]) ).
% 2.89/0.98  
% 2.89/0.98  cnf(c_4675,plain,
% 2.89/0.98      ( k2_tarski(sK2,sK2) = sK1
% 2.89/0.98      | k4_xboole_0(k2_tarski(sK2,sK2),sK1) = k1_xboole_0
% 2.89/0.98      | sK1 = k1_xboole_0 ),
% 2.89/0.98      inference(superposition,[status(thm)],[c_4662,c_19]) ).
% 2.89/0.98  
% 2.89/0.98  cnf(c_14,plain,
% 2.89/0.98      ( r1_tarski(k2_tarski(X0,X1),k2_tarski(X0,X1)) ),
% 2.89/0.98      inference(cnf_transformation,[],[f76]) ).
% 2.89/0.98  
% 2.89/0.98  cnf(c_954,plain,
% 2.89/0.98      ( r1_tarski(k2_tarski(X0,X1),k2_tarski(X0,X1)) = iProver_top ),
% 2.89/0.98      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 2.89/0.98  
% 2.89/0.98  cnf(c_1683,plain,
% 2.89/0.98      ( k4_xboole_0(k2_tarski(X0,X1),k2_tarski(X0,X1)) = k1_xboole_0 ),
% 2.89/0.98      inference(superposition,[status(thm)],[c_954,c_964]) ).
% 2.89/0.98  
% 2.89/0.98  cnf(c_3522,plain,
% 2.89/0.98      ( k2_tarski(sK2,sK3) = sK1
% 2.89/0.98      | k2_tarski(sK2,sK2) = sK1
% 2.89/0.98      | k4_xboole_0(sK1,sK1) = k1_xboole_0
% 2.89/0.98      | sK1 = k1_xboole_0 ),
% 2.89/0.98      inference(superposition,[status(thm)],[c_3004,c_1683]) ).
% 2.89/0.98  
% 2.89/0.98  cnf(c_3839,plain,
% 2.89/0.98      ( k2_tarski(sK2,sK2) = sK1
% 2.89/0.98      | k4_xboole_0(sK1,sK1) = k1_xboole_0
% 2.89/0.98      | sK1 = k1_xboole_0 ),
% 2.89/0.98      inference(superposition,[status(thm)],[c_3522,c_1683]) ).
% 2.89/0.98  
% 2.89/0.98  cnf(c_22,negated_conjecture,
% 2.89/0.98      ( k2_tarski(sK2,sK3) != sK1
% 2.89/0.98      | k1_xboole_0 != k4_xboole_0(sK1,k2_tarski(sK2,sK3)) ),
% 2.89/0.98      inference(cnf_transformation,[],[f60]) ).
% 2.89/0.98  
% 2.89/0.98  cnf(c_4685,plain,
% 2.89/0.98      ( k2_tarski(sK2,sK3) != sK1
% 2.89/0.98      | k2_tarski(sK2,sK2) = sK1
% 2.89/0.98      | k4_xboole_0(sK1,sK1) != k1_xboole_0
% 2.89/0.98      | sK1 = k1_xboole_0 ),
% 2.89/0.98      inference(superposition,[status(thm)],[c_4662,c_22]) ).
% 2.89/0.98  
% 2.89/0.98  cnf(c_4692,plain,
% 2.89/0.98      ( k2_tarski(sK2,sK2) = sK1
% 2.89/0.98      | k4_xboole_0(sK1,sK1) != k1_xboole_0
% 2.89/0.98      | sK1 = k1_xboole_0 ),
% 2.89/0.98      inference(forward_subsumption_resolution,[status(thm)],[c_4685,c_4662]) ).
% 2.89/0.98  
% 2.89/0.98  cnf(c_5040,plain,
% 2.89/0.98      ( k2_tarski(sK2,sK2) = sK1 | sK1 = k1_xboole_0 ),
% 2.89/0.98      inference(global_propositional_subsumption,
% 2.89/0.98                [status(thm)],
% 2.89/0.98                [c_4675,c_3839,c_4692]) ).
% 2.89/0.98  
% 2.89/0.98  cnf(c_5063,plain,
% 2.89/0.98      ( k4_xboole_0(sK1,k2_tarski(sK2,X0)) = k1_xboole_0 | sK1 = k1_xboole_0 ),
% 2.89/0.98      inference(superposition,[status(thm)],[c_5040,c_19]) ).
% 2.89/0.98  
% 2.89/0.98  cnf(c_24,negated_conjecture,
% 2.89/0.98      ( k2_tarski(sK2,sK2) != sK1
% 2.89/0.98      | k1_xboole_0 != k4_xboole_0(sK1,k2_tarski(sK2,sK3)) ),
% 2.89/0.98      inference(cnf_transformation,[],[f69]) ).
% 2.89/0.98  
% 2.89/0.98  cnf(c_5256,plain,
% 2.89/0.98      ( k2_tarski(sK2,sK2) != sK1 | sK1 = k1_xboole_0 ),
% 2.89/0.98      inference(superposition,[status(thm)],[c_5063,c_24]) ).
% 2.89/0.98  
% 2.89/0.98  cnf(c_5295,plain,
% 2.89/0.98      ( sK1 = k1_xboole_0 ),
% 2.89/0.98      inference(global_propositional_subsumption,[status(thm)],[c_5256,c_5040]) ).
% 2.89/0.98  
% 2.89/0.98  cnf(c_25,negated_conjecture,
% 2.89/0.98      ( k1_xboole_0 != k4_xboole_0(sK1,k2_tarski(sK2,sK3))
% 2.89/0.98      | k1_xboole_0 != sK1 ),
% 2.89/0.98      inference(cnf_transformation,[],[f57]) ).
% 2.89/0.98  
% 2.89/0.98  cnf(c_5309,plain,
% 2.89/0.98      ( k4_xboole_0(k1_xboole_0,k2_tarski(sK2,sK3)) != k1_xboole_0
% 2.89/0.98      | k1_xboole_0 != k1_xboole_0 ),
% 2.89/0.98      inference(demodulation,[status(thm)],[c_5295,c_25]) ).
% 2.89/0.98  
% 2.89/0.98  cnf(c_5310,plain,
% 2.89/0.98      ( k4_xboole_0(k1_xboole_0,k2_tarski(sK2,sK3)) != k1_xboole_0 ),
% 2.89/0.98      inference(equality_resolution_simp,[status(thm)],[c_5309]) ).
% 2.89/0.98  
% 2.89/0.98  cnf(c_6,plain,
% 2.89/0.98      ( k4_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
% 2.89/0.98      inference(cnf_transformation,[],[f39]) ).
% 2.89/0.98  
% 2.89/0.98  cnf(c_5312,plain,
% 2.89/0.98      ( k1_xboole_0 != k1_xboole_0 ),
% 2.89/0.98      inference(demodulation,[status(thm)],[c_5310,c_6]) ).
% 2.89/0.98  
% 2.89/0.98  cnf(c_5313,plain,
% 2.89/0.98      ( $false ),
% 2.89/0.98      inference(equality_resolution_simp,[status(thm)],[c_5312]) ).
% 2.89/0.98  
% 2.89/0.98  
% 2.89/0.98  % SZS output end CNFRefutation for theBenchmark.p
% 2.89/0.98  
% 2.89/0.98  ------                               Statistics
% 2.89/0.98  
% 2.89/0.98  ------ General
% 2.89/0.98  
% 2.89/0.98  abstr_ref_over_cycles:                  0
% 2.89/0.98  abstr_ref_under_cycles:                 0
% 2.89/0.98  gc_basic_clause_elim:                   0
% 2.89/0.98  forced_gc_time:                         0
% 2.89/0.98  parsing_time:                           0.008
% 2.89/0.98  unif_index_cands_time:                  0.
% 2.89/0.98  unif_index_add_time:                    0.
% 2.89/0.98  orderings_time:                         0.
% 2.89/0.98  out_proof_time:                         0.006
% 2.89/0.98  total_time:                             0.175
% 2.89/0.98  num_of_symbols:                         41
% 2.89/0.98  num_of_terms:                           5355
% 2.89/0.98  
% 2.89/0.98  ------ Preprocessing
% 2.89/0.98  
% 2.89/0.98  num_of_splits:                          0
% 2.89/0.98  num_of_split_atoms:                     0
% 2.89/0.98  num_of_reused_defs:                     0
% 2.89/0.98  num_eq_ax_congr_red:                    8
% 2.89/0.98  num_of_sem_filtered_clauses:            1
% 2.89/0.98  num_of_subtypes:                        0
% 2.89/0.98  monotx_restored_types:                  0
% 2.89/0.98  sat_num_of_epr_types:                   0
% 2.89/0.98  sat_num_of_non_cyclic_types:            0
% 2.89/0.98  sat_guarded_non_collapsed_types:        0
% 2.89/0.98  num_pure_diseq_elim:                    0
% 2.89/0.98  simp_replaced_by:                       0
% 2.89/0.98  res_preprocessed:                       96
% 2.89/0.98  prep_upred:                             0
% 2.89/0.98  prep_unflattend:                        26
% 2.89/0.98  smt_new_axioms:                         0
% 2.89/0.98  pred_elim_cands:                        2
% 2.89/0.98  pred_elim:                              0
% 2.89/0.98  pred_elim_cl:                           0
% 2.89/0.98  pred_elim_cycles:                       1
% 2.89/0.98  merged_defs:                            12
% 2.89/0.98  merged_defs_ncl:                        0
% 2.89/0.98  bin_hyper_res:                          12
% 2.89/0.98  prep_cycles:                            3
% 2.89/0.98  pred_elim_time:                         0.003
% 2.89/0.98  splitting_time:                         0.
% 2.89/0.98  sem_filter_time:                        0.
% 2.89/0.98  monotx_time:                            0.
% 2.89/0.98  subtype_inf_time:                       0.
% 2.89/0.98  
% 2.89/0.98  ------ Problem properties
% 2.89/0.98  
% 2.89/0.98  clauses:                                27
% 2.89/0.98  conjectures:                            5
% 2.89/0.98  epr:                                    1
% 2.89/0.98  horn:                                   23
% 2.89/0.98  ground:                                 5
% 2.89/0.98  unary:                                  11
% 2.89/0.98  binary:                                 10
% 2.89/0.98  lits:                                   54
% 2.89/0.98  lits_eq:                                35
% 2.89/0.98  fd_pure:                                0
% 2.89/0.98  fd_pseudo:                              0
% 2.89/0.98  fd_cond:                                0
% 2.89/0.98  fd_pseudo_cond:                         4
% 2.89/0.98  ac_symbols:                             0
% 2.89/0.98  
% 2.89/0.98  ------ Propositional Solver
% 2.89/0.98  
% 2.89/0.98  prop_solver_calls:                      23
% 2.89/0.98  prop_fast_solver_calls:                 576
% 2.89/0.98  smt_solver_calls:                       0
% 2.89/0.98  smt_fast_solver_calls:                  0
% 2.89/0.98  prop_num_of_clauses:                    1810
% 2.89/0.98  prop_preprocess_simplified:             5232
% 2.89/0.98  prop_fo_subsumed:                       3
% 2.89/0.98  prop_solver_time:                       0.
% 2.89/0.98  smt_solver_time:                        0.
% 2.89/0.98  smt_fast_solver_time:                   0.
% 2.89/0.98  prop_fast_solver_time:                  0.
% 2.89/0.98  prop_unsat_core_time:                   0.
% 2.89/0.98  
% 2.89/0.98  ------ QBF
% 2.89/0.98  
% 2.89/0.98  qbf_q_res:                              0
% 2.89/0.98  qbf_num_tautologies:                    0
% 2.89/0.98  qbf_prep_cycles:                        0
% 2.89/0.98  
% 2.89/0.98  ------ BMC1
% 2.89/0.98  
% 2.89/0.98  bmc1_current_bound:                     -1
% 2.89/0.98  bmc1_last_solved_bound:                 -1
% 2.89/0.98  bmc1_unsat_core_size:                   -1
% 2.89/0.98  bmc1_unsat_core_parents_size:           -1
% 2.89/0.98  bmc1_merge_next_fun:                    0
% 2.89/0.98  bmc1_unsat_core_clauses_time:           0.
% 2.89/0.98  
% 2.89/0.98  ------ Instantiation
% 2.89/0.98  
% 2.89/0.98  inst_num_of_clauses:                    577
% 2.89/0.98  inst_num_in_passive:                    61
% 2.89/0.98  inst_num_in_active:                     242
% 2.89/0.98  inst_num_in_unprocessed:                274
% 2.89/0.98  inst_num_of_loops:                      260
% 2.89/0.98  inst_num_of_learning_restarts:          0
% 2.89/0.98  inst_num_moves_active_passive:          16
% 2.89/0.98  inst_lit_activity:                      0
% 2.89/0.98  inst_lit_activity_moves:                0
% 2.89/0.98  inst_num_tautologies:                   0
% 2.89/0.98  inst_num_prop_implied:                  0
% 2.89/0.98  inst_num_existing_simplified:           0
% 2.89/0.98  inst_num_eq_res_simplified:             0
% 2.89/0.98  inst_num_child_elim:                    0
% 2.89/0.98  inst_num_of_dismatching_blockings:      233
% 2.89/0.98  inst_num_of_non_proper_insts:           709
% 2.89/0.98  inst_num_of_duplicates:                 0
% 2.89/0.98  inst_inst_num_from_inst_to_res:         0
% 2.89/0.98  inst_dismatching_checking_time:         0.
% 2.89/0.98  
% 2.89/0.98  ------ Resolution
% 2.89/0.98  
% 2.89/0.98  res_num_of_clauses:                     0
% 2.89/0.98  res_num_in_passive:                     0
% 2.89/0.98  res_num_in_active:                      0
% 2.89/0.98  res_num_of_loops:                       99
% 2.89/0.98  res_forward_subset_subsumed:            69
% 2.89/0.98  res_backward_subset_subsumed:           0
% 2.89/0.98  res_forward_subsumed:                   0
% 2.89/0.98  res_backward_subsumed:                  0
% 2.89/0.98  res_forward_subsumption_resolution:     0
% 2.89/0.98  res_backward_subsumption_resolution:    0
% 2.89/0.98  res_clause_to_clause_subsumption:       345
% 2.89/0.98  res_orphan_elimination:                 0
% 2.89/0.98  res_tautology_del:                      60
% 2.89/0.98  res_num_eq_res_simplified:              0
% 2.89/0.98  res_num_sel_changes:                    0
% 2.89/0.98  res_moves_from_active_to_pass:          0
% 2.89/0.98  
% 2.89/0.98  ------ Superposition
% 2.89/0.98  
% 2.89/0.98  sup_time_total:                         0.
% 2.89/0.98  sup_time_generating:                    0.
% 2.89/0.98  sup_time_sim_full:                      0.
% 2.89/0.98  sup_time_sim_immed:                     0.
% 2.89/0.98  
% 2.89/0.98  sup_num_of_clauses:                     83
% 2.89/0.98  sup_num_in_active:                      32
% 2.89/0.98  sup_num_in_passive:                     51
% 2.89/0.98  sup_num_of_loops:                       51
% 2.89/0.98  sup_fw_superposition:                   78
% 2.89/0.98  sup_bw_superposition:                   142
% 2.89/0.98  sup_immediate_simplified:               41
% 2.89/0.98  sup_given_eliminated:                   1
% 2.89/0.98  comparisons_done:                       0
% 2.89/0.98  comparisons_avoided:                    15
% 2.89/0.98  
% 2.89/0.98  ------ Simplifications
% 2.89/0.98  
% 2.89/0.98  
% 2.89/0.98  sim_fw_subset_subsumed:                 20
% 2.89/0.98  sim_bw_subset_subsumed:                 35
% 2.89/0.98  sim_fw_subsumed:                        9
% 2.89/0.98  sim_bw_subsumed:                        5
% 2.89/0.98  sim_fw_subsumption_res:                 1
% 2.89/0.98  sim_bw_subsumption_res:                 0
% 2.89/0.98  sim_tautology_del:                      22
% 2.89/0.98  sim_eq_tautology_del:                   6
% 2.89/0.98  sim_eq_res_simp:                        1
% 2.89/0.98  sim_fw_demodulated:                     9
% 2.89/0.98  sim_bw_demodulated:                     13
% 2.89/0.98  sim_light_normalised:                   6
% 2.89/0.98  sim_joinable_taut:                      0
% 2.89/0.98  sim_joinable_simp:                      0
% 2.89/0.98  sim_ac_normalised:                      0
% 2.89/0.98  sim_smt_subsumption:                    0
% 2.89/0.98  
%------------------------------------------------------------------------------
