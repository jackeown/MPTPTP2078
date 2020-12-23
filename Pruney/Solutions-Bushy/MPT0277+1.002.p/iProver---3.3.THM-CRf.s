%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0277+1.002 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:42:54 EST 2020

% Result     : Theorem 1.62s
% Output     : CNFRefutation 1.62s
% Verified   : 
% Statistics : Number of formulae       :   80 ( 674 expanded)
%              Number of clauses        :   40 ( 161 expanded)
%              Number of leaves         :    5 ( 146 expanded)
%              Depth                    :   24
%              Number of atoms          :  252 (3036 expanded)
%              Number of equality atoms :  220 (2734 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal clause size      :   20 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f4,conjecture,(
    ! [X0,X1,X2] :
      ( k1_xboole_0 = k4_xboole_0(X0,k2_tarski(X1,X2))
    <=> ~ ( k2_tarski(X1,X2) != X0
          & k1_tarski(X2) != X0
          & k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f5,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( k1_xboole_0 = k4_xboole_0(X0,k2_tarski(X1,X2))
      <=> ~ ( k2_tarski(X1,X2) != X0
            & k1_tarski(X2) != X0
            & k1_tarski(X1) != X0
            & k1_xboole_0 != X0 ) ) ),
    inference(negated_conjecture,[],[f4])).

fof(f7,plain,(
    ? [X0,X1,X2] :
      ( k1_xboole_0 = k4_xboole_0(X0,k2_tarski(X1,X2))
    <~> ( k2_tarski(X1,X2) = X0
        | k1_tarski(X2) = X0
        | k1_tarski(X1) = X0
        | k1_xboole_0 = X0 ) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f11,plain,(
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
    inference(nnf_transformation,[],[f7])).

fof(f12,plain,(
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
    inference(flattening,[],[f11])).

fof(f13,plain,
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
   => ( ( ( k2_tarski(sK1,sK2) != sK0
          & k1_tarski(sK2) != sK0
          & k1_tarski(sK1) != sK0
          & k1_xboole_0 != sK0 )
        | k1_xboole_0 != k4_xboole_0(sK0,k2_tarski(sK1,sK2)) )
      & ( k2_tarski(sK1,sK2) = sK0
        | k1_tarski(sK2) = sK0
        | k1_tarski(sK1) = sK0
        | k1_xboole_0 = sK0
        | k1_xboole_0 = k4_xboole_0(sK0,k2_tarski(sK1,sK2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f14,plain,
    ( ( ( k2_tarski(sK1,sK2) != sK0
        & k1_tarski(sK2) != sK0
        & k1_tarski(sK1) != sK0
        & k1_xboole_0 != sK0 )
      | k1_xboole_0 != k4_xboole_0(sK0,k2_tarski(sK1,sK2)) )
    & ( k2_tarski(sK1,sK2) = sK0
      | k1_tarski(sK2) = sK0
      | k1_tarski(sK1) = sK0
      | k1_xboole_0 = sK0
      | k1_xboole_0 = k4_xboole_0(sK0,k2_tarski(sK1,sK2)) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f12,f13])).

fof(f23,plain,
    ( k2_tarski(sK1,sK2) = sK0
    | k1_tarski(sK2) = sK0
    | k1_tarski(sK1) = sK0
    | k1_xboole_0 = sK0
    | k1_xboole_0 = k4_xboole_0(sK0,k2_tarski(sK1,sK2)) ),
    inference(cnf_transformation,[],[f14])).

fof(f1,axiom,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf_transformation,[],[f1])).

fof(f36,plain,
    ( k2_tarski(sK1,sK2) = sK0
    | k1_tarski(sK2) = sK0
    | k1_tarski(sK1) = sK0
    | o_0_0_xboole_0 = sK0
    | o_0_0_xboole_0 = k4_xboole_0(sK0,k2_tarski(sK1,sK2)) ),
    inference(definition_unfolding,[],[f23,f15,f15])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,X1)
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f10,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k4_xboole_0(X0,X1)
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k1_xboole_0 != k4_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f21,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | k1_xboole_0 != k4_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f31,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | o_0_0_xboole_0 != k4_xboole_0(X0,X1) ) ),
    inference(definition_unfolding,[],[f21,f15])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_tarski(X1,X2))
    <=> ~ ( k2_tarski(X1,X2) != X0
          & k1_tarski(X2) != X0
          & k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f6,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_tarski(X1,X2))
    <=> ( k2_tarski(X1,X2) = X0
        | k1_tarski(X2) = X0
        | k1_tarski(X1) = X0
        | k1_xboole_0 = X0 ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f8,plain,(
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
    inference(nnf_transformation,[],[f6])).

fof(f9,plain,(
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
    inference(flattening,[],[f8])).

fof(f16,plain,(
    ! [X2,X0,X1] :
      ( k2_tarski(X1,X2) = X0
      | k1_tarski(X2) = X0
      | k1_tarski(X1) = X0
      | k1_xboole_0 = X0
      | ~ r1_tarski(X0,k2_tarski(X1,X2)) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f29,plain,(
    ! [X2,X0,X1] :
      ( k2_tarski(X1,X2) = X0
      | k1_tarski(X2) = X0
      | k1_tarski(X1) = X0
      | o_0_0_xboole_0 = X0
      | ~ r1_tarski(X0,k2_tarski(X1,X2)) ) ),
    inference(definition_unfolding,[],[f16,f15])).

fof(f27,plain,
    ( k2_tarski(sK1,sK2) != sK0
    | k1_xboole_0 != k4_xboole_0(sK0,k2_tarski(sK1,sK2)) ),
    inference(cnf_transformation,[],[f14])).

fof(f32,plain,
    ( k2_tarski(sK1,sK2) != sK0
    | o_0_0_xboole_0 != k4_xboole_0(sK0,k2_tarski(sK1,sK2)) ),
    inference(definition_unfolding,[],[f27,f15])).

fof(f22,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f30,plain,(
    ! [X0,X1] :
      ( o_0_0_xboole_0 = k4_xboole_0(X0,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f22,f15])).

fof(f20,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k2_tarski(X1,X2))
      | k2_tarski(X1,X2) != X0 ) ),
    inference(cnf_transformation,[],[f9])).

fof(f37,plain,(
    ! [X2,X1] : r1_tarski(k2_tarski(X1,X2),k2_tarski(X1,X2)) ),
    inference(equality_resolution,[],[f20])).

fof(f19,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k2_tarski(X1,X2))
      | k1_tarski(X2) != X0 ) ),
    inference(cnf_transformation,[],[f9])).

fof(f38,plain,(
    ! [X2,X1] : r1_tarski(k1_tarski(X2),k2_tarski(X1,X2)) ),
    inference(equality_resolution,[],[f19])).

fof(f26,plain,
    ( k1_tarski(sK2) != sK0
    | k1_xboole_0 != k4_xboole_0(sK0,k2_tarski(sK1,sK2)) ),
    inference(cnf_transformation,[],[f14])).

fof(f33,plain,
    ( k1_tarski(sK2) != sK0
    | o_0_0_xboole_0 != k4_xboole_0(sK0,k2_tarski(sK1,sK2)) ),
    inference(definition_unfolding,[],[f26,f15])).

fof(f18,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k2_tarski(X1,X2))
      | k1_tarski(X1) != X0 ) ),
    inference(cnf_transformation,[],[f9])).

fof(f39,plain,(
    ! [X2,X1] : r1_tarski(k1_tarski(X1),k2_tarski(X1,X2)) ),
    inference(equality_resolution,[],[f18])).

fof(f25,plain,
    ( k1_tarski(sK1) != sK0
    | k1_xboole_0 != k4_xboole_0(sK0,k2_tarski(sK1,sK2)) ),
    inference(cnf_transformation,[],[f14])).

fof(f34,plain,
    ( k1_tarski(sK1) != sK0
    | o_0_0_xboole_0 != k4_xboole_0(sK0,k2_tarski(sK1,sK2)) ),
    inference(definition_unfolding,[],[f25,f15])).

fof(f24,plain,
    ( k1_xboole_0 != sK0
    | k1_xboole_0 != k4_xboole_0(sK0,k2_tarski(sK1,sK2)) ),
    inference(cnf_transformation,[],[f14])).

fof(f35,plain,
    ( o_0_0_xboole_0 != sK0
    | o_0_0_xboole_0 != k4_xboole_0(sK0,k2_tarski(sK1,sK2)) ),
    inference(definition_unfolding,[],[f24,f15,f15])).

fof(f17,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k2_tarski(X1,X2))
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f9])).

fof(f28,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k2_tarski(X1,X2))
      | o_0_0_xboole_0 != X0 ) ),
    inference(definition_unfolding,[],[f17,f15])).

fof(f40,plain,(
    ! [X2,X1] : r1_tarski(o_0_0_xboole_0,k2_tarski(X1,X2)) ),
    inference(equality_resolution,[],[f28])).

cnf(c_11,negated_conjecture,
    ( k2_tarski(sK1,sK2) = sK0
    | k1_tarski(sK2) = sK0
    | k1_tarski(sK1) = sK0
    | o_0_0_xboole_0 = k4_xboole_0(sK0,k2_tarski(sK1,sK2))
    | o_0_0_xboole_0 = sK0 ),
    inference(cnf_transformation,[],[f36])).

cnf(c_6,plain,
    ( r1_tarski(X0,X1)
    | k4_xboole_0(X0,X1) != o_0_0_xboole_0 ),
    inference(cnf_transformation,[],[f31])).

cnf(c_427,plain,
    ( k4_xboole_0(X0,X1) != o_0_0_xboole_0
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_710,plain,
    ( k2_tarski(sK1,sK2) = sK0
    | k1_tarski(sK2) = sK0
    | k1_tarski(sK1) = sK0
    | sK0 = o_0_0_xboole_0
    | r1_tarski(sK0,k2_tarski(sK1,sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_11,c_427])).

cnf(c_4,plain,
    ( ~ r1_tarski(X0,k2_tarski(X1,X2))
    | k2_tarski(X1,X2) = X0
    | k1_tarski(X2) = X0
    | k1_tarski(X1) = X0
    | o_0_0_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f29])).

cnf(c_429,plain,
    ( k2_tarski(X0,X1) = X2
    | k1_tarski(X1) = X2
    | k1_tarski(X0) = X2
    | o_0_0_xboole_0 = X2
    | r1_tarski(X2,k2_tarski(X0,X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_876,plain,
    ( k2_tarski(sK1,sK2) = sK0
    | k1_tarski(sK2) = sK0
    | k1_tarski(sK1) = sK0
    | sK0 = o_0_0_xboole_0 ),
    inference(superposition,[status(thm)],[c_710,c_429])).

cnf(c_7,negated_conjecture,
    ( k2_tarski(sK1,sK2) != sK0
    | o_0_0_xboole_0 != k4_xboole_0(sK0,k2_tarski(sK1,sK2)) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_896,plain,
    ( k4_xboole_0(sK0,sK0) != o_0_0_xboole_0
    | k2_tarski(sK1,sK2) != sK0
    | k1_tarski(sK2) = sK0
    | k1_tarski(sK1) = sK0
    | sK0 = o_0_0_xboole_0 ),
    inference(superposition,[status(thm)],[c_876,c_7])).

cnf(c_905,plain,
    ( k4_xboole_0(sK0,sK0) != o_0_0_xboole_0
    | k1_tarski(sK2) = sK0
    | k1_tarski(sK1) = sK0
    | sK0 = o_0_0_xboole_0 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_896,c_876])).

cnf(c_5,plain,
    ( ~ r1_tarski(X0,X1)
    | k4_xboole_0(X0,X1) = o_0_0_xboole_0 ),
    inference(cnf_transformation,[],[f30])).

cnf(c_15,plain,
    ( k4_xboole_0(X0,X1) = o_0_0_xboole_0
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_17,plain,
    ( k4_xboole_0(sK0,sK0) = o_0_0_xboole_0
    | r1_tarski(sK0,sK0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_15])).

cnf(c_0,plain,
    ( r1_tarski(k2_tarski(X0,X1),k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_433,plain,
    ( r1_tarski(k2_tarski(X0,X1),k2_tarski(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_890,plain,
    ( k1_tarski(sK2) = sK0
    | k1_tarski(sK1) = sK0
    | sK0 = o_0_0_xboole_0
    | r1_tarski(sK0,sK0) = iProver_top ),
    inference(superposition,[status(thm)],[c_876,c_433])).

cnf(c_1050,plain,
    ( k1_tarski(sK2) = sK0
    | k1_tarski(sK1) = sK0
    | sK0 = o_0_0_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_905,c_17,c_890])).

cnf(c_1,plain,
    ( r1_tarski(k1_tarski(X0),k2_tarski(X1,X0)) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_432,plain,
    ( r1_tarski(k1_tarski(X0),k2_tarski(X1,X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_1055,plain,
    ( k1_tarski(sK1) = sK0
    | sK0 = o_0_0_xboole_0
    | r1_tarski(sK0,k2_tarski(X0,sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1050,c_432])).

cnf(c_428,plain,
    ( k4_xboole_0(X0,X1) = o_0_0_xboole_0
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_1083,plain,
    ( k4_xboole_0(sK0,k2_tarski(X0,sK2)) = o_0_0_xboole_0
    | k1_tarski(sK1) = sK0
    | sK0 = o_0_0_xboole_0 ),
    inference(superposition,[status(thm)],[c_1055,c_428])).

cnf(c_8,negated_conjecture,
    ( k1_tarski(sK2) != sK0
    | o_0_0_xboole_0 != k4_xboole_0(sK0,k2_tarski(sK1,sK2)) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_1319,plain,
    ( k1_tarski(sK2) != sK0
    | k1_tarski(sK1) = sK0
    | sK0 = o_0_0_xboole_0 ),
    inference(superposition,[status(thm)],[c_1083,c_8])).

cnf(c_1378,plain,
    ( k1_tarski(sK1) = sK0
    | sK0 = o_0_0_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1319,c_1050])).

cnf(c_2,plain,
    ( r1_tarski(k1_tarski(X0),k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_431,plain,
    ( r1_tarski(k1_tarski(X0),k2_tarski(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_771,plain,
    ( k4_xboole_0(k1_tarski(X0),k2_tarski(X0,X1)) = o_0_0_xboole_0 ),
    inference(superposition,[status(thm)],[c_431,c_428])).

cnf(c_1382,plain,
    ( k4_xboole_0(sK0,k2_tarski(sK1,X0)) = o_0_0_xboole_0
    | sK0 = o_0_0_xboole_0 ),
    inference(superposition,[status(thm)],[c_1378,c_771])).

cnf(c_9,negated_conjecture,
    ( k1_tarski(sK1) != sK0
    | o_0_0_xboole_0 != k4_xboole_0(sK0,k2_tarski(sK1,sK2)) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_1417,plain,
    ( k1_tarski(sK1) != sK0
    | sK0 = o_0_0_xboole_0 ),
    inference(superposition,[status(thm)],[c_1382,c_9])).

cnf(c_1500,plain,
    ( sK0 = o_0_0_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1417,c_1378])).

cnf(c_10,negated_conjecture,
    ( o_0_0_xboole_0 != k4_xboole_0(sK0,k2_tarski(sK1,sK2))
    | o_0_0_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f35])).

cnf(c_1512,plain,
    ( k4_xboole_0(o_0_0_xboole_0,k2_tarski(sK1,sK2)) != o_0_0_xboole_0
    | o_0_0_xboole_0 != o_0_0_xboole_0 ),
    inference(demodulation,[status(thm)],[c_1500,c_10])).

cnf(c_1513,plain,
    ( k4_xboole_0(o_0_0_xboole_0,k2_tarski(sK1,sK2)) != o_0_0_xboole_0 ),
    inference(equality_resolution_simp,[status(thm)],[c_1512])).

cnf(c_3,plain,
    ( r1_tarski(o_0_0_xboole_0,k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_430,plain,
    ( r1_tarski(o_0_0_xboole_0,k2_tarski(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_772,plain,
    ( k4_xboole_0(o_0_0_xboole_0,k2_tarski(X0,X1)) = o_0_0_xboole_0 ),
    inference(superposition,[status(thm)],[c_430,c_428])).

cnf(c_1515,plain,
    ( o_0_0_xboole_0 != o_0_0_xboole_0 ),
    inference(demodulation,[status(thm)],[c_1513,c_772])).

cnf(c_1516,plain,
    ( $false ),
    inference(equality_resolution_simp,[status(thm)],[c_1515])).


%------------------------------------------------------------------------------
