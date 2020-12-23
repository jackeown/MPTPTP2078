%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0277+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n026.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:42:54 EST 2020

% Result     : Theorem 1.52s
% Output     : CNFRefutation 1.52s
% Verified   : 
% Statistics : Number of formulae       :   66 ( 478 expanded)
%              Number of clauses        :   37 ( 157 expanded)
%              Number of leaves         :    5 (  79 expanded)
%              Depth                    :   22
%              Number of atoms          :  218 (2673 expanded)
%              Number of equality atoms :  193 (2418 expanded)
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

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

fof(f2,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,X1)
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f10,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k4_xboole_0(X0,X1)
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k1_xboole_0 != k4_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f20,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | k1_xboole_0 != k4_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_tarski(X1,X2))
    <=> ~ ( k2_tarski(X1,X2) != X0
          & k1_tarski(X2) != X0
          & k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f6,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_tarski(X1,X2))
    <=> ( k2_tarski(X1,X2) = X0
        | k1_tarski(X2) = X0
        | k1_tarski(X1) = X0
        | k1_xboole_0 = X0 ) ) ),
    inference(ennf_transformation,[],[f1])).

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

fof(f15,plain,(
    ! [X2,X0,X1] :
      ( k2_tarski(X1,X2) = X0
      | k1_tarski(X2) = X0
      | k1_tarski(X1) = X0
      | k1_xboole_0 = X0
      | ~ r1_tarski(X0,k2_tarski(X1,X2)) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f19,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k2_tarski(X1,X2))
      | k2_tarski(X1,X2) != X0 ) ),
    inference(cnf_transformation,[],[f9])).

fof(f28,plain,(
    ! [X2,X1] : r1_tarski(k2_tarski(X1,X2),k2_tarski(X1,X2)) ),
    inference(equality_resolution,[],[f19])).

fof(f21,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f27,plain,
    ( k2_tarski(sK1,sK2) != sK0
    | k1_xboole_0 != k4_xboole_0(sK0,k2_tarski(sK1,sK2)) ),
    inference(cnf_transformation,[],[f14])).

fof(f18,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k2_tarski(X1,X2))
      | k1_tarski(X2) != X0 ) ),
    inference(cnf_transformation,[],[f9])).

fof(f29,plain,(
    ! [X2,X1] : r1_tarski(k1_tarski(X2),k2_tarski(X1,X2)) ),
    inference(equality_resolution,[],[f18])).

fof(f26,plain,
    ( k1_tarski(sK2) != sK0
    | k1_xboole_0 != k4_xboole_0(sK0,k2_tarski(sK1,sK2)) ),
    inference(cnf_transformation,[],[f14])).

fof(f17,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k2_tarski(X1,X2))
      | k1_tarski(X1) != X0 ) ),
    inference(cnf_transformation,[],[f9])).

fof(f30,plain,(
    ! [X2,X1] : r1_tarski(k1_tarski(X1),k2_tarski(X1,X2)) ),
    inference(equality_resolution,[],[f17])).

fof(f25,plain,
    ( k1_tarski(sK1) != sK0
    | k1_xboole_0 != k4_xboole_0(sK0,k2_tarski(sK1,sK2)) ),
    inference(cnf_transformation,[],[f14])).

fof(f24,plain,
    ( k1_xboole_0 != sK0
    | k1_xboole_0 != k4_xboole_0(sK0,k2_tarski(sK1,sK2)) ),
    inference(cnf_transformation,[],[f14])).

fof(f3,axiom,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f3])).

cnf(c_12,negated_conjecture,
    ( k2_tarski(sK1,sK2) = sK0
    | k1_tarski(sK2) = sK0
    | k1_tarski(sK1) = sK0
    | k1_xboole_0 = k4_xboole_0(sK0,k2_tarski(sK1,sK2))
    | k1_xboole_0 = sK0 ),
    inference(cnf_transformation,[],[f23])).

cnf(c_6,plain,
    ( r1_tarski(X0,X1)
    | k4_xboole_0(X0,X1) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f20])).

cnf(c_426,plain,
    ( k4_xboole_0(X0,X1) != k1_xboole_0
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_709,plain,
    ( k2_tarski(sK1,sK2) = sK0
    | k1_tarski(sK2) = sK0
    | k1_tarski(sK1) = sK0
    | sK0 = k1_xboole_0
    | r1_tarski(sK0,k2_tarski(sK1,sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_12,c_426])).

cnf(c_4,plain,
    ( ~ r1_tarski(X0,k2_tarski(X1,X2))
    | k2_tarski(X1,X2) = X0
    | k1_tarski(X2) = X0
    | k1_tarski(X1) = X0
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f15])).

cnf(c_428,plain,
    ( k2_tarski(X0,X1) = X2
    | k1_tarski(X1) = X2
    | k1_tarski(X0) = X2
    | k1_xboole_0 = X2
    | r1_tarski(X2,k2_tarski(X0,X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_1105,plain,
    ( k2_tarski(sK1,sK2) = sK0
    | k1_tarski(sK2) = sK0
    | k1_tarski(sK1) = sK0
    | sK0 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_709,c_428])).

cnf(c_0,plain,
    ( r1_tarski(k2_tarski(X0,X1),k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f28])).

cnf(c_432,plain,
    ( r1_tarski(k2_tarski(X0,X1),k2_tarski(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_5,plain,
    ( ~ r1_tarski(X0,X1)
    | k4_xboole_0(X0,X1) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f21])).

cnf(c_427,plain,
    ( k4_xboole_0(X0,X1) = k1_xboole_0
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_847,plain,
    ( k4_xboole_0(k2_tarski(X0,X1),k2_tarski(X0,X1)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_432,c_427])).

cnf(c_1119,plain,
    ( k4_xboole_0(sK0,sK0) = k1_xboole_0
    | k1_tarski(sK2) = sK0
    | k1_tarski(sK1) = sK0
    | sK0 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1105,c_847])).

cnf(c_8,negated_conjecture,
    ( k2_tarski(sK1,sK2) != sK0
    | k1_xboole_0 != k4_xboole_0(sK0,k2_tarski(sK1,sK2)) ),
    inference(cnf_transformation,[],[f27])).

cnf(c_1130,plain,
    ( k4_xboole_0(sK0,sK0) != k1_xboole_0
    | k2_tarski(sK1,sK2) != sK0
    | k1_tarski(sK2) = sK0
    | k1_tarski(sK1) = sK0
    | sK0 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1105,c_8])).

cnf(c_1139,plain,
    ( k4_xboole_0(sK0,sK0) != k1_xboole_0
    | k1_tarski(sK2) = sK0
    | k1_tarski(sK1) = sK0
    | sK0 = k1_xboole_0 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_1130,c_1105])).

cnf(c_1192,plain,
    ( k1_tarski(sK2) = sK0
    | k1_tarski(sK1) = sK0
    | sK0 = k1_xboole_0 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_1119,c_1139])).

cnf(c_1,plain,
    ( r1_tarski(k1_tarski(X0),k2_tarski(X1,X0)) ),
    inference(cnf_transformation,[],[f29])).

cnf(c_431,plain,
    ( r1_tarski(k1_tarski(X0),k2_tarski(X1,X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_848,plain,
    ( k4_xboole_0(k1_tarski(X0),k2_tarski(X1,X0)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_431,c_427])).

cnf(c_1256,plain,
    ( k4_xboole_0(sK0,k2_tarski(X0,sK2)) = k1_xboole_0
    | k1_tarski(sK1) = sK0
    | sK0 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1192,c_848])).

cnf(c_9,negated_conjecture,
    ( k1_tarski(sK2) != sK0
    | k1_xboole_0 != k4_xboole_0(sK0,k2_tarski(sK1,sK2)) ),
    inference(cnf_transformation,[],[f26])).

cnf(c_1415,plain,
    ( k1_tarski(sK2) != sK0
    | k1_tarski(sK1) = sK0
    | sK0 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1256,c_9])).

cnf(c_1429,plain,
    ( k1_tarski(sK1) = sK0
    | sK0 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1415,c_1192])).

cnf(c_2,plain,
    ( r1_tarski(k1_tarski(X0),k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_430,plain,
    ( r1_tarski(k1_tarski(X0),k2_tarski(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_849,plain,
    ( k4_xboole_0(k1_tarski(X0),k2_tarski(X0,X1)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_430,c_427])).

cnf(c_1433,plain,
    ( k4_xboole_0(sK0,k2_tarski(sK1,X0)) = k1_xboole_0
    | sK0 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1429,c_849])).

cnf(c_10,negated_conjecture,
    ( k1_tarski(sK1) != sK0
    | k1_xboole_0 != k4_xboole_0(sK0,k2_tarski(sK1,sK2)) ),
    inference(cnf_transformation,[],[f25])).

cnf(c_1512,plain,
    ( k1_tarski(sK1) != sK0
    | sK0 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1433,c_10])).

cnf(c_1527,plain,
    ( sK0 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1512,c_1429])).

cnf(c_11,negated_conjecture,
    ( k1_xboole_0 != k4_xboole_0(sK0,k2_tarski(sK1,sK2))
    | k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f24])).

cnf(c_1540,plain,
    ( k4_xboole_0(k1_xboole_0,k2_tarski(sK1,sK2)) != k1_xboole_0
    | k1_xboole_0 != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_1527,c_11])).

cnf(c_1541,plain,
    ( k4_xboole_0(k1_xboole_0,k2_tarski(sK1,sK2)) != k1_xboole_0 ),
    inference(equality_resolution_simp,[status(thm)],[c_1540])).

cnf(c_7,plain,
    ( k4_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f22])).

cnf(c_1543,plain,
    ( k1_xboole_0 != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_1541,c_7])).

cnf(c_1544,plain,
    ( $false ),
    inference(equality_resolution_simp,[status(thm)],[c_1543])).


%------------------------------------------------------------------------------
