%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0247+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n026.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:42:49 EST 2020

% Result     : Theorem 0.93s
% Output     : CNFRefutation 0.93s
% Verified   : 
% Statistics : Number of formulae       :   77 ( 359 expanded)
%              Number of clauses        :   52 ( 132 expanded)
%              Number of leaves         :    5 (  59 expanded)
%              Depth                    :   22
%              Number of atoms          :  248 (2195 expanded)
%              Number of equality atoms :  194 (1755 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal clause size      :   20 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_tarski(X1,X2))
    <=> ~ ( k2_tarski(X1,X2) != X0
          & k1_tarski(X2) != X0
          & k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f4,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_tarski(X1,X2))
    <=> ( k2_tarski(X1,X2) = X0
        | k1_tarski(X2) = X0
        | k1_tarski(X1) = X0
        | k1_xboole_0 = X0 ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f6,plain,(
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
    inference(nnf_transformation,[],[f4])).

fof(f7,plain,(
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
    inference(flattening,[],[f6])).

fof(f12,plain,(
    ! [X2,X0,X1] :
      ( k2_tarski(X1,X2) = X0
      | k1_tarski(X2) = X0
      | k1_tarski(X1) = X0
      | k1_xboole_0 = X0
      | ~ r1_tarski(X0,k2_tarski(X1,X2)) ) ),
    inference(cnf_transformation,[],[f7])).

fof(f2,conjecture,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_tarski(X1,X2))
    <=> ~ ( k2_tarski(X1,X2) != X0
          & k1_tarski(X2) != X0
          & k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f3,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( r1_tarski(X0,k2_tarski(X1,X2))
      <=> ~ ( k2_tarski(X1,X2) != X0
            & k1_tarski(X2) != X0
            & k1_tarski(X1) != X0
            & k1_xboole_0 != X0 ) ) ),
    inference(negated_conjecture,[],[f2])).

fof(f5,plain,(
    ? [X0,X1,X2] :
      ( r1_tarski(X0,k2_tarski(X1,X2))
    <~> ( k2_tarski(X1,X2) = X0
        | k1_tarski(X2) = X0
        | k1_tarski(X1) = X0
        | k1_xboole_0 = X0 ) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f8,plain,(
    ? [X0,X1,X2] :
      ( ( ( k2_tarski(X1,X2) != X0
          & k1_tarski(X2) != X0
          & k1_tarski(X1) != X0
          & k1_xboole_0 != X0 )
        | ~ r1_tarski(X0,k2_tarski(X1,X2)) )
      & ( k2_tarski(X1,X2) = X0
        | k1_tarski(X2) = X0
        | k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | r1_tarski(X0,k2_tarski(X1,X2)) ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f9,plain,(
    ? [X0,X1,X2] :
      ( ( ( k2_tarski(X1,X2) != X0
          & k1_tarski(X2) != X0
          & k1_tarski(X1) != X0
          & k1_xboole_0 != X0 )
        | ~ r1_tarski(X0,k2_tarski(X1,X2)) )
      & ( k2_tarski(X1,X2) = X0
        | k1_tarski(X2) = X0
        | k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | r1_tarski(X0,k2_tarski(X1,X2)) ) ) ),
    inference(flattening,[],[f8])).

fof(f10,plain,
    ( ? [X0,X1,X2] :
        ( ( ( k2_tarski(X1,X2) != X0
            & k1_tarski(X2) != X0
            & k1_tarski(X1) != X0
            & k1_xboole_0 != X0 )
          | ~ r1_tarski(X0,k2_tarski(X1,X2)) )
        & ( k2_tarski(X1,X2) = X0
          | k1_tarski(X2) = X0
          | k1_tarski(X1) = X0
          | k1_xboole_0 = X0
          | r1_tarski(X0,k2_tarski(X1,X2)) ) )
   => ( ( ( k2_tarski(sK1,sK2) != sK0
          & k1_tarski(sK2) != sK0
          & k1_tarski(sK1) != sK0
          & k1_xboole_0 != sK0 )
        | ~ r1_tarski(sK0,k2_tarski(sK1,sK2)) )
      & ( k2_tarski(sK1,sK2) = sK0
        | k1_tarski(sK2) = sK0
        | k1_tarski(sK1) = sK0
        | k1_xboole_0 = sK0
        | r1_tarski(sK0,k2_tarski(sK1,sK2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f11,plain,
    ( ( ( k2_tarski(sK1,sK2) != sK0
        & k1_tarski(sK2) != sK0
        & k1_tarski(sK1) != sK0
        & k1_xboole_0 != sK0 )
      | ~ r1_tarski(sK0,k2_tarski(sK1,sK2)) )
    & ( k2_tarski(sK1,sK2) = sK0
      | k1_tarski(sK2) = sK0
      | k1_tarski(sK1) = sK0
      | k1_xboole_0 = sK0
      | r1_tarski(sK0,k2_tarski(sK1,sK2)) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f9,f10])).

fof(f17,plain,
    ( k2_tarski(sK1,sK2) = sK0
    | k1_tarski(sK2) = sK0
    | k1_tarski(sK1) = sK0
    | k1_xboole_0 = sK0
    | r1_tarski(sK0,k2_tarski(sK1,sK2)) ),
    inference(cnf_transformation,[],[f11])).

fof(f19,plain,
    ( k1_tarski(sK1) != sK0
    | ~ r1_tarski(sK0,k2_tarski(sK1,sK2)) ),
    inference(cnf_transformation,[],[f11])).

fof(f21,plain,
    ( k2_tarski(sK1,sK2) != sK0
    | ~ r1_tarski(sK0,k2_tarski(sK1,sK2)) ),
    inference(cnf_transformation,[],[f11])).

fof(f20,plain,
    ( k1_tarski(sK2) != sK0
    | ~ r1_tarski(sK0,k2_tarski(sK1,sK2)) ),
    inference(cnf_transformation,[],[f11])).

fof(f18,plain,
    ( k1_xboole_0 != sK0
    | ~ r1_tarski(sK0,k2_tarski(sK1,sK2)) ),
    inference(cnf_transformation,[],[f11])).

fof(f16,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k2_tarski(X1,X2))
      | k2_tarski(X1,X2) != X0 ) ),
    inference(cnf_transformation,[],[f7])).

fof(f22,plain,(
    ! [X2,X1] : r1_tarski(k2_tarski(X1,X2),k2_tarski(X1,X2)) ),
    inference(equality_resolution,[],[f16])).

fof(f15,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k2_tarski(X1,X2))
      | k1_tarski(X2) != X0 ) ),
    inference(cnf_transformation,[],[f7])).

fof(f23,plain,(
    ! [X2,X1] : r1_tarski(k1_tarski(X2),k2_tarski(X1,X2)) ),
    inference(equality_resolution,[],[f15])).

fof(f14,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k2_tarski(X1,X2))
      | k1_tarski(X1) != X0 ) ),
    inference(cnf_transformation,[],[f7])).

fof(f24,plain,(
    ! [X2,X1] : r1_tarski(k1_tarski(X1),k2_tarski(X1,X2)) ),
    inference(equality_resolution,[],[f14])).

fof(f13,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k2_tarski(X1,X2))
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f7])).

fof(f25,plain,(
    ! [X2,X1] : r1_tarski(k1_xboole_0,k2_tarski(X1,X2)) ),
    inference(equality_resolution,[],[f13])).

cnf(c_4,plain,
    ( ~ r1_tarski(X0,k2_tarski(X1,X2))
    | k2_tarski(X1,X2) = X0
    | k1_tarski(X2) = X0
    | k1_tarski(X1) = X0
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f12])).

cnf(c_378,plain,
    ( ~ r1_tarski(X0_35,k2_tarski(X0_36,X1_36))
    | k2_tarski(X0_36,X1_36) = X0_35
    | k1_tarski(X1_36) = X0_35
    | k1_tarski(X0_36) = X0_35
    | k1_xboole_0 = X0_35 ),
    inference(subtyping,[status(esa)],[c_4])).

cnf(c_563,plain,
    ( k2_tarski(X0_36,X1_36) = X0_35
    | k1_tarski(X1_36) = X0_35
    | k1_tarski(X0_36) = X0_35
    | k1_xboole_0 = X0_35
    | r1_tarski(X0_35,k2_tarski(X0_36,X1_36)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_378])).

cnf(c_9,negated_conjecture,
    ( r1_tarski(sK0,k2_tarski(sK1,sK2))
    | k2_tarski(sK1,sK2) = sK0
    | k1_tarski(sK2) = sK0
    | k1_tarski(sK1) = sK0
    | k1_xboole_0 = sK0 ),
    inference(cnf_transformation,[],[f17])).

cnf(c_373,negated_conjecture,
    ( r1_tarski(sK0,k2_tarski(sK1,sK2))
    | k2_tarski(sK1,sK2) = sK0
    | k1_tarski(sK2) = sK0
    | k1_tarski(sK1) = sK0
    | k1_xboole_0 = sK0 ),
    inference(subtyping,[status(esa)],[c_9])).

cnf(c_568,plain,
    ( k2_tarski(sK1,sK2) = sK0
    | k1_tarski(sK2) = sK0
    | k1_tarski(sK1) = sK0
    | k1_xboole_0 = sK0
    | r1_tarski(sK0,k2_tarski(sK1,sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_373])).

cnf(c_613,plain,
    ( k2_tarski(sK1,sK2) = sK0
    | k1_tarski(sK2) = sK0
    | k1_tarski(sK1) = sK0
    | sK0 = k1_xboole_0 ),
    inference(backward_subsumption_resolution,[status(thm)],[c_563,c_568])).

cnf(c_989,plain,
    ( k2_tarski(sK1,sK2) = X0_35
    | k1_tarski(sK2) = X0_35
    | k1_tarski(sK2) = sK0
    | k1_tarski(sK1) = X0_35
    | k1_tarski(sK1) = sK0
    | sK0 = k1_xboole_0
    | k1_xboole_0 = X0_35
    | r1_tarski(X0_35,sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_613,c_563])).

cnf(c_7,negated_conjecture,
    ( ~ r1_tarski(sK0,k2_tarski(sK1,sK2))
    | k1_tarski(sK1) != sK0 ),
    inference(cnf_transformation,[],[f19])).

cnf(c_375,negated_conjecture,
    ( ~ r1_tarski(sK0,k2_tarski(sK1,sK2))
    | k1_tarski(sK1) != sK0 ),
    inference(subtyping,[status(esa)],[c_7])).

cnf(c_566,plain,
    ( k1_tarski(sK1) != sK0
    | r1_tarski(sK0,k2_tarski(sK1,sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_375])).

cnf(c_5,negated_conjecture,
    ( ~ r1_tarski(sK0,k2_tarski(sK1,sK2))
    | k2_tarski(sK1,sK2) != sK0 ),
    inference(cnf_transformation,[],[f21])).

cnf(c_377,negated_conjecture,
    ( ~ r1_tarski(sK0,k2_tarski(sK1,sK2))
    | k2_tarski(sK1,sK2) != sK0 ),
    inference(subtyping,[status(esa)],[c_5])).

cnf(c_403,plain,
    ( k2_tarski(sK1,sK2) != sK0
    | r1_tarski(sK0,k2_tarski(sK1,sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_377])).

cnf(c_6,negated_conjecture,
    ( ~ r1_tarski(sK0,k2_tarski(sK1,sK2))
    | k1_tarski(sK2) != sK0 ),
    inference(cnf_transformation,[],[f20])).

cnf(c_376,negated_conjecture,
    ( ~ r1_tarski(sK0,k2_tarski(sK1,sK2))
    | k1_tarski(sK2) != sK0 ),
    inference(subtyping,[status(esa)],[c_6])).

cnf(c_404,plain,
    ( k1_tarski(sK2) != sK0
    | r1_tarski(sK0,k2_tarski(sK1,sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_376])).

cnf(c_405,plain,
    ( k1_tarski(sK1) != sK0
    | r1_tarski(sK0,k2_tarski(sK1,sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_375])).

cnf(c_8,negated_conjecture,
    ( ~ r1_tarski(sK0,k2_tarski(sK1,sK2))
    | k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f18])).

cnf(c_374,negated_conjecture,
    ( ~ r1_tarski(sK0,k2_tarski(sK1,sK2))
    | k1_xboole_0 != sK0 ),
    inference(subtyping,[status(esa)],[c_8])).

cnf(c_406,plain,
    ( k1_xboole_0 != sK0
    | r1_tarski(sK0,k2_tarski(sK1,sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_374])).

cnf(c_385,plain,
    ( X0_35 != X1_35
    | X2_35 != X1_35
    | X2_35 = X0_35 ),
    theory(equality)).

cnf(c_648,plain,
    ( sK0 != X0_35
    | k1_xboole_0 != X0_35
    | k1_xboole_0 = sK0 ),
    inference(instantiation,[status(thm)],[c_385])).

cnf(c_667,plain,
    ( sK0 != k1_xboole_0
    | k1_xboole_0 = sK0
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_648])).

cnf(c_384,plain,
    ( X0_35 = X0_35 ),
    theory(equality)).

cnf(c_668,plain,
    ( k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_384])).

cnf(c_724,plain,
    ( r1_tarski(sK0,k2_tarski(sK1,sK2)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_566,c_403,c_404,c_405,c_406,c_613,c_667,c_668])).

cnf(c_0,plain,
    ( r1_tarski(k2_tarski(X0,X1),k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f22])).

cnf(c_382,plain,
    ( r1_tarski(k2_tarski(X0_36,X1_36),k2_tarski(X0_36,X1_36)) ),
    inference(subtyping,[status(esa)],[c_0])).

cnf(c_559,plain,
    ( r1_tarski(k2_tarski(X0_36,X1_36),k2_tarski(X0_36,X1_36)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_382])).

cnf(c_877,plain,
    ( k1_tarski(sK2) = sK0
    | k1_tarski(sK1) = sK0
    | sK0 = k1_xboole_0
    | r1_tarski(sK0,sK0) = iProver_top ),
    inference(superposition,[status(thm)],[c_613,c_559])).

cnf(c_738,plain,
    ( k1_tarski(sK2) = sK0
    | k1_tarski(sK1) = sK0
    | sK0 = k1_xboole_0
    | r1_tarski(sK0,sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_613,c_724])).

cnf(c_1010,plain,
    ( sK0 = k1_xboole_0
    | k1_tarski(sK1) = sK0
    | k1_tarski(sK2) = sK0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_877,c_738])).

cnf(c_1011,plain,
    ( k1_tarski(sK2) = sK0
    | k1_tarski(sK1) = sK0
    | sK0 = k1_xboole_0 ),
    inference(renaming,[status(thm)],[c_1010])).

cnf(c_1,plain,
    ( r1_tarski(k1_tarski(X0),k2_tarski(X1,X0)) ),
    inference(cnf_transformation,[],[f23])).

cnf(c_381,plain,
    ( r1_tarski(k1_tarski(X0_36),k2_tarski(X1_36,X0_36)) ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_560,plain,
    ( r1_tarski(k1_tarski(X0_36),k2_tarski(X1_36,X0_36)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_381])).

cnf(c_1017,plain,
    ( k1_tarski(sK1) = sK0
    | sK0 = k1_xboole_0
    | r1_tarski(sK0,k2_tarski(X0_36,sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1011,c_560])).

cnf(c_1034,plain,
    ( k1_tarski(sK1) = sK0
    | sK0 = k1_xboole_0
    | r1_tarski(sK0,k2_tarski(sK1,sK2)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_1017])).

cnf(c_1098,plain,
    ( k1_tarski(sK1) = sK0
    | sK0 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_989,c_403,c_404,c_405,c_406,c_613,c_667,c_668,c_1034])).

cnf(c_2,plain,
    ( r1_tarski(k1_tarski(X0),k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f24])).

cnf(c_380,plain,
    ( r1_tarski(k1_tarski(X0_36),k2_tarski(X0_36,X1_36)) ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_561,plain,
    ( r1_tarski(k1_tarski(X0_36),k2_tarski(X0_36,X1_36)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_380])).

cnf(c_1102,plain,
    ( sK0 = k1_xboole_0
    | r1_tarski(sK0,k2_tarski(sK1,X0_36)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1098,c_561])).

cnf(c_1120,plain,
    ( sK0 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1102,c_724])).

cnf(c_567,plain,
    ( k1_xboole_0 != sK0
    | r1_tarski(sK0,k2_tarski(sK1,sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_374])).

cnf(c_1217,plain,
    ( k1_xboole_0 != k1_xboole_0
    | r1_tarski(k1_xboole_0,k2_tarski(sK1,sK2)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1120,c_567])).

cnf(c_1218,plain,
    ( r1_tarski(k1_xboole_0,k2_tarski(sK1,sK2)) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_1217])).

cnf(c_3,plain,
    ( r1_tarski(k1_xboole_0,k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f25])).

cnf(c_379,plain,
    ( r1_tarski(k1_xboole_0,k2_tarski(X0_36,X1_36)) ),
    inference(subtyping,[status(esa)],[c_3])).

cnf(c_562,plain,
    ( r1_tarski(k1_xboole_0,k2_tarski(X0_36,X1_36)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_379])).

cnf(c_1224,plain,
    ( $false ),
    inference(forward_subsumption_resolution,[status(thm)],[c_1218,c_562])).


%------------------------------------------------------------------------------
