%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:46:43 EST 2020

% Result     : Theorem 35.20s
% Output     : CNFRefutation 35.20s
% Verified   : 
% Statistics : Number of formulae       :   81 ( 157 expanded)
%              Number of clauses        :   43 (  57 expanded)
%              Number of leaves         :   11 (  33 expanded)
%              Depth                    :   13
%              Number of atoms          :  145 ( 314 expanded)
%              Number of equality atoms :   65 ( 112 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal clause size      :    6 (   1 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f12,conjecture,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(X0,X1)
       => r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f13,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( v1_relat_1(X2)
       => ( r1_tarski(X0,X1)
         => r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f19,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
      & r1_tarski(X0,X1)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f20,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
      & r1_tarski(X0,X1)
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f19])).

fof(f32,plain,
    ( ? [X0,X1,X2] :
        ( ~ r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
        & r1_tarski(X0,X1)
        & v1_relat_1(X2) )
   => ( ~ r1_tarski(k9_relat_1(sK4,sK2),k9_relat_1(sK4,sK3))
      & r1_tarski(sK2,sK3)
      & v1_relat_1(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,
    ( ~ r1_tarski(k9_relat_1(sK4,sK2),k9_relat_1(sK4,sK3))
    & r1_tarski(sK2,sK3)
    & v1_relat_1(sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f20,f32])).

fof(f55,plain,(
    r1_tarski(sK2,sK3) ),
    inference(cnf_transformation,[],[f33])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f5,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f47,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f9,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f51,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    inference(cnf_transformation,[],[f9])).

fof(f63,plain,(
    ! [X0] : k6_subset_1(X0,k1_xboole_0) = X0 ),
    inference(definition_unfolding,[],[f47,f51])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k4_xboole_0(X0,X1),X2)
     => r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X1,X2))
      | ~ r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k2_xboole_0(X1,X2))
      | ~ r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k2_xboole_0(X1,X2))
      | ~ r1_tarski(k6_subset_1(X0,X1),X2) ) ),
    inference(definition_unfolding,[],[f49,f51])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X1,X2))
     => r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k4_xboole_0(X0,X1),X2)
      | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k4_xboole_0(X0,X1),X2)
      | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k6_subset_1(X0,X1),X2)
      | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(definition_unfolding,[],[f48,f51])).

fof(f8,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f50,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f30])).

fof(f46,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f54,plain,(
    v1_relat_1(sK4) ),
    inference(cnf_transformation,[],[f33])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => k2_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) = k9_relat_1(X2,k2_xboole_0(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) = k9_relat_1(X2,k2_xboole_0(X0,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( k2_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) = k9_relat_1(X2,k2_xboole_0(X0,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => r1_tarski(k6_subset_1(k9_relat_1(X2,X0),k9_relat_1(X2,X1)),k9_relat_1(X2,k6_subset_1(X0,X1))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k6_subset_1(k9_relat_1(X2,X0),k9_relat_1(X2,X1)),k9_relat_1(X2,k6_subset_1(X0,X1)))
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k6_subset_1(k9_relat_1(X2,X0),k9_relat_1(X2,X1)),k9_relat_1(X2,k6_subset_1(X0,X1)))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f44,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f31])).

fof(f70,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f44])).

fof(f56,plain,(
    ~ r1_tarski(k9_relat_1(sK4,sK2),k9_relat_1(sK4,sK3)) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_20,negated_conjecture,
    ( r1_tarski(sK2,sK3) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_774,plain,
    ( r1_tarski(sK2,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_0,plain,
    ( k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_13,plain,
    ( k6_subset_1(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f63])).

cnf(c_15,plain,
    ( r1_tarski(X0,k2_xboole_0(X1,X2))
    | ~ r1_tarski(k6_subset_1(X0,X1),X2) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_779,plain,
    ( r1_tarski(X0,k2_xboole_0(X1,X2)) = iProver_top
    | r1_tarski(k6_subset_1(X0,X1),X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_1821,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X0,k2_xboole_0(k1_xboole_0,X1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_13,c_779])).

cnf(c_2015,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X0,k2_xboole_0(X1,k1_xboole_0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_0,c_1821])).

cnf(c_14,plain,
    ( ~ r1_tarski(X0,k2_xboole_0(X1,X2))
    | r1_tarski(k6_subset_1(X0,X1),X2) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_780,plain,
    ( r1_tarski(X0,k2_xboole_0(X1,X2)) != iProver_top
    | r1_tarski(k6_subset_1(X0,X1),X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_2240,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(k6_subset_1(X0,X1),k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_2015,c_780])).

cnf(c_16,plain,
    ( r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_778,plain,
    ( r1_tarski(X0,k2_xboole_0(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_2237,plain,
    ( r1_tarski(k6_subset_1(X0,X0),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_778,c_780])).

cnf(c_3453,plain,
    ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_13,c_2237])).

cnf(c_10,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f46])).

cnf(c_782,plain,
    ( X0 = X1
    | r1_tarski(X1,X0) != iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_3477,plain,
    ( k1_xboole_0 = X0
    | r1_tarski(X0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_3453,c_782])).

cnf(c_9929,plain,
    ( k6_subset_1(X0,X1) = k1_xboole_0
    | r1_tarski(X0,X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_2240,c_3477])).

cnf(c_125882,plain,
    ( k6_subset_1(sK2,sK3) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_774,c_9929])).

cnf(c_21,negated_conjecture,
    ( v1_relat_1(sK4) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_773,plain,
    ( v1_relat_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_17,plain,
    ( ~ v1_relat_1(X0)
    | k2_xboole_0(k9_relat_1(X0,X1),k9_relat_1(X0,X2)) = k9_relat_1(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_777,plain,
    ( k2_xboole_0(k9_relat_1(X0,X1),k9_relat_1(X0,X2)) = k9_relat_1(X0,k2_xboole_0(X1,X2))
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_1850,plain,
    ( k2_xboole_0(k9_relat_1(sK4,X0),k9_relat_1(sK4,X1)) = k9_relat_1(sK4,k2_xboole_0(X0,X1)) ),
    inference(superposition,[status(thm)],[c_773,c_777])).

cnf(c_18,plain,
    ( r1_tarski(k6_subset_1(k9_relat_1(X0,X1),k9_relat_1(X0,X2)),k9_relat_1(X0,k6_subset_1(X1,X2)))
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_776,plain,
    ( r1_tarski(k6_subset_1(k9_relat_1(X0,X1),k9_relat_1(X0,X2)),k9_relat_1(X0,k6_subset_1(X1,X2))) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_1819,plain,
    ( r1_tarski(k9_relat_1(X0,X1),k2_xboole_0(k9_relat_1(X0,X2),k9_relat_1(X0,k6_subset_1(X1,X2)))) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_776,c_779])).

cnf(c_7321,plain,
    ( r1_tarski(k9_relat_1(sK4,X0),k9_relat_1(sK4,k2_xboole_0(X1,k6_subset_1(X0,X1)))) = iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_1850,c_1819])).

cnf(c_22,plain,
    ( v1_relat_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_66939,plain,
    ( r1_tarski(k9_relat_1(sK4,X0),k9_relat_1(sK4,k2_xboole_0(X1,k6_subset_1(X0,X1)))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_7321,c_22])).

cnf(c_129336,plain,
    ( r1_tarski(k9_relat_1(sK4,sK2),k9_relat_1(sK4,k2_xboole_0(sK3,k1_xboole_0))) = iProver_top ),
    inference(superposition,[status(thm)],[c_125882,c_66939])).

cnf(c_12,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_781,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_2236,plain,
    ( r1_tarski(k6_subset_1(k2_xboole_0(X0,X1),X0),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_781,c_780])).

cnf(c_4016,plain,
    ( r1_tarski(k2_xboole_0(k1_xboole_0,X0),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_13,c_2236])).

cnf(c_4269,plain,
    ( r1_tarski(k2_xboole_0(X0,k1_xboole_0),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_0,c_4016])).

cnf(c_2496,plain,
    ( k2_xboole_0(X0,X1) = X0
    | r1_tarski(k2_xboole_0(X0,X1),X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_778,c_782])).

cnf(c_10905,plain,
    ( k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(superposition,[status(thm)],[c_4269,c_2496])).

cnf(c_129593,plain,
    ( r1_tarski(k9_relat_1(sK4,sK2),k9_relat_1(sK4,sK3)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_129336,c_10905])).

cnf(c_19,negated_conjecture,
    ( ~ r1_tarski(k9_relat_1(sK4,sK2),k9_relat_1(sK4,sK3)) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_24,plain,
    ( r1_tarski(k9_relat_1(sK4,sK2),k9_relat_1(sK4,sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_129593,c_24])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.13/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : iproveropt_run.sh %d %s
% 0.14/0.34  % Computer   : n007.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 20:05:51 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running in FOF mode
% 35.20/5.00  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 35.20/5.00  
% 35.20/5.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 35.20/5.00  
% 35.20/5.00  ------  iProver source info
% 35.20/5.00  
% 35.20/5.00  git: date: 2020-06-30 10:37:57 +0100
% 35.20/5.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 35.20/5.00  git: non_committed_changes: false
% 35.20/5.00  git: last_make_outside_of_git: false
% 35.20/5.00  
% 35.20/5.00  ------ 
% 35.20/5.00  
% 35.20/5.00  ------ Input Options
% 35.20/5.00  
% 35.20/5.00  --out_options                           all
% 35.20/5.00  --tptp_safe_out                         true
% 35.20/5.00  --problem_path                          ""
% 35.20/5.00  --include_path                          ""
% 35.20/5.00  --clausifier                            res/vclausify_rel
% 35.20/5.00  --clausifier_options                    --mode clausify
% 35.20/5.00  --stdin                                 false
% 35.20/5.00  --stats_out                             sel
% 35.20/5.00  
% 35.20/5.00  ------ General Options
% 35.20/5.00  
% 35.20/5.00  --fof                                   false
% 35.20/5.00  --time_out_real                         604.99
% 35.20/5.00  --time_out_virtual                      -1.
% 35.20/5.00  --symbol_type_check                     false
% 35.20/5.00  --clausify_out                          false
% 35.20/5.00  --sig_cnt_out                           false
% 35.20/5.00  --trig_cnt_out                          false
% 35.20/5.00  --trig_cnt_out_tolerance                1.
% 35.20/5.00  --trig_cnt_out_sk_spl                   false
% 35.20/5.00  --abstr_cl_out                          false
% 35.20/5.00  
% 35.20/5.00  ------ Global Options
% 35.20/5.00  
% 35.20/5.00  --schedule                              none
% 35.20/5.00  --add_important_lit                     false
% 35.20/5.00  --prop_solver_per_cl                    1000
% 35.20/5.00  --min_unsat_core                        false
% 35.20/5.00  --soft_assumptions                      false
% 35.20/5.00  --soft_lemma_size                       3
% 35.20/5.00  --prop_impl_unit_size                   0
% 35.20/5.00  --prop_impl_unit                        []
% 35.20/5.00  --share_sel_clauses                     true
% 35.20/5.00  --reset_solvers                         false
% 35.20/5.00  --bc_imp_inh                            [conj_cone]
% 35.20/5.00  --conj_cone_tolerance                   3.
% 35.20/5.00  --extra_neg_conj                        none
% 35.20/5.00  --large_theory_mode                     true
% 35.20/5.00  --prolific_symb_bound                   200
% 35.20/5.00  --lt_threshold                          2000
% 35.20/5.00  --clause_weak_htbl                      true
% 35.20/5.00  --gc_record_bc_elim                     false
% 35.20/5.00  
% 35.20/5.00  ------ Preprocessing Options
% 35.20/5.00  
% 35.20/5.00  --preprocessing_flag                    true
% 35.20/5.00  --time_out_prep_mult                    0.1
% 35.20/5.00  --splitting_mode                        input
% 35.20/5.00  --splitting_grd                         true
% 35.20/5.00  --splitting_cvd                         false
% 35.20/5.00  --splitting_cvd_svl                     false
% 35.20/5.00  --splitting_nvd                         32
% 35.20/5.00  --sub_typing                            true
% 35.20/5.00  --prep_gs_sim                           false
% 35.20/5.00  --prep_unflatten                        true
% 35.20/5.00  --prep_res_sim                          true
% 35.20/5.00  --prep_upred                            true
% 35.20/5.00  --prep_sem_filter                       exhaustive
% 35.20/5.00  --prep_sem_filter_out                   false
% 35.20/5.00  --pred_elim                             false
% 35.20/5.00  --res_sim_input                         true
% 35.20/5.00  --eq_ax_congr_red                       true
% 35.20/5.00  --pure_diseq_elim                       true
% 35.20/5.00  --brand_transform                       false
% 35.20/5.00  --non_eq_to_eq                          false
% 35.20/5.00  --prep_def_merge                        true
% 35.20/5.00  --prep_def_merge_prop_impl              false
% 35.20/5.00  --prep_def_merge_mbd                    true
% 35.20/5.00  --prep_def_merge_tr_red                 false
% 35.20/5.00  --prep_def_merge_tr_cl                  false
% 35.20/5.00  --smt_preprocessing                     true
% 35.20/5.00  --smt_ac_axioms                         fast
% 35.20/5.00  --preprocessed_out                      false
% 35.20/5.00  --preprocessed_stats                    false
% 35.20/5.00  
% 35.20/5.00  ------ Abstraction refinement Options
% 35.20/5.00  
% 35.20/5.00  --abstr_ref                             []
% 35.20/5.00  --abstr_ref_prep                        false
% 35.20/5.00  --abstr_ref_until_sat                   false
% 35.20/5.00  --abstr_ref_sig_restrict                funpre
% 35.20/5.00  --abstr_ref_af_restrict_to_split_sk     false
% 35.20/5.00  --abstr_ref_under                       []
% 35.20/5.00  
% 35.20/5.00  ------ SAT Options
% 35.20/5.00  
% 35.20/5.00  --sat_mode                              false
% 35.20/5.00  --sat_fm_restart_options                ""
% 35.20/5.00  --sat_gr_def                            false
% 35.20/5.00  --sat_epr_types                         true
% 35.20/5.00  --sat_non_cyclic_types                  false
% 35.20/5.00  --sat_finite_models                     false
% 35.20/5.00  --sat_fm_lemmas                         false
% 35.20/5.00  --sat_fm_prep                           false
% 35.20/5.00  --sat_fm_uc_incr                        true
% 35.20/5.00  --sat_out_model                         small
% 35.20/5.00  --sat_out_clauses                       false
% 35.20/5.00  
% 35.20/5.00  ------ QBF Options
% 35.20/5.00  
% 35.20/5.00  --qbf_mode                              false
% 35.20/5.00  --qbf_elim_univ                         false
% 35.20/5.00  --qbf_dom_inst                          none
% 35.20/5.00  --qbf_dom_pre_inst                      false
% 35.20/5.00  --qbf_sk_in                             false
% 35.20/5.00  --qbf_pred_elim                         true
% 35.20/5.00  --qbf_split                             512
% 35.20/5.00  
% 35.20/5.00  ------ BMC1 Options
% 35.20/5.00  
% 35.20/5.00  --bmc1_incremental                      false
% 35.20/5.00  --bmc1_axioms                           reachable_all
% 35.20/5.00  --bmc1_min_bound                        0
% 35.20/5.00  --bmc1_max_bound                        -1
% 35.20/5.00  --bmc1_max_bound_default                -1
% 35.20/5.00  --bmc1_symbol_reachability              true
% 35.20/5.00  --bmc1_property_lemmas                  false
% 35.20/5.00  --bmc1_k_induction                      false
% 35.20/5.00  --bmc1_non_equiv_states                 false
% 35.20/5.00  --bmc1_deadlock                         false
% 35.20/5.00  --bmc1_ucm                              false
% 35.20/5.00  --bmc1_add_unsat_core                   none
% 35.20/5.00  --bmc1_unsat_core_children              false
% 35.20/5.00  --bmc1_unsat_core_extrapolate_axioms    false
% 35.20/5.00  --bmc1_out_stat                         full
% 35.20/5.00  --bmc1_ground_init                      false
% 35.20/5.00  --bmc1_pre_inst_next_state              false
% 35.20/5.00  --bmc1_pre_inst_state                   false
% 35.20/5.00  --bmc1_pre_inst_reach_state             false
% 35.20/5.00  --bmc1_out_unsat_core                   false
% 35.20/5.00  --bmc1_aig_witness_out                  false
% 35.20/5.00  --bmc1_verbose                          false
% 35.20/5.00  --bmc1_dump_clauses_tptp                false
% 35.20/5.00  --bmc1_dump_unsat_core_tptp             false
% 35.20/5.00  --bmc1_dump_file                        -
% 35.20/5.00  --bmc1_ucm_expand_uc_limit              128
% 35.20/5.00  --bmc1_ucm_n_expand_iterations          6
% 35.20/5.00  --bmc1_ucm_extend_mode                  1
% 35.20/5.00  --bmc1_ucm_init_mode                    2
% 35.20/5.00  --bmc1_ucm_cone_mode                    none
% 35.20/5.00  --bmc1_ucm_reduced_relation_type        0
% 35.20/5.00  --bmc1_ucm_relax_model                  4
% 35.20/5.00  --bmc1_ucm_full_tr_after_sat            true
% 35.20/5.00  --bmc1_ucm_expand_neg_assumptions       false
% 35.20/5.00  --bmc1_ucm_layered_model                none
% 35.20/5.00  --bmc1_ucm_max_lemma_size               10
% 35.20/5.00  
% 35.20/5.00  ------ AIG Options
% 35.20/5.00  
% 35.20/5.00  --aig_mode                              false
% 35.20/5.00  
% 35.20/5.00  ------ Instantiation Options
% 35.20/5.00  
% 35.20/5.00  --instantiation_flag                    true
% 35.20/5.00  --inst_sos_flag                         false
% 35.20/5.00  --inst_sos_phase                        true
% 35.20/5.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 35.20/5.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 35.20/5.00  --inst_lit_sel_side                     num_symb
% 35.20/5.00  --inst_solver_per_active                1400
% 35.20/5.00  --inst_solver_calls_frac                1.
% 35.20/5.00  --inst_passive_queue_type               priority_queues
% 35.20/5.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 35.20/5.00  --inst_passive_queues_freq              [25;2]
% 35.20/5.00  --inst_dismatching                      true
% 35.20/5.00  --inst_eager_unprocessed_to_passive     true
% 35.20/5.00  --inst_prop_sim_given                   true
% 35.20/5.00  --inst_prop_sim_new                     false
% 35.20/5.00  --inst_subs_new                         false
% 35.20/5.00  --inst_eq_res_simp                      false
% 35.20/5.00  --inst_subs_given                       false
% 35.20/5.00  --inst_orphan_elimination               true
% 35.20/5.00  --inst_learning_loop_flag               true
% 35.20/5.00  --inst_learning_start                   3000
% 35.20/5.00  --inst_learning_factor                  2
% 35.20/5.00  --inst_start_prop_sim_after_learn       3
% 35.20/5.00  --inst_sel_renew                        solver
% 35.20/5.00  --inst_lit_activity_flag                true
% 35.20/5.00  --inst_restr_to_given                   false
% 35.20/5.00  --inst_activity_threshold               500
% 35.20/5.00  --inst_out_proof                        true
% 35.20/5.00  
% 35.20/5.00  ------ Resolution Options
% 35.20/5.00  
% 35.20/5.00  --resolution_flag                       true
% 35.20/5.00  --res_lit_sel                           adaptive
% 35.20/5.00  --res_lit_sel_side                      none
% 35.20/5.00  --res_ordering                          kbo
% 35.20/5.00  --res_to_prop_solver                    active
% 35.20/5.00  --res_prop_simpl_new                    false
% 35.20/5.00  --res_prop_simpl_given                  true
% 35.20/5.00  --res_passive_queue_type                priority_queues
% 35.20/5.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 35.20/5.00  --res_passive_queues_freq               [15;5]
% 35.20/5.00  --res_forward_subs                      full
% 35.20/5.00  --res_backward_subs                     full
% 35.20/5.00  --res_forward_subs_resolution           true
% 35.20/5.00  --res_backward_subs_resolution          true
% 35.20/5.00  --res_orphan_elimination                true
% 35.20/5.00  --res_time_limit                        2.
% 35.20/5.00  --res_out_proof                         true
% 35.20/5.00  
% 35.20/5.00  ------ Superposition Options
% 35.20/5.00  
% 35.20/5.00  --superposition_flag                    true
% 35.20/5.00  --sup_passive_queue_type                priority_queues
% 35.20/5.00  --sup_passive_queues                    [[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 35.20/5.00  --sup_passive_queues_freq               [1;4]
% 35.20/5.00  --demod_completeness_check              fast
% 35.20/5.00  --demod_use_ground                      true
% 35.20/5.00  --sup_to_prop_solver                    passive
% 35.20/5.00  --sup_prop_simpl_new                    true
% 35.20/5.00  --sup_prop_simpl_given                  true
% 35.20/5.00  --sup_fun_splitting                     false
% 35.20/5.00  --sup_smt_interval                      50000
% 35.20/5.00  
% 35.20/5.00  ------ Superposition Simplification Setup
% 35.20/5.00  
% 35.20/5.00  --sup_indices_passive                   []
% 35.20/5.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 35.20/5.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 35.20/5.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 35.20/5.00  --sup_full_triv                         [TrivRules;PropSubs]
% 35.20/5.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 35.20/5.00  --sup_full_bw                           [BwDemod]
% 35.20/5.00  --sup_immed_triv                        [TrivRules]
% 35.20/5.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 35.20/5.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 35.20/5.00  --sup_immed_bw_main                     []
% 35.20/5.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 35.20/5.00  --sup_input_triv                        [Unflattening;TrivRules]
% 35.20/5.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 35.20/5.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 35.20/5.00  
% 35.20/5.00  ------ Combination Options
% 35.20/5.00  
% 35.20/5.00  --comb_res_mult                         3
% 35.20/5.00  --comb_sup_mult                         2
% 35.20/5.00  --comb_inst_mult                        10
% 35.20/5.00  
% 35.20/5.00  ------ Debug Options
% 35.20/5.00  
% 35.20/5.00  --dbg_backtrace                         false
% 35.20/5.00  --dbg_dump_prop_clauses                 false
% 35.20/5.00  --dbg_dump_prop_clauses_file            -
% 35.20/5.00  --dbg_out_stat                          false
% 35.20/5.00  ------ Parsing...
% 35.20/5.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 35.20/5.00  
% 35.20/5.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 1 0s  sf_e 
% 35.20/5.00  
% 35.20/5.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 35.20/5.00  
% 35.20/5.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 35.20/5.00  ------ Proving...
% 35.20/5.00  ------ Problem Properties 
% 35.20/5.00  
% 35.20/5.00  
% 35.20/5.00  clauses                                 21
% 35.20/5.00  conjectures                             3
% 35.20/5.00  EPR                                     5
% 35.20/5.00  Horn                                    16
% 35.20/5.00  unary                                   7
% 35.20/5.00  binary                                  8
% 35.20/5.00  lits                                    42
% 35.20/5.00  lits eq                                 7
% 35.20/5.00  fd_pure                                 0
% 35.20/5.00  fd_pseudo                               0
% 35.20/5.00  fd_cond                                 0
% 35.20/5.00  fd_pseudo_cond                          4
% 35.20/5.00  AC symbols                              0
% 35.20/5.00  
% 35.20/5.00  ------ Input Options Time Limit: Unbounded
% 35.20/5.00  
% 35.20/5.00  
% 35.20/5.00  ------ 
% 35.20/5.00  Current options:
% 35.20/5.00  ------ 
% 35.20/5.00  
% 35.20/5.00  ------ Input Options
% 35.20/5.00  
% 35.20/5.00  --out_options                           all
% 35.20/5.00  --tptp_safe_out                         true
% 35.20/5.00  --problem_path                          ""
% 35.20/5.00  --include_path                          ""
% 35.20/5.00  --clausifier                            res/vclausify_rel
% 35.20/5.00  --clausifier_options                    --mode clausify
% 35.20/5.00  --stdin                                 false
% 35.20/5.00  --stats_out                             sel
% 35.20/5.00  
% 35.20/5.00  ------ General Options
% 35.20/5.00  
% 35.20/5.00  --fof                                   false
% 35.20/5.00  --time_out_real                         604.99
% 35.20/5.00  --time_out_virtual                      -1.
% 35.20/5.00  --symbol_type_check                     false
% 35.20/5.00  --clausify_out                          false
% 35.20/5.00  --sig_cnt_out                           false
% 35.20/5.00  --trig_cnt_out                          false
% 35.20/5.00  --trig_cnt_out_tolerance                1.
% 35.20/5.00  --trig_cnt_out_sk_spl                   false
% 35.20/5.00  --abstr_cl_out                          false
% 35.20/5.00  
% 35.20/5.00  ------ Global Options
% 35.20/5.00  
% 35.20/5.00  --schedule                              none
% 35.20/5.00  --add_important_lit                     false
% 35.20/5.00  --prop_solver_per_cl                    1000
% 35.20/5.00  --min_unsat_core                        false
% 35.20/5.00  --soft_assumptions                      false
% 35.20/5.00  --soft_lemma_size                       3
% 35.20/5.00  --prop_impl_unit_size                   0
% 35.20/5.00  --prop_impl_unit                        []
% 35.20/5.00  --share_sel_clauses                     true
% 35.20/5.00  --reset_solvers                         false
% 35.20/5.00  --bc_imp_inh                            [conj_cone]
% 35.20/5.00  --conj_cone_tolerance                   3.
% 35.20/5.00  --extra_neg_conj                        none
% 35.20/5.00  --large_theory_mode                     true
% 35.20/5.00  --prolific_symb_bound                   200
% 35.20/5.00  --lt_threshold                          2000
% 35.20/5.00  --clause_weak_htbl                      true
% 35.20/5.00  --gc_record_bc_elim                     false
% 35.20/5.00  
% 35.20/5.00  ------ Preprocessing Options
% 35.20/5.00  
% 35.20/5.00  --preprocessing_flag                    true
% 35.20/5.00  --time_out_prep_mult                    0.1
% 35.20/5.00  --splitting_mode                        input
% 35.20/5.00  --splitting_grd                         true
% 35.20/5.00  --splitting_cvd                         false
% 35.20/5.00  --splitting_cvd_svl                     false
% 35.20/5.00  --splitting_nvd                         32
% 35.20/5.00  --sub_typing                            true
% 35.20/5.00  --prep_gs_sim                           false
% 35.20/5.00  --prep_unflatten                        true
% 35.20/5.00  --prep_res_sim                          true
% 35.20/5.00  --prep_upred                            true
% 35.20/5.00  --prep_sem_filter                       exhaustive
% 35.20/5.00  --prep_sem_filter_out                   false
% 35.20/5.00  --pred_elim                             false
% 35.20/5.00  --res_sim_input                         true
% 35.20/5.00  --eq_ax_congr_red                       true
% 35.20/5.00  --pure_diseq_elim                       true
% 35.20/5.00  --brand_transform                       false
% 35.20/5.00  --non_eq_to_eq                          false
% 35.20/5.00  --prep_def_merge                        true
% 35.20/5.00  --prep_def_merge_prop_impl              false
% 35.20/5.00  --prep_def_merge_mbd                    true
% 35.20/5.00  --prep_def_merge_tr_red                 false
% 35.20/5.00  --prep_def_merge_tr_cl                  false
% 35.20/5.00  --smt_preprocessing                     true
% 35.20/5.00  --smt_ac_axioms                         fast
% 35.20/5.00  --preprocessed_out                      false
% 35.20/5.00  --preprocessed_stats                    false
% 35.20/5.00  
% 35.20/5.00  ------ Abstraction refinement Options
% 35.20/5.00  
% 35.20/5.00  --abstr_ref                             []
% 35.20/5.00  --abstr_ref_prep                        false
% 35.20/5.00  --abstr_ref_until_sat                   false
% 35.20/5.00  --abstr_ref_sig_restrict                funpre
% 35.20/5.00  --abstr_ref_af_restrict_to_split_sk     false
% 35.20/5.00  --abstr_ref_under                       []
% 35.20/5.00  
% 35.20/5.00  ------ SAT Options
% 35.20/5.00  
% 35.20/5.00  --sat_mode                              false
% 35.20/5.00  --sat_fm_restart_options                ""
% 35.20/5.00  --sat_gr_def                            false
% 35.20/5.00  --sat_epr_types                         true
% 35.20/5.00  --sat_non_cyclic_types                  false
% 35.20/5.00  --sat_finite_models                     false
% 35.20/5.00  --sat_fm_lemmas                         false
% 35.20/5.00  --sat_fm_prep                           false
% 35.20/5.00  --sat_fm_uc_incr                        true
% 35.20/5.00  --sat_out_model                         small
% 35.20/5.00  --sat_out_clauses                       false
% 35.20/5.00  
% 35.20/5.00  ------ QBF Options
% 35.20/5.00  
% 35.20/5.00  --qbf_mode                              false
% 35.20/5.00  --qbf_elim_univ                         false
% 35.20/5.00  --qbf_dom_inst                          none
% 35.20/5.00  --qbf_dom_pre_inst                      false
% 35.20/5.00  --qbf_sk_in                             false
% 35.20/5.00  --qbf_pred_elim                         true
% 35.20/5.00  --qbf_split                             512
% 35.20/5.00  
% 35.20/5.00  ------ BMC1 Options
% 35.20/5.00  
% 35.20/5.00  --bmc1_incremental                      false
% 35.20/5.00  --bmc1_axioms                           reachable_all
% 35.20/5.00  --bmc1_min_bound                        0
% 35.20/5.00  --bmc1_max_bound                        -1
% 35.20/5.00  --bmc1_max_bound_default                -1
% 35.20/5.00  --bmc1_symbol_reachability              true
% 35.20/5.00  --bmc1_property_lemmas                  false
% 35.20/5.00  --bmc1_k_induction                      false
% 35.20/5.00  --bmc1_non_equiv_states                 false
% 35.20/5.00  --bmc1_deadlock                         false
% 35.20/5.00  --bmc1_ucm                              false
% 35.20/5.00  --bmc1_add_unsat_core                   none
% 35.20/5.00  --bmc1_unsat_core_children              false
% 35.20/5.00  --bmc1_unsat_core_extrapolate_axioms    false
% 35.20/5.00  --bmc1_out_stat                         full
% 35.20/5.00  --bmc1_ground_init                      false
% 35.20/5.00  --bmc1_pre_inst_next_state              false
% 35.20/5.00  --bmc1_pre_inst_state                   false
% 35.20/5.00  --bmc1_pre_inst_reach_state             false
% 35.20/5.00  --bmc1_out_unsat_core                   false
% 35.20/5.00  --bmc1_aig_witness_out                  false
% 35.20/5.00  --bmc1_verbose                          false
% 35.20/5.00  --bmc1_dump_clauses_tptp                false
% 35.20/5.00  --bmc1_dump_unsat_core_tptp             false
% 35.20/5.00  --bmc1_dump_file                        -
% 35.20/5.00  --bmc1_ucm_expand_uc_limit              128
% 35.20/5.00  --bmc1_ucm_n_expand_iterations          6
% 35.20/5.00  --bmc1_ucm_extend_mode                  1
% 35.20/5.00  --bmc1_ucm_init_mode                    2
% 35.20/5.00  --bmc1_ucm_cone_mode                    none
% 35.20/5.00  --bmc1_ucm_reduced_relation_type        0
% 35.20/5.00  --bmc1_ucm_relax_model                  4
% 35.20/5.00  --bmc1_ucm_full_tr_after_sat            true
% 35.20/5.00  --bmc1_ucm_expand_neg_assumptions       false
% 35.20/5.00  --bmc1_ucm_layered_model                none
% 35.20/5.00  --bmc1_ucm_max_lemma_size               10
% 35.20/5.00  
% 35.20/5.00  ------ AIG Options
% 35.20/5.00  
% 35.20/5.00  --aig_mode                              false
% 35.20/5.00  
% 35.20/5.00  ------ Instantiation Options
% 35.20/5.00  
% 35.20/5.00  --instantiation_flag                    true
% 35.20/5.00  --inst_sos_flag                         false
% 35.20/5.00  --inst_sos_phase                        true
% 35.20/5.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 35.20/5.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 35.20/5.00  --inst_lit_sel_side                     num_symb
% 35.20/5.00  --inst_solver_per_active                1400
% 35.20/5.00  --inst_solver_calls_frac                1.
% 35.20/5.00  --inst_passive_queue_type               priority_queues
% 35.20/5.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 35.20/5.00  --inst_passive_queues_freq              [25;2]
% 35.20/5.00  --inst_dismatching                      true
% 35.20/5.00  --inst_eager_unprocessed_to_passive     true
% 35.20/5.00  --inst_prop_sim_given                   true
% 35.20/5.00  --inst_prop_sim_new                     false
% 35.20/5.00  --inst_subs_new                         false
% 35.20/5.00  --inst_eq_res_simp                      false
% 35.20/5.00  --inst_subs_given                       false
% 35.20/5.00  --inst_orphan_elimination               true
% 35.20/5.00  --inst_learning_loop_flag               true
% 35.20/5.00  --inst_learning_start                   3000
% 35.20/5.00  --inst_learning_factor                  2
% 35.20/5.00  --inst_start_prop_sim_after_learn       3
% 35.20/5.00  --inst_sel_renew                        solver
% 35.20/5.00  --inst_lit_activity_flag                true
% 35.20/5.00  --inst_restr_to_given                   false
% 35.20/5.00  --inst_activity_threshold               500
% 35.20/5.00  --inst_out_proof                        true
% 35.20/5.00  
% 35.20/5.00  ------ Resolution Options
% 35.20/5.00  
% 35.20/5.00  --resolution_flag                       true
% 35.20/5.00  --res_lit_sel                           adaptive
% 35.20/5.00  --res_lit_sel_side                      none
% 35.20/5.00  --res_ordering                          kbo
% 35.20/5.00  --res_to_prop_solver                    active
% 35.20/5.00  --res_prop_simpl_new                    false
% 35.20/5.00  --res_prop_simpl_given                  true
% 35.20/5.00  --res_passive_queue_type                priority_queues
% 35.20/5.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 35.20/5.00  --res_passive_queues_freq               [15;5]
% 35.20/5.00  --res_forward_subs                      full
% 35.20/5.00  --res_backward_subs                     full
% 35.20/5.00  --res_forward_subs_resolution           true
% 35.20/5.00  --res_backward_subs_resolution          true
% 35.20/5.00  --res_orphan_elimination                true
% 35.20/5.00  --res_time_limit                        2.
% 35.20/5.00  --res_out_proof                         true
% 35.20/5.00  
% 35.20/5.00  ------ Superposition Options
% 35.20/5.00  
% 35.20/5.00  --superposition_flag                    true
% 35.20/5.00  --sup_passive_queue_type                priority_queues
% 35.20/5.00  --sup_passive_queues                    [[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 35.20/5.00  --sup_passive_queues_freq               [1;4]
% 35.20/5.00  --demod_completeness_check              fast
% 35.20/5.00  --demod_use_ground                      true
% 35.20/5.00  --sup_to_prop_solver                    passive
% 35.20/5.00  --sup_prop_simpl_new                    true
% 35.20/5.00  --sup_prop_simpl_given                  true
% 35.20/5.00  --sup_fun_splitting                     false
% 35.20/5.00  --sup_smt_interval                      50000
% 35.20/5.00  
% 35.20/5.00  ------ Superposition Simplification Setup
% 35.20/5.00  
% 35.20/5.00  --sup_indices_passive                   []
% 35.20/5.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 35.20/5.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 35.20/5.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 35.20/5.00  --sup_full_triv                         [TrivRules;PropSubs]
% 35.20/5.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 35.20/5.00  --sup_full_bw                           [BwDemod]
% 35.20/5.00  --sup_immed_triv                        [TrivRules]
% 35.20/5.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 35.20/5.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 35.20/5.00  --sup_immed_bw_main                     []
% 35.20/5.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 35.20/5.00  --sup_input_triv                        [Unflattening;TrivRules]
% 35.20/5.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 35.20/5.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 35.20/5.00  
% 35.20/5.00  ------ Combination Options
% 35.20/5.00  
% 35.20/5.00  --comb_res_mult                         3
% 35.20/5.00  --comb_sup_mult                         2
% 35.20/5.00  --comb_inst_mult                        10
% 35.20/5.00  
% 35.20/5.00  ------ Debug Options
% 35.20/5.00  
% 35.20/5.00  --dbg_backtrace                         false
% 35.20/5.00  --dbg_dump_prop_clauses                 false
% 35.20/5.00  --dbg_dump_prop_clauses_file            -
% 35.20/5.00  --dbg_out_stat                          false
% 35.20/5.00  
% 35.20/5.00  
% 35.20/5.00  
% 35.20/5.00  
% 35.20/5.00  ------ Proving...
% 35.20/5.00  
% 35.20/5.00  
% 35.20/5.00  % SZS status Theorem for theBenchmark.p
% 35.20/5.00  
% 35.20/5.00  % SZS output start CNFRefutation for theBenchmark.p
% 35.20/5.00  
% 35.20/5.00  fof(f12,conjecture,(
% 35.20/5.00    ! [X0,X1,X2] : (v1_relat_1(X2) => (r1_tarski(X0,X1) => r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))))),
% 35.20/5.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 35.20/5.00  
% 35.20/5.00  fof(f13,negated_conjecture,(
% 35.20/5.00    ~! [X0,X1,X2] : (v1_relat_1(X2) => (r1_tarski(X0,X1) => r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))))),
% 35.20/5.00    inference(negated_conjecture,[],[f12])).
% 35.20/5.00  
% 35.20/5.00  fof(f19,plain,(
% 35.20/5.00    ? [X0,X1,X2] : ((~r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) & r1_tarski(X0,X1)) & v1_relat_1(X2))),
% 35.20/5.00    inference(ennf_transformation,[],[f13])).
% 35.20/5.00  
% 35.20/5.00  fof(f20,plain,(
% 35.20/5.00    ? [X0,X1,X2] : (~r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) & r1_tarski(X0,X1) & v1_relat_1(X2))),
% 35.20/5.00    inference(flattening,[],[f19])).
% 35.20/5.00  
% 35.20/5.00  fof(f32,plain,(
% 35.20/5.00    ? [X0,X1,X2] : (~r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) & r1_tarski(X0,X1) & v1_relat_1(X2)) => (~r1_tarski(k9_relat_1(sK4,sK2),k9_relat_1(sK4,sK3)) & r1_tarski(sK2,sK3) & v1_relat_1(sK4))),
% 35.20/5.00    introduced(choice_axiom,[])).
% 35.20/5.00  
% 35.20/5.00  fof(f33,plain,(
% 35.20/5.00    ~r1_tarski(k9_relat_1(sK4,sK2),k9_relat_1(sK4,sK3)) & r1_tarski(sK2,sK3) & v1_relat_1(sK4)),
% 35.20/5.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f20,f32])).
% 35.20/5.00  
% 35.20/5.00  fof(f55,plain,(
% 35.20/5.00    r1_tarski(sK2,sK3)),
% 35.20/5.00    inference(cnf_transformation,[],[f33])).
% 35.20/5.00  
% 35.20/5.00  fof(f1,axiom,(
% 35.20/5.00    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 35.20/5.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 35.20/5.00  
% 35.20/5.00  fof(f34,plain,(
% 35.20/5.00    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 35.20/5.00    inference(cnf_transformation,[],[f1])).
% 35.20/5.00  
% 35.20/5.00  fof(f5,axiom,(
% 35.20/5.00    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 35.20/5.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 35.20/5.00  
% 35.20/5.00  fof(f47,plain,(
% 35.20/5.00    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 35.20/5.00    inference(cnf_transformation,[],[f5])).
% 35.20/5.00  
% 35.20/5.00  fof(f9,axiom,(
% 35.20/5.00    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)),
% 35.20/5.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 35.20/5.00  
% 35.20/5.00  fof(f51,plain,(
% 35.20/5.00    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)) )),
% 35.20/5.00    inference(cnf_transformation,[],[f9])).
% 35.20/5.00  
% 35.20/5.00  fof(f63,plain,(
% 35.20/5.00    ( ! [X0] : (k6_subset_1(X0,k1_xboole_0) = X0) )),
% 35.20/5.00    inference(definition_unfolding,[],[f47,f51])).
% 35.20/5.00  
% 35.20/5.00  fof(f7,axiom,(
% 35.20/5.00    ! [X0,X1,X2] : (r1_tarski(k4_xboole_0(X0,X1),X2) => r1_tarski(X0,k2_xboole_0(X1,X2)))),
% 35.20/5.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 35.20/5.00  
% 35.20/5.00  fof(f16,plain,(
% 35.20/5.00    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X1,X2)) | ~r1_tarski(k4_xboole_0(X0,X1),X2))),
% 35.20/5.00    inference(ennf_transformation,[],[f7])).
% 35.20/5.00  
% 35.20/5.00  fof(f49,plain,(
% 35.20/5.00    ( ! [X2,X0,X1] : (r1_tarski(X0,k2_xboole_0(X1,X2)) | ~r1_tarski(k4_xboole_0(X0,X1),X2)) )),
% 35.20/5.00    inference(cnf_transformation,[],[f16])).
% 35.20/5.00  
% 35.20/5.00  fof(f65,plain,(
% 35.20/5.00    ( ! [X2,X0,X1] : (r1_tarski(X0,k2_xboole_0(X1,X2)) | ~r1_tarski(k6_subset_1(X0,X1),X2)) )),
% 35.20/5.00    inference(definition_unfolding,[],[f49,f51])).
% 35.20/5.00  
% 35.20/5.00  fof(f6,axiom,(
% 35.20/5.00    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X1,X2)) => r1_tarski(k4_xboole_0(X0,X1),X2))),
% 35.20/5.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 35.20/5.00  
% 35.20/5.00  fof(f15,plain,(
% 35.20/5.00    ! [X0,X1,X2] : (r1_tarski(k4_xboole_0(X0,X1),X2) | ~r1_tarski(X0,k2_xboole_0(X1,X2)))),
% 35.20/5.00    inference(ennf_transformation,[],[f6])).
% 35.20/5.00  
% 35.20/5.00  fof(f48,plain,(
% 35.20/5.00    ( ! [X2,X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X2) | ~r1_tarski(X0,k2_xboole_0(X1,X2))) )),
% 35.20/5.00    inference(cnf_transformation,[],[f15])).
% 35.20/5.00  
% 35.20/5.00  fof(f64,plain,(
% 35.20/5.00    ( ! [X2,X0,X1] : (r1_tarski(k6_subset_1(X0,X1),X2) | ~r1_tarski(X0,k2_xboole_0(X1,X2))) )),
% 35.20/5.00    inference(definition_unfolding,[],[f48,f51])).
% 35.20/5.00  
% 35.20/5.00  fof(f8,axiom,(
% 35.20/5.00    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 35.20/5.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 35.20/5.00  
% 35.20/5.00  fof(f50,plain,(
% 35.20/5.00    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 35.20/5.00    inference(cnf_transformation,[],[f8])).
% 35.20/5.00  
% 35.20/5.00  fof(f4,axiom,(
% 35.20/5.00    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 35.20/5.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 35.20/5.00  
% 35.20/5.00  fof(f30,plain,(
% 35.20/5.00    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 35.20/5.00    inference(nnf_transformation,[],[f4])).
% 35.20/5.00  
% 35.20/5.00  fof(f31,plain,(
% 35.20/5.00    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 35.20/5.00    inference(flattening,[],[f30])).
% 35.20/5.00  
% 35.20/5.00  fof(f46,plain,(
% 35.20/5.00    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 35.20/5.00    inference(cnf_transformation,[],[f31])).
% 35.20/5.00  
% 35.20/5.00  fof(f54,plain,(
% 35.20/5.00    v1_relat_1(sK4)),
% 35.20/5.00    inference(cnf_transformation,[],[f33])).
% 35.20/5.00  
% 35.20/5.00  fof(f10,axiom,(
% 35.20/5.00    ! [X0,X1,X2] : (v1_relat_1(X2) => k2_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) = k9_relat_1(X2,k2_xboole_0(X0,X1)))),
% 35.20/5.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 35.20/5.00  
% 35.20/5.00  fof(f17,plain,(
% 35.20/5.00    ! [X0,X1,X2] : (k2_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) = k9_relat_1(X2,k2_xboole_0(X0,X1)) | ~v1_relat_1(X2))),
% 35.20/5.00    inference(ennf_transformation,[],[f10])).
% 35.20/5.00  
% 35.20/5.00  fof(f52,plain,(
% 35.20/5.00    ( ! [X2,X0,X1] : (k2_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) = k9_relat_1(X2,k2_xboole_0(X0,X1)) | ~v1_relat_1(X2)) )),
% 35.20/5.00    inference(cnf_transformation,[],[f17])).
% 35.20/5.00  
% 35.20/5.00  fof(f11,axiom,(
% 35.20/5.00    ! [X0,X1,X2] : (v1_relat_1(X2) => r1_tarski(k6_subset_1(k9_relat_1(X2,X0),k9_relat_1(X2,X1)),k9_relat_1(X2,k6_subset_1(X0,X1))))),
% 35.20/5.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 35.20/5.00  
% 35.20/5.00  fof(f18,plain,(
% 35.20/5.00    ! [X0,X1,X2] : (r1_tarski(k6_subset_1(k9_relat_1(X2,X0),k9_relat_1(X2,X1)),k9_relat_1(X2,k6_subset_1(X0,X1))) | ~v1_relat_1(X2))),
% 35.20/5.00    inference(ennf_transformation,[],[f11])).
% 35.20/5.00  
% 35.20/5.00  fof(f53,plain,(
% 35.20/5.00    ( ! [X2,X0,X1] : (r1_tarski(k6_subset_1(k9_relat_1(X2,X0),k9_relat_1(X2,X1)),k9_relat_1(X2,k6_subset_1(X0,X1))) | ~v1_relat_1(X2)) )),
% 35.20/5.00    inference(cnf_transformation,[],[f18])).
% 35.20/5.00  
% 35.20/5.00  fof(f44,plain,(
% 35.20/5.00    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 35.20/5.00    inference(cnf_transformation,[],[f31])).
% 35.20/5.00  
% 35.20/5.00  fof(f70,plain,(
% 35.20/5.00    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 35.20/5.00    inference(equality_resolution,[],[f44])).
% 35.20/5.00  
% 35.20/5.00  fof(f56,plain,(
% 35.20/5.00    ~r1_tarski(k9_relat_1(sK4,sK2),k9_relat_1(sK4,sK3))),
% 35.20/5.00    inference(cnf_transformation,[],[f33])).
% 35.20/5.00  
% 35.20/5.00  cnf(c_20,negated_conjecture,
% 35.20/5.00      ( r1_tarski(sK2,sK3) ),
% 35.20/5.00      inference(cnf_transformation,[],[f55]) ).
% 35.20/5.00  
% 35.20/5.00  cnf(c_774,plain,
% 35.20/5.00      ( r1_tarski(sK2,sK3) = iProver_top ),
% 35.20/5.00      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 35.20/5.00  
% 35.20/5.00  cnf(c_0,plain,
% 35.20/5.00      ( k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
% 35.20/5.00      inference(cnf_transformation,[],[f34]) ).
% 35.20/5.00  
% 35.20/5.00  cnf(c_13,plain,
% 35.20/5.00      ( k6_subset_1(X0,k1_xboole_0) = X0 ),
% 35.20/5.00      inference(cnf_transformation,[],[f63]) ).
% 35.20/5.00  
% 35.20/5.00  cnf(c_15,plain,
% 35.20/5.00      ( r1_tarski(X0,k2_xboole_0(X1,X2))
% 35.20/5.00      | ~ r1_tarski(k6_subset_1(X0,X1),X2) ),
% 35.20/5.00      inference(cnf_transformation,[],[f65]) ).
% 35.20/5.00  
% 35.20/5.00  cnf(c_779,plain,
% 35.20/5.00      ( r1_tarski(X0,k2_xboole_0(X1,X2)) = iProver_top
% 35.20/5.00      | r1_tarski(k6_subset_1(X0,X1),X2) != iProver_top ),
% 35.20/5.00      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 35.20/5.00  
% 35.20/5.00  cnf(c_1821,plain,
% 35.20/5.00      ( r1_tarski(X0,X1) != iProver_top
% 35.20/5.00      | r1_tarski(X0,k2_xboole_0(k1_xboole_0,X1)) = iProver_top ),
% 35.20/5.00      inference(superposition,[status(thm)],[c_13,c_779]) ).
% 35.20/5.00  
% 35.20/5.00  cnf(c_2015,plain,
% 35.20/5.00      ( r1_tarski(X0,X1) != iProver_top
% 35.20/5.00      | r1_tarski(X0,k2_xboole_0(X1,k1_xboole_0)) = iProver_top ),
% 35.20/5.00      inference(superposition,[status(thm)],[c_0,c_1821]) ).
% 35.20/5.00  
% 35.20/5.00  cnf(c_14,plain,
% 35.20/5.00      ( ~ r1_tarski(X0,k2_xboole_0(X1,X2))
% 35.20/5.00      | r1_tarski(k6_subset_1(X0,X1),X2) ),
% 35.20/5.00      inference(cnf_transformation,[],[f64]) ).
% 35.20/5.00  
% 35.20/5.00  cnf(c_780,plain,
% 35.20/5.00      ( r1_tarski(X0,k2_xboole_0(X1,X2)) != iProver_top
% 35.20/5.00      | r1_tarski(k6_subset_1(X0,X1),X2) = iProver_top ),
% 35.20/5.00      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 35.20/5.00  
% 35.20/5.00  cnf(c_2240,plain,
% 35.20/5.00      ( r1_tarski(X0,X1) != iProver_top
% 35.20/5.00      | r1_tarski(k6_subset_1(X0,X1),k1_xboole_0) = iProver_top ),
% 35.20/5.00      inference(superposition,[status(thm)],[c_2015,c_780]) ).
% 35.20/5.00  
% 35.20/5.00  cnf(c_16,plain,
% 35.20/5.00      ( r1_tarski(X0,k2_xboole_0(X0,X1)) ),
% 35.20/5.00      inference(cnf_transformation,[],[f50]) ).
% 35.20/5.00  
% 35.20/5.00  cnf(c_778,plain,
% 35.20/5.00      ( r1_tarski(X0,k2_xboole_0(X0,X1)) = iProver_top ),
% 35.20/5.00      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 35.20/5.00  
% 35.20/5.00  cnf(c_2237,plain,
% 35.20/5.00      ( r1_tarski(k6_subset_1(X0,X0),X1) = iProver_top ),
% 35.20/5.00      inference(superposition,[status(thm)],[c_778,c_780]) ).
% 35.20/5.00  
% 35.20/5.00  cnf(c_3453,plain,
% 35.20/5.00      ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
% 35.20/5.00      inference(superposition,[status(thm)],[c_13,c_2237]) ).
% 35.20/5.00  
% 35.20/5.00  cnf(c_10,plain,
% 35.20/5.00      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X1 = X0 ),
% 35.20/5.00      inference(cnf_transformation,[],[f46]) ).
% 35.20/5.00  
% 35.20/5.00  cnf(c_782,plain,
% 35.20/5.00      ( X0 = X1
% 35.20/5.00      | r1_tarski(X1,X0) != iProver_top
% 35.20/5.00      | r1_tarski(X0,X1) != iProver_top ),
% 35.20/5.00      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 35.20/5.00  
% 35.20/5.00  cnf(c_3477,plain,
% 35.20/5.00      ( k1_xboole_0 = X0 | r1_tarski(X0,k1_xboole_0) != iProver_top ),
% 35.20/5.00      inference(superposition,[status(thm)],[c_3453,c_782]) ).
% 35.20/5.00  
% 35.20/5.00  cnf(c_9929,plain,
% 35.20/5.00      ( k6_subset_1(X0,X1) = k1_xboole_0
% 35.20/5.00      | r1_tarski(X0,X1) != iProver_top ),
% 35.20/5.00      inference(superposition,[status(thm)],[c_2240,c_3477]) ).
% 35.20/5.00  
% 35.20/5.00  cnf(c_125882,plain,
% 35.20/5.00      ( k6_subset_1(sK2,sK3) = k1_xboole_0 ),
% 35.20/5.00      inference(superposition,[status(thm)],[c_774,c_9929]) ).
% 35.20/5.00  
% 35.20/5.00  cnf(c_21,negated_conjecture,
% 35.20/5.00      ( v1_relat_1(sK4) ),
% 35.20/5.00      inference(cnf_transformation,[],[f54]) ).
% 35.20/5.00  
% 35.20/5.00  cnf(c_773,plain,
% 35.20/5.00      ( v1_relat_1(sK4) = iProver_top ),
% 35.20/5.00      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 35.20/5.00  
% 35.20/5.00  cnf(c_17,plain,
% 35.20/5.00      ( ~ v1_relat_1(X0)
% 35.20/5.00      | k2_xboole_0(k9_relat_1(X0,X1),k9_relat_1(X0,X2)) = k9_relat_1(X0,k2_xboole_0(X1,X2)) ),
% 35.20/5.00      inference(cnf_transformation,[],[f52]) ).
% 35.20/5.00  
% 35.20/5.00  cnf(c_777,plain,
% 35.20/5.00      ( k2_xboole_0(k9_relat_1(X0,X1),k9_relat_1(X0,X2)) = k9_relat_1(X0,k2_xboole_0(X1,X2))
% 35.20/5.00      | v1_relat_1(X0) != iProver_top ),
% 35.20/5.00      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 35.20/5.00  
% 35.20/5.00  cnf(c_1850,plain,
% 35.20/5.00      ( k2_xboole_0(k9_relat_1(sK4,X0),k9_relat_1(sK4,X1)) = k9_relat_1(sK4,k2_xboole_0(X0,X1)) ),
% 35.20/5.00      inference(superposition,[status(thm)],[c_773,c_777]) ).
% 35.20/5.00  
% 35.20/5.00  cnf(c_18,plain,
% 35.20/5.00      ( r1_tarski(k6_subset_1(k9_relat_1(X0,X1),k9_relat_1(X0,X2)),k9_relat_1(X0,k6_subset_1(X1,X2)))
% 35.20/5.00      | ~ v1_relat_1(X0) ),
% 35.20/5.00      inference(cnf_transformation,[],[f53]) ).
% 35.20/5.00  
% 35.20/5.00  cnf(c_776,plain,
% 35.20/5.00      ( r1_tarski(k6_subset_1(k9_relat_1(X0,X1),k9_relat_1(X0,X2)),k9_relat_1(X0,k6_subset_1(X1,X2))) = iProver_top
% 35.20/5.00      | v1_relat_1(X0) != iProver_top ),
% 35.20/5.00      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 35.20/5.00  
% 35.20/5.00  cnf(c_1819,plain,
% 35.20/5.00      ( r1_tarski(k9_relat_1(X0,X1),k2_xboole_0(k9_relat_1(X0,X2),k9_relat_1(X0,k6_subset_1(X1,X2)))) = iProver_top
% 35.20/5.00      | v1_relat_1(X0) != iProver_top ),
% 35.20/5.00      inference(superposition,[status(thm)],[c_776,c_779]) ).
% 35.20/5.00  
% 35.20/5.00  cnf(c_7321,plain,
% 35.20/5.00      ( r1_tarski(k9_relat_1(sK4,X0),k9_relat_1(sK4,k2_xboole_0(X1,k6_subset_1(X0,X1)))) = iProver_top
% 35.20/5.00      | v1_relat_1(sK4) != iProver_top ),
% 35.20/5.00      inference(superposition,[status(thm)],[c_1850,c_1819]) ).
% 35.20/5.00  
% 35.20/5.00  cnf(c_22,plain,
% 35.20/5.00      ( v1_relat_1(sK4) = iProver_top ),
% 35.20/5.00      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 35.20/5.00  
% 35.20/5.00  cnf(c_66939,plain,
% 35.20/5.00      ( r1_tarski(k9_relat_1(sK4,X0),k9_relat_1(sK4,k2_xboole_0(X1,k6_subset_1(X0,X1)))) = iProver_top ),
% 35.20/5.00      inference(global_propositional_subsumption,
% 35.20/5.00                [status(thm)],
% 35.20/5.00                [c_7321,c_22]) ).
% 35.20/5.00  
% 35.20/5.00  cnf(c_129336,plain,
% 35.20/5.00      ( r1_tarski(k9_relat_1(sK4,sK2),k9_relat_1(sK4,k2_xboole_0(sK3,k1_xboole_0))) = iProver_top ),
% 35.20/5.00      inference(superposition,[status(thm)],[c_125882,c_66939]) ).
% 35.20/5.00  
% 35.20/5.00  cnf(c_12,plain,
% 35.20/5.00      ( r1_tarski(X0,X0) ),
% 35.20/5.00      inference(cnf_transformation,[],[f70]) ).
% 35.20/5.00  
% 35.20/5.00  cnf(c_781,plain,
% 35.20/5.00      ( r1_tarski(X0,X0) = iProver_top ),
% 35.20/5.00      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 35.20/5.00  
% 35.20/5.00  cnf(c_2236,plain,
% 35.20/5.00      ( r1_tarski(k6_subset_1(k2_xboole_0(X0,X1),X0),X1) = iProver_top ),
% 35.20/5.00      inference(superposition,[status(thm)],[c_781,c_780]) ).
% 35.20/5.00  
% 35.20/5.00  cnf(c_4016,plain,
% 35.20/5.00      ( r1_tarski(k2_xboole_0(k1_xboole_0,X0),X0) = iProver_top ),
% 35.20/5.00      inference(superposition,[status(thm)],[c_13,c_2236]) ).
% 35.20/5.00  
% 35.20/5.00  cnf(c_4269,plain,
% 35.20/5.00      ( r1_tarski(k2_xboole_0(X0,k1_xboole_0),X0) = iProver_top ),
% 35.20/5.00      inference(superposition,[status(thm)],[c_0,c_4016]) ).
% 35.20/5.00  
% 35.20/5.00  cnf(c_2496,plain,
% 35.20/5.00      ( k2_xboole_0(X0,X1) = X0
% 35.20/5.00      | r1_tarski(k2_xboole_0(X0,X1),X0) != iProver_top ),
% 35.20/5.00      inference(superposition,[status(thm)],[c_778,c_782]) ).
% 35.20/5.00  
% 35.20/5.00  cnf(c_10905,plain,
% 35.20/5.00      ( k2_xboole_0(X0,k1_xboole_0) = X0 ),
% 35.20/5.00      inference(superposition,[status(thm)],[c_4269,c_2496]) ).
% 35.20/5.00  
% 35.20/5.00  cnf(c_129593,plain,
% 35.20/5.00      ( r1_tarski(k9_relat_1(sK4,sK2),k9_relat_1(sK4,sK3)) = iProver_top ),
% 35.20/5.00      inference(demodulation,[status(thm)],[c_129336,c_10905]) ).
% 35.20/5.00  
% 35.20/5.00  cnf(c_19,negated_conjecture,
% 35.20/5.00      ( ~ r1_tarski(k9_relat_1(sK4,sK2),k9_relat_1(sK4,sK3)) ),
% 35.20/5.00      inference(cnf_transformation,[],[f56]) ).
% 35.20/5.00  
% 35.20/5.00  cnf(c_24,plain,
% 35.20/5.00      ( r1_tarski(k9_relat_1(sK4,sK2),k9_relat_1(sK4,sK3)) != iProver_top ),
% 35.20/5.00      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 35.20/5.00  
% 35.20/5.00  cnf(contradiction,plain,
% 35.20/5.00      ( $false ),
% 35.20/5.00      inference(minisat,[status(thm)],[c_129593,c_24]) ).
% 35.20/5.00  
% 35.20/5.00  
% 35.20/5.00  % SZS output end CNFRefutation for theBenchmark.p
% 35.20/5.00  
% 35.20/5.00  ------                               Statistics
% 35.20/5.00  
% 35.20/5.00  ------ Selected
% 35.20/5.00  
% 35.20/5.00  total_time:                             4.147
% 35.20/5.00  
%------------------------------------------------------------------------------
