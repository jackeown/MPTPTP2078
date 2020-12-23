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
% DateTime   : Thu Dec  3 11:51:42 EST 2020

% Result     : Theorem 7.72s
% Output     : CNFRefutation 7.72s
% Verified   : 
% Statistics : Number of formulae       :   76 ( 271 expanded)
%              Number of clauses        :   45 ( 108 expanded)
%              Number of leaves         :   10 (  51 expanded)
%              Depth                    :   17
%              Number of atoms          :  127 ( 584 expanded)
%              Number of equality atoms :   64 ( 159 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal clause size      :    6 (   1 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f9,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k7_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f49,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f14,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(X0,k1_relat_1(X1))
       => r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => ( r1_tarski(X0,k1_relat_1(X1))
         => r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) ) ) ),
    inference(negated_conjecture,[],[f14])).

fof(f27,plain,(
    ? [X0,X1] :
      ( ~ r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))
      & r1_tarski(X0,k1_relat_1(X1))
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f28,plain,(
    ? [X0,X1] :
      ( ~ r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))
      & r1_tarski(X0,k1_relat_1(X1))
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f27])).

fof(f35,plain,
    ( ? [X0,X1] :
        ( ~ r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))
        & r1_tarski(X0,k1_relat_1(X1))
        & v1_relat_1(X1) )
   => ( ~ r1_tarski(sK1,k10_relat_1(sK2,k9_relat_1(sK2,sK1)))
      & r1_tarski(sK1,k1_relat_1(sK2))
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,
    ( ~ r1_tarski(sK1,k10_relat_1(sK2,k9_relat_1(sK2,sK1)))
    & r1_tarski(sK1,k1_relat_1(sK2))
    & v1_relat_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f28,f35])).

fof(f55,plain,(
    r1_tarski(sK1,k1_relat_1(sK2)) ),
    inference(cnf_transformation,[],[f36])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f47,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f54,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f36])).

fof(f12,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0] :
      ( k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f52,plain,(
    ! [X0] :
      ( k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => k3_xboole_0(X0,k10_relat_1(X2,X1)) = k10_relat_1(k7_relat_1(X2,X0),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,k10_relat_1(X2,X1)) = k10_relat_1(k7_relat_1(X2,X0),X1)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X0,k10_relat_1(X2,X1)) = k10_relat_1(k7_relat_1(X2,X0),X1)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] :
      ( r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f51,plain,(
    ! [X0,X1] :
      ( r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f50,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f6,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f56,plain,(
    ~ r1_tarski(sK1,k10_relat_1(sK2,k9_relat_1(sK2,sK1))) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_12,plain,
    ( ~ v1_relat_1(X0)
    | v1_relat_1(k7_relat_1(X0,X1)) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_663,plain,
    ( v1_relat_1(X0) != iProver_top
    | v1_relat_1(k7_relat_1(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_18,negated_conjecture,
    ( r1_tarski(sK1,k1_relat_1(sK2)) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_657,plain,
    ( r1_tarski(sK1,k1_relat_1(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_10,plain,
    ( ~ r1_tarski(X0,X1)
    | k3_xboole_0(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f47])).

cnf(c_665,plain,
    ( k3_xboole_0(X0,X1) = X0
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_1254,plain,
    ( k3_xboole_0(sK1,k1_relat_1(sK2)) = sK1 ),
    inference(superposition,[status(thm)],[c_657,c_665])).

cnf(c_19,negated_conjecture,
    ( v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_656,plain,
    ( v1_relat_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_15,plain,
    ( ~ v1_relat_1(X0)
    | k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_660,plain,
    ( k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0)
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_1337,plain,
    ( k10_relat_1(sK2,k2_relat_1(sK2)) = k1_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_656,c_660])).

cnf(c_16,plain,
    ( ~ v1_relat_1(X0)
    | k10_relat_1(k7_relat_1(X0,X1),X2) = k3_xboole_0(X1,k10_relat_1(X0,X2)) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_659,plain,
    ( k10_relat_1(k7_relat_1(X0,X1),X2) = k3_xboole_0(X1,k10_relat_1(X0,X2))
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_1246,plain,
    ( k10_relat_1(k7_relat_1(sK2,X0),X1) = k3_xboole_0(X0,k10_relat_1(sK2,X1)) ),
    inference(superposition,[status(thm)],[c_656,c_659])).

cnf(c_14,plain,
    ( r1_tarski(k10_relat_1(X0,X1),k1_relat_1(X0))
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_661,plain,
    ( r1_tarski(k10_relat_1(X0,X1),k1_relat_1(X0)) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_1819,plain,
    ( r1_tarski(k3_xboole_0(X0,k10_relat_1(sK2,X1)),k1_relat_1(k7_relat_1(sK2,X0))) = iProver_top
    | v1_relat_1(k7_relat_1(sK2,X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1246,c_661])).

cnf(c_2412,plain,
    ( r1_tarski(k3_xboole_0(X0,k1_relat_1(sK2)),k1_relat_1(k7_relat_1(sK2,X0))) = iProver_top
    | v1_relat_1(k7_relat_1(sK2,X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1337,c_1819])).

cnf(c_2489,plain,
    ( r1_tarski(sK1,k1_relat_1(k7_relat_1(sK2,sK1))) = iProver_top
    | v1_relat_1(k7_relat_1(sK2,sK1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1254,c_2412])).

cnf(c_2510,plain,
    ( k3_xboole_0(sK1,k1_relat_1(k7_relat_1(sK2,sK1))) = sK1
    | v1_relat_1(k7_relat_1(sK2,sK1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2489,c_665])).

cnf(c_2606,plain,
    ( k3_xboole_0(sK1,k1_relat_1(k7_relat_1(sK2,sK1))) = sK1
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_663,c_2510])).

cnf(c_20,plain,
    ( v1_relat_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_16551,plain,
    ( k3_xboole_0(sK1,k1_relat_1(k7_relat_1(sK2,sK1))) = sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2606,c_20])).

cnf(c_1336,plain,
    ( k10_relat_1(k7_relat_1(X0,X1),k2_relat_1(k7_relat_1(X0,X1))) = k1_relat_1(k7_relat_1(X0,X1))
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_663,c_660])).

cnf(c_4466,plain,
    ( k10_relat_1(k7_relat_1(sK2,X0),k2_relat_1(k7_relat_1(sK2,X0))) = k1_relat_1(k7_relat_1(sK2,X0)) ),
    inference(superposition,[status(thm)],[c_656,c_1336])).

cnf(c_13,plain,
    ( ~ v1_relat_1(X0)
    | k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_662,plain,
    ( k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1)
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_1950,plain,
    ( k2_relat_1(k7_relat_1(sK2,X0)) = k9_relat_1(sK2,X0) ),
    inference(superposition,[status(thm)],[c_656,c_662])).

cnf(c_4467,plain,
    ( k10_relat_1(k7_relat_1(sK2,X0),k9_relat_1(sK2,X0)) = k1_relat_1(k7_relat_1(sK2,X0)) ),
    inference(light_normalisation,[status(thm)],[c_4466,c_1950])).

cnf(c_4809,plain,
    ( k3_xboole_0(X0,k10_relat_1(sK2,k9_relat_1(sK2,X0))) = k1_relat_1(k7_relat_1(sK2,X0)) ),
    inference(superposition,[status(thm)],[c_4467,c_1246])).

cnf(c_9,plain,
    ( r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_666,plain,
    ( r1_tarski(k3_xboole_0(X0,X1),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_1253,plain,
    ( k3_xboole_0(k3_xboole_0(X0,X1),X0) = k3_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_666,c_665])).

cnf(c_0,plain,
    ( k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_3625,plain,
    ( k3_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_1253,c_0])).

cnf(c_4938,plain,
    ( k3_xboole_0(X0,k10_relat_1(sK2,k9_relat_1(sK2,X0))) = k3_xboole_0(X0,k1_relat_1(k7_relat_1(sK2,X0))) ),
    inference(superposition,[status(thm)],[c_4809,c_3625])).

cnf(c_4957,plain,
    ( k3_xboole_0(X0,k1_relat_1(k7_relat_1(sK2,X0))) = k1_relat_1(k7_relat_1(sK2,X0)) ),
    inference(demodulation,[status(thm)],[c_4938,c_4809])).

cnf(c_16586,plain,
    ( k1_relat_1(k7_relat_1(sK2,sK1)) = sK1 ),
    inference(superposition,[status(thm)],[c_16551,c_4957])).

cnf(c_1031,plain,
    ( r1_tarski(k3_xboole_0(X0,X1),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_0,c_666])).

cnf(c_4943,plain,
    ( r1_tarski(k1_relat_1(k7_relat_1(sK2,X0)),k10_relat_1(sK2,k9_relat_1(sK2,X0))) = iProver_top ),
    inference(superposition,[status(thm)],[c_4809,c_1031])).

cnf(c_24801,plain,
    ( r1_tarski(sK1,k10_relat_1(sK2,k9_relat_1(sK2,sK1))) = iProver_top ),
    inference(superposition,[status(thm)],[c_16586,c_4943])).

cnf(c_17,negated_conjecture,
    ( ~ r1_tarski(sK1,k10_relat_1(sK2,k9_relat_1(sK2,sK1))) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_22,plain,
    ( r1_tarski(sK1,k10_relat_1(sK2,k9_relat_1(sK2,sK1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_24801,c_22])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n021.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 10:23:04 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  % Running in FOF mode
% 7.72/1.49  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.72/1.49  
% 7.72/1.49  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.72/1.49  
% 7.72/1.49  ------  iProver source info
% 7.72/1.49  
% 7.72/1.49  git: date: 2020-06-30 10:37:57 +0100
% 7.72/1.49  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.72/1.49  git: non_committed_changes: false
% 7.72/1.49  git: last_make_outside_of_git: false
% 7.72/1.49  
% 7.72/1.49  ------ 
% 7.72/1.49  
% 7.72/1.49  ------ Input Options
% 7.72/1.49  
% 7.72/1.49  --out_options                           all
% 7.72/1.49  --tptp_safe_out                         true
% 7.72/1.49  --problem_path                          ""
% 7.72/1.49  --include_path                          ""
% 7.72/1.49  --clausifier                            res/vclausify_rel
% 7.72/1.49  --clausifier_options                    ""
% 7.72/1.49  --stdin                                 false
% 7.72/1.49  --stats_out                             all
% 7.72/1.49  
% 7.72/1.49  ------ General Options
% 7.72/1.49  
% 7.72/1.49  --fof                                   false
% 7.72/1.49  --time_out_real                         305.
% 7.72/1.49  --time_out_virtual                      -1.
% 7.72/1.49  --symbol_type_check                     false
% 7.72/1.49  --clausify_out                          false
% 7.72/1.49  --sig_cnt_out                           false
% 7.72/1.49  --trig_cnt_out                          false
% 7.72/1.49  --trig_cnt_out_tolerance                1.
% 7.72/1.49  --trig_cnt_out_sk_spl                   false
% 7.72/1.49  --abstr_cl_out                          false
% 7.72/1.49  
% 7.72/1.49  ------ Global Options
% 7.72/1.49  
% 7.72/1.49  --schedule                              default
% 7.72/1.49  --add_important_lit                     false
% 7.72/1.49  --prop_solver_per_cl                    1000
% 7.72/1.49  --min_unsat_core                        false
% 7.72/1.49  --soft_assumptions                      false
% 7.72/1.49  --soft_lemma_size                       3
% 7.72/1.49  --prop_impl_unit_size                   0
% 7.72/1.49  --prop_impl_unit                        []
% 7.72/1.49  --share_sel_clauses                     true
% 7.72/1.49  --reset_solvers                         false
% 7.72/1.49  --bc_imp_inh                            [conj_cone]
% 7.72/1.49  --conj_cone_tolerance                   3.
% 7.72/1.49  --extra_neg_conj                        none
% 7.72/1.49  --large_theory_mode                     true
% 7.72/1.49  --prolific_symb_bound                   200
% 7.72/1.49  --lt_threshold                          2000
% 7.72/1.49  --clause_weak_htbl                      true
% 7.72/1.49  --gc_record_bc_elim                     false
% 7.72/1.49  
% 7.72/1.49  ------ Preprocessing Options
% 7.72/1.49  
% 7.72/1.49  --preprocessing_flag                    true
% 7.72/1.49  --time_out_prep_mult                    0.1
% 7.72/1.49  --splitting_mode                        input
% 7.72/1.49  --splitting_grd                         true
% 7.72/1.49  --splitting_cvd                         false
% 7.72/1.49  --splitting_cvd_svl                     false
% 7.72/1.49  --splitting_nvd                         32
% 7.72/1.49  --sub_typing                            true
% 7.72/1.49  --prep_gs_sim                           true
% 7.72/1.49  --prep_unflatten                        true
% 7.72/1.49  --prep_res_sim                          true
% 7.72/1.49  --prep_upred                            true
% 7.72/1.49  --prep_sem_filter                       exhaustive
% 7.72/1.49  --prep_sem_filter_out                   false
% 7.72/1.49  --pred_elim                             true
% 7.72/1.49  --res_sim_input                         true
% 7.72/1.49  --eq_ax_congr_red                       true
% 7.72/1.49  --pure_diseq_elim                       true
% 7.72/1.49  --brand_transform                       false
% 7.72/1.49  --non_eq_to_eq                          false
% 7.72/1.49  --prep_def_merge                        true
% 7.72/1.49  --prep_def_merge_prop_impl              false
% 7.72/1.49  --prep_def_merge_mbd                    true
% 7.72/1.49  --prep_def_merge_tr_red                 false
% 7.72/1.49  --prep_def_merge_tr_cl                  false
% 7.72/1.49  --smt_preprocessing                     true
% 7.72/1.49  --smt_ac_axioms                         fast
% 7.72/1.49  --preprocessed_out                      false
% 7.72/1.49  --preprocessed_stats                    false
% 7.72/1.49  
% 7.72/1.49  ------ Abstraction refinement Options
% 7.72/1.49  
% 7.72/1.49  --abstr_ref                             []
% 7.72/1.49  --abstr_ref_prep                        false
% 7.72/1.49  --abstr_ref_until_sat                   false
% 7.72/1.49  --abstr_ref_sig_restrict                funpre
% 7.72/1.49  --abstr_ref_af_restrict_to_split_sk     false
% 7.72/1.49  --abstr_ref_under                       []
% 7.72/1.49  
% 7.72/1.49  ------ SAT Options
% 7.72/1.49  
% 7.72/1.49  --sat_mode                              false
% 7.72/1.49  --sat_fm_restart_options                ""
% 7.72/1.49  --sat_gr_def                            false
% 7.72/1.49  --sat_epr_types                         true
% 7.72/1.49  --sat_non_cyclic_types                  false
% 7.72/1.49  --sat_finite_models                     false
% 7.72/1.49  --sat_fm_lemmas                         false
% 7.72/1.49  --sat_fm_prep                           false
% 7.72/1.49  --sat_fm_uc_incr                        true
% 7.72/1.49  --sat_out_model                         small
% 7.72/1.49  --sat_out_clauses                       false
% 7.72/1.49  
% 7.72/1.49  ------ QBF Options
% 7.72/1.49  
% 7.72/1.49  --qbf_mode                              false
% 7.72/1.49  --qbf_elim_univ                         false
% 7.72/1.49  --qbf_dom_inst                          none
% 7.72/1.49  --qbf_dom_pre_inst                      false
% 7.72/1.49  --qbf_sk_in                             false
% 7.72/1.49  --qbf_pred_elim                         true
% 7.72/1.49  --qbf_split                             512
% 7.72/1.49  
% 7.72/1.49  ------ BMC1 Options
% 7.72/1.49  
% 7.72/1.49  --bmc1_incremental                      false
% 7.72/1.49  --bmc1_axioms                           reachable_all
% 7.72/1.49  --bmc1_min_bound                        0
% 7.72/1.49  --bmc1_max_bound                        -1
% 7.72/1.49  --bmc1_max_bound_default                -1
% 7.72/1.49  --bmc1_symbol_reachability              true
% 7.72/1.49  --bmc1_property_lemmas                  false
% 7.72/1.49  --bmc1_k_induction                      false
% 7.72/1.49  --bmc1_non_equiv_states                 false
% 7.72/1.49  --bmc1_deadlock                         false
% 7.72/1.49  --bmc1_ucm                              false
% 7.72/1.49  --bmc1_add_unsat_core                   none
% 7.72/1.49  --bmc1_unsat_core_children              false
% 7.72/1.49  --bmc1_unsat_core_extrapolate_axioms    false
% 7.72/1.49  --bmc1_out_stat                         full
% 7.72/1.49  --bmc1_ground_init                      false
% 7.72/1.49  --bmc1_pre_inst_next_state              false
% 7.72/1.49  --bmc1_pre_inst_state                   false
% 7.72/1.49  --bmc1_pre_inst_reach_state             false
% 7.72/1.49  --bmc1_out_unsat_core                   false
% 7.72/1.49  --bmc1_aig_witness_out                  false
% 7.72/1.49  --bmc1_verbose                          false
% 7.72/1.49  --bmc1_dump_clauses_tptp                false
% 7.72/1.49  --bmc1_dump_unsat_core_tptp             false
% 7.72/1.49  --bmc1_dump_file                        -
% 7.72/1.49  --bmc1_ucm_expand_uc_limit              128
% 7.72/1.49  --bmc1_ucm_n_expand_iterations          6
% 7.72/1.49  --bmc1_ucm_extend_mode                  1
% 7.72/1.49  --bmc1_ucm_init_mode                    2
% 7.72/1.49  --bmc1_ucm_cone_mode                    none
% 7.72/1.49  --bmc1_ucm_reduced_relation_type        0
% 7.72/1.49  --bmc1_ucm_relax_model                  4
% 7.72/1.49  --bmc1_ucm_full_tr_after_sat            true
% 7.72/1.49  --bmc1_ucm_expand_neg_assumptions       false
% 7.72/1.49  --bmc1_ucm_layered_model                none
% 7.72/1.49  --bmc1_ucm_max_lemma_size               10
% 7.72/1.49  
% 7.72/1.49  ------ AIG Options
% 7.72/1.49  
% 7.72/1.49  --aig_mode                              false
% 7.72/1.49  
% 7.72/1.49  ------ Instantiation Options
% 7.72/1.49  
% 7.72/1.49  --instantiation_flag                    true
% 7.72/1.49  --inst_sos_flag                         true
% 7.72/1.49  --inst_sos_phase                        true
% 7.72/1.49  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.72/1.49  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.72/1.49  --inst_lit_sel_side                     num_symb
% 7.72/1.49  --inst_solver_per_active                1400
% 7.72/1.49  --inst_solver_calls_frac                1.
% 7.72/1.49  --inst_passive_queue_type               priority_queues
% 7.72/1.49  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.72/1.49  --inst_passive_queues_freq              [25;2]
% 7.72/1.49  --inst_dismatching                      true
% 7.72/1.49  --inst_eager_unprocessed_to_passive     true
% 7.72/1.49  --inst_prop_sim_given                   true
% 7.72/1.49  --inst_prop_sim_new                     false
% 7.72/1.49  --inst_subs_new                         false
% 7.72/1.49  --inst_eq_res_simp                      false
% 7.72/1.49  --inst_subs_given                       false
% 7.72/1.49  --inst_orphan_elimination               true
% 7.72/1.49  --inst_learning_loop_flag               true
% 7.72/1.49  --inst_learning_start                   3000
% 7.72/1.49  --inst_learning_factor                  2
% 7.72/1.49  --inst_start_prop_sim_after_learn       3
% 7.72/1.49  --inst_sel_renew                        solver
% 7.72/1.49  --inst_lit_activity_flag                true
% 7.72/1.49  --inst_restr_to_given                   false
% 7.72/1.49  --inst_activity_threshold               500
% 7.72/1.49  --inst_out_proof                        true
% 7.72/1.49  
% 7.72/1.49  ------ Resolution Options
% 7.72/1.49  
% 7.72/1.49  --resolution_flag                       true
% 7.72/1.49  --res_lit_sel                           adaptive
% 7.72/1.49  --res_lit_sel_side                      none
% 7.72/1.49  --res_ordering                          kbo
% 7.72/1.49  --res_to_prop_solver                    active
% 7.72/1.49  --res_prop_simpl_new                    false
% 7.72/1.49  --res_prop_simpl_given                  true
% 7.72/1.49  --res_passive_queue_type                priority_queues
% 7.72/1.49  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.72/1.49  --res_passive_queues_freq               [15;5]
% 7.72/1.49  --res_forward_subs                      full
% 7.72/1.49  --res_backward_subs                     full
% 7.72/1.49  --res_forward_subs_resolution           true
% 7.72/1.49  --res_backward_subs_resolution          true
% 7.72/1.49  --res_orphan_elimination                true
% 7.72/1.49  --res_time_limit                        2.
% 7.72/1.49  --res_out_proof                         true
% 7.72/1.49  
% 7.72/1.49  ------ Superposition Options
% 7.72/1.49  
% 7.72/1.49  --superposition_flag                    true
% 7.72/1.49  --sup_passive_queue_type                priority_queues
% 7.72/1.49  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.72/1.49  --sup_passive_queues_freq               [8;1;4]
% 7.72/1.49  --demod_completeness_check              fast
% 7.72/1.49  --demod_use_ground                      true
% 7.72/1.49  --sup_to_prop_solver                    passive
% 7.72/1.49  --sup_prop_simpl_new                    true
% 7.72/1.49  --sup_prop_simpl_given                  true
% 7.72/1.49  --sup_fun_splitting                     true
% 7.72/1.49  --sup_smt_interval                      50000
% 7.72/1.49  
% 7.72/1.49  ------ Superposition Simplification Setup
% 7.72/1.49  
% 7.72/1.49  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 7.72/1.49  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 7.72/1.49  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 7.72/1.49  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 7.72/1.49  --sup_full_triv                         [TrivRules;PropSubs]
% 7.72/1.49  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 7.72/1.49  --sup_full_bw                           [BwDemod;BwSubsumption]
% 7.72/1.49  --sup_immed_triv                        [TrivRules]
% 7.72/1.49  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.72/1.49  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.72/1.49  --sup_immed_bw_main                     []
% 7.72/1.49  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 7.72/1.49  --sup_input_triv                        [Unflattening;TrivRules]
% 7.72/1.49  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.72/1.49  --sup_input_bw                          []
% 7.72/1.49  
% 7.72/1.49  ------ Combination Options
% 7.72/1.49  
% 7.72/1.49  --comb_res_mult                         3
% 7.72/1.49  --comb_sup_mult                         2
% 7.72/1.49  --comb_inst_mult                        10
% 7.72/1.49  
% 7.72/1.49  ------ Debug Options
% 7.72/1.49  
% 7.72/1.49  --dbg_backtrace                         false
% 7.72/1.49  --dbg_dump_prop_clauses                 false
% 7.72/1.49  --dbg_dump_prop_clauses_file            -
% 7.72/1.49  --dbg_out_stat                          false
% 7.72/1.49  ------ Parsing...
% 7.72/1.49  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.72/1.49  
% 7.72/1.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e  sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 7.72/1.49  
% 7.72/1.49  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.72/1.49  
% 7.72/1.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.72/1.49  ------ Proving...
% 7.72/1.49  ------ Problem Properties 
% 7.72/1.49  
% 7.72/1.49  
% 7.72/1.49  clauses                                 19
% 7.72/1.49  conjectures                             3
% 7.72/1.49  EPR                                     4
% 7.72/1.49  Horn                                    18
% 7.72/1.49  unary                                   6
% 7.72/1.49  binary                                  10
% 7.72/1.49  lits                                    35
% 7.72/1.49  lits eq                                 7
% 7.72/1.49  fd_pure                                 0
% 7.72/1.49  fd_pseudo                               0
% 7.72/1.49  fd_cond                                 0
% 7.72/1.49  fd_pseudo_cond                          1
% 7.72/1.49  AC symbols                              0
% 7.72/1.49  
% 7.72/1.49  ------ Schedule dynamic 5 is on 
% 7.72/1.49  
% 7.72/1.49  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 7.72/1.49  
% 7.72/1.49  
% 7.72/1.49  ------ 
% 7.72/1.49  Current options:
% 7.72/1.49  ------ 
% 7.72/1.49  
% 7.72/1.49  ------ Input Options
% 7.72/1.49  
% 7.72/1.49  --out_options                           all
% 7.72/1.49  --tptp_safe_out                         true
% 7.72/1.49  --problem_path                          ""
% 7.72/1.49  --include_path                          ""
% 7.72/1.49  --clausifier                            res/vclausify_rel
% 7.72/1.49  --clausifier_options                    ""
% 7.72/1.49  --stdin                                 false
% 7.72/1.49  --stats_out                             all
% 7.72/1.49  
% 7.72/1.49  ------ General Options
% 7.72/1.49  
% 7.72/1.49  --fof                                   false
% 7.72/1.49  --time_out_real                         305.
% 7.72/1.49  --time_out_virtual                      -1.
% 7.72/1.49  --symbol_type_check                     false
% 7.72/1.49  --clausify_out                          false
% 7.72/1.49  --sig_cnt_out                           false
% 7.72/1.49  --trig_cnt_out                          false
% 7.72/1.49  --trig_cnt_out_tolerance                1.
% 7.72/1.49  --trig_cnt_out_sk_spl                   false
% 7.72/1.49  --abstr_cl_out                          false
% 7.72/1.49  
% 7.72/1.49  ------ Global Options
% 7.72/1.49  
% 7.72/1.49  --schedule                              default
% 7.72/1.49  --add_important_lit                     false
% 7.72/1.49  --prop_solver_per_cl                    1000
% 7.72/1.49  --min_unsat_core                        false
% 7.72/1.49  --soft_assumptions                      false
% 7.72/1.49  --soft_lemma_size                       3
% 7.72/1.49  --prop_impl_unit_size                   0
% 7.72/1.49  --prop_impl_unit                        []
% 7.72/1.49  --share_sel_clauses                     true
% 7.72/1.49  --reset_solvers                         false
% 7.72/1.49  --bc_imp_inh                            [conj_cone]
% 7.72/1.49  --conj_cone_tolerance                   3.
% 7.72/1.49  --extra_neg_conj                        none
% 7.72/1.49  --large_theory_mode                     true
% 7.72/1.49  --prolific_symb_bound                   200
% 7.72/1.49  --lt_threshold                          2000
% 7.72/1.49  --clause_weak_htbl                      true
% 7.72/1.49  --gc_record_bc_elim                     false
% 7.72/1.49  
% 7.72/1.49  ------ Preprocessing Options
% 7.72/1.49  
% 7.72/1.49  --preprocessing_flag                    true
% 7.72/1.49  --time_out_prep_mult                    0.1
% 7.72/1.49  --splitting_mode                        input
% 7.72/1.49  --splitting_grd                         true
% 7.72/1.49  --splitting_cvd                         false
% 7.72/1.49  --splitting_cvd_svl                     false
% 7.72/1.49  --splitting_nvd                         32
% 7.72/1.49  --sub_typing                            true
% 7.72/1.49  --prep_gs_sim                           true
% 7.72/1.49  --prep_unflatten                        true
% 7.72/1.49  --prep_res_sim                          true
% 7.72/1.49  --prep_upred                            true
% 7.72/1.49  --prep_sem_filter                       exhaustive
% 7.72/1.49  --prep_sem_filter_out                   false
% 7.72/1.49  --pred_elim                             true
% 7.72/1.49  --res_sim_input                         true
% 7.72/1.49  --eq_ax_congr_red                       true
% 7.72/1.49  --pure_diseq_elim                       true
% 7.72/1.49  --brand_transform                       false
% 7.72/1.49  --non_eq_to_eq                          false
% 7.72/1.49  --prep_def_merge                        true
% 7.72/1.49  --prep_def_merge_prop_impl              false
% 7.72/1.49  --prep_def_merge_mbd                    true
% 7.72/1.49  --prep_def_merge_tr_red                 false
% 7.72/1.49  --prep_def_merge_tr_cl                  false
% 7.72/1.49  --smt_preprocessing                     true
% 7.72/1.49  --smt_ac_axioms                         fast
% 7.72/1.49  --preprocessed_out                      false
% 7.72/1.49  --preprocessed_stats                    false
% 7.72/1.49  
% 7.72/1.49  ------ Abstraction refinement Options
% 7.72/1.49  
% 7.72/1.49  --abstr_ref                             []
% 7.72/1.49  --abstr_ref_prep                        false
% 7.72/1.49  --abstr_ref_until_sat                   false
% 7.72/1.49  --abstr_ref_sig_restrict                funpre
% 7.72/1.49  --abstr_ref_af_restrict_to_split_sk     false
% 7.72/1.49  --abstr_ref_under                       []
% 7.72/1.49  
% 7.72/1.49  ------ SAT Options
% 7.72/1.49  
% 7.72/1.49  --sat_mode                              false
% 7.72/1.49  --sat_fm_restart_options                ""
% 7.72/1.49  --sat_gr_def                            false
% 7.72/1.49  --sat_epr_types                         true
% 7.72/1.49  --sat_non_cyclic_types                  false
% 7.72/1.49  --sat_finite_models                     false
% 7.72/1.49  --sat_fm_lemmas                         false
% 7.72/1.49  --sat_fm_prep                           false
% 7.72/1.49  --sat_fm_uc_incr                        true
% 7.72/1.49  --sat_out_model                         small
% 7.72/1.49  --sat_out_clauses                       false
% 7.72/1.49  
% 7.72/1.49  ------ QBF Options
% 7.72/1.49  
% 7.72/1.49  --qbf_mode                              false
% 7.72/1.49  --qbf_elim_univ                         false
% 7.72/1.49  --qbf_dom_inst                          none
% 7.72/1.49  --qbf_dom_pre_inst                      false
% 7.72/1.49  --qbf_sk_in                             false
% 7.72/1.49  --qbf_pred_elim                         true
% 7.72/1.49  --qbf_split                             512
% 7.72/1.49  
% 7.72/1.49  ------ BMC1 Options
% 7.72/1.49  
% 7.72/1.49  --bmc1_incremental                      false
% 7.72/1.49  --bmc1_axioms                           reachable_all
% 7.72/1.49  --bmc1_min_bound                        0
% 7.72/1.49  --bmc1_max_bound                        -1
% 7.72/1.49  --bmc1_max_bound_default                -1
% 7.72/1.49  --bmc1_symbol_reachability              true
% 7.72/1.49  --bmc1_property_lemmas                  false
% 7.72/1.49  --bmc1_k_induction                      false
% 7.72/1.49  --bmc1_non_equiv_states                 false
% 7.72/1.49  --bmc1_deadlock                         false
% 7.72/1.49  --bmc1_ucm                              false
% 7.72/1.49  --bmc1_add_unsat_core                   none
% 7.72/1.49  --bmc1_unsat_core_children              false
% 7.72/1.49  --bmc1_unsat_core_extrapolate_axioms    false
% 7.72/1.49  --bmc1_out_stat                         full
% 7.72/1.49  --bmc1_ground_init                      false
% 7.72/1.49  --bmc1_pre_inst_next_state              false
% 7.72/1.49  --bmc1_pre_inst_state                   false
% 7.72/1.49  --bmc1_pre_inst_reach_state             false
% 7.72/1.49  --bmc1_out_unsat_core                   false
% 7.72/1.49  --bmc1_aig_witness_out                  false
% 7.72/1.49  --bmc1_verbose                          false
% 7.72/1.49  --bmc1_dump_clauses_tptp                false
% 7.72/1.49  --bmc1_dump_unsat_core_tptp             false
% 7.72/1.49  --bmc1_dump_file                        -
% 7.72/1.49  --bmc1_ucm_expand_uc_limit              128
% 7.72/1.49  --bmc1_ucm_n_expand_iterations          6
% 7.72/1.49  --bmc1_ucm_extend_mode                  1
% 7.72/1.49  --bmc1_ucm_init_mode                    2
% 7.72/1.49  --bmc1_ucm_cone_mode                    none
% 7.72/1.49  --bmc1_ucm_reduced_relation_type        0
% 7.72/1.49  --bmc1_ucm_relax_model                  4
% 7.72/1.49  --bmc1_ucm_full_tr_after_sat            true
% 7.72/1.49  --bmc1_ucm_expand_neg_assumptions       false
% 7.72/1.49  --bmc1_ucm_layered_model                none
% 7.72/1.49  --bmc1_ucm_max_lemma_size               10
% 7.72/1.49  
% 7.72/1.49  ------ AIG Options
% 7.72/1.49  
% 7.72/1.49  --aig_mode                              false
% 7.72/1.49  
% 7.72/1.49  ------ Instantiation Options
% 7.72/1.49  
% 7.72/1.49  --instantiation_flag                    true
% 7.72/1.49  --inst_sos_flag                         true
% 7.72/1.49  --inst_sos_phase                        true
% 7.72/1.49  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.72/1.49  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.72/1.49  --inst_lit_sel_side                     none
% 7.72/1.49  --inst_solver_per_active                1400
% 7.72/1.49  --inst_solver_calls_frac                1.
% 7.72/1.49  --inst_passive_queue_type               priority_queues
% 7.72/1.49  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.72/1.49  --inst_passive_queues_freq              [25;2]
% 7.72/1.49  --inst_dismatching                      true
% 7.72/1.49  --inst_eager_unprocessed_to_passive     true
% 7.72/1.49  --inst_prop_sim_given                   true
% 7.72/1.49  --inst_prop_sim_new                     false
% 7.72/1.49  --inst_subs_new                         false
% 7.72/1.49  --inst_eq_res_simp                      false
% 7.72/1.49  --inst_subs_given                       false
% 7.72/1.49  --inst_orphan_elimination               true
% 7.72/1.49  --inst_learning_loop_flag               true
% 7.72/1.49  --inst_learning_start                   3000
% 7.72/1.49  --inst_learning_factor                  2
% 7.72/1.49  --inst_start_prop_sim_after_learn       3
% 7.72/1.49  --inst_sel_renew                        solver
% 7.72/1.49  --inst_lit_activity_flag                true
% 7.72/1.49  --inst_restr_to_given                   false
% 7.72/1.49  --inst_activity_threshold               500
% 7.72/1.49  --inst_out_proof                        true
% 7.72/1.49  
% 7.72/1.49  ------ Resolution Options
% 7.72/1.49  
% 7.72/1.49  --resolution_flag                       false
% 7.72/1.49  --res_lit_sel                           adaptive
% 7.72/1.49  --res_lit_sel_side                      none
% 7.72/1.49  --res_ordering                          kbo
% 7.72/1.49  --res_to_prop_solver                    active
% 7.72/1.49  --res_prop_simpl_new                    false
% 7.72/1.49  --res_prop_simpl_given                  true
% 7.72/1.49  --res_passive_queue_type                priority_queues
% 7.72/1.49  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.72/1.49  --res_passive_queues_freq               [15;5]
% 7.72/1.49  --res_forward_subs                      full
% 7.72/1.49  --res_backward_subs                     full
% 7.72/1.49  --res_forward_subs_resolution           true
% 7.72/1.49  --res_backward_subs_resolution          true
% 7.72/1.49  --res_orphan_elimination                true
% 7.72/1.49  --res_time_limit                        2.
% 7.72/1.49  --res_out_proof                         true
% 7.72/1.49  
% 7.72/1.49  ------ Superposition Options
% 7.72/1.49  
% 7.72/1.49  --superposition_flag                    true
% 7.72/1.49  --sup_passive_queue_type                priority_queues
% 7.72/1.49  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.72/1.49  --sup_passive_queues_freq               [8;1;4]
% 7.72/1.49  --demod_completeness_check              fast
% 7.72/1.49  --demod_use_ground                      true
% 7.72/1.49  --sup_to_prop_solver                    passive
% 7.72/1.49  --sup_prop_simpl_new                    true
% 7.72/1.49  --sup_prop_simpl_given                  true
% 7.72/1.49  --sup_fun_splitting                     true
% 7.72/1.49  --sup_smt_interval                      50000
% 7.72/1.49  
% 7.72/1.49  ------ Superposition Simplification Setup
% 7.72/1.49  
% 7.72/1.49  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 7.72/1.49  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 7.72/1.49  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 7.72/1.49  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 7.72/1.49  --sup_full_triv                         [TrivRules;PropSubs]
% 7.72/1.49  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 7.72/1.49  --sup_full_bw                           [BwDemod;BwSubsumption]
% 7.72/1.49  --sup_immed_triv                        [TrivRules]
% 7.72/1.49  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.72/1.49  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.72/1.49  --sup_immed_bw_main                     []
% 7.72/1.49  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 7.72/1.49  --sup_input_triv                        [Unflattening;TrivRules]
% 7.72/1.49  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.72/1.49  --sup_input_bw                          []
% 7.72/1.49  
% 7.72/1.49  ------ Combination Options
% 7.72/1.49  
% 7.72/1.49  --comb_res_mult                         3
% 7.72/1.49  --comb_sup_mult                         2
% 7.72/1.49  --comb_inst_mult                        10
% 7.72/1.49  
% 7.72/1.49  ------ Debug Options
% 7.72/1.49  
% 7.72/1.49  --dbg_backtrace                         false
% 7.72/1.49  --dbg_dump_prop_clauses                 false
% 7.72/1.49  --dbg_dump_prop_clauses_file            -
% 7.72/1.49  --dbg_out_stat                          false
% 7.72/1.49  
% 7.72/1.49  
% 7.72/1.49  
% 7.72/1.49  
% 7.72/1.49  ------ Proving...
% 7.72/1.49  
% 7.72/1.49  
% 7.72/1.49  % SZS status Theorem for theBenchmark.p
% 7.72/1.49  
% 7.72/1.49  % SZS output start CNFRefutation for theBenchmark.p
% 7.72/1.49  
% 7.72/1.49  fof(f9,axiom,(
% 7.72/1.49    ! [X0,X1] : (v1_relat_1(X0) => v1_relat_1(k7_relat_1(X0,X1)))),
% 7.72/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.72/1.49  
% 7.72/1.49  fof(f22,plain,(
% 7.72/1.49    ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0))),
% 7.72/1.49    inference(ennf_transformation,[],[f9])).
% 7.72/1.49  
% 7.72/1.49  fof(f49,plain,(
% 7.72/1.49    ( ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0)) )),
% 7.72/1.49    inference(cnf_transformation,[],[f22])).
% 7.72/1.49  
% 7.72/1.49  fof(f14,conjecture,(
% 7.72/1.49    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(X0,k1_relat_1(X1)) => r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))))),
% 7.72/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.72/1.49  
% 7.72/1.49  fof(f15,negated_conjecture,(
% 7.72/1.49    ~! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(X0,k1_relat_1(X1)) => r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))))),
% 7.72/1.49    inference(negated_conjecture,[],[f14])).
% 7.72/1.49  
% 7.72/1.49  fof(f27,plain,(
% 7.72/1.49    ? [X0,X1] : ((~r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) & r1_tarski(X0,k1_relat_1(X1))) & v1_relat_1(X1))),
% 7.72/1.49    inference(ennf_transformation,[],[f15])).
% 7.72/1.49  
% 7.72/1.49  fof(f28,plain,(
% 7.72/1.49    ? [X0,X1] : (~r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) & r1_tarski(X0,k1_relat_1(X1)) & v1_relat_1(X1))),
% 7.72/1.49    inference(flattening,[],[f27])).
% 7.72/1.49  
% 7.72/1.49  fof(f35,plain,(
% 7.72/1.49    ? [X0,X1] : (~r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) & r1_tarski(X0,k1_relat_1(X1)) & v1_relat_1(X1)) => (~r1_tarski(sK1,k10_relat_1(sK2,k9_relat_1(sK2,sK1))) & r1_tarski(sK1,k1_relat_1(sK2)) & v1_relat_1(sK2))),
% 7.72/1.49    introduced(choice_axiom,[])).
% 7.72/1.49  
% 7.72/1.49  fof(f36,plain,(
% 7.72/1.49    ~r1_tarski(sK1,k10_relat_1(sK2,k9_relat_1(sK2,sK1))) & r1_tarski(sK1,k1_relat_1(sK2)) & v1_relat_1(sK2)),
% 7.72/1.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f28,f35])).
% 7.72/1.49  
% 7.72/1.49  fof(f55,plain,(
% 7.72/1.49    r1_tarski(sK1,k1_relat_1(sK2))),
% 7.72/1.49    inference(cnf_transformation,[],[f36])).
% 7.72/1.49  
% 7.72/1.49  fof(f7,axiom,(
% 7.72/1.49    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 7.72/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.72/1.49  
% 7.72/1.49  fof(f19,plain,(
% 7.72/1.49    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 7.72/1.49    inference(ennf_transformation,[],[f7])).
% 7.72/1.49  
% 7.72/1.49  fof(f47,plain,(
% 7.72/1.49    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 7.72/1.49    inference(cnf_transformation,[],[f19])).
% 7.72/1.49  
% 7.72/1.49  fof(f54,plain,(
% 7.72/1.49    v1_relat_1(sK2)),
% 7.72/1.49    inference(cnf_transformation,[],[f36])).
% 7.72/1.49  
% 7.72/1.49  fof(f12,axiom,(
% 7.72/1.49    ! [X0] : (v1_relat_1(X0) => k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0))),
% 7.72/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.72/1.49  
% 7.72/1.49  fof(f25,plain,(
% 7.72/1.49    ! [X0] : (k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) | ~v1_relat_1(X0))),
% 7.72/1.49    inference(ennf_transformation,[],[f12])).
% 7.72/1.49  
% 7.72/1.49  fof(f52,plain,(
% 7.72/1.49    ( ! [X0] : (k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) | ~v1_relat_1(X0)) )),
% 7.72/1.49    inference(cnf_transformation,[],[f25])).
% 7.72/1.49  
% 7.72/1.49  fof(f13,axiom,(
% 7.72/1.49    ! [X0,X1,X2] : (v1_relat_1(X2) => k3_xboole_0(X0,k10_relat_1(X2,X1)) = k10_relat_1(k7_relat_1(X2,X0),X1))),
% 7.72/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.72/1.49  
% 7.72/1.49  fof(f26,plain,(
% 7.72/1.49    ! [X0,X1,X2] : (k3_xboole_0(X0,k10_relat_1(X2,X1)) = k10_relat_1(k7_relat_1(X2,X0),X1) | ~v1_relat_1(X2))),
% 7.72/1.49    inference(ennf_transformation,[],[f13])).
% 7.72/1.49  
% 7.72/1.49  fof(f53,plain,(
% 7.72/1.49    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k10_relat_1(X2,X1)) = k10_relat_1(k7_relat_1(X2,X0),X1) | ~v1_relat_1(X2)) )),
% 7.72/1.49    inference(cnf_transformation,[],[f26])).
% 7.72/1.49  
% 7.72/1.49  fof(f11,axiom,(
% 7.72/1.49    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)))),
% 7.72/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.72/1.49  
% 7.72/1.49  fof(f24,plain,(
% 7.72/1.49    ! [X0,X1] : (r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)) | ~v1_relat_1(X1))),
% 7.72/1.49    inference(ennf_transformation,[],[f11])).
% 7.72/1.49  
% 7.72/1.49  fof(f51,plain,(
% 7.72/1.49    ( ! [X0,X1] : (r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 7.72/1.49    inference(cnf_transformation,[],[f24])).
% 7.72/1.49  
% 7.72/1.49  fof(f10,axiom,(
% 7.72/1.49    ! [X0,X1] : (v1_relat_1(X1) => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0))),
% 7.72/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.72/1.49  
% 7.72/1.49  fof(f23,plain,(
% 7.72/1.49    ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 7.72/1.49    inference(ennf_transformation,[],[f10])).
% 7.72/1.49  
% 7.72/1.49  fof(f50,plain,(
% 7.72/1.49    ( ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 7.72/1.49    inference(cnf_transformation,[],[f23])).
% 7.72/1.49  
% 7.72/1.49  fof(f6,axiom,(
% 7.72/1.49    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 7.72/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.72/1.49  
% 7.72/1.49  fof(f46,plain,(
% 7.72/1.49    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 7.72/1.49    inference(cnf_transformation,[],[f6])).
% 7.72/1.49  
% 7.72/1.49  fof(f1,axiom,(
% 7.72/1.49    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 7.72/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.72/1.49  
% 7.72/1.49  fof(f37,plain,(
% 7.72/1.49    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 7.72/1.49    inference(cnf_transformation,[],[f1])).
% 7.72/1.49  
% 7.72/1.49  fof(f56,plain,(
% 7.72/1.49    ~r1_tarski(sK1,k10_relat_1(sK2,k9_relat_1(sK2,sK1)))),
% 7.72/1.49    inference(cnf_transformation,[],[f36])).
% 7.72/1.49  
% 7.72/1.49  cnf(c_12,plain,
% 7.72/1.49      ( ~ v1_relat_1(X0) | v1_relat_1(k7_relat_1(X0,X1)) ),
% 7.72/1.49      inference(cnf_transformation,[],[f49]) ).
% 7.72/1.49  
% 7.72/1.49  cnf(c_663,plain,
% 7.72/1.49      ( v1_relat_1(X0) != iProver_top
% 7.72/1.49      | v1_relat_1(k7_relat_1(X0,X1)) = iProver_top ),
% 7.72/1.49      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 7.72/1.49  
% 7.72/1.49  cnf(c_18,negated_conjecture,
% 7.72/1.49      ( r1_tarski(sK1,k1_relat_1(sK2)) ),
% 7.72/1.49      inference(cnf_transformation,[],[f55]) ).
% 7.72/1.49  
% 7.72/1.49  cnf(c_657,plain,
% 7.72/1.49      ( r1_tarski(sK1,k1_relat_1(sK2)) = iProver_top ),
% 7.72/1.49      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 7.72/1.49  
% 7.72/1.49  cnf(c_10,plain,
% 7.72/1.49      ( ~ r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0 ),
% 7.72/1.49      inference(cnf_transformation,[],[f47]) ).
% 7.72/1.49  
% 7.72/1.49  cnf(c_665,plain,
% 7.72/1.49      ( k3_xboole_0(X0,X1) = X0 | r1_tarski(X0,X1) != iProver_top ),
% 7.72/1.49      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 7.72/1.49  
% 7.72/1.49  cnf(c_1254,plain,
% 7.72/1.49      ( k3_xboole_0(sK1,k1_relat_1(sK2)) = sK1 ),
% 7.72/1.49      inference(superposition,[status(thm)],[c_657,c_665]) ).
% 7.72/1.49  
% 7.72/1.49  cnf(c_19,negated_conjecture,
% 7.72/1.49      ( v1_relat_1(sK2) ),
% 7.72/1.49      inference(cnf_transformation,[],[f54]) ).
% 7.72/1.49  
% 7.72/1.49  cnf(c_656,plain,
% 7.72/1.49      ( v1_relat_1(sK2) = iProver_top ),
% 7.72/1.49      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 7.72/1.49  
% 7.72/1.49  cnf(c_15,plain,
% 7.72/1.49      ( ~ v1_relat_1(X0)
% 7.72/1.49      | k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) ),
% 7.72/1.49      inference(cnf_transformation,[],[f52]) ).
% 7.72/1.49  
% 7.72/1.49  cnf(c_660,plain,
% 7.72/1.49      ( k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0)
% 7.72/1.49      | v1_relat_1(X0) != iProver_top ),
% 7.72/1.49      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 7.72/1.49  
% 7.72/1.49  cnf(c_1337,plain,
% 7.72/1.49      ( k10_relat_1(sK2,k2_relat_1(sK2)) = k1_relat_1(sK2) ),
% 7.72/1.49      inference(superposition,[status(thm)],[c_656,c_660]) ).
% 7.72/1.49  
% 7.72/1.49  cnf(c_16,plain,
% 7.72/1.49      ( ~ v1_relat_1(X0)
% 7.72/1.49      | k10_relat_1(k7_relat_1(X0,X1),X2) = k3_xboole_0(X1,k10_relat_1(X0,X2)) ),
% 7.72/1.49      inference(cnf_transformation,[],[f53]) ).
% 7.72/1.49  
% 7.72/1.49  cnf(c_659,plain,
% 7.72/1.49      ( k10_relat_1(k7_relat_1(X0,X1),X2) = k3_xboole_0(X1,k10_relat_1(X0,X2))
% 7.72/1.49      | v1_relat_1(X0) != iProver_top ),
% 7.72/1.49      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 7.72/1.49  
% 7.72/1.49  cnf(c_1246,plain,
% 7.72/1.49      ( k10_relat_1(k7_relat_1(sK2,X0),X1) = k3_xboole_0(X0,k10_relat_1(sK2,X1)) ),
% 7.72/1.49      inference(superposition,[status(thm)],[c_656,c_659]) ).
% 7.72/1.49  
% 7.72/1.49  cnf(c_14,plain,
% 7.72/1.49      ( r1_tarski(k10_relat_1(X0,X1),k1_relat_1(X0)) | ~ v1_relat_1(X0) ),
% 7.72/1.49      inference(cnf_transformation,[],[f51]) ).
% 7.72/1.49  
% 7.72/1.49  cnf(c_661,plain,
% 7.72/1.49      ( r1_tarski(k10_relat_1(X0,X1),k1_relat_1(X0)) = iProver_top
% 7.72/1.49      | v1_relat_1(X0) != iProver_top ),
% 7.72/1.49      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 7.72/1.49  
% 7.72/1.49  cnf(c_1819,plain,
% 7.72/1.49      ( r1_tarski(k3_xboole_0(X0,k10_relat_1(sK2,X1)),k1_relat_1(k7_relat_1(sK2,X0))) = iProver_top
% 7.72/1.49      | v1_relat_1(k7_relat_1(sK2,X0)) != iProver_top ),
% 7.72/1.49      inference(superposition,[status(thm)],[c_1246,c_661]) ).
% 7.72/1.49  
% 7.72/1.49  cnf(c_2412,plain,
% 7.72/1.49      ( r1_tarski(k3_xboole_0(X0,k1_relat_1(sK2)),k1_relat_1(k7_relat_1(sK2,X0))) = iProver_top
% 7.72/1.49      | v1_relat_1(k7_relat_1(sK2,X0)) != iProver_top ),
% 7.72/1.49      inference(superposition,[status(thm)],[c_1337,c_1819]) ).
% 7.72/1.49  
% 7.72/1.49  cnf(c_2489,plain,
% 7.72/1.49      ( r1_tarski(sK1,k1_relat_1(k7_relat_1(sK2,sK1))) = iProver_top
% 7.72/1.49      | v1_relat_1(k7_relat_1(sK2,sK1)) != iProver_top ),
% 7.72/1.49      inference(superposition,[status(thm)],[c_1254,c_2412]) ).
% 7.72/1.49  
% 7.72/1.49  cnf(c_2510,plain,
% 7.72/1.49      ( k3_xboole_0(sK1,k1_relat_1(k7_relat_1(sK2,sK1))) = sK1
% 7.72/1.49      | v1_relat_1(k7_relat_1(sK2,sK1)) != iProver_top ),
% 7.72/1.49      inference(superposition,[status(thm)],[c_2489,c_665]) ).
% 7.72/1.49  
% 7.72/1.49  cnf(c_2606,plain,
% 7.72/1.49      ( k3_xboole_0(sK1,k1_relat_1(k7_relat_1(sK2,sK1))) = sK1
% 7.72/1.49      | v1_relat_1(sK2) != iProver_top ),
% 7.72/1.49      inference(superposition,[status(thm)],[c_663,c_2510]) ).
% 7.72/1.49  
% 7.72/1.49  cnf(c_20,plain,
% 7.72/1.49      ( v1_relat_1(sK2) = iProver_top ),
% 7.72/1.49      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 7.72/1.49  
% 7.72/1.49  cnf(c_16551,plain,
% 7.72/1.49      ( k3_xboole_0(sK1,k1_relat_1(k7_relat_1(sK2,sK1))) = sK1 ),
% 7.72/1.49      inference(global_propositional_subsumption,
% 7.72/1.49                [status(thm)],
% 7.72/1.49                [c_2606,c_20]) ).
% 7.72/1.49  
% 7.72/1.49  cnf(c_1336,plain,
% 7.72/1.49      ( k10_relat_1(k7_relat_1(X0,X1),k2_relat_1(k7_relat_1(X0,X1))) = k1_relat_1(k7_relat_1(X0,X1))
% 7.72/1.49      | v1_relat_1(X0) != iProver_top ),
% 7.72/1.49      inference(superposition,[status(thm)],[c_663,c_660]) ).
% 7.72/1.49  
% 7.72/1.49  cnf(c_4466,plain,
% 7.72/1.49      ( k10_relat_1(k7_relat_1(sK2,X0),k2_relat_1(k7_relat_1(sK2,X0))) = k1_relat_1(k7_relat_1(sK2,X0)) ),
% 7.72/1.49      inference(superposition,[status(thm)],[c_656,c_1336]) ).
% 7.72/1.49  
% 7.72/1.49  cnf(c_13,plain,
% 7.72/1.49      ( ~ v1_relat_1(X0)
% 7.72/1.49      | k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1) ),
% 7.72/1.49      inference(cnf_transformation,[],[f50]) ).
% 7.72/1.49  
% 7.72/1.49  cnf(c_662,plain,
% 7.72/1.49      ( k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1)
% 7.72/1.49      | v1_relat_1(X0) != iProver_top ),
% 7.72/1.49      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 7.72/1.49  
% 7.72/1.49  cnf(c_1950,plain,
% 7.72/1.49      ( k2_relat_1(k7_relat_1(sK2,X0)) = k9_relat_1(sK2,X0) ),
% 7.72/1.49      inference(superposition,[status(thm)],[c_656,c_662]) ).
% 7.72/1.49  
% 7.72/1.49  cnf(c_4467,plain,
% 7.72/1.49      ( k10_relat_1(k7_relat_1(sK2,X0),k9_relat_1(sK2,X0)) = k1_relat_1(k7_relat_1(sK2,X0)) ),
% 7.72/1.49      inference(light_normalisation,[status(thm)],[c_4466,c_1950]) ).
% 7.72/1.49  
% 7.72/1.49  cnf(c_4809,plain,
% 7.72/1.49      ( k3_xboole_0(X0,k10_relat_1(sK2,k9_relat_1(sK2,X0))) = k1_relat_1(k7_relat_1(sK2,X0)) ),
% 7.72/1.49      inference(superposition,[status(thm)],[c_4467,c_1246]) ).
% 7.72/1.49  
% 7.72/1.49  cnf(c_9,plain,
% 7.72/1.49      ( r1_tarski(k3_xboole_0(X0,X1),X0) ),
% 7.72/1.49      inference(cnf_transformation,[],[f46]) ).
% 7.72/1.49  
% 7.72/1.49  cnf(c_666,plain,
% 7.72/1.49      ( r1_tarski(k3_xboole_0(X0,X1),X0) = iProver_top ),
% 7.72/1.49      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 7.72/1.49  
% 7.72/1.49  cnf(c_1253,plain,
% 7.72/1.49      ( k3_xboole_0(k3_xboole_0(X0,X1),X0) = k3_xboole_0(X0,X1) ),
% 7.72/1.49      inference(superposition,[status(thm)],[c_666,c_665]) ).
% 7.72/1.49  
% 7.72/1.49  cnf(c_0,plain,
% 7.72/1.49      ( k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
% 7.72/1.49      inference(cnf_transformation,[],[f37]) ).
% 7.72/1.49  
% 7.72/1.49  cnf(c_3625,plain,
% 7.72/1.49      ( k3_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
% 7.72/1.49      inference(superposition,[status(thm)],[c_1253,c_0]) ).
% 7.72/1.49  
% 7.72/1.49  cnf(c_4938,plain,
% 7.72/1.49      ( k3_xboole_0(X0,k10_relat_1(sK2,k9_relat_1(sK2,X0))) = k3_xboole_0(X0,k1_relat_1(k7_relat_1(sK2,X0))) ),
% 7.72/1.49      inference(superposition,[status(thm)],[c_4809,c_3625]) ).
% 7.72/1.49  
% 7.72/1.49  cnf(c_4957,plain,
% 7.72/1.49      ( k3_xboole_0(X0,k1_relat_1(k7_relat_1(sK2,X0))) = k1_relat_1(k7_relat_1(sK2,X0)) ),
% 7.72/1.49      inference(demodulation,[status(thm)],[c_4938,c_4809]) ).
% 7.72/1.49  
% 7.72/1.49  cnf(c_16586,plain,
% 7.72/1.49      ( k1_relat_1(k7_relat_1(sK2,sK1)) = sK1 ),
% 7.72/1.49      inference(superposition,[status(thm)],[c_16551,c_4957]) ).
% 7.72/1.49  
% 7.72/1.49  cnf(c_1031,plain,
% 7.72/1.49      ( r1_tarski(k3_xboole_0(X0,X1),X1) = iProver_top ),
% 7.72/1.49      inference(superposition,[status(thm)],[c_0,c_666]) ).
% 7.72/1.49  
% 7.72/1.49  cnf(c_4943,plain,
% 7.72/1.49      ( r1_tarski(k1_relat_1(k7_relat_1(sK2,X0)),k10_relat_1(sK2,k9_relat_1(sK2,X0))) = iProver_top ),
% 7.72/1.49      inference(superposition,[status(thm)],[c_4809,c_1031]) ).
% 7.72/1.49  
% 7.72/1.49  cnf(c_24801,plain,
% 7.72/1.49      ( r1_tarski(sK1,k10_relat_1(sK2,k9_relat_1(sK2,sK1))) = iProver_top ),
% 7.72/1.49      inference(superposition,[status(thm)],[c_16586,c_4943]) ).
% 7.72/1.49  
% 7.72/1.49  cnf(c_17,negated_conjecture,
% 7.72/1.49      ( ~ r1_tarski(sK1,k10_relat_1(sK2,k9_relat_1(sK2,sK1))) ),
% 7.72/1.49      inference(cnf_transformation,[],[f56]) ).
% 7.72/1.49  
% 7.72/1.49  cnf(c_22,plain,
% 7.72/1.49      ( r1_tarski(sK1,k10_relat_1(sK2,k9_relat_1(sK2,sK1))) != iProver_top ),
% 7.72/1.49      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 7.72/1.49  
% 7.72/1.49  cnf(contradiction,plain,
% 7.72/1.49      ( $false ),
% 7.72/1.49      inference(minisat,[status(thm)],[c_24801,c_22]) ).
% 7.72/1.49  
% 7.72/1.49  
% 7.72/1.49  % SZS output end CNFRefutation for theBenchmark.p
% 7.72/1.49  
% 7.72/1.49  ------                               Statistics
% 7.72/1.49  
% 7.72/1.49  ------ General
% 7.72/1.49  
% 7.72/1.49  abstr_ref_over_cycles:                  0
% 7.72/1.49  abstr_ref_under_cycles:                 0
% 7.72/1.49  gc_basic_clause_elim:                   0
% 7.72/1.49  forced_gc_time:                         0
% 7.72/1.49  parsing_time:                           0.007
% 7.72/1.49  unif_index_cands_time:                  0.
% 7.72/1.49  unif_index_add_time:                    0.
% 7.72/1.49  orderings_time:                         0.
% 7.72/1.49  out_proof_time:                         0.007
% 7.72/1.49  total_time:                             0.67
% 7.72/1.49  num_of_symbols:                         44
% 7.72/1.49  num_of_terms:                           25864
% 7.72/1.49  
% 7.72/1.49  ------ Preprocessing
% 7.72/1.49  
% 7.72/1.49  num_of_splits:                          0
% 7.72/1.49  num_of_split_atoms:                     0
% 7.72/1.49  num_of_reused_defs:                     0
% 7.72/1.49  num_eq_ax_congr_red:                    24
% 7.72/1.49  num_of_sem_filtered_clauses:            1
% 7.72/1.49  num_of_subtypes:                        0
% 7.72/1.49  monotx_restored_types:                  0
% 7.72/1.49  sat_num_of_epr_types:                   0
% 7.72/1.49  sat_num_of_non_cyclic_types:            0
% 7.72/1.49  sat_guarded_non_collapsed_types:        0
% 7.72/1.49  num_pure_diseq_elim:                    0
% 7.72/1.49  simp_replaced_by:                       0
% 7.72/1.49  res_preprocessed:                       97
% 7.72/1.49  prep_upred:                             0
% 7.72/1.49  prep_unflattend:                        0
% 7.72/1.49  smt_new_axioms:                         0
% 7.72/1.49  pred_elim_cands:                        3
% 7.72/1.49  pred_elim:                              0
% 7.72/1.49  pred_elim_cl:                           0
% 7.72/1.49  pred_elim_cycles:                       2
% 7.72/1.49  merged_defs:                            0
% 7.72/1.49  merged_defs_ncl:                        0
% 7.72/1.49  bin_hyper_res:                          0
% 7.72/1.49  prep_cycles:                            4
% 7.72/1.49  pred_elim_time:                         0.
% 7.72/1.49  splitting_time:                         0.
% 7.72/1.49  sem_filter_time:                        0.
% 7.72/1.49  monotx_time:                            0.
% 7.72/1.49  subtype_inf_time:                       0.
% 7.72/1.49  
% 7.72/1.49  ------ Problem properties
% 7.72/1.49  
% 7.72/1.49  clauses:                                19
% 7.72/1.49  conjectures:                            3
% 7.72/1.49  epr:                                    4
% 7.72/1.49  horn:                                   18
% 7.72/1.49  ground:                                 3
% 7.72/1.49  unary:                                  6
% 7.72/1.49  binary:                                 10
% 7.72/1.49  lits:                                   35
% 7.72/1.49  lits_eq:                                7
% 7.72/1.49  fd_pure:                                0
% 7.72/1.49  fd_pseudo:                              0
% 7.72/1.49  fd_cond:                                0
% 7.72/1.49  fd_pseudo_cond:                         1
% 7.72/1.49  ac_symbols:                             0
% 7.72/1.49  
% 7.72/1.49  ------ Propositional Solver
% 7.72/1.49  
% 7.72/1.49  prop_solver_calls:                      33
% 7.72/1.49  prop_fast_solver_calls:                 805
% 7.72/1.49  smt_solver_calls:                       0
% 7.72/1.49  smt_fast_solver_calls:                  0
% 7.72/1.49  prop_num_of_clauses:                    10196
% 7.72/1.49  prop_preprocess_simplified:             16318
% 7.72/1.49  prop_fo_subsumed:                       3
% 7.72/1.49  prop_solver_time:                       0.
% 7.72/1.49  smt_solver_time:                        0.
% 7.72/1.49  smt_fast_solver_time:                   0.
% 7.72/1.49  prop_fast_solver_time:                  0.
% 7.72/1.49  prop_unsat_core_time:                   0.
% 7.72/1.49  
% 7.72/1.49  ------ QBF
% 7.72/1.49  
% 7.72/1.49  qbf_q_res:                              0
% 7.72/1.49  qbf_num_tautologies:                    0
% 7.72/1.49  qbf_prep_cycles:                        0
% 7.72/1.49  
% 7.72/1.49  ------ BMC1
% 7.72/1.49  
% 7.72/1.49  bmc1_current_bound:                     -1
% 7.72/1.49  bmc1_last_solved_bound:                 -1
% 7.72/1.49  bmc1_unsat_core_size:                   -1
% 7.72/1.49  bmc1_unsat_core_parents_size:           -1
% 7.72/1.49  bmc1_merge_next_fun:                    0
% 7.72/1.49  bmc1_unsat_core_clauses_time:           0.
% 7.72/1.49  
% 7.72/1.49  ------ Instantiation
% 7.72/1.49  
% 7.72/1.49  inst_num_of_clauses:                    2084
% 7.72/1.49  inst_num_in_passive:                    968
% 7.72/1.49  inst_num_in_active:                     808
% 7.72/1.49  inst_num_in_unprocessed:                308
% 7.72/1.49  inst_num_of_loops:                      1110
% 7.72/1.49  inst_num_of_learning_restarts:          0
% 7.72/1.49  inst_num_moves_active_passive:          299
% 7.72/1.49  inst_lit_activity:                      0
% 7.72/1.49  inst_lit_activity_moves:                0
% 7.72/1.49  inst_num_tautologies:                   0
% 7.72/1.49  inst_num_prop_implied:                  0
% 7.72/1.49  inst_num_existing_simplified:           0
% 7.72/1.49  inst_num_eq_res_simplified:             0
% 7.72/1.49  inst_num_child_elim:                    0
% 7.72/1.49  inst_num_of_dismatching_blockings:      1424
% 7.72/1.49  inst_num_of_non_proper_insts:           3000
% 7.72/1.49  inst_num_of_duplicates:                 0
% 7.72/1.49  inst_inst_num_from_inst_to_res:         0
% 7.72/1.49  inst_dismatching_checking_time:         0.
% 7.72/1.49  
% 7.72/1.49  ------ Resolution
% 7.72/1.49  
% 7.72/1.49  res_num_of_clauses:                     0
% 7.72/1.49  res_num_in_passive:                     0
% 7.72/1.49  res_num_in_active:                      0
% 7.72/1.49  res_num_of_loops:                       101
% 7.72/1.49  res_forward_subset_subsumed:            321
% 7.72/1.49  res_backward_subset_subsumed:           0
% 7.72/1.49  res_forward_subsumed:                   0
% 7.72/1.49  res_backward_subsumed:                  0
% 7.72/1.49  res_forward_subsumption_resolution:     0
% 7.72/1.49  res_backward_subsumption_resolution:    0
% 7.72/1.49  res_clause_to_clause_subsumption:       8049
% 7.72/1.49  res_orphan_elimination:                 0
% 7.72/1.49  res_tautology_del:                      209
% 7.72/1.49  res_num_eq_res_simplified:              0
% 7.72/1.49  res_num_sel_changes:                    0
% 7.72/1.49  res_moves_from_active_to_pass:          0
% 7.72/1.49  
% 7.72/1.49  ------ Superposition
% 7.72/1.49  
% 7.72/1.49  sup_time_total:                         0.
% 7.72/1.49  sup_time_generating:                    0.
% 7.72/1.49  sup_time_sim_full:                      0.
% 7.72/1.49  sup_time_sim_immed:                     0.
% 7.72/1.49  
% 7.72/1.49  sup_num_of_clauses:                     904
% 7.72/1.49  sup_num_in_active:                      203
% 7.72/1.49  sup_num_in_passive:                     701
% 7.72/1.49  sup_num_of_loops:                       220
% 7.72/1.49  sup_fw_superposition:                   2631
% 7.72/1.49  sup_bw_superposition:                   997
% 7.72/1.49  sup_immediate_simplified:               1219
% 7.72/1.49  sup_given_eliminated:                   1
% 7.72/1.49  comparisons_done:                       0
% 7.72/1.49  comparisons_avoided:                    0
% 7.72/1.49  
% 7.72/1.49  ------ Simplifications
% 7.72/1.49  
% 7.72/1.49  
% 7.72/1.49  sim_fw_subset_subsumed:                 41
% 7.72/1.49  sim_bw_subset_subsumed:                 7
% 7.72/1.49  sim_fw_subsumed:                        132
% 7.72/1.49  sim_bw_subsumed:                        1
% 7.72/1.49  sim_fw_subsumption_res:                 0
% 7.72/1.49  sim_bw_subsumption_res:                 0
% 7.72/1.49  sim_tautology_del:                      39
% 7.72/1.49  sim_eq_tautology_del:                   100
% 7.72/1.49  sim_eq_res_simp:                        0
% 7.72/1.49  sim_fw_demodulated:                     662
% 7.72/1.49  sim_bw_demodulated:                     22
% 7.72/1.49  sim_light_normalised:                   542
% 7.72/1.49  sim_joinable_taut:                      0
% 7.72/1.49  sim_joinable_simp:                      0
% 7.72/1.49  sim_ac_normalised:                      0
% 7.72/1.49  sim_smt_subsumption:                    0
% 7.72/1.49  
%------------------------------------------------------------------------------
