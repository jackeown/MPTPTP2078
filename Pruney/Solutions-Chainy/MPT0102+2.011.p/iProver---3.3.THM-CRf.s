%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:25:04 EST 2020

% Result     : Theorem 11.41s
% Output     : CNFRefutation 11.41s
% Verified   : 
% Statistics : Number of formulae       :   66 ( 153 expanded)
%              Number of clauses        :   35 (  62 expanded)
%              Number of leaves         :   13 (  42 expanded)
%              Depth                    :   12
%              Number of atoms          :   67 ( 154 expanded)
%              Number of equality atoms :   66 ( 153 expanded)
%              Maximal formula depth    :    5 (   2 average)
%              Maximal clause size      :    2 (   1 average)
%              Maximal term depth       :    5 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f9,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f9])).

fof(f2,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f13,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f13])).

fof(f36,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(definition_unfolding,[],[f23,f34,f34])).

fof(f8,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f8])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f12,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f12])).

fof(f10,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f10])).

fof(f14,conjecture,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,negated_conjecture,(
    ~ ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) ),
    inference(negated_conjecture,[],[f14])).

fof(f19,plain,(
    ? [X0,X1] : k3_xboole_0(X0,X1) != k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) ),
    inference(ennf_transformation,[],[f15])).

fof(f20,plain,
    ( ? [X0,X1] : k3_xboole_0(X0,X1) != k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))
   => k3_xboole_0(sK0,sK1) != k5_xboole_0(k5_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK1)) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    k3_xboole_0(sK0,sK1) != k5_xboole_0(k5_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK1)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f19,f20])).

fof(f35,plain,(
    k3_xboole_0(sK0,sK1) != k5_xboole_0(k5_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK1)) ),
    inference(cnf_transformation,[],[f21])).

fof(f3,axiom,(
    ! [X0,X1] : k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) = k5_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] : k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) = k5_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f3])).

fof(f38,plain,(
    k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k2_xboole_0(sK0,sK1)),k4_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)))) != k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) ),
    inference(definition_unfolding,[],[f35,f34,f24,f24])).

fof(f7,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f7])).

fof(f11,axiom,(
    ! [X0,X1,X2] : k2_xboole_0(k4_xboole_0(X0,X2),k4_xboole_0(X1,X2)) = k4_xboole_0(k2_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X2,X0,X1] : k2_xboole_0(k4_xboole_0(X0,X2),k4_xboole_0(X1,X2)) = k4_xboole_0(k2_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f11])).

fof(f6,axiom,(
    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f6])).

fof(f37,plain,(
    ! [X0] : k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) = k1_xboole_0 ),
    inference(definition_unfolding,[],[f27,f34])).

cnf(c_7,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),X1) = k4_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_1,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_378,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,k2_xboole_0(X0,X1))) ),
    inference(superposition,[status(thm)],[c_7,c_1])).

cnf(c_6,plain,
    ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f29])).

cnf(c_0,plain,
    ( k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f22])).

cnf(c_10,plain,
    ( k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f33])).

cnf(c_192,plain,
    ( k4_xboole_0(X0,k2_xboole_0(X1,X0)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_0,c_10])).

cnf(c_383,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X1 ),
    inference(demodulation,[status(thm)],[c_378,c_6,c_192])).

cnf(c_8,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f31])).

cnf(c_1063,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(k4_xboole_0(X0,X1),X2)) = k4_xboole_0(X1,X2) ),
    inference(superposition,[status(thm)],[c_383,c_8])).

cnf(c_11,negated_conjecture,
    ( k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k2_xboole_0(sK0,sK1)),k4_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)))) != k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_153,plain,
    ( k2_xboole_0(k4_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0))),k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k2_xboole_0(sK0,sK1))) != k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) ),
    inference(demodulation,[status(thm)],[c_0,c_11])).

cnf(c_39252,plain,
    ( k2_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK0)),k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k2_xboole_0(sK0,sK1))) != k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) ),
    inference(demodulation,[status(thm)],[c_1063,c_153])).

cnf(c_5,plain,
    ( k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f28])).

cnf(c_252,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X1,X0)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_5,c_192])).

cnf(c_715,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X0,X1)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_0,c_252])).

cnf(c_9,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X2,X1)) = k4_xboole_0(k2_xboole_0(X0,X2),X1) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_1391,plain,
    ( k4_xboole_0(k2_xboole_0(k4_xboole_0(X0,X1),X2),k2_xboole_0(X0,X1)) = k2_xboole_0(k1_xboole_0,k4_xboole_0(X2,k2_xboole_0(X0,X1))) ),
    inference(superposition,[status(thm)],[c_715,c_9])).

cnf(c_4,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f37])).

cnf(c_68,plain,
    ( k4_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_4,c_6])).

cnf(c_503,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),X0) = k2_xboole_0(k1_xboole_0,k4_xboole_0(X1,X0)) ),
    inference(superposition,[status(thm)],[c_68,c_9])).

cnf(c_294,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),X0) = k4_xboole_0(X1,X0) ),
    inference(superposition,[status(thm)],[c_0,c_7])).

cnf(c_524,plain,
    ( k2_xboole_0(k1_xboole_0,k4_xboole_0(X0,X1)) = k4_xboole_0(X0,X1) ),
    inference(light_normalisation,[status(thm)],[c_503,c_294])).

cnf(c_1405,plain,
    ( k4_xboole_0(k2_xboole_0(k4_xboole_0(X0,X1),X2),k2_xboole_0(X0,X1)) = k4_xboole_0(X2,k2_xboole_0(X0,X1)) ),
    inference(demodulation,[status(thm)],[c_1391,c_524])).

cnf(c_39253,plain,
    ( k2_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK0)),k4_xboole_0(k4_xboole_0(sK1,sK0),k2_xboole_0(sK0,sK1))) != k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) ),
    inference(demodulation,[status(thm)],[c_39252,c_1405])).

cnf(c_915,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),X1) = k4_xboole_0(k2_xboole_0(X1,X0),X1) ),
    inference(superposition,[status(thm)],[c_5,c_294])).

cnf(c_935,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),X1) = k4_xboole_0(X0,X1) ),
    inference(demodulation,[status(thm)],[c_915,c_294])).

cnf(c_1929,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
    inference(superposition,[status(thm)],[c_935,c_8])).

cnf(c_1941,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X1,X2)) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(light_normalisation,[status(thm)],[c_1929,c_8])).

cnf(c_39254,plain,
    ( k2_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK0)),k4_xboole_0(sK1,k2_xboole_0(sK0,sK1))) != k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) ),
    inference(demodulation,[status(thm)],[c_39253,c_1941])).

cnf(c_511,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),X1) = k2_xboole_0(k4_xboole_0(X0,X1),k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_68,c_9])).

cnf(c_520,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),k1_xboole_0) = k4_xboole_0(X0,X1) ),
    inference(light_normalisation,[status(thm)],[c_511,c_7])).

cnf(c_39255,plain,
    ( k4_xboole_0(sK1,k4_xboole_0(sK1,sK0)) != k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) ),
    inference(demodulation,[status(thm)],[c_39254,c_192,c_520])).

cnf(c_266,plain,
    ( k4_xboole_0(sK1,k4_xboole_0(sK1,sK0)) = k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_39255,c_266])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n017.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 16:39:16 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  % Running in FOF mode
% 11.41/2.01  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 11.41/2.01  
% 11.41/2.01  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 11.41/2.01  
% 11.41/2.01  ------  iProver source info
% 11.41/2.01  
% 11.41/2.01  git: date: 2020-06-30 10:37:57 +0100
% 11.41/2.01  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 11.41/2.01  git: non_committed_changes: false
% 11.41/2.01  git: last_make_outside_of_git: false
% 11.41/2.01  
% 11.41/2.01  ------ 
% 11.41/2.01  
% 11.41/2.01  ------ Input Options
% 11.41/2.01  
% 11.41/2.01  --out_options                           all
% 11.41/2.01  --tptp_safe_out                         true
% 11.41/2.01  --problem_path                          ""
% 11.41/2.01  --include_path                          ""
% 11.41/2.01  --clausifier                            res/vclausify_rel
% 11.41/2.01  --clausifier_options                    ""
% 11.41/2.01  --stdin                                 false
% 11.41/2.01  --stats_out                             all
% 11.41/2.01  
% 11.41/2.01  ------ General Options
% 11.41/2.01  
% 11.41/2.01  --fof                                   false
% 11.41/2.01  --time_out_real                         305.
% 11.41/2.01  --time_out_virtual                      -1.
% 11.41/2.01  --symbol_type_check                     false
% 11.41/2.01  --clausify_out                          false
% 11.41/2.01  --sig_cnt_out                           false
% 11.41/2.01  --trig_cnt_out                          false
% 11.41/2.01  --trig_cnt_out_tolerance                1.
% 11.41/2.01  --trig_cnt_out_sk_spl                   false
% 11.41/2.01  --abstr_cl_out                          false
% 11.41/2.01  
% 11.41/2.01  ------ Global Options
% 11.41/2.01  
% 11.41/2.01  --schedule                              default
% 11.41/2.01  --add_important_lit                     false
% 11.41/2.01  --prop_solver_per_cl                    1000
% 11.41/2.01  --min_unsat_core                        false
% 11.41/2.01  --soft_assumptions                      false
% 11.41/2.01  --soft_lemma_size                       3
% 11.41/2.01  --prop_impl_unit_size                   0
% 11.41/2.01  --prop_impl_unit                        []
% 11.41/2.01  --share_sel_clauses                     true
% 11.41/2.01  --reset_solvers                         false
% 11.41/2.01  --bc_imp_inh                            [conj_cone]
% 11.41/2.01  --conj_cone_tolerance                   3.
% 11.41/2.01  --extra_neg_conj                        none
% 11.41/2.01  --large_theory_mode                     true
% 11.41/2.01  --prolific_symb_bound                   200
% 11.41/2.01  --lt_threshold                          2000
% 11.41/2.01  --clause_weak_htbl                      true
% 11.41/2.01  --gc_record_bc_elim                     false
% 11.41/2.01  
% 11.41/2.01  ------ Preprocessing Options
% 11.41/2.01  
% 11.41/2.01  --preprocessing_flag                    true
% 11.41/2.01  --time_out_prep_mult                    0.1
% 11.41/2.01  --splitting_mode                        input
% 11.41/2.01  --splitting_grd                         true
% 11.41/2.01  --splitting_cvd                         false
% 11.41/2.01  --splitting_cvd_svl                     false
% 11.41/2.01  --splitting_nvd                         32
% 11.41/2.01  --sub_typing                            true
% 11.41/2.01  --prep_gs_sim                           true
% 11.41/2.01  --prep_unflatten                        true
% 11.41/2.01  --prep_res_sim                          true
% 11.41/2.01  --prep_upred                            true
% 11.41/2.01  --prep_sem_filter                       exhaustive
% 11.41/2.01  --prep_sem_filter_out                   false
% 11.41/2.01  --pred_elim                             true
% 11.41/2.01  --res_sim_input                         true
% 11.41/2.01  --eq_ax_congr_red                       true
% 11.41/2.01  --pure_diseq_elim                       true
% 11.41/2.01  --brand_transform                       false
% 11.41/2.01  --non_eq_to_eq                          false
% 11.41/2.01  --prep_def_merge                        true
% 11.41/2.01  --prep_def_merge_prop_impl              false
% 11.41/2.01  --prep_def_merge_mbd                    true
% 11.41/2.01  --prep_def_merge_tr_red                 false
% 11.41/2.01  --prep_def_merge_tr_cl                  false
% 11.41/2.01  --smt_preprocessing                     true
% 11.41/2.01  --smt_ac_axioms                         fast
% 11.41/2.01  --preprocessed_out                      false
% 11.41/2.01  --preprocessed_stats                    false
% 11.41/2.01  
% 11.41/2.01  ------ Abstraction refinement Options
% 11.41/2.01  
% 11.41/2.01  --abstr_ref                             []
% 11.41/2.01  --abstr_ref_prep                        false
% 11.41/2.01  --abstr_ref_until_sat                   false
% 11.41/2.01  --abstr_ref_sig_restrict                funpre
% 11.41/2.01  --abstr_ref_af_restrict_to_split_sk     false
% 11.41/2.01  --abstr_ref_under                       []
% 11.41/2.01  
% 11.41/2.01  ------ SAT Options
% 11.41/2.01  
% 11.41/2.01  --sat_mode                              false
% 11.41/2.01  --sat_fm_restart_options                ""
% 11.41/2.01  --sat_gr_def                            false
% 11.41/2.01  --sat_epr_types                         true
% 11.41/2.01  --sat_non_cyclic_types                  false
% 11.41/2.01  --sat_finite_models                     false
% 11.41/2.01  --sat_fm_lemmas                         false
% 11.41/2.01  --sat_fm_prep                           false
% 11.41/2.01  --sat_fm_uc_incr                        true
% 11.41/2.01  --sat_out_model                         small
% 11.41/2.01  --sat_out_clauses                       false
% 11.41/2.01  
% 11.41/2.01  ------ QBF Options
% 11.41/2.01  
% 11.41/2.01  --qbf_mode                              false
% 11.41/2.01  --qbf_elim_univ                         false
% 11.41/2.01  --qbf_dom_inst                          none
% 11.41/2.01  --qbf_dom_pre_inst                      false
% 11.41/2.01  --qbf_sk_in                             false
% 11.41/2.01  --qbf_pred_elim                         true
% 11.41/2.01  --qbf_split                             512
% 11.41/2.01  
% 11.41/2.01  ------ BMC1 Options
% 11.41/2.01  
% 11.41/2.01  --bmc1_incremental                      false
% 11.41/2.01  --bmc1_axioms                           reachable_all
% 11.41/2.01  --bmc1_min_bound                        0
% 11.41/2.01  --bmc1_max_bound                        -1
% 11.41/2.01  --bmc1_max_bound_default                -1
% 11.41/2.01  --bmc1_symbol_reachability              true
% 11.41/2.01  --bmc1_property_lemmas                  false
% 11.41/2.01  --bmc1_k_induction                      false
% 11.41/2.01  --bmc1_non_equiv_states                 false
% 11.41/2.01  --bmc1_deadlock                         false
% 11.41/2.01  --bmc1_ucm                              false
% 11.41/2.01  --bmc1_add_unsat_core                   none
% 11.41/2.01  --bmc1_unsat_core_children              false
% 11.41/2.01  --bmc1_unsat_core_extrapolate_axioms    false
% 11.41/2.01  --bmc1_out_stat                         full
% 11.41/2.01  --bmc1_ground_init                      false
% 11.41/2.01  --bmc1_pre_inst_next_state              false
% 11.41/2.01  --bmc1_pre_inst_state                   false
% 11.41/2.01  --bmc1_pre_inst_reach_state             false
% 11.41/2.01  --bmc1_out_unsat_core                   false
% 11.41/2.01  --bmc1_aig_witness_out                  false
% 11.41/2.01  --bmc1_verbose                          false
% 11.41/2.01  --bmc1_dump_clauses_tptp                false
% 11.41/2.01  --bmc1_dump_unsat_core_tptp             false
% 11.41/2.01  --bmc1_dump_file                        -
% 11.41/2.01  --bmc1_ucm_expand_uc_limit              128
% 11.41/2.01  --bmc1_ucm_n_expand_iterations          6
% 11.41/2.01  --bmc1_ucm_extend_mode                  1
% 11.41/2.01  --bmc1_ucm_init_mode                    2
% 11.41/2.01  --bmc1_ucm_cone_mode                    none
% 11.41/2.01  --bmc1_ucm_reduced_relation_type        0
% 11.41/2.01  --bmc1_ucm_relax_model                  4
% 11.41/2.01  --bmc1_ucm_full_tr_after_sat            true
% 11.41/2.01  --bmc1_ucm_expand_neg_assumptions       false
% 11.41/2.01  --bmc1_ucm_layered_model                none
% 11.41/2.01  --bmc1_ucm_max_lemma_size               10
% 11.41/2.01  
% 11.41/2.01  ------ AIG Options
% 11.41/2.01  
% 11.41/2.01  --aig_mode                              false
% 11.41/2.01  
% 11.41/2.01  ------ Instantiation Options
% 11.41/2.01  
% 11.41/2.01  --instantiation_flag                    true
% 11.41/2.01  --inst_sos_flag                         true
% 11.41/2.01  --inst_sos_phase                        true
% 11.41/2.01  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 11.41/2.01  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 11.41/2.01  --inst_lit_sel_side                     num_symb
% 11.41/2.01  --inst_solver_per_active                1400
% 11.41/2.01  --inst_solver_calls_frac                1.
% 11.41/2.01  --inst_passive_queue_type               priority_queues
% 11.41/2.01  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 11.41/2.01  --inst_passive_queues_freq              [25;2]
% 11.41/2.01  --inst_dismatching                      true
% 11.41/2.01  --inst_eager_unprocessed_to_passive     true
% 11.41/2.01  --inst_prop_sim_given                   true
% 11.41/2.01  --inst_prop_sim_new                     false
% 11.41/2.01  --inst_subs_new                         false
% 11.41/2.01  --inst_eq_res_simp                      false
% 11.41/2.01  --inst_subs_given                       false
% 11.41/2.01  --inst_orphan_elimination               true
% 11.41/2.01  --inst_learning_loop_flag               true
% 11.41/2.01  --inst_learning_start                   3000
% 11.41/2.01  --inst_learning_factor                  2
% 11.41/2.01  --inst_start_prop_sim_after_learn       3
% 11.41/2.01  --inst_sel_renew                        solver
% 11.41/2.01  --inst_lit_activity_flag                true
% 11.41/2.01  --inst_restr_to_given                   false
% 11.41/2.01  --inst_activity_threshold               500
% 11.41/2.01  --inst_out_proof                        true
% 11.41/2.01  
% 11.41/2.01  ------ Resolution Options
% 11.41/2.01  
% 11.41/2.01  --resolution_flag                       true
% 11.41/2.01  --res_lit_sel                           adaptive
% 11.41/2.01  --res_lit_sel_side                      none
% 11.41/2.01  --res_ordering                          kbo
% 11.41/2.01  --res_to_prop_solver                    active
% 11.41/2.01  --res_prop_simpl_new                    false
% 11.41/2.01  --res_prop_simpl_given                  true
% 11.41/2.01  --res_passive_queue_type                priority_queues
% 11.41/2.01  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 11.41/2.01  --res_passive_queues_freq               [15;5]
% 11.41/2.01  --res_forward_subs                      full
% 11.41/2.01  --res_backward_subs                     full
% 11.41/2.01  --res_forward_subs_resolution           true
% 11.41/2.01  --res_backward_subs_resolution          true
% 11.41/2.01  --res_orphan_elimination                true
% 11.41/2.01  --res_time_limit                        2.
% 11.41/2.01  --res_out_proof                         true
% 11.41/2.01  
% 11.41/2.01  ------ Superposition Options
% 11.41/2.01  
% 11.41/2.01  --superposition_flag                    true
% 11.41/2.01  --sup_passive_queue_type                priority_queues
% 11.41/2.01  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 11.41/2.01  --sup_passive_queues_freq               [8;1;4]
% 11.41/2.01  --demod_completeness_check              fast
% 11.41/2.01  --demod_use_ground                      true
% 11.41/2.01  --sup_to_prop_solver                    passive
% 11.41/2.01  --sup_prop_simpl_new                    true
% 11.41/2.01  --sup_prop_simpl_given                  true
% 11.41/2.01  --sup_fun_splitting                     true
% 11.41/2.01  --sup_smt_interval                      50000
% 11.41/2.01  
% 11.41/2.01  ------ Superposition Simplification Setup
% 11.41/2.01  
% 11.41/2.01  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 11.41/2.01  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 11.41/2.01  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 11.41/2.01  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 11.41/2.01  --sup_full_triv                         [TrivRules;PropSubs]
% 11.41/2.01  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 11.41/2.01  --sup_full_bw                           [BwDemod;BwSubsumption]
% 11.41/2.01  --sup_immed_triv                        [TrivRules]
% 11.41/2.01  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 11.41/2.01  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 11.41/2.01  --sup_immed_bw_main                     []
% 11.41/2.01  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 11.41/2.01  --sup_input_triv                        [Unflattening;TrivRules]
% 11.41/2.01  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 11.41/2.01  --sup_input_bw                          []
% 11.41/2.01  
% 11.41/2.01  ------ Combination Options
% 11.41/2.01  
% 11.41/2.01  --comb_res_mult                         3
% 11.41/2.01  --comb_sup_mult                         2
% 11.41/2.01  --comb_inst_mult                        10
% 11.41/2.01  
% 11.41/2.01  ------ Debug Options
% 11.41/2.01  
% 11.41/2.01  --dbg_backtrace                         false
% 11.41/2.01  --dbg_dump_prop_clauses                 false
% 11.41/2.01  --dbg_dump_prop_clauses_file            -
% 11.41/2.01  --dbg_out_stat                          false
% 11.41/2.01  ------ Parsing...
% 11.41/2.01  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 11.41/2.01  
% 11.41/2.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 11.41/2.01  
% 11.41/2.01  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 11.41/2.01  
% 11.41/2.01  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 11.41/2.01  ------ Proving...
% 11.41/2.01  ------ Problem Properties 
% 11.41/2.01  
% 11.41/2.01  
% 11.41/2.01  clauses                                 11
% 11.41/2.01  conjectures                             1
% 11.41/2.01  EPR                                     0
% 11.41/2.01  Horn                                    11
% 11.41/2.01  unary                                   10
% 11.41/2.01  binary                                  1
% 11.41/2.01  lits                                    12
% 11.41/2.01  lits eq                                 12
% 11.41/2.01  fd_pure                                 0
% 11.41/2.01  fd_pseudo                               0
% 11.41/2.01  fd_cond                                 0
% 11.41/2.01  fd_pseudo_cond                          0
% 11.41/2.01  AC symbols                              0
% 11.41/2.01  
% 11.41/2.01  ------ Schedule dynamic 5 is on 
% 11.41/2.01  
% 11.41/2.01  ------ pure equality problem: resolution off 
% 11.41/2.01  
% 11.41/2.01  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 11.41/2.01  
% 11.41/2.01  
% 11.41/2.01  ------ 
% 11.41/2.01  Current options:
% 11.41/2.01  ------ 
% 11.41/2.01  
% 11.41/2.01  ------ Input Options
% 11.41/2.01  
% 11.41/2.01  --out_options                           all
% 11.41/2.01  --tptp_safe_out                         true
% 11.41/2.01  --problem_path                          ""
% 11.41/2.01  --include_path                          ""
% 11.41/2.01  --clausifier                            res/vclausify_rel
% 11.41/2.01  --clausifier_options                    ""
% 11.41/2.01  --stdin                                 false
% 11.41/2.01  --stats_out                             all
% 11.41/2.01  
% 11.41/2.01  ------ General Options
% 11.41/2.01  
% 11.41/2.01  --fof                                   false
% 11.41/2.01  --time_out_real                         305.
% 11.41/2.01  --time_out_virtual                      -1.
% 11.41/2.01  --symbol_type_check                     false
% 11.41/2.01  --clausify_out                          false
% 11.41/2.01  --sig_cnt_out                           false
% 11.41/2.01  --trig_cnt_out                          false
% 11.41/2.01  --trig_cnt_out_tolerance                1.
% 11.41/2.01  --trig_cnt_out_sk_spl                   false
% 11.41/2.01  --abstr_cl_out                          false
% 11.41/2.01  
% 11.41/2.01  ------ Global Options
% 11.41/2.01  
% 11.41/2.01  --schedule                              default
% 11.41/2.01  --add_important_lit                     false
% 11.41/2.01  --prop_solver_per_cl                    1000
% 11.41/2.01  --min_unsat_core                        false
% 11.41/2.01  --soft_assumptions                      false
% 11.41/2.01  --soft_lemma_size                       3
% 11.41/2.01  --prop_impl_unit_size                   0
% 11.41/2.01  --prop_impl_unit                        []
% 11.41/2.01  --share_sel_clauses                     true
% 11.41/2.01  --reset_solvers                         false
% 11.41/2.01  --bc_imp_inh                            [conj_cone]
% 11.41/2.01  --conj_cone_tolerance                   3.
% 11.41/2.01  --extra_neg_conj                        none
% 11.41/2.01  --large_theory_mode                     true
% 11.41/2.01  --prolific_symb_bound                   200
% 11.41/2.01  --lt_threshold                          2000
% 11.41/2.01  --clause_weak_htbl                      true
% 11.41/2.01  --gc_record_bc_elim                     false
% 11.41/2.01  
% 11.41/2.01  ------ Preprocessing Options
% 11.41/2.01  
% 11.41/2.01  --preprocessing_flag                    true
% 11.41/2.01  --time_out_prep_mult                    0.1
% 11.41/2.01  --splitting_mode                        input
% 11.41/2.01  --splitting_grd                         true
% 11.41/2.01  --splitting_cvd                         false
% 11.41/2.01  --splitting_cvd_svl                     false
% 11.41/2.01  --splitting_nvd                         32
% 11.41/2.01  --sub_typing                            true
% 11.41/2.01  --prep_gs_sim                           true
% 11.41/2.01  --prep_unflatten                        true
% 11.41/2.01  --prep_res_sim                          true
% 11.41/2.01  --prep_upred                            true
% 11.41/2.01  --prep_sem_filter                       exhaustive
% 11.41/2.01  --prep_sem_filter_out                   false
% 11.41/2.01  --pred_elim                             true
% 11.41/2.01  --res_sim_input                         true
% 11.41/2.01  --eq_ax_congr_red                       true
% 11.41/2.01  --pure_diseq_elim                       true
% 11.41/2.01  --brand_transform                       false
% 11.41/2.01  --non_eq_to_eq                          false
% 11.41/2.01  --prep_def_merge                        true
% 11.41/2.01  --prep_def_merge_prop_impl              false
% 11.41/2.01  --prep_def_merge_mbd                    true
% 11.41/2.01  --prep_def_merge_tr_red                 false
% 11.41/2.01  --prep_def_merge_tr_cl                  false
% 11.41/2.01  --smt_preprocessing                     true
% 11.41/2.01  --smt_ac_axioms                         fast
% 11.41/2.01  --preprocessed_out                      false
% 11.41/2.01  --preprocessed_stats                    false
% 11.41/2.01  
% 11.41/2.01  ------ Abstraction refinement Options
% 11.41/2.01  
% 11.41/2.01  --abstr_ref                             []
% 11.41/2.01  --abstr_ref_prep                        false
% 11.41/2.01  --abstr_ref_until_sat                   false
% 11.41/2.01  --abstr_ref_sig_restrict                funpre
% 11.41/2.01  --abstr_ref_af_restrict_to_split_sk     false
% 11.41/2.01  --abstr_ref_under                       []
% 11.41/2.01  
% 11.41/2.01  ------ SAT Options
% 11.41/2.01  
% 11.41/2.01  --sat_mode                              false
% 11.41/2.01  --sat_fm_restart_options                ""
% 11.41/2.01  --sat_gr_def                            false
% 11.41/2.01  --sat_epr_types                         true
% 11.41/2.01  --sat_non_cyclic_types                  false
% 11.41/2.01  --sat_finite_models                     false
% 11.41/2.01  --sat_fm_lemmas                         false
% 11.41/2.01  --sat_fm_prep                           false
% 11.41/2.01  --sat_fm_uc_incr                        true
% 11.41/2.01  --sat_out_model                         small
% 11.41/2.01  --sat_out_clauses                       false
% 11.41/2.01  
% 11.41/2.01  ------ QBF Options
% 11.41/2.01  
% 11.41/2.01  --qbf_mode                              false
% 11.41/2.01  --qbf_elim_univ                         false
% 11.41/2.01  --qbf_dom_inst                          none
% 11.41/2.01  --qbf_dom_pre_inst                      false
% 11.41/2.01  --qbf_sk_in                             false
% 11.41/2.01  --qbf_pred_elim                         true
% 11.41/2.01  --qbf_split                             512
% 11.41/2.01  
% 11.41/2.01  ------ BMC1 Options
% 11.41/2.01  
% 11.41/2.01  --bmc1_incremental                      false
% 11.41/2.01  --bmc1_axioms                           reachable_all
% 11.41/2.01  --bmc1_min_bound                        0
% 11.41/2.01  --bmc1_max_bound                        -1
% 11.41/2.01  --bmc1_max_bound_default                -1
% 11.41/2.01  --bmc1_symbol_reachability              true
% 11.41/2.01  --bmc1_property_lemmas                  false
% 11.41/2.01  --bmc1_k_induction                      false
% 11.41/2.01  --bmc1_non_equiv_states                 false
% 11.41/2.01  --bmc1_deadlock                         false
% 11.41/2.01  --bmc1_ucm                              false
% 11.41/2.01  --bmc1_add_unsat_core                   none
% 11.41/2.01  --bmc1_unsat_core_children              false
% 11.41/2.01  --bmc1_unsat_core_extrapolate_axioms    false
% 11.41/2.01  --bmc1_out_stat                         full
% 11.41/2.01  --bmc1_ground_init                      false
% 11.41/2.01  --bmc1_pre_inst_next_state              false
% 11.41/2.01  --bmc1_pre_inst_state                   false
% 11.41/2.01  --bmc1_pre_inst_reach_state             false
% 11.41/2.01  --bmc1_out_unsat_core                   false
% 11.41/2.01  --bmc1_aig_witness_out                  false
% 11.41/2.01  --bmc1_verbose                          false
% 11.41/2.01  --bmc1_dump_clauses_tptp                false
% 11.41/2.01  --bmc1_dump_unsat_core_tptp             false
% 11.41/2.01  --bmc1_dump_file                        -
% 11.41/2.01  --bmc1_ucm_expand_uc_limit              128
% 11.41/2.01  --bmc1_ucm_n_expand_iterations          6
% 11.41/2.01  --bmc1_ucm_extend_mode                  1
% 11.41/2.01  --bmc1_ucm_init_mode                    2
% 11.41/2.01  --bmc1_ucm_cone_mode                    none
% 11.41/2.01  --bmc1_ucm_reduced_relation_type        0
% 11.41/2.01  --bmc1_ucm_relax_model                  4
% 11.41/2.01  --bmc1_ucm_full_tr_after_sat            true
% 11.41/2.01  --bmc1_ucm_expand_neg_assumptions       false
% 11.41/2.01  --bmc1_ucm_layered_model                none
% 11.41/2.01  --bmc1_ucm_max_lemma_size               10
% 11.41/2.01  
% 11.41/2.01  ------ AIG Options
% 11.41/2.01  
% 11.41/2.01  --aig_mode                              false
% 11.41/2.01  
% 11.41/2.01  ------ Instantiation Options
% 11.41/2.01  
% 11.41/2.01  --instantiation_flag                    true
% 11.41/2.01  --inst_sos_flag                         true
% 11.41/2.01  --inst_sos_phase                        true
% 11.41/2.01  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 11.41/2.01  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 11.41/2.01  --inst_lit_sel_side                     none
% 11.41/2.01  --inst_solver_per_active                1400
% 11.41/2.01  --inst_solver_calls_frac                1.
% 11.41/2.01  --inst_passive_queue_type               priority_queues
% 11.41/2.01  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 11.41/2.01  --inst_passive_queues_freq              [25;2]
% 11.41/2.01  --inst_dismatching                      true
% 11.41/2.01  --inst_eager_unprocessed_to_passive     true
% 11.41/2.01  --inst_prop_sim_given                   true
% 11.41/2.01  --inst_prop_sim_new                     false
% 11.41/2.01  --inst_subs_new                         false
% 11.41/2.01  --inst_eq_res_simp                      false
% 11.41/2.01  --inst_subs_given                       false
% 11.41/2.01  --inst_orphan_elimination               true
% 11.41/2.01  --inst_learning_loop_flag               true
% 11.41/2.01  --inst_learning_start                   3000
% 11.41/2.01  --inst_learning_factor                  2
% 11.41/2.01  --inst_start_prop_sim_after_learn       3
% 11.41/2.01  --inst_sel_renew                        solver
% 11.41/2.01  --inst_lit_activity_flag                true
% 11.41/2.01  --inst_restr_to_given                   false
% 11.41/2.01  --inst_activity_threshold               500
% 11.41/2.01  --inst_out_proof                        true
% 11.41/2.01  
% 11.41/2.01  ------ Resolution Options
% 11.41/2.01  
% 11.41/2.01  --resolution_flag                       false
% 11.41/2.01  --res_lit_sel                           adaptive
% 11.41/2.01  --res_lit_sel_side                      none
% 11.41/2.01  --res_ordering                          kbo
% 11.41/2.01  --res_to_prop_solver                    active
% 11.41/2.01  --res_prop_simpl_new                    false
% 11.41/2.01  --res_prop_simpl_given                  true
% 11.41/2.01  --res_passive_queue_type                priority_queues
% 11.41/2.01  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 11.41/2.01  --res_passive_queues_freq               [15;5]
% 11.41/2.01  --res_forward_subs                      full
% 11.41/2.01  --res_backward_subs                     full
% 11.41/2.01  --res_forward_subs_resolution           true
% 11.41/2.01  --res_backward_subs_resolution          true
% 11.41/2.01  --res_orphan_elimination                true
% 11.41/2.01  --res_time_limit                        2.
% 11.41/2.01  --res_out_proof                         true
% 11.41/2.01  
% 11.41/2.01  ------ Superposition Options
% 11.41/2.01  
% 11.41/2.01  --superposition_flag                    true
% 11.41/2.01  --sup_passive_queue_type                priority_queues
% 11.41/2.01  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 11.41/2.01  --sup_passive_queues_freq               [8;1;4]
% 11.41/2.01  --demod_completeness_check              fast
% 11.41/2.01  --demod_use_ground                      true
% 11.41/2.01  --sup_to_prop_solver                    passive
% 11.41/2.01  --sup_prop_simpl_new                    true
% 11.41/2.01  --sup_prop_simpl_given                  true
% 11.41/2.01  --sup_fun_splitting                     true
% 11.41/2.01  --sup_smt_interval                      50000
% 11.41/2.01  
% 11.41/2.01  ------ Superposition Simplification Setup
% 11.41/2.01  
% 11.41/2.01  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 11.41/2.01  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 11.41/2.01  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 11.41/2.01  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 11.41/2.01  --sup_full_triv                         [TrivRules;PropSubs]
% 11.41/2.01  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 11.41/2.01  --sup_full_bw                           [BwDemod;BwSubsumption]
% 11.41/2.01  --sup_immed_triv                        [TrivRules]
% 11.41/2.01  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 11.41/2.01  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 11.41/2.01  --sup_immed_bw_main                     []
% 11.41/2.01  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 11.41/2.01  --sup_input_triv                        [Unflattening;TrivRules]
% 11.41/2.01  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 11.41/2.01  --sup_input_bw                          []
% 11.41/2.01  
% 11.41/2.01  ------ Combination Options
% 11.41/2.01  
% 11.41/2.01  --comb_res_mult                         3
% 11.41/2.01  --comb_sup_mult                         2
% 11.41/2.01  --comb_inst_mult                        10
% 11.41/2.01  
% 11.41/2.01  ------ Debug Options
% 11.41/2.01  
% 11.41/2.01  --dbg_backtrace                         false
% 11.41/2.01  --dbg_dump_prop_clauses                 false
% 11.41/2.01  --dbg_dump_prop_clauses_file            -
% 11.41/2.01  --dbg_out_stat                          false
% 11.41/2.01  
% 11.41/2.01  
% 11.41/2.01  
% 11.41/2.01  
% 11.41/2.01  ------ Proving...
% 11.41/2.01  
% 11.41/2.01  
% 11.41/2.01  % SZS status Theorem for theBenchmark.p
% 11.41/2.01  
% 11.41/2.01  % SZS output start CNFRefutation for theBenchmark.p
% 11.41/2.01  
% 11.41/2.01  fof(f9,axiom,(
% 11.41/2.01    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1)),
% 11.41/2.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.41/2.01  
% 11.41/2.01  fof(f30,plain,(
% 11.41/2.01    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1)) )),
% 11.41/2.01    inference(cnf_transformation,[],[f9])).
% 11.41/2.01  
% 11.41/2.01  fof(f2,axiom,(
% 11.41/2.01    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 11.41/2.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.41/2.01  
% 11.41/2.01  fof(f23,plain,(
% 11.41/2.01    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 11.41/2.01    inference(cnf_transformation,[],[f2])).
% 11.41/2.01  
% 11.41/2.01  fof(f13,axiom,(
% 11.41/2.01    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 11.41/2.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.41/2.01  
% 11.41/2.01  fof(f34,plain,(
% 11.41/2.01    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 11.41/2.01    inference(cnf_transformation,[],[f13])).
% 11.41/2.01  
% 11.41/2.01  fof(f36,plain,(
% 11.41/2.01    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0))) )),
% 11.41/2.01    inference(definition_unfolding,[],[f23,f34,f34])).
% 11.41/2.01  
% 11.41/2.01  fof(f8,axiom,(
% 11.41/2.01    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 11.41/2.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.41/2.01  
% 11.41/2.01  fof(f29,plain,(
% 11.41/2.01    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 11.41/2.01    inference(cnf_transformation,[],[f8])).
% 11.41/2.01  
% 11.41/2.01  fof(f1,axiom,(
% 11.41/2.01    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 11.41/2.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.41/2.01  
% 11.41/2.01  fof(f22,plain,(
% 11.41/2.01    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 11.41/2.01    inference(cnf_transformation,[],[f1])).
% 11.41/2.01  
% 11.41/2.01  fof(f12,axiom,(
% 11.41/2.01    ! [X0,X1] : k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0),
% 11.41/2.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.41/2.01  
% 11.41/2.01  fof(f33,plain,(
% 11.41/2.01    ( ! [X0,X1] : (k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0) )),
% 11.41/2.01    inference(cnf_transformation,[],[f12])).
% 11.41/2.01  
% 11.41/2.01  fof(f10,axiom,(
% 11.41/2.01    ! [X0,X1,X2] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2)),
% 11.41/2.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.41/2.01  
% 11.41/2.01  fof(f31,plain,(
% 11.41/2.01    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2)) )),
% 11.41/2.01    inference(cnf_transformation,[],[f10])).
% 11.41/2.01  
% 11.41/2.01  fof(f14,conjecture,(
% 11.41/2.01    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))),
% 11.41/2.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.41/2.01  
% 11.41/2.01  fof(f15,negated_conjecture,(
% 11.41/2.01    ~! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))),
% 11.41/2.01    inference(negated_conjecture,[],[f14])).
% 11.41/2.01  
% 11.41/2.01  fof(f19,plain,(
% 11.41/2.01    ? [X0,X1] : k3_xboole_0(X0,X1) != k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))),
% 11.41/2.01    inference(ennf_transformation,[],[f15])).
% 11.41/2.01  
% 11.41/2.01  fof(f20,plain,(
% 11.41/2.01    ? [X0,X1] : k3_xboole_0(X0,X1) != k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) => k3_xboole_0(sK0,sK1) != k5_xboole_0(k5_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK1))),
% 11.41/2.01    introduced(choice_axiom,[])).
% 11.41/2.01  
% 11.41/2.01  fof(f21,plain,(
% 11.41/2.01    k3_xboole_0(sK0,sK1) != k5_xboole_0(k5_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK1))),
% 11.41/2.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f19,f20])).
% 11.41/2.01  
% 11.41/2.01  fof(f35,plain,(
% 11.41/2.01    k3_xboole_0(sK0,sK1) != k5_xboole_0(k5_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK1))),
% 11.41/2.01    inference(cnf_transformation,[],[f21])).
% 11.41/2.01  
% 11.41/2.01  fof(f3,axiom,(
% 11.41/2.01    ! [X0,X1] : k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) = k5_xboole_0(X0,X1)),
% 11.41/2.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.41/2.01  
% 11.41/2.01  fof(f24,plain,(
% 11.41/2.01    ( ! [X0,X1] : (k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) = k5_xboole_0(X0,X1)) )),
% 11.41/2.01    inference(cnf_transformation,[],[f3])).
% 11.41/2.01  
% 11.41/2.01  fof(f38,plain,(
% 11.41/2.01    k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k2_xboole_0(sK0,sK1)),k4_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)))) != k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),
% 11.41/2.01    inference(definition_unfolding,[],[f35,f34,f24,f24])).
% 11.41/2.01  
% 11.41/2.01  fof(f7,axiom,(
% 11.41/2.01    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))),
% 11.41/2.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.41/2.01  
% 11.41/2.01  fof(f28,plain,(
% 11.41/2.01    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 11.41/2.01    inference(cnf_transformation,[],[f7])).
% 11.41/2.01  
% 11.41/2.01  fof(f11,axiom,(
% 11.41/2.01    ! [X0,X1,X2] : k2_xboole_0(k4_xboole_0(X0,X2),k4_xboole_0(X1,X2)) = k4_xboole_0(k2_xboole_0(X0,X1),X2)),
% 11.41/2.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.41/2.01  
% 11.41/2.01  fof(f32,plain,(
% 11.41/2.01    ( ! [X2,X0,X1] : (k2_xboole_0(k4_xboole_0(X0,X2),k4_xboole_0(X1,X2)) = k4_xboole_0(k2_xboole_0(X0,X1),X2)) )),
% 11.41/2.01    inference(cnf_transformation,[],[f11])).
% 11.41/2.01  
% 11.41/2.01  fof(f6,axiom,(
% 11.41/2.01    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0),
% 11.41/2.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.41/2.01  
% 11.41/2.01  fof(f27,plain,(
% 11.41/2.01    ( ! [X0] : (k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0) )),
% 11.41/2.01    inference(cnf_transformation,[],[f6])).
% 11.41/2.01  
% 11.41/2.01  fof(f37,plain,(
% 11.41/2.01    ( ! [X0] : (k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) = k1_xboole_0) )),
% 11.41/2.01    inference(definition_unfolding,[],[f27,f34])).
% 11.41/2.01  
% 11.41/2.01  cnf(c_7,plain,
% 11.41/2.01      ( k4_xboole_0(k2_xboole_0(X0,X1),X1) = k4_xboole_0(X0,X1) ),
% 11.41/2.01      inference(cnf_transformation,[],[f30]) ).
% 11.41/2.01  
% 11.41/2.01  cnf(c_1,plain,
% 11.41/2.01      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
% 11.41/2.01      inference(cnf_transformation,[],[f36]) ).
% 11.41/2.01  
% 11.41/2.01  cnf(c_378,plain,
% 11.41/2.01      ( k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,k2_xboole_0(X0,X1))) ),
% 11.41/2.01      inference(superposition,[status(thm)],[c_7,c_1]) ).
% 11.41/2.01  
% 11.41/2.01  cnf(c_6,plain,
% 11.41/2.01      ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
% 11.41/2.01      inference(cnf_transformation,[],[f29]) ).
% 11.41/2.01  
% 11.41/2.01  cnf(c_0,plain,
% 11.41/2.01      ( k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
% 11.41/2.01      inference(cnf_transformation,[],[f22]) ).
% 11.41/2.01  
% 11.41/2.01  cnf(c_10,plain,
% 11.41/2.01      ( k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0 ),
% 11.41/2.01      inference(cnf_transformation,[],[f33]) ).
% 11.41/2.01  
% 11.41/2.01  cnf(c_192,plain,
% 11.41/2.01      ( k4_xboole_0(X0,k2_xboole_0(X1,X0)) = k1_xboole_0 ),
% 11.41/2.01      inference(superposition,[status(thm)],[c_0,c_10]) ).
% 11.41/2.01  
% 11.41/2.01  cnf(c_383,plain,
% 11.41/2.01      ( k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X1 ),
% 11.41/2.01      inference(demodulation,[status(thm)],[c_378,c_6,c_192]) ).
% 11.41/2.01  
% 11.41/2.01  cnf(c_8,plain,
% 11.41/2.01      ( k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
% 11.41/2.01      inference(cnf_transformation,[],[f31]) ).
% 11.41/2.01  
% 11.41/2.01  cnf(c_1063,plain,
% 11.41/2.01      ( k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(k4_xboole_0(X0,X1),X2)) = k4_xboole_0(X1,X2) ),
% 11.41/2.01      inference(superposition,[status(thm)],[c_383,c_8]) ).
% 11.41/2.01  
% 11.41/2.01  cnf(c_11,negated_conjecture,
% 11.41/2.01      ( k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k2_xboole_0(sK0,sK1)),k4_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)))) != k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) ),
% 11.41/2.01      inference(cnf_transformation,[],[f38]) ).
% 11.41/2.01  
% 11.41/2.01  cnf(c_153,plain,
% 11.41/2.01      ( k2_xboole_0(k4_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0))),k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k2_xboole_0(sK0,sK1))) != k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) ),
% 11.41/2.01      inference(demodulation,[status(thm)],[c_0,c_11]) ).
% 11.41/2.01  
% 11.41/2.01  cnf(c_39252,plain,
% 11.41/2.01      ( k2_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK0)),k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k2_xboole_0(sK0,sK1))) != k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) ),
% 11.41/2.01      inference(demodulation,[status(thm)],[c_1063,c_153]) ).
% 11.41/2.01  
% 11.41/2.01  cnf(c_5,plain,
% 11.41/2.01      ( k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
% 11.41/2.01      inference(cnf_transformation,[],[f28]) ).
% 11.41/2.01  
% 11.41/2.01  cnf(c_252,plain,
% 11.41/2.01      ( k4_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X1,X0)) = k1_xboole_0 ),
% 11.41/2.01      inference(superposition,[status(thm)],[c_5,c_192]) ).
% 11.41/2.01  
% 11.41/2.01  cnf(c_715,plain,
% 11.41/2.01      ( k4_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X0,X1)) = k1_xboole_0 ),
% 11.41/2.01      inference(superposition,[status(thm)],[c_0,c_252]) ).
% 11.41/2.01  
% 11.41/2.01  cnf(c_9,plain,
% 11.41/2.01      ( k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X2,X1)) = k4_xboole_0(k2_xboole_0(X0,X2),X1) ),
% 11.41/2.01      inference(cnf_transformation,[],[f32]) ).
% 11.41/2.01  
% 11.41/2.01  cnf(c_1391,plain,
% 11.41/2.01      ( k4_xboole_0(k2_xboole_0(k4_xboole_0(X0,X1),X2),k2_xboole_0(X0,X1)) = k2_xboole_0(k1_xboole_0,k4_xboole_0(X2,k2_xboole_0(X0,X1))) ),
% 11.41/2.01      inference(superposition,[status(thm)],[c_715,c_9]) ).
% 11.41/2.01  
% 11.41/2.01  cnf(c_4,plain,
% 11.41/2.01      ( k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) = k1_xboole_0 ),
% 11.41/2.01      inference(cnf_transformation,[],[f37]) ).
% 11.41/2.01  
% 11.41/2.01  cnf(c_68,plain,
% 11.41/2.01      ( k4_xboole_0(X0,X0) = k1_xboole_0 ),
% 11.41/2.01      inference(light_normalisation,[status(thm)],[c_4,c_6]) ).
% 11.41/2.01  
% 11.41/2.01  cnf(c_503,plain,
% 11.41/2.01      ( k4_xboole_0(k2_xboole_0(X0,X1),X0) = k2_xboole_0(k1_xboole_0,k4_xboole_0(X1,X0)) ),
% 11.41/2.01      inference(superposition,[status(thm)],[c_68,c_9]) ).
% 11.41/2.01  
% 11.41/2.01  cnf(c_294,plain,
% 11.41/2.01      ( k4_xboole_0(k2_xboole_0(X0,X1),X0) = k4_xboole_0(X1,X0) ),
% 11.41/2.01      inference(superposition,[status(thm)],[c_0,c_7]) ).
% 11.41/2.01  
% 11.41/2.01  cnf(c_524,plain,
% 11.41/2.01      ( k2_xboole_0(k1_xboole_0,k4_xboole_0(X0,X1)) = k4_xboole_0(X0,X1) ),
% 11.41/2.01      inference(light_normalisation,[status(thm)],[c_503,c_294]) ).
% 11.41/2.01  
% 11.41/2.01  cnf(c_1405,plain,
% 11.41/2.01      ( k4_xboole_0(k2_xboole_0(k4_xboole_0(X0,X1),X2),k2_xboole_0(X0,X1)) = k4_xboole_0(X2,k2_xboole_0(X0,X1)) ),
% 11.41/2.01      inference(demodulation,[status(thm)],[c_1391,c_524]) ).
% 11.41/2.01  
% 11.41/2.01  cnf(c_39253,plain,
% 11.41/2.01      ( k2_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK0)),k4_xboole_0(k4_xboole_0(sK1,sK0),k2_xboole_0(sK0,sK1))) != k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) ),
% 11.41/2.01      inference(demodulation,[status(thm)],[c_39252,c_1405]) ).
% 11.41/2.01  
% 11.41/2.01  cnf(c_915,plain,
% 11.41/2.01      ( k4_xboole_0(k4_xboole_0(X0,X1),X1) = k4_xboole_0(k2_xboole_0(X1,X0),X1) ),
% 11.41/2.01      inference(superposition,[status(thm)],[c_5,c_294]) ).
% 11.41/2.01  
% 11.41/2.01  cnf(c_935,plain,
% 11.41/2.01      ( k4_xboole_0(k4_xboole_0(X0,X1),X1) = k4_xboole_0(X0,X1) ),
% 11.41/2.01      inference(demodulation,[status(thm)],[c_915,c_294]) ).
% 11.41/2.01  
% 11.41/2.01  cnf(c_1929,plain,
% 11.41/2.01      ( k4_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
% 11.41/2.01      inference(superposition,[status(thm)],[c_935,c_8]) ).
% 11.41/2.01  
% 11.41/2.01  cnf(c_1941,plain,
% 11.41/2.01      ( k4_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X1,X2)) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
% 11.41/2.01      inference(light_normalisation,[status(thm)],[c_1929,c_8]) ).
% 11.41/2.01  
% 11.41/2.01  cnf(c_39254,plain,
% 11.41/2.01      ( k2_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK0)),k4_xboole_0(sK1,k2_xboole_0(sK0,sK1))) != k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) ),
% 11.41/2.01      inference(demodulation,[status(thm)],[c_39253,c_1941]) ).
% 11.41/2.01  
% 11.41/2.01  cnf(c_511,plain,
% 11.41/2.01      ( k4_xboole_0(k2_xboole_0(X0,X1),X1) = k2_xboole_0(k4_xboole_0(X0,X1),k1_xboole_0) ),
% 11.41/2.01      inference(superposition,[status(thm)],[c_68,c_9]) ).
% 11.41/2.01  
% 11.41/2.01  cnf(c_520,plain,
% 11.41/2.01      ( k2_xboole_0(k4_xboole_0(X0,X1),k1_xboole_0) = k4_xboole_0(X0,X1) ),
% 11.41/2.01      inference(light_normalisation,[status(thm)],[c_511,c_7]) ).
% 11.41/2.01  
% 11.41/2.01  cnf(c_39255,plain,
% 11.41/2.01      ( k4_xboole_0(sK1,k4_xboole_0(sK1,sK0)) != k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) ),
% 11.41/2.01      inference(demodulation,[status(thm)],[c_39254,c_192,c_520]) ).
% 11.41/2.01  
% 11.41/2.01  cnf(c_266,plain,
% 11.41/2.01      ( k4_xboole_0(sK1,k4_xboole_0(sK1,sK0)) = k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) ),
% 11.41/2.01      inference(instantiation,[status(thm)],[c_1]) ).
% 11.41/2.01  
% 11.41/2.01  cnf(contradiction,plain,
% 11.41/2.01      ( $false ),
% 11.41/2.01      inference(minisat,[status(thm)],[c_39255,c_266]) ).
% 11.41/2.01  
% 11.41/2.01  
% 11.41/2.01  % SZS output end CNFRefutation for theBenchmark.p
% 11.41/2.01  
% 11.41/2.01  ------                               Statistics
% 11.41/2.01  
% 11.41/2.01  ------ General
% 11.41/2.01  
% 11.41/2.01  abstr_ref_over_cycles:                  0
% 11.41/2.01  abstr_ref_under_cycles:                 0
% 11.41/2.01  gc_basic_clause_elim:                   0
% 11.41/2.01  forced_gc_time:                         0
% 11.41/2.01  parsing_time:                           0.006
% 11.41/2.01  unif_index_cands_time:                  0.
% 11.41/2.01  unif_index_add_time:                    0.
% 11.41/2.01  orderings_time:                         0.
% 11.41/2.01  out_proof_time:                         0.007
% 11.41/2.01  total_time:                             1.04
% 11.41/2.01  num_of_symbols:                         39
% 11.41/2.01  num_of_terms:                           56511
% 11.41/2.01  
% 11.41/2.01  ------ Preprocessing
% 11.41/2.01  
% 11.41/2.01  num_of_splits:                          0
% 11.41/2.01  num_of_split_atoms:                     2
% 11.41/2.01  num_of_reused_defs:                     3
% 11.41/2.01  num_eq_ax_congr_red:                    2
% 11.41/2.01  num_of_sem_filtered_clauses:            0
% 11.41/2.01  num_of_subtypes:                        0
% 11.41/2.01  monotx_restored_types:                  0
% 11.41/2.01  sat_num_of_epr_types:                   0
% 11.41/2.01  sat_num_of_non_cyclic_types:            0
% 11.41/2.01  sat_guarded_non_collapsed_types:        0
% 11.41/2.01  num_pure_diseq_elim:                    0
% 11.41/2.01  simp_replaced_by:                       0
% 11.41/2.01  res_preprocessed:                       38
% 11.41/2.01  prep_upred:                             0
% 11.41/2.01  prep_unflattend:                        0
% 11.41/2.01  smt_new_axioms:                         0
% 11.41/2.01  pred_elim_cands:                        0
% 11.41/2.01  pred_elim:                              1
% 11.41/2.01  pred_elim_cl:                           1
% 11.41/2.01  pred_elim_cycles:                       2
% 11.41/2.01  merged_defs:                            0
% 11.41/2.01  merged_defs_ncl:                        0
% 11.41/2.01  bin_hyper_res:                          0
% 11.41/2.01  prep_cycles:                            3
% 11.41/2.01  pred_elim_time:                         0.
% 11.41/2.01  splitting_time:                         0.
% 11.41/2.01  sem_filter_time:                        0.
% 11.41/2.01  monotx_time:                            0.
% 11.41/2.01  subtype_inf_time:                       0.
% 11.41/2.01  
% 11.41/2.01  ------ Problem properties
% 11.41/2.01  
% 11.41/2.01  clauses:                                11
% 11.41/2.01  conjectures:                            1
% 11.41/2.01  epr:                                    0
% 11.41/2.01  horn:                                   11
% 11.41/2.01  ground:                                 1
% 11.41/2.01  unary:                                  10
% 11.41/2.01  binary:                                 1
% 11.41/2.01  lits:                                   12
% 11.41/2.01  lits_eq:                                12
% 11.41/2.01  fd_pure:                                0
% 11.41/2.01  fd_pseudo:                              0
% 11.41/2.01  fd_cond:                                0
% 11.41/2.01  fd_pseudo_cond:                         0
% 11.41/2.01  ac_symbols:                             0
% 11.41/2.01  
% 11.41/2.01  ------ Propositional Solver
% 11.41/2.01  
% 11.41/2.01  prop_solver_calls:                      30
% 11.41/2.01  prop_fast_solver_calls:                 290
% 11.41/2.01  smt_solver_calls:                       0
% 11.41/2.01  smt_fast_solver_calls:                  0
% 11.41/2.01  prop_num_of_clauses:                    7786
% 11.41/2.01  prop_preprocess_simplified:             8033
% 11.41/2.01  prop_fo_subsumed:                       0
% 11.41/2.01  prop_solver_time:                       0.
% 11.41/2.01  smt_solver_time:                        0.
% 11.41/2.01  smt_fast_solver_time:                   0.
% 11.41/2.01  prop_fast_solver_time:                  0.
% 11.41/2.01  prop_unsat_core_time:                   0.
% 11.41/2.01  
% 11.41/2.01  ------ QBF
% 11.41/2.01  
% 11.41/2.01  qbf_q_res:                              0
% 11.41/2.01  qbf_num_tautologies:                    0
% 11.41/2.01  qbf_prep_cycles:                        0
% 11.41/2.01  
% 11.41/2.01  ------ BMC1
% 11.41/2.01  
% 11.41/2.01  bmc1_current_bound:                     -1
% 11.41/2.01  bmc1_last_solved_bound:                 -1
% 11.41/2.01  bmc1_unsat_core_size:                   -1
% 11.41/2.01  bmc1_unsat_core_parents_size:           -1
% 11.41/2.01  bmc1_merge_next_fun:                    0
% 11.41/2.01  bmc1_unsat_core_clauses_time:           0.
% 11.41/2.01  
% 11.41/2.01  ------ Instantiation
% 11.41/2.01  
% 11.41/2.01  inst_num_of_clauses:                    2249
% 11.41/2.01  inst_num_in_passive:                    588
% 11.41/2.01  inst_num_in_active:                     715
% 11.41/2.01  inst_num_in_unprocessed:                946
% 11.41/2.01  inst_num_of_loops:                      760
% 11.41/2.01  inst_num_of_learning_restarts:          0
% 11.41/2.01  inst_num_moves_active_passive:          39
% 11.41/2.01  inst_lit_activity:                      0
% 11.41/2.01  inst_lit_activity_moves:                0
% 11.41/2.01  inst_num_tautologies:                   0
% 11.41/2.01  inst_num_prop_implied:                  0
% 11.41/2.01  inst_num_existing_simplified:           0
% 11.41/2.01  inst_num_eq_res_simplified:             0
% 11.41/2.01  inst_num_child_elim:                    0
% 11.41/2.01  inst_num_of_dismatching_blockings:      1207
% 11.41/2.01  inst_num_of_non_proper_insts:           3646
% 11.41/2.01  inst_num_of_duplicates:                 0
% 11.41/2.01  inst_inst_num_from_inst_to_res:         0
% 11.41/2.01  inst_dismatching_checking_time:         0.
% 11.41/2.01  
% 11.41/2.01  ------ Resolution
% 11.41/2.01  
% 11.41/2.01  res_num_of_clauses:                     0
% 11.41/2.01  res_num_in_passive:                     0
% 11.41/2.01  res_num_in_active:                      0
% 11.41/2.01  res_num_of_loops:                       41
% 11.41/2.01  res_forward_subset_subsumed:            728
% 11.41/2.01  res_backward_subset_subsumed:           12
% 11.41/2.01  res_forward_subsumed:                   0
% 11.41/2.01  res_backward_subsumed:                  0
% 11.41/2.01  res_forward_subsumption_resolution:     0
% 11.41/2.01  res_backward_subsumption_resolution:    0
% 11.41/2.01  res_clause_to_clause_subsumption:       71201
% 11.41/2.01  res_orphan_elimination:                 0
% 11.41/2.01  res_tautology_del:                      541
% 11.41/2.01  res_num_eq_res_simplified:              0
% 11.41/2.01  res_num_sel_changes:                    0
% 11.41/2.01  res_moves_from_active_to_pass:          0
% 11.41/2.01  
% 11.41/2.01  ------ Superposition
% 11.41/2.01  
% 11.41/2.01  sup_time_total:                         0.
% 11.41/2.01  sup_time_generating:                    0.
% 11.41/2.01  sup_time_sim_full:                      0.
% 11.41/2.01  sup_time_sim_immed:                     0.
% 11.41/2.01  
% 11.41/2.01  sup_num_of_clauses:                     2892
% 11.41/2.01  sup_num_in_active:                      131
% 11.41/2.01  sup_num_in_passive:                     2761
% 11.41/2.01  sup_num_of_loops:                       151
% 11.41/2.01  sup_fw_superposition:                   11062
% 11.41/2.01  sup_bw_superposition:                   7981
% 11.41/2.01  sup_immediate_simplified:               8669
% 11.41/2.01  sup_given_eliminated:                   5
% 11.41/2.01  comparisons_done:                       0
% 11.41/2.01  comparisons_avoided:                    0
% 11.41/2.01  
% 11.41/2.01  ------ Simplifications
% 11.41/2.01  
% 11.41/2.01  
% 11.41/2.01  sim_fw_subset_subsumed:                 5
% 11.41/2.01  sim_bw_subset_subsumed:                 0
% 11.41/2.01  sim_fw_subsumed:                        1533
% 11.41/2.01  sim_bw_subsumed:                        34
% 11.41/2.01  sim_fw_subsumption_res:                 0
% 11.41/2.01  sim_bw_subsumption_res:                 0
% 11.41/2.01  sim_tautology_del:                      17
% 11.41/2.01  sim_eq_tautology_del:                   2427
% 11.41/2.01  sim_eq_res_simp:                        5
% 11.41/2.01  sim_fw_demodulated:                     5075
% 11.41/2.01  sim_bw_demodulated:                     73
% 11.41/2.01  sim_light_normalised:                   3528
% 11.41/2.01  sim_joinable_taut:                      0
% 11.41/2.01  sim_joinable_simp:                      0
% 11.41/2.01  sim_ac_normalised:                      0
% 11.41/2.01  sim_smt_subsumption:                    0
% 11.41/2.01  
%------------------------------------------------------------------------------
