%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:28:35 EST 2020

% Result     : Theorem 10.85s
% Output     : CNFRefutation 10.85s
% Verified   : 
% Statistics : Number of formulae       :   57 ( 254 expanded)
%              Number of clauses        :   19 (  30 expanded)
%              Number of leaves         :   13 (  84 expanded)
%              Depth                    :   13
%              Number of atoms          :   58 ( 255 expanded)
%              Number of equality atoms :   57 ( 254 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal clause size      :    2 (   1 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f13,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k1_enumset1(X0,X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k1_enumset1(X0,X2,X1) ),
    inference(cnf_transformation,[],[f13])).

fof(f8,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f8])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f9])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f10])).

fof(f33,plain,(
    ! [X2,X0,X3,X1] : k4_enumset1(X0,X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f27,f28])).

fof(f34,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k4_enumset1(X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f26,f33])).

fof(f43,plain,(
    ! [X2,X0,X1] : k4_enumset1(X0,X0,X0,X0,X1,X2) = k4_enumset1(X0,X0,X0,X0,X2,X1) ),
    inference(definition_unfolding,[],[f31,f34,f34])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f11])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k2_tarski(X5,X6)) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k2_tarski(X5,X6)) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f5])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f1])).

fof(f7,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f7])).

fof(f35,plain,(
    ! [X0,X1] : k4_enumset1(X0,X0,X0,X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(definition_unfolding,[],[f25,f34])).

fof(f37,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_xboole_0(k4_enumset1(X0,X0,X1,X2,X3,X4),k4_xboole_0(k4_enumset1(X5,X5,X5,X5,X5,X6),k4_enumset1(X0,X0,X1,X2,X3,X4))) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    inference(definition_unfolding,[],[f23,f19,f28,f35])).

fof(f41,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k5_xboole_0(k4_enumset1(X0,X0,X0,X1,X2,X3),k4_xboole_0(k4_enumset1(X4,X4,X4,X4,X4,X5),k4_enumset1(X0,X0,X0,X1,X2,X3))) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f29,f37])).

fof(f4,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k1_tarski(X5)) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k1_tarski(X5)) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f4])).

fof(f6,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f36,plain,(
    ! [X0] : k4_enumset1(X0,X0,X0,X0,X0,X0) = k1_tarski(X0) ),
    inference(definition_unfolding,[],[f24,f35])).

fof(f38,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k5_xboole_0(k4_enumset1(X0,X0,X1,X2,X3,X4),k4_xboole_0(k4_enumset1(X5,X5,X5,X5,X5,X5),k4_enumset1(X0,X0,X1,X2,X3,X4))) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f22,f19,f28,f36])).

fof(f2,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k1_enumset1(X1,X2,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k1_enumset1(X1,X2,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f39,plain,(
    ! [X2,X0,X1] : k4_enumset1(X0,X0,X0,X0,X1,X2) = k4_enumset1(X1,X1,X1,X1,X2,X0) ),
    inference(definition_unfolding,[],[f20,f34,f34])).

fof(f14,conjecture,(
    ! [X0,X1,X2] : k2_xboole_0(k2_tarski(X1,X0),k2_tarski(X2,X0)) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,negated_conjecture,(
    ~ ! [X0,X1,X2] : k2_xboole_0(k2_tarski(X1,X0),k2_tarski(X2,X0)) = k1_enumset1(X0,X1,X2) ),
    inference(negated_conjecture,[],[f14])).

fof(f16,plain,(
    ? [X0,X1,X2] : k2_xboole_0(k2_tarski(X1,X0),k2_tarski(X2,X0)) != k1_enumset1(X0,X1,X2) ),
    inference(ennf_transformation,[],[f15])).

fof(f17,plain,
    ( ? [X0,X1,X2] : k2_xboole_0(k2_tarski(X1,X0),k2_tarski(X2,X0)) != k1_enumset1(X0,X1,X2)
   => k2_xboole_0(k2_tarski(sK1,sK0),k2_tarski(sK2,sK0)) != k1_enumset1(sK0,sK1,sK2) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    k2_xboole_0(k2_tarski(sK1,sK0),k2_tarski(sK2,sK0)) != k1_enumset1(sK0,sK1,sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f16,f17])).

fof(f32,plain,(
    k2_xboole_0(k2_tarski(sK1,sK0),k2_tarski(sK2,sK0)) != k1_enumset1(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f18])).

fof(f44,plain,(
    k5_xboole_0(k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK0),k4_xboole_0(k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK0),k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK0))) != k4_enumset1(sK0,sK0,sK0,sK0,sK1,sK2) ),
    inference(definition_unfolding,[],[f32,f19,f35,f35,f34])).

cnf(c_5,plain,
    ( k4_enumset1(X0,X0,X0,X0,X1,X2) = k4_enumset1(X0,X0,X0,X0,X2,X1) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_16,plain,
    ( k4_enumset1(X0_37,X0_37,X0_37,X0_37,X1_37,X2_37) = k4_enumset1(X0_37,X0_37,X0_37,X0_37,X2_37,X1_37) ),
    inference(subtyping,[status(esa)],[c_5])).

cnf(c_3,plain,
    ( k5_xboole_0(k4_enumset1(X0,X0,X0,X1,X2,X3),k4_xboole_0(k4_enumset1(X4,X4,X4,X4,X4,X5),k4_enumset1(X0,X0,X0,X1,X2,X3))) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_18,plain,
    ( k5_xboole_0(k4_enumset1(X0_37,X0_37,X0_37,X1_37,X2_37,X3_37),k4_xboole_0(k4_enumset1(X4_37,X4_37,X4_37,X4_37,X4_37,X5_37),k4_enumset1(X0_37,X0_37,X0_37,X1_37,X2_37,X3_37))) = k4_enumset1(X0_37,X1_37,X2_37,X3_37,X4_37,X5_37) ),
    inference(subtyping,[status(esa)],[c_3])).

cnf(c_142,plain,
    ( k5_xboole_0(k4_enumset1(X0_37,X0_37,X0_37,X0_37,X1_37,X2_37),k4_xboole_0(k4_enumset1(X3_37,X3_37,X3_37,X3_37,X3_37,X4_37),k4_enumset1(X0_37,X0_37,X0_37,X0_37,X1_37,X2_37))) = k4_enumset1(X0_37,X0_37,X2_37,X1_37,X3_37,X4_37) ),
    inference(superposition,[status(thm)],[c_16,c_18])).

cnf(c_0,plain,
    ( k5_xboole_0(k4_enumset1(X0,X0,X1,X2,X3,X4),k4_xboole_0(k4_enumset1(X5,X5,X5,X5,X5,X5),k4_enumset1(X0,X0,X1,X2,X3,X4))) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_21,plain,
    ( k5_xboole_0(k4_enumset1(X0_37,X0_37,X1_37,X2_37,X3_37,X4_37),k4_xboole_0(k4_enumset1(X5_37,X5_37,X5_37,X5_37,X5_37,X5_37),k4_enumset1(X0_37,X0_37,X1_37,X2_37,X3_37,X4_37))) = k4_enumset1(X0_37,X1_37,X2_37,X3_37,X4_37,X5_37) ),
    inference(subtyping,[status(esa)],[c_0])).

cnf(c_2124,plain,
    ( k4_enumset1(X0_37,X0_37,X1_37,X2_37,X3_37,X3_37) = k4_enumset1(X0_37,X0_37,X0_37,X2_37,X1_37,X3_37) ),
    inference(superposition,[status(thm)],[c_142,c_21])).

cnf(c_206,plain,
    ( k4_enumset1(X0_37,X1_37,X2_37,X3_37,X4_37,X4_37) = k4_enumset1(X0_37,X0_37,X1_37,X2_37,X3_37,X4_37) ),
    inference(superposition,[status(thm)],[c_21,c_18])).

cnf(c_260,plain,
    ( k4_enumset1(X0_37,X1_37,X2_37,X3_37,X3_37,X3_37) = k4_enumset1(X0_37,X0_37,X0_37,X1_37,X2_37,X3_37) ),
    inference(superposition,[status(thm)],[c_206,c_206])).

cnf(c_2350,plain,
    ( k4_enumset1(X0_37,X0_37,X0_37,X1_37,X2_37,X1_37) = k4_enumset1(X0_37,X0_37,X0_37,X0_37,X2_37,X1_37) ),
    inference(superposition,[status(thm)],[c_2124,c_260])).

cnf(c_1,plain,
    ( k4_enumset1(X0,X0,X0,X0,X1,X2) = k4_enumset1(X2,X2,X2,X2,X0,X1) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_20,plain,
    ( k4_enumset1(X0_37,X0_37,X0_37,X0_37,X1_37,X2_37) = k4_enumset1(X2_37,X2_37,X2_37,X2_37,X0_37,X1_37) ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_6,negated_conjecture,
    ( k5_xboole_0(k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK0),k4_xboole_0(k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK0),k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK0))) != k4_enumset1(sK0,sK0,sK0,sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_15,negated_conjecture,
    ( k5_xboole_0(k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK0),k4_xboole_0(k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK0),k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK0))) != k4_enumset1(sK0,sK0,sK0,sK0,sK1,sK2) ),
    inference(subtyping,[status(esa)],[c_6])).

cnf(c_34,plain,
    ( k4_enumset1(sK1,sK1,sK1,sK0,sK2,sK0) != k4_enumset1(sK0,sK0,sK0,sK0,sK1,sK2) ),
    inference(demodulation,[status(thm)],[c_15,c_18])).

cnf(c_43,plain,
    ( k4_enumset1(sK1,sK1,sK1,sK1,sK2,sK0) != k4_enumset1(sK1,sK1,sK1,sK0,sK2,sK0) ),
    inference(demodulation,[status(thm)],[c_20,c_34])).

cnf(c_32073,plain,
    ( k4_enumset1(sK1,sK1,sK1,sK1,sK2,sK0) != k4_enumset1(sK1,sK1,sK1,sK1,sK2,sK0) ),
    inference(demodulation,[status(thm)],[c_2350,c_43])).

cnf(c_32588,plain,
    ( $false ),
    inference(equality_resolution_simp,[status(thm)],[c_32073])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 15:20:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  % Running in FOF mode
% 10.85/2.01  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 10.85/2.01  
% 10.85/2.01  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 10.85/2.01  
% 10.85/2.01  ------  iProver source info
% 10.85/2.01  
% 10.85/2.01  git: date: 2020-06-30 10:37:57 +0100
% 10.85/2.01  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 10.85/2.01  git: non_committed_changes: false
% 10.85/2.01  git: last_make_outside_of_git: false
% 10.85/2.01  
% 10.85/2.01  ------ 
% 10.85/2.01  
% 10.85/2.01  ------ Input Options
% 10.85/2.01  
% 10.85/2.01  --out_options                           all
% 10.85/2.01  --tptp_safe_out                         true
% 10.85/2.01  --problem_path                          ""
% 10.85/2.01  --include_path                          ""
% 10.85/2.01  --clausifier                            res/vclausify_rel
% 10.85/2.01  --clausifier_options                    --mode clausify
% 10.85/2.01  --stdin                                 false
% 10.85/2.01  --stats_out                             all
% 10.85/2.01  
% 10.85/2.01  ------ General Options
% 10.85/2.01  
% 10.85/2.01  --fof                                   false
% 10.85/2.01  --time_out_real                         305.
% 10.85/2.01  --time_out_virtual                      -1.
% 10.85/2.01  --symbol_type_check                     false
% 10.85/2.01  --clausify_out                          false
% 10.85/2.01  --sig_cnt_out                           false
% 10.85/2.01  --trig_cnt_out                          false
% 10.85/2.01  --trig_cnt_out_tolerance                1.
% 10.85/2.01  --trig_cnt_out_sk_spl                   false
% 10.85/2.01  --abstr_cl_out                          false
% 10.85/2.01  
% 10.85/2.01  ------ Global Options
% 10.85/2.01  
% 10.85/2.01  --schedule                              default
% 10.85/2.01  --add_important_lit                     false
% 10.85/2.01  --prop_solver_per_cl                    1000
% 10.85/2.01  --min_unsat_core                        false
% 10.85/2.01  --soft_assumptions                      false
% 10.85/2.01  --soft_lemma_size                       3
% 10.85/2.01  --prop_impl_unit_size                   0
% 10.85/2.01  --prop_impl_unit                        []
% 10.85/2.01  --share_sel_clauses                     true
% 10.85/2.01  --reset_solvers                         false
% 10.85/2.01  --bc_imp_inh                            [conj_cone]
% 10.85/2.01  --conj_cone_tolerance                   3.
% 10.85/2.01  --extra_neg_conj                        none
% 10.85/2.01  --large_theory_mode                     true
% 10.85/2.01  --prolific_symb_bound                   200
% 10.85/2.01  --lt_threshold                          2000
% 10.85/2.01  --clause_weak_htbl                      true
% 10.85/2.01  --gc_record_bc_elim                     false
% 10.85/2.01  
% 10.85/2.01  ------ Preprocessing Options
% 10.85/2.01  
% 10.85/2.01  --preprocessing_flag                    true
% 10.85/2.01  --time_out_prep_mult                    0.1
% 10.85/2.01  --splitting_mode                        input
% 10.85/2.01  --splitting_grd                         true
% 10.85/2.01  --splitting_cvd                         false
% 10.85/2.01  --splitting_cvd_svl                     false
% 10.85/2.01  --splitting_nvd                         32
% 10.85/2.01  --sub_typing                            true
% 10.85/2.01  --prep_gs_sim                           true
% 10.85/2.01  --prep_unflatten                        true
% 10.85/2.01  --prep_res_sim                          true
% 10.85/2.01  --prep_upred                            true
% 10.85/2.01  --prep_sem_filter                       exhaustive
% 10.85/2.01  --prep_sem_filter_out                   false
% 10.85/2.01  --pred_elim                             true
% 10.85/2.01  --res_sim_input                         true
% 10.85/2.01  --eq_ax_congr_red                       true
% 10.85/2.01  --pure_diseq_elim                       true
% 10.85/2.01  --brand_transform                       false
% 10.85/2.01  --non_eq_to_eq                          false
% 10.85/2.01  --prep_def_merge                        true
% 10.85/2.01  --prep_def_merge_prop_impl              false
% 10.85/2.01  --prep_def_merge_mbd                    true
% 10.85/2.01  --prep_def_merge_tr_red                 false
% 10.85/2.01  --prep_def_merge_tr_cl                  false
% 10.85/2.01  --smt_preprocessing                     true
% 10.85/2.01  --smt_ac_axioms                         fast
% 10.85/2.01  --preprocessed_out                      false
% 10.85/2.01  --preprocessed_stats                    false
% 10.85/2.01  
% 10.85/2.01  ------ Abstraction refinement Options
% 10.85/2.01  
% 10.85/2.01  --abstr_ref                             []
% 10.85/2.01  --abstr_ref_prep                        false
% 10.85/2.01  --abstr_ref_until_sat                   false
% 10.85/2.01  --abstr_ref_sig_restrict                funpre
% 10.85/2.01  --abstr_ref_af_restrict_to_split_sk     false
% 10.85/2.01  --abstr_ref_under                       []
% 10.85/2.01  
% 10.85/2.01  ------ SAT Options
% 10.85/2.01  
% 10.85/2.01  --sat_mode                              false
% 10.85/2.01  --sat_fm_restart_options                ""
% 10.85/2.01  --sat_gr_def                            false
% 10.85/2.01  --sat_epr_types                         true
% 10.85/2.01  --sat_non_cyclic_types                  false
% 10.85/2.01  --sat_finite_models                     false
% 10.85/2.01  --sat_fm_lemmas                         false
% 10.85/2.01  --sat_fm_prep                           false
% 10.85/2.01  --sat_fm_uc_incr                        true
% 10.85/2.01  --sat_out_model                         small
% 10.85/2.01  --sat_out_clauses                       false
% 10.85/2.01  
% 10.85/2.01  ------ QBF Options
% 10.85/2.01  
% 10.85/2.01  --qbf_mode                              false
% 10.85/2.01  --qbf_elim_univ                         false
% 10.85/2.01  --qbf_dom_inst                          none
% 10.85/2.01  --qbf_dom_pre_inst                      false
% 10.85/2.01  --qbf_sk_in                             false
% 10.85/2.01  --qbf_pred_elim                         true
% 10.85/2.01  --qbf_split                             512
% 10.85/2.01  
% 10.85/2.01  ------ BMC1 Options
% 10.85/2.01  
% 10.85/2.01  --bmc1_incremental                      false
% 10.85/2.01  --bmc1_axioms                           reachable_all
% 10.85/2.01  --bmc1_min_bound                        0
% 10.85/2.01  --bmc1_max_bound                        -1
% 10.85/2.01  --bmc1_max_bound_default                -1
% 10.85/2.01  --bmc1_symbol_reachability              true
% 10.85/2.01  --bmc1_property_lemmas                  false
% 10.85/2.01  --bmc1_k_induction                      false
% 10.85/2.01  --bmc1_non_equiv_states                 false
% 10.85/2.01  --bmc1_deadlock                         false
% 10.85/2.01  --bmc1_ucm                              false
% 10.85/2.01  --bmc1_add_unsat_core                   none
% 10.85/2.01  --bmc1_unsat_core_children              false
% 10.85/2.01  --bmc1_unsat_core_extrapolate_axioms    false
% 10.85/2.01  --bmc1_out_stat                         full
% 10.85/2.01  --bmc1_ground_init                      false
% 10.85/2.01  --bmc1_pre_inst_next_state              false
% 10.85/2.01  --bmc1_pre_inst_state                   false
% 10.85/2.01  --bmc1_pre_inst_reach_state             false
% 10.85/2.01  --bmc1_out_unsat_core                   false
% 10.85/2.01  --bmc1_aig_witness_out                  false
% 10.85/2.01  --bmc1_verbose                          false
% 10.85/2.01  --bmc1_dump_clauses_tptp                false
% 10.85/2.01  --bmc1_dump_unsat_core_tptp             false
% 10.85/2.01  --bmc1_dump_file                        -
% 10.85/2.01  --bmc1_ucm_expand_uc_limit              128
% 10.85/2.01  --bmc1_ucm_n_expand_iterations          6
% 10.85/2.01  --bmc1_ucm_extend_mode                  1
% 10.85/2.01  --bmc1_ucm_init_mode                    2
% 10.85/2.01  --bmc1_ucm_cone_mode                    none
% 10.85/2.01  --bmc1_ucm_reduced_relation_type        0
% 10.85/2.01  --bmc1_ucm_relax_model                  4
% 10.85/2.01  --bmc1_ucm_full_tr_after_sat            true
% 10.85/2.01  --bmc1_ucm_expand_neg_assumptions       false
% 10.85/2.01  --bmc1_ucm_layered_model                none
% 10.85/2.01  --bmc1_ucm_max_lemma_size               10
% 10.85/2.01  
% 10.85/2.01  ------ AIG Options
% 10.85/2.01  
% 10.85/2.01  --aig_mode                              false
% 10.85/2.01  
% 10.85/2.01  ------ Instantiation Options
% 10.85/2.01  
% 10.85/2.01  --instantiation_flag                    true
% 10.85/2.01  --inst_sos_flag                         false
% 10.85/2.01  --inst_sos_phase                        true
% 10.85/2.01  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 10.85/2.01  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 10.85/2.01  --inst_lit_sel_side                     num_symb
% 10.85/2.01  --inst_solver_per_active                1400
% 10.85/2.01  --inst_solver_calls_frac                1.
% 10.85/2.01  --inst_passive_queue_type               priority_queues
% 10.85/2.01  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 10.85/2.01  --inst_passive_queues_freq              [25;2]
% 10.85/2.01  --inst_dismatching                      true
% 10.85/2.01  --inst_eager_unprocessed_to_passive     true
% 10.85/2.01  --inst_prop_sim_given                   true
% 10.85/2.01  --inst_prop_sim_new                     false
% 10.85/2.01  --inst_subs_new                         false
% 10.85/2.01  --inst_eq_res_simp                      false
% 10.85/2.01  --inst_subs_given                       false
% 10.85/2.01  --inst_orphan_elimination               true
% 10.85/2.01  --inst_learning_loop_flag               true
% 10.85/2.01  --inst_learning_start                   3000
% 10.85/2.01  --inst_learning_factor                  2
% 10.85/2.01  --inst_start_prop_sim_after_learn       3
% 10.85/2.01  --inst_sel_renew                        solver
% 10.85/2.01  --inst_lit_activity_flag                true
% 10.85/2.01  --inst_restr_to_given                   false
% 10.85/2.01  --inst_activity_threshold               500
% 10.85/2.01  --inst_out_proof                        true
% 10.85/2.01  
% 10.85/2.01  ------ Resolution Options
% 10.85/2.01  
% 10.85/2.01  --resolution_flag                       true
% 10.85/2.01  --res_lit_sel                           adaptive
% 10.85/2.01  --res_lit_sel_side                      none
% 10.85/2.01  --res_ordering                          kbo
% 10.85/2.01  --res_to_prop_solver                    active
% 10.85/2.01  --res_prop_simpl_new                    false
% 10.85/2.01  --res_prop_simpl_given                  true
% 10.85/2.01  --res_passive_queue_type                priority_queues
% 10.85/2.01  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 10.85/2.01  --res_passive_queues_freq               [15;5]
% 10.85/2.01  --res_forward_subs                      full
% 10.85/2.01  --res_backward_subs                     full
% 10.85/2.01  --res_forward_subs_resolution           true
% 10.85/2.01  --res_backward_subs_resolution          true
% 10.85/2.01  --res_orphan_elimination                true
% 10.85/2.01  --res_time_limit                        2.
% 10.85/2.01  --res_out_proof                         true
% 10.85/2.01  
% 10.85/2.01  ------ Superposition Options
% 10.85/2.01  
% 10.85/2.01  --superposition_flag                    true
% 10.85/2.01  --sup_passive_queue_type                priority_queues
% 10.85/2.01  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 10.85/2.01  --sup_passive_queues_freq               [8;1;4]
% 10.85/2.01  --demod_completeness_check              fast
% 10.85/2.01  --demod_use_ground                      true
% 10.85/2.01  --sup_to_prop_solver                    passive
% 10.85/2.01  --sup_prop_simpl_new                    true
% 10.85/2.01  --sup_prop_simpl_given                  true
% 10.85/2.01  --sup_fun_splitting                     false
% 10.85/2.01  --sup_smt_interval                      50000
% 10.85/2.01  
% 10.85/2.01  ------ Superposition Simplification Setup
% 10.85/2.01  
% 10.85/2.01  --sup_indices_passive                   []
% 10.85/2.01  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 10.85/2.01  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 10.85/2.01  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 10.85/2.01  --sup_full_triv                         [TrivRules;PropSubs]
% 10.85/2.01  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 10.85/2.01  --sup_full_bw                           [BwDemod]
% 10.85/2.01  --sup_immed_triv                        [TrivRules]
% 10.85/2.01  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 10.85/2.01  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 10.85/2.01  --sup_immed_bw_main                     []
% 10.85/2.01  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 10.85/2.01  --sup_input_triv                        [Unflattening;TrivRules]
% 10.85/2.01  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 10.85/2.01  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 10.85/2.01  
% 10.85/2.01  ------ Combination Options
% 10.85/2.01  
% 10.85/2.01  --comb_res_mult                         3
% 10.85/2.01  --comb_sup_mult                         2
% 10.85/2.01  --comb_inst_mult                        10
% 10.85/2.01  
% 10.85/2.01  ------ Debug Options
% 10.85/2.01  
% 10.85/2.01  --dbg_backtrace                         false
% 10.85/2.01  --dbg_dump_prop_clauses                 false
% 10.85/2.01  --dbg_dump_prop_clauses_file            -
% 10.85/2.01  --dbg_out_stat                          false
% 10.85/2.01  ------ Parsing...
% 10.85/2.01  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 10.85/2.01  
% 10.85/2.01  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  pe_s  pe_e 
% 10.85/2.01  
% 10.85/2.01  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 10.85/2.01  
% 10.85/2.01  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 10.85/2.01  ------ Proving...
% 10.85/2.01  ------ Problem Properties 
% 10.85/2.01  
% 10.85/2.01  
% 10.85/2.01  clauses                                 7
% 10.85/2.01  conjectures                             1
% 10.85/2.01  EPR                                     0
% 10.85/2.01  Horn                                    7
% 10.85/2.01  unary                                   7
% 10.85/2.01  binary                                  0
% 10.85/2.01  lits                                    7
% 10.85/2.01  lits eq                                 7
% 10.85/2.01  fd_pure                                 0
% 10.85/2.01  fd_pseudo                               0
% 10.85/2.01  fd_cond                                 0
% 10.85/2.01  fd_pseudo_cond                          0
% 10.85/2.01  AC symbols                              0
% 10.85/2.01  
% 10.85/2.01  ------ Schedule UEQ
% 10.85/2.01  
% 10.85/2.01  ------ pure equality problem: resolution off 
% 10.85/2.01  
% 10.85/2.01  ------ Option_UEQ Time Limit: Unbounded
% 10.85/2.01  
% 10.85/2.01  
% 10.85/2.01  ------ 
% 10.85/2.01  Current options:
% 10.85/2.01  ------ 
% 10.85/2.01  
% 10.85/2.01  ------ Input Options
% 10.85/2.01  
% 10.85/2.01  --out_options                           all
% 10.85/2.01  --tptp_safe_out                         true
% 10.85/2.01  --problem_path                          ""
% 10.85/2.01  --include_path                          ""
% 10.85/2.01  --clausifier                            res/vclausify_rel
% 10.85/2.01  --clausifier_options                    --mode clausify
% 10.85/2.01  --stdin                                 false
% 10.85/2.01  --stats_out                             all
% 10.85/2.01  
% 10.85/2.01  ------ General Options
% 10.85/2.01  
% 10.85/2.01  --fof                                   false
% 10.85/2.01  --time_out_real                         305.
% 10.85/2.01  --time_out_virtual                      -1.
% 10.85/2.01  --symbol_type_check                     false
% 10.85/2.01  --clausify_out                          false
% 10.85/2.01  --sig_cnt_out                           false
% 10.85/2.01  --trig_cnt_out                          false
% 10.85/2.01  --trig_cnt_out_tolerance                1.
% 10.85/2.01  --trig_cnt_out_sk_spl                   false
% 10.85/2.01  --abstr_cl_out                          false
% 10.85/2.01  
% 10.85/2.01  ------ Global Options
% 10.85/2.01  
% 10.85/2.01  --schedule                              default
% 10.85/2.01  --add_important_lit                     false
% 10.85/2.01  --prop_solver_per_cl                    1000
% 10.85/2.01  --min_unsat_core                        false
% 10.85/2.01  --soft_assumptions                      false
% 10.85/2.01  --soft_lemma_size                       3
% 10.85/2.01  --prop_impl_unit_size                   0
% 10.85/2.01  --prop_impl_unit                        []
% 10.85/2.01  --share_sel_clauses                     true
% 10.85/2.01  --reset_solvers                         false
% 10.85/2.01  --bc_imp_inh                            [conj_cone]
% 10.85/2.01  --conj_cone_tolerance                   3.
% 10.85/2.01  --extra_neg_conj                        none
% 10.85/2.01  --large_theory_mode                     true
% 10.85/2.01  --prolific_symb_bound                   200
% 10.85/2.01  --lt_threshold                          2000
% 10.85/2.01  --clause_weak_htbl                      true
% 10.85/2.01  --gc_record_bc_elim                     false
% 10.85/2.01  
% 10.85/2.01  ------ Preprocessing Options
% 10.85/2.01  
% 10.85/2.01  --preprocessing_flag                    true
% 10.85/2.01  --time_out_prep_mult                    0.1
% 10.85/2.01  --splitting_mode                        input
% 10.85/2.01  --splitting_grd                         true
% 10.85/2.01  --splitting_cvd                         false
% 10.85/2.01  --splitting_cvd_svl                     false
% 10.85/2.01  --splitting_nvd                         32
% 10.85/2.01  --sub_typing                            true
% 10.85/2.01  --prep_gs_sim                           true
% 10.85/2.01  --prep_unflatten                        true
% 10.85/2.01  --prep_res_sim                          true
% 10.85/2.01  --prep_upred                            true
% 10.85/2.01  --prep_sem_filter                       exhaustive
% 10.85/2.01  --prep_sem_filter_out                   false
% 10.85/2.01  --pred_elim                             true
% 10.85/2.01  --res_sim_input                         true
% 10.85/2.01  --eq_ax_congr_red                       true
% 10.85/2.01  --pure_diseq_elim                       true
% 10.85/2.01  --brand_transform                       false
% 10.85/2.01  --non_eq_to_eq                          false
% 10.85/2.01  --prep_def_merge                        true
% 10.85/2.01  --prep_def_merge_prop_impl              false
% 10.85/2.01  --prep_def_merge_mbd                    true
% 10.85/2.01  --prep_def_merge_tr_red                 false
% 10.85/2.01  --prep_def_merge_tr_cl                  false
% 10.85/2.01  --smt_preprocessing                     true
% 10.85/2.01  --smt_ac_axioms                         fast
% 10.85/2.01  --preprocessed_out                      false
% 10.85/2.01  --preprocessed_stats                    false
% 10.85/2.01  
% 10.85/2.01  ------ Abstraction refinement Options
% 10.85/2.01  
% 10.85/2.01  --abstr_ref                             []
% 10.85/2.01  --abstr_ref_prep                        false
% 10.85/2.01  --abstr_ref_until_sat                   false
% 10.85/2.01  --abstr_ref_sig_restrict                funpre
% 10.85/2.01  --abstr_ref_af_restrict_to_split_sk     false
% 10.85/2.01  --abstr_ref_under                       []
% 10.85/2.01  
% 10.85/2.01  ------ SAT Options
% 10.85/2.01  
% 10.85/2.01  --sat_mode                              false
% 10.85/2.01  --sat_fm_restart_options                ""
% 10.85/2.01  --sat_gr_def                            false
% 10.85/2.01  --sat_epr_types                         true
% 10.85/2.01  --sat_non_cyclic_types                  false
% 10.85/2.01  --sat_finite_models                     false
% 10.85/2.01  --sat_fm_lemmas                         false
% 10.85/2.01  --sat_fm_prep                           false
% 10.85/2.01  --sat_fm_uc_incr                        true
% 10.85/2.01  --sat_out_model                         small
% 10.85/2.01  --sat_out_clauses                       false
% 10.85/2.01  
% 10.85/2.01  ------ QBF Options
% 10.85/2.01  
% 10.85/2.01  --qbf_mode                              false
% 10.85/2.01  --qbf_elim_univ                         false
% 10.85/2.01  --qbf_dom_inst                          none
% 10.85/2.01  --qbf_dom_pre_inst                      false
% 10.85/2.01  --qbf_sk_in                             false
% 10.85/2.01  --qbf_pred_elim                         true
% 10.85/2.01  --qbf_split                             512
% 10.85/2.01  
% 10.85/2.01  ------ BMC1 Options
% 10.85/2.01  
% 10.85/2.01  --bmc1_incremental                      false
% 10.85/2.01  --bmc1_axioms                           reachable_all
% 10.85/2.01  --bmc1_min_bound                        0
% 10.85/2.01  --bmc1_max_bound                        -1
% 10.85/2.01  --bmc1_max_bound_default                -1
% 10.85/2.01  --bmc1_symbol_reachability              true
% 10.85/2.01  --bmc1_property_lemmas                  false
% 10.85/2.01  --bmc1_k_induction                      false
% 10.85/2.01  --bmc1_non_equiv_states                 false
% 10.85/2.01  --bmc1_deadlock                         false
% 10.85/2.01  --bmc1_ucm                              false
% 10.85/2.01  --bmc1_add_unsat_core                   none
% 10.85/2.01  --bmc1_unsat_core_children              false
% 10.85/2.01  --bmc1_unsat_core_extrapolate_axioms    false
% 10.85/2.01  --bmc1_out_stat                         full
% 10.85/2.01  --bmc1_ground_init                      false
% 10.85/2.01  --bmc1_pre_inst_next_state              false
% 10.85/2.01  --bmc1_pre_inst_state                   false
% 10.85/2.01  --bmc1_pre_inst_reach_state             false
% 10.85/2.01  --bmc1_out_unsat_core                   false
% 10.85/2.01  --bmc1_aig_witness_out                  false
% 10.85/2.01  --bmc1_verbose                          false
% 10.85/2.01  --bmc1_dump_clauses_tptp                false
% 10.85/2.01  --bmc1_dump_unsat_core_tptp             false
% 10.85/2.01  --bmc1_dump_file                        -
% 10.85/2.01  --bmc1_ucm_expand_uc_limit              128
% 10.85/2.01  --bmc1_ucm_n_expand_iterations          6
% 10.85/2.01  --bmc1_ucm_extend_mode                  1
% 10.85/2.01  --bmc1_ucm_init_mode                    2
% 10.85/2.01  --bmc1_ucm_cone_mode                    none
% 10.85/2.01  --bmc1_ucm_reduced_relation_type        0
% 10.85/2.01  --bmc1_ucm_relax_model                  4
% 10.85/2.01  --bmc1_ucm_full_tr_after_sat            true
% 10.85/2.01  --bmc1_ucm_expand_neg_assumptions       false
% 10.85/2.01  --bmc1_ucm_layered_model                none
% 10.85/2.01  --bmc1_ucm_max_lemma_size               10
% 10.85/2.01  
% 10.85/2.01  ------ AIG Options
% 10.85/2.01  
% 10.85/2.01  --aig_mode                              false
% 10.85/2.01  
% 10.85/2.01  ------ Instantiation Options
% 10.85/2.01  
% 10.85/2.01  --instantiation_flag                    false
% 10.85/2.01  --inst_sos_flag                         false
% 10.85/2.01  --inst_sos_phase                        true
% 10.85/2.01  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 10.85/2.01  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 10.85/2.01  --inst_lit_sel_side                     num_symb
% 10.85/2.01  --inst_solver_per_active                1400
% 10.85/2.01  --inst_solver_calls_frac                1.
% 10.85/2.01  --inst_passive_queue_type               priority_queues
% 10.85/2.01  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 10.85/2.01  --inst_passive_queues_freq              [25;2]
% 10.85/2.01  --inst_dismatching                      true
% 10.85/2.01  --inst_eager_unprocessed_to_passive     true
% 10.85/2.01  --inst_prop_sim_given                   true
% 10.85/2.01  --inst_prop_sim_new                     false
% 10.85/2.01  --inst_subs_new                         false
% 10.85/2.01  --inst_eq_res_simp                      false
% 10.85/2.01  --inst_subs_given                       false
% 10.85/2.01  --inst_orphan_elimination               true
% 10.85/2.01  --inst_learning_loop_flag               true
% 10.85/2.01  --inst_learning_start                   3000
% 10.85/2.01  --inst_learning_factor                  2
% 10.85/2.01  --inst_start_prop_sim_after_learn       3
% 10.85/2.01  --inst_sel_renew                        solver
% 10.85/2.01  --inst_lit_activity_flag                true
% 10.85/2.01  --inst_restr_to_given                   false
% 10.85/2.01  --inst_activity_threshold               500
% 10.85/2.01  --inst_out_proof                        true
% 10.85/2.01  
% 10.85/2.01  ------ Resolution Options
% 10.85/2.01  
% 10.85/2.01  --resolution_flag                       false
% 10.85/2.01  --res_lit_sel                           adaptive
% 10.85/2.01  --res_lit_sel_side                      none
% 10.85/2.01  --res_ordering                          kbo
% 10.85/2.01  --res_to_prop_solver                    active
% 10.85/2.01  --res_prop_simpl_new                    false
% 10.85/2.01  --res_prop_simpl_given                  true
% 10.85/2.01  --res_passive_queue_type                priority_queues
% 10.85/2.01  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 10.85/2.01  --res_passive_queues_freq               [15;5]
% 10.85/2.01  --res_forward_subs                      full
% 10.85/2.01  --res_backward_subs                     full
% 10.85/2.01  --res_forward_subs_resolution           true
% 10.85/2.01  --res_backward_subs_resolution          true
% 10.85/2.01  --res_orphan_elimination                true
% 10.85/2.01  --res_time_limit                        2.
% 10.85/2.01  --res_out_proof                         true
% 10.85/2.01  
% 10.85/2.01  ------ Superposition Options
% 10.85/2.01  
% 10.85/2.01  --superposition_flag                    true
% 10.85/2.01  --sup_passive_queue_type                priority_queues
% 10.85/2.01  --sup_passive_queues                    [[-conj_dist;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 10.85/2.01  --sup_passive_queues_freq               [8;1;4]
% 10.85/2.01  --demod_completeness_check              fast
% 10.85/2.01  --demod_use_ground                      true
% 10.85/2.01  --sup_to_prop_solver                    active
% 10.85/2.01  --sup_prop_simpl_new                    false
% 10.85/2.01  --sup_prop_simpl_given                  false
% 10.85/2.01  --sup_fun_splitting                     true
% 10.85/2.01  --sup_smt_interval                      10000
% 10.85/2.01  
% 10.85/2.01  ------ Superposition Simplification Setup
% 10.85/2.01  
% 10.85/2.01  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 10.85/2.01  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 10.85/2.01  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 10.85/2.01  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 10.85/2.01  --sup_full_triv                         [TrivRules]
% 10.85/2.01  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 10.85/2.01  --sup_full_bw                           [BwDemod;BwSubsumption]
% 10.85/2.01  --sup_immed_triv                        [TrivRules]
% 10.85/2.01  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 10.85/2.01  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 10.85/2.01  --sup_immed_bw_main                     []
% 10.85/2.01  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 10.85/2.01  --sup_input_triv                        [Unflattening;TrivRules]
% 10.85/2.01  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 10.85/2.01  --sup_input_bw                          [BwDemod;BwSubsumption]
% 10.85/2.01  
% 10.85/2.01  ------ Combination Options
% 10.85/2.01  
% 10.85/2.01  --comb_res_mult                         1
% 10.85/2.01  --comb_sup_mult                         1
% 10.85/2.01  --comb_inst_mult                        1000000
% 10.85/2.01  
% 10.85/2.01  ------ Debug Options
% 10.85/2.01  
% 10.85/2.01  --dbg_backtrace                         false
% 10.85/2.01  --dbg_dump_prop_clauses                 false
% 10.85/2.01  --dbg_dump_prop_clauses_file            -
% 10.85/2.01  --dbg_out_stat                          false
% 10.85/2.01  
% 10.85/2.01  
% 10.85/2.01  
% 10.85/2.01  
% 10.85/2.01  ------ Proving...
% 10.85/2.01  
% 10.85/2.01  
% 10.85/2.01  % SZS status Theorem for theBenchmark.p
% 10.85/2.01  
% 10.85/2.01   Resolution empty clause
% 10.85/2.01  
% 10.85/2.01  % SZS output start CNFRefutation for theBenchmark.p
% 10.85/2.01  
% 10.85/2.01  fof(f13,axiom,(
% 10.85/2.01    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k1_enumset1(X0,X2,X1)),
% 10.85/2.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 10.85/2.01  
% 10.85/2.01  fof(f31,plain,(
% 10.85/2.01    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k1_enumset1(X0,X2,X1)) )),
% 10.85/2.01    inference(cnf_transformation,[],[f13])).
% 10.85/2.01  
% 10.85/2.01  fof(f8,axiom,(
% 10.85/2.01    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 10.85/2.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 10.85/2.01  
% 10.85/2.01  fof(f26,plain,(
% 10.85/2.01    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 10.85/2.01    inference(cnf_transformation,[],[f8])).
% 10.85/2.01  
% 10.85/2.01  fof(f9,axiom,(
% 10.85/2.01    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 10.85/2.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 10.85/2.01  
% 10.85/2.01  fof(f27,plain,(
% 10.85/2.01    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 10.85/2.01    inference(cnf_transformation,[],[f9])).
% 10.85/2.01  
% 10.85/2.01  fof(f10,axiom,(
% 10.85/2.01    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)),
% 10.85/2.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 10.85/2.01  
% 10.85/2.01  fof(f28,plain,(
% 10.85/2.01    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 10.85/2.01    inference(cnf_transformation,[],[f10])).
% 10.85/2.01  
% 10.85/2.01  fof(f33,plain,(
% 10.85/2.01    ( ! [X2,X0,X3,X1] : (k4_enumset1(X0,X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 10.85/2.01    inference(definition_unfolding,[],[f27,f28])).
% 10.85/2.01  
% 10.85/2.01  fof(f34,plain,(
% 10.85/2.01    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k4_enumset1(X0,X0,X0,X0,X1,X2)) )),
% 10.85/2.01    inference(definition_unfolding,[],[f26,f33])).
% 10.85/2.01  
% 10.85/2.01  fof(f43,plain,(
% 10.85/2.01    ( ! [X2,X0,X1] : (k4_enumset1(X0,X0,X0,X0,X1,X2) = k4_enumset1(X0,X0,X0,X0,X2,X1)) )),
% 10.85/2.01    inference(definition_unfolding,[],[f31,f34,f34])).
% 10.85/2.01  
% 10.85/2.01  fof(f11,axiom,(
% 10.85/2.01    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)),
% 10.85/2.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 10.85/2.01  
% 10.85/2.01  fof(f29,plain,(
% 10.85/2.01    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)) )),
% 10.85/2.01    inference(cnf_transformation,[],[f11])).
% 10.85/2.01  
% 10.85/2.01  fof(f5,axiom,(
% 10.85/2.01    ! [X0,X1,X2,X3,X4,X5,X6] : k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k2_tarski(X5,X6)) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)),
% 10.85/2.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 10.85/2.01  
% 10.85/2.01  fof(f23,plain,(
% 10.85/2.01    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k2_tarski(X5,X6)) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)) )),
% 10.85/2.01    inference(cnf_transformation,[],[f5])).
% 10.85/2.01  
% 10.85/2.01  fof(f1,axiom,(
% 10.85/2.01    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 10.85/2.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 10.85/2.01  
% 10.85/2.01  fof(f19,plain,(
% 10.85/2.01    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 10.85/2.01    inference(cnf_transformation,[],[f1])).
% 10.85/2.01  
% 10.85/2.01  fof(f7,axiom,(
% 10.85/2.01    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 10.85/2.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 10.85/2.01  
% 10.85/2.01  fof(f25,plain,(
% 10.85/2.01    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 10.85/2.01    inference(cnf_transformation,[],[f7])).
% 10.85/2.01  
% 10.85/2.01  fof(f35,plain,(
% 10.85/2.01    ( ! [X0,X1] : (k4_enumset1(X0,X0,X0,X0,X0,X1) = k2_tarski(X0,X1)) )),
% 10.85/2.01    inference(definition_unfolding,[],[f25,f34])).
% 10.85/2.01  
% 10.85/2.01  fof(f37,plain,(
% 10.85/2.01    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_xboole_0(k4_enumset1(X0,X0,X1,X2,X3,X4),k4_xboole_0(k4_enumset1(X5,X5,X5,X5,X5,X6),k4_enumset1(X0,X0,X1,X2,X3,X4))) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)) )),
% 10.85/2.01    inference(definition_unfolding,[],[f23,f19,f28,f35])).
% 10.85/2.01  
% 10.85/2.01  fof(f41,plain,(
% 10.85/2.01    ( ! [X4,X2,X0,X5,X3,X1] : (k5_xboole_0(k4_enumset1(X0,X0,X0,X1,X2,X3),k4_xboole_0(k4_enumset1(X4,X4,X4,X4,X4,X5),k4_enumset1(X0,X0,X0,X1,X2,X3))) = k4_enumset1(X0,X1,X2,X3,X4,X5)) )),
% 10.85/2.01    inference(definition_unfolding,[],[f29,f37])).
% 10.85/2.01  
% 10.85/2.01  fof(f4,axiom,(
% 10.85/2.01    ! [X0,X1,X2,X3,X4,X5] : k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k1_tarski(X5)) = k4_enumset1(X0,X1,X2,X3,X4,X5)),
% 10.85/2.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 10.85/2.01  
% 10.85/2.01  fof(f22,plain,(
% 10.85/2.01    ( ! [X4,X2,X0,X5,X3,X1] : (k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k1_tarski(X5)) = k4_enumset1(X0,X1,X2,X3,X4,X5)) )),
% 10.85/2.01    inference(cnf_transformation,[],[f4])).
% 10.85/2.01  
% 10.85/2.01  fof(f6,axiom,(
% 10.85/2.01    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)),
% 10.85/2.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 10.85/2.01  
% 10.85/2.01  fof(f24,plain,(
% 10.85/2.01    ( ! [X0] : (k1_tarski(X0) = k2_tarski(X0,X0)) )),
% 10.85/2.01    inference(cnf_transformation,[],[f6])).
% 10.85/2.01  
% 10.85/2.01  fof(f36,plain,(
% 10.85/2.01    ( ! [X0] : (k4_enumset1(X0,X0,X0,X0,X0,X0) = k1_tarski(X0)) )),
% 10.85/2.01    inference(definition_unfolding,[],[f24,f35])).
% 10.85/2.01  
% 10.85/2.01  fof(f38,plain,(
% 10.85/2.01    ( ! [X4,X2,X0,X5,X3,X1] : (k5_xboole_0(k4_enumset1(X0,X0,X1,X2,X3,X4),k4_xboole_0(k4_enumset1(X5,X5,X5,X5,X5,X5),k4_enumset1(X0,X0,X1,X2,X3,X4))) = k4_enumset1(X0,X1,X2,X3,X4,X5)) )),
% 10.85/2.01    inference(definition_unfolding,[],[f22,f19,f28,f36])).
% 10.85/2.01  
% 10.85/2.01  fof(f2,axiom,(
% 10.85/2.01    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k1_enumset1(X1,X2,X0)),
% 10.85/2.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 10.85/2.01  
% 10.85/2.01  fof(f20,plain,(
% 10.85/2.01    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k1_enumset1(X1,X2,X0)) )),
% 10.85/2.01    inference(cnf_transformation,[],[f2])).
% 10.85/2.01  
% 10.85/2.01  fof(f39,plain,(
% 10.85/2.01    ( ! [X2,X0,X1] : (k4_enumset1(X0,X0,X0,X0,X1,X2) = k4_enumset1(X1,X1,X1,X1,X2,X0)) )),
% 10.85/2.01    inference(definition_unfolding,[],[f20,f34,f34])).
% 10.85/2.01  
% 10.85/2.01  fof(f14,conjecture,(
% 10.85/2.01    ! [X0,X1,X2] : k2_xboole_0(k2_tarski(X1,X0),k2_tarski(X2,X0)) = k1_enumset1(X0,X1,X2)),
% 10.85/2.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 10.85/2.01  
% 10.85/2.01  fof(f15,negated_conjecture,(
% 10.85/2.01    ~! [X0,X1,X2] : k2_xboole_0(k2_tarski(X1,X0),k2_tarski(X2,X0)) = k1_enumset1(X0,X1,X2)),
% 10.85/2.01    inference(negated_conjecture,[],[f14])).
% 10.85/2.01  
% 10.85/2.01  fof(f16,plain,(
% 10.85/2.01    ? [X0,X1,X2] : k2_xboole_0(k2_tarski(X1,X0),k2_tarski(X2,X0)) != k1_enumset1(X0,X1,X2)),
% 10.85/2.01    inference(ennf_transformation,[],[f15])).
% 10.85/2.01  
% 10.85/2.01  fof(f17,plain,(
% 10.85/2.01    ? [X0,X1,X2] : k2_xboole_0(k2_tarski(X1,X0),k2_tarski(X2,X0)) != k1_enumset1(X0,X1,X2) => k2_xboole_0(k2_tarski(sK1,sK0),k2_tarski(sK2,sK0)) != k1_enumset1(sK0,sK1,sK2)),
% 10.85/2.01    introduced(choice_axiom,[])).
% 10.85/2.01  
% 10.85/2.01  fof(f18,plain,(
% 10.85/2.01    k2_xboole_0(k2_tarski(sK1,sK0),k2_tarski(sK2,sK0)) != k1_enumset1(sK0,sK1,sK2)),
% 10.85/2.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f16,f17])).
% 10.85/2.01  
% 10.85/2.01  fof(f32,plain,(
% 10.85/2.01    k2_xboole_0(k2_tarski(sK1,sK0),k2_tarski(sK2,sK0)) != k1_enumset1(sK0,sK1,sK2)),
% 10.85/2.01    inference(cnf_transformation,[],[f18])).
% 10.85/2.01  
% 10.85/2.01  fof(f44,plain,(
% 10.85/2.01    k5_xboole_0(k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK0),k4_xboole_0(k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK0),k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK0))) != k4_enumset1(sK0,sK0,sK0,sK0,sK1,sK2)),
% 10.85/2.01    inference(definition_unfolding,[],[f32,f19,f35,f35,f34])).
% 10.85/2.01  
% 10.85/2.01  cnf(c_5,plain,
% 10.85/2.01      ( k4_enumset1(X0,X0,X0,X0,X1,X2) = k4_enumset1(X0,X0,X0,X0,X2,X1) ),
% 10.85/2.01      inference(cnf_transformation,[],[f43]) ).
% 10.85/2.01  
% 10.85/2.01  cnf(c_16,plain,
% 10.85/2.01      ( k4_enumset1(X0_37,X0_37,X0_37,X0_37,X1_37,X2_37) = k4_enumset1(X0_37,X0_37,X0_37,X0_37,X2_37,X1_37) ),
% 10.85/2.01      inference(subtyping,[status(esa)],[c_5]) ).
% 10.85/2.01  
% 10.85/2.01  cnf(c_3,plain,
% 10.85/2.01      ( k5_xboole_0(k4_enumset1(X0,X0,X0,X1,X2,X3),k4_xboole_0(k4_enumset1(X4,X4,X4,X4,X4,X5),k4_enumset1(X0,X0,X0,X1,X2,X3))) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
% 10.85/2.01      inference(cnf_transformation,[],[f41]) ).
% 10.85/2.01  
% 10.85/2.01  cnf(c_18,plain,
% 10.85/2.01      ( k5_xboole_0(k4_enumset1(X0_37,X0_37,X0_37,X1_37,X2_37,X3_37),k4_xboole_0(k4_enumset1(X4_37,X4_37,X4_37,X4_37,X4_37,X5_37),k4_enumset1(X0_37,X0_37,X0_37,X1_37,X2_37,X3_37))) = k4_enumset1(X0_37,X1_37,X2_37,X3_37,X4_37,X5_37) ),
% 10.85/2.01      inference(subtyping,[status(esa)],[c_3]) ).
% 10.85/2.01  
% 10.85/2.01  cnf(c_142,plain,
% 10.85/2.01      ( k5_xboole_0(k4_enumset1(X0_37,X0_37,X0_37,X0_37,X1_37,X2_37),k4_xboole_0(k4_enumset1(X3_37,X3_37,X3_37,X3_37,X3_37,X4_37),k4_enumset1(X0_37,X0_37,X0_37,X0_37,X1_37,X2_37))) = k4_enumset1(X0_37,X0_37,X2_37,X1_37,X3_37,X4_37) ),
% 10.85/2.01      inference(superposition,[status(thm)],[c_16,c_18]) ).
% 10.85/2.01  
% 10.85/2.01  cnf(c_0,plain,
% 10.85/2.01      ( k5_xboole_0(k4_enumset1(X0,X0,X1,X2,X3,X4),k4_xboole_0(k4_enumset1(X5,X5,X5,X5,X5,X5),k4_enumset1(X0,X0,X1,X2,X3,X4))) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
% 10.85/2.01      inference(cnf_transformation,[],[f38]) ).
% 10.85/2.01  
% 10.85/2.01  cnf(c_21,plain,
% 10.85/2.01      ( k5_xboole_0(k4_enumset1(X0_37,X0_37,X1_37,X2_37,X3_37,X4_37),k4_xboole_0(k4_enumset1(X5_37,X5_37,X5_37,X5_37,X5_37,X5_37),k4_enumset1(X0_37,X0_37,X1_37,X2_37,X3_37,X4_37))) = k4_enumset1(X0_37,X1_37,X2_37,X3_37,X4_37,X5_37) ),
% 10.85/2.01      inference(subtyping,[status(esa)],[c_0]) ).
% 10.85/2.01  
% 10.85/2.01  cnf(c_2124,plain,
% 10.85/2.01      ( k4_enumset1(X0_37,X0_37,X1_37,X2_37,X3_37,X3_37) = k4_enumset1(X0_37,X0_37,X0_37,X2_37,X1_37,X3_37) ),
% 10.85/2.01      inference(superposition,[status(thm)],[c_142,c_21]) ).
% 10.85/2.01  
% 10.85/2.01  cnf(c_206,plain,
% 10.85/2.01      ( k4_enumset1(X0_37,X1_37,X2_37,X3_37,X4_37,X4_37) = k4_enumset1(X0_37,X0_37,X1_37,X2_37,X3_37,X4_37) ),
% 10.85/2.01      inference(superposition,[status(thm)],[c_21,c_18]) ).
% 10.85/2.01  
% 10.85/2.01  cnf(c_260,plain,
% 10.85/2.01      ( k4_enumset1(X0_37,X1_37,X2_37,X3_37,X3_37,X3_37) = k4_enumset1(X0_37,X0_37,X0_37,X1_37,X2_37,X3_37) ),
% 10.85/2.01      inference(superposition,[status(thm)],[c_206,c_206]) ).
% 10.85/2.01  
% 10.85/2.01  cnf(c_2350,plain,
% 10.85/2.01      ( k4_enumset1(X0_37,X0_37,X0_37,X1_37,X2_37,X1_37) = k4_enumset1(X0_37,X0_37,X0_37,X0_37,X2_37,X1_37) ),
% 10.85/2.01      inference(superposition,[status(thm)],[c_2124,c_260]) ).
% 10.85/2.01  
% 10.85/2.01  cnf(c_1,plain,
% 10.85/2.01      ( k4_enumset1(X0,X0,X0,X0,X1,X2) = k4_enumset1(X2,X2,X2,X2,X0,X1) ),
% 10.85/2.01      inference(cnf_transformation,[],[f39]) ).
% 10.85/2.01  
% 10.85/2.01  cnf(c_20,plain,
% 10.85/2.01      ( k4_enumset1(X0_37,X0_37,X0_37,X0_37,X1_37,X2_37) = k4_enumset1(X2_37,X2_37,X2_37,X2_37,X0_37,X1_37) ),
% 10.85/2.01      inference(subtyping,[status(esa)],[c_1]) ).
% 10.85/2.01  
% 10.85/2.01  cnf(c_6,negated_conjecture,
% 10.85/2.01      ( k5_xboole_0(k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK0),k4_xboole_0(k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK0),k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK0))) != k4_enumset1(sK0,sK0,sK0,sK0,sK1,sK2) ),
% 10.85/2.01      inference(cnf_transformation,[],[f44]) ).
% 10.85/2.01  
% 10.85/2.01  cnf(c_15,negated_conjecture,
% 10.85/2.01      ( k5_xboole_0(k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK0),k4_xboole_0(k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK0),k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK0))) != k4_enumset1(sK0,sK0,sK0,sK0,sK1,sK2) ),
% 10.85/2.01      inference(subtyping,[status(esa)],[c_6]) ).
% 10.85/2.01  
% 10.85/2.01  cnf(c_34,plain,
% 10.85/2.01      ( k4_enumset1(sK1,sK1,sK1,sK0,sK2,sK0) != k4_enumset1(sK0,sK0,sK0,sK0,sK1,sK2) ),
% 10.85/2.01      inference(demodulation,[status(thm)],[c_15,c_18]) ).
% 10.85/2.01  
% 10.85/2.01  cnf(c_43,plain,
% 10.85/2.01      ( k4_enumset1(sK1,sK1,sK1,sK1,sK2,sK0) != k4_enumset1(sK1,sK1,sK1,sK0,sK2,sK0) ),
% 10.85/2.01      inference(demodulation,[status(thm)],[c_20,c_34]) ).
% 10.85/2.01  
% 10.85/2.01  cnf(c_32073,plain,
% 10.85/2.01      ( k4_enumset1(sK1,sK1,sK1,sK1,sK2,sK0) != k4_enumset1(sK1,sK1,sK1,sK1,sK2,sK0) ),
% 10.85/2.01      inference(demodulation,[status(thm)],[c_2350,c_43]) ).
% 10.85/2.01  
% 10.85/2.01  cnf(c_32588,plain,
% 10.85/2.01      ( $false ),
% 10.85/2.01      inference(equality_resolution_simp,[status(thm)],[c_32073]) ).
% 10.85/2.01  
% 10.85/2.01  
% 10.85/2.01  % SZS output end CNFRefutation for theBenchmark.p
% 10.85/2.01  
% 10.85/2.01  ------                               Statistics
% 10.85/2.01  
% 10.85/2.01  ------ General
% 10.85/2.01  
% 10.85/2.01  abstr_ref_over_cycles:                  0
% 10.85/2.01  abstr_ref_under_cycles:                 0
% 10.85/2.01  gc_basic_clause_elim:                   0
% 10.85/2.01  forced_gc_time:                         0
% 10.85/2.01  parsing_time:                           0.01
% 10.85/2.01  unif_index_cands_time:                  0.
% 10.85/2.01  unif_index_add_time:                    0.
% 10.85/2.01  orderings_time:                         0.
% 10.85/2.01  out_proof_time:                         0.005
% 10.85/2.01  total_time:                             1.034
% 10.85/2.01  num_of_symbols:                         38
% 10.85/2.01  num_of_terms:                           9826
% 10.85/2.01  
% 10.85/2.01  ------ Preprocessing
% 10.85/2.01  
% 10.85/2.01  num_of_splits:                          0
% 10.85/2.01  num_of_split_atoms:                     0
% 10.85/2.01  num_of_reused_defs:                     0
% 10.85/2.01  num_eq_ax_congr_red:                    22
% 10.85/2.01  num_of_sem_filtered_clauses:            0
% 10.85/2.01  num_of_subtypes:                        3
% 10.85/2.01  monotx_restored_types:                  0
% 10.85/2.01  sat_num_of_epr_types:                   0
% 10.85/2.01  sat_num_of_non_cyclic_types:            0
% 10.85/2.01  sat_guarded_non_collapsed_types:        0
% 10.85/2.01  num_pure_diseq_elim:                    0
% 10.85/2.01  simp_replaced_by:                       0
% 10.85/2.01  res_preprocessed:                       19
% 10.85/2.01  prep_upred:                             0
% 10.85/2.01  prep_unflattend:                        0
% 10.85/2.01  smt_new_axioms:                         0
% 10.85/2.01  pred_elim_cands:                        0
% 10.85/2.01  pred_elim:                              0
% 10.85/2.01  pred_elim_cl:                           0
% 10.85/2.01  pred_elim_cycles:                       0
% 10.85/2.01  merged_defs:                            0
% 10.85/2.01  merged_defs_ncl:                        0
% 10.85/2.01  bin_hyper_res:                          0
% 10.85/2.01  prep_cycles:                            2
% 10.85/2.01  pred_elim_time:                         0.
% 10.85/2.01  splitting_time:                         0.
% 10.85/2.01  sem_filter_time:                        0.
% 10.85/2.01  monotx_time:                            0.
% 10.85/2.01  subtype_inf_time:                       0.
% 10.85/2.01  
% 10.85/2.01  ------ Problem properties
% 10.85/2.01  
% 10.85/2.01  clauses:                                7
% 10.85/2.01  conjectures:                            1
% 10.85/2.01  epr:                                    0
% 10.85/2.01  horn:                                   7
% 10.85/2.01  ground:                                 1
% 10.85/2.01  unary:                                  7
% 10.85/2.01  binary:                                 0
% 10.85/2.01  lits:                                   7
% 10.85/2.01  lits_eq:                                7
% 10.85/2.01  fd_pure:                                0
% 10.85/2.01  fd_pseudo:                              0
% 10.85/2.01  fd_cond:                                0
% 10.85/2.01  fd_pseudo_cond:                         0
% 10.85/2.01  ac_symbols:                             0
% 10.85/2.01  
% 10.85/2.01  ------ Propositional Solver
% 10.85/2.01  
% 10.85/2.01  prop_solver_calls:                      13
% 10.85/2.01  prop_fast_solver_calls:                 50
% 10.85/2.01  smt_solver_calls:                       0
% 10.85/2.01  smt_fast_solver_calls:                  0
% 10.85/2.01  prop_num_of_clauses:                    161
% 10.85/2.01  prop_preprocess_simplified:             376
% 10.85/2.01  prop_fo_subsumed:                       0
% 10.85/2.01  prop_solver_time:                       0.
% 10.85/2.01  smt_solver_time:                        0.
% 10.85/2.01  smt_fast_solver_time:                   0.
% 10.85/2.01  prop_fast_solver_time:                  0.
% 10.85/2.01  prop_unsat_core_time:                   0.
% 10.85/2.01  
% 10.85/2.01  ------ QBF
% 10.85/2.01  
% 10.85/2.01  qbf_q_res:                              0
% 10.85/2.01  qbf_num_tautologies:                    0
% 10.85/2.01  qbf_prep_cycles:                        0
% 10.85/2.01  
% 10.85/2.01  ------ BMC1
% 10.85/2.01  
% 10.85/2.01  bmc1_current_bound:                     -1
% 10.85/2.01  bmc1_last_solved_bound:                 -1
% 10.85/2.01  bmc1_unsat_core_size:                   -1
% 10.85/2.01  bmc1_unsat_core_parents_size:           -1
% 10.85/2.01  bmc1_merge_next_fun:                    0
% 10.85/2.01  bmc1_unsat_core_clauses_time:           0.
% 10.85/2.01  
% 10.85/2.01  ------ Instantiation
% 10.85/2.01  
% 10.85/2.01  inst_num_of_clauses:                    0
% 10.85/2.01  inst_num_in_passive:                    0
% 10.85/2.01  inst_num_in_active:                     0
% 10.85/2.01  inst_num_in_unprocessed:                0
% 10.85/2.01  inst_num_of_loops:                      0
% 10.85/2.01  inst_num_of_learning_restarts:          0
% 10.85/2.01  inst_num_moves_active_passive:          0
% 10.85/2.01  inst_lit_activity:                      0
% 10.85/2.01  inst_lit_activity_moves:                0
% 10.85/2.01  inst_num_tautologies:                   0
% 10.85/2.01  inst_num_prop_implied:                  0
% 10.85/2.01  inst_num_existing_simplified:           0
% 10.85/2.01  inst_num_eq_res_simplified:             0
% 10.85/2.01  inst_num_child_elim:                    0
% 10.85/2.01  inst_num_of_dismatching_blockings:      0
% 10.85/2.01  inst_num_of_non_proper_insts:           0
% 10.85/2.01  inst_num_of_duplicates:                 0
% 10.85/2.01  inst_inst_num_from_inst_to_res:         0
% 10.85/2.01  inst_dismatching_checking_time:         0.
% 10.85/2.01  
% 10.85/2.01  ------ Resolution
% 10.85/2.01  
% 10.85/2.01  res_num_of_clauses:                     0
% 10.85/2.01  res_num_in_passive:                     0
% 10.85/2.01  res_num_in_active:                      0
% 10.85/2.01  res_num_of_loops:                       21
% 10.85/2.01  res_forward_subset_subsumed:            0
% 10.85/2.01  res_backward_subset_subsumed:           0
% 10.85/2.01  res_forward_subsumed:                   0
% 10.85/2.01  res_backward_subsumed:                  0
% 10.85/2.01  res_forward_subsumption_resolution:     0
% 10.85/2.01  res_backward_subsumption_resolution:    0
% 10.85/2.01  res_clause_to_clause_subsumption:       168167
% 10.85/2.01  res_orphan_elimination:                 0
% 10.85/2.01  res_tautology_del:                      0
% 10.85/2.01  res_num_eq_res_simplified:              0
% 10.85/2.01  res_num_sel_changes:                    0
% 10.85/2.01  res_moves_from_active_to_pass:          0
% 10.85/2.01  
% 10.85/2.01  ------ Superposition
% 10.85/2.01  
% 10.85/2.01  sup_time_total:                         0.
% 10.85/2.01  sup_time_generating:                    0.
% 10.85/2.01  sup_time_sim_full:                      0.
% 10.85/2.01  sup_time_sim_immed:                     0.
% 10.85/2.01  
% 10.85/2.01  sup_num_of_clauses:                     2858
% 10.85/2.01  sup_num_in_active:                      134
% 10.85/2.01  sup_num_in_passive:                     2724
% 10.85/2.01  sup_num_of_loops:                       137
% 10.85/2.01  sup_fw_superposition:                   16697
% 10.85/2.01  sup_bw_superposition:                   15073
% 10.85/2.01  sup_immediate_simplified:               1093
% 10.85/2.01  sup_given_eliminated:                   0
% 10.85/2.01  comparisons_done:                       0
% 10.85/2.01  comparisons_avoided:                    0
% 10.85/2.01  
% 10.85/2.01  ------ Simplifications
% 10.85/2.01  
% 10.85/2.01  
% 10.85/2.01  sim_fw_subset_subsumed:                 0
% 10.85/2.01  sim_bw_subset_subsumed:                 0
% 10.85/2.01  sim_fw_subsumed:                        270
% 10.85/2.01  sim_bw_subsumed:                        69
% 10.85/2.01  sim_fw_subsumption_res:                 0
% 10.85/2.01  sim_bw_subsumption_res:                 0
% 10.85/2.01  sim_tautology_del:                      0
% 10.85/2.01  sim_eq_tautology_del:                   15
% 10.85/2.01  sim_eq_res_simp:                        0
% 10.85/2.01  sim_fw_demodulated:                     618
% 10.85/2.01  sim_bw_demodulated:                     2
% 10.85/2.01  sim_light_normalised:                   163
% 10.85/2.01  sim_joinable_taut:                      0
% 10.85/2.01  sim_joinable_simp:                      0
% 10.85/2.01  sim_ac_normalised:                      0
% 10.85/2.01  sim_smt_subsumption:                    0
% 10.85/2.01  
%------------------------------------------------------------------------------
