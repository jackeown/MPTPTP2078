%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:26:08 EST 2020

% Result     : Theorem 9.50s
% Output     : CNFRefutation 9.50s
% Verified   : 
% Statistics : Number of formulae       :   60 ( 355 expanded)
%              Number of clauses        :   37 ( 141 expanded)
%              Number of leaves         :    9 (  95 expanded)
%              Depth                    :   14
%              Number of atoms          :   61 ( 356 expanded)
%              Number of equality atoms :   60 ( 355 expanded)
%              Maximal formula depth    :    6 (   2 average)
%              Maximal clause size      :    2 (   1 average)
%              Maximal term depth       :    5 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f3,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f10,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f3])).

fof(f16,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f10])).

fof(f5,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(k3_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(k3_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f5])).

fof(f6,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f6])).

fof(f4,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f22,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) = k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(k3_xboole_0(X0,X1),X2)) ),
    inference(definition_unfolding,[],[f19,f17,f17])).

fof(f7,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X2,X0,X1] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f7])).

fof(f2,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f8,conjecture,(
    ! [X0,X1,X2] : k3_xboole_0(k4_xboole_0(X0,X2),X1) = k4_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X2,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f9,negated_conjecture,(
    ~ ! [X0,X1,X2] : k3_xboole_0(k4_xboole_0(X0,X2),X1) = k4_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X2,X1)) ),
    inference(negated_conjecture,[],[f8])).

fof(f11,plain,(
    ? [X0,X1,X2] : k3_xboole_0(k4_xboole_0(X0,X2),X1) != k4_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X2,X1)) ),
    inference(ennf_transformation,[],[f9])).

fof(f12,plain,
    ( ? [X0,X1,X2] : k3_xboole_0(k4_xboole_0(X0,X2),X1) != k4_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X2,X1))
   => k3_xboole_0(k4_xboole_0(sK0,sK2),sK1) != k4_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK2,sK1)) ),
    introduced(choice_axiom,[])).

fof(f13,plain,(
    k3_xboole_0(k4_xboole_0(sK0,sK2),sK1) != k4_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK2,sK1)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f11,f12])).

fof(f21,plain,(
    k3_xboole_0(k4_xboole_0(sK0,sK2),sK1) != k4_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK2,sK1)) ),
    inference(cnf_transformation,[],[f13])).

fof(f23,plain,(
    k3_xboole_0(k5_xboole_0(sK0,k3_xboole_0(sK0,sK2)),sK1) != k5_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK2,sK1))) ),
    inference(definition_unfolding,[],[f21,f17,f17])).

cnf(c_0,plain,
    ( k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f14])).

cnf(c_2,plain,
    ( k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f16])).

cnf(c_3,plain,
    ( k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f18])).

cnf(c_33,plain,
    ( k3_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_2,c_3])).

cnf(c_37,plain,
    ( k3_xboole_0(X0,k3_xboole_0(X1,X0)) = k3_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_0,c_33])).

cnf(c_49,plain,
    ( k3_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k3_xboole_0(k3_xboole_0(X0,X1),X0) ),
    inference(superposition,[status(thm)],[c_33,c_37])).

cnf(c_58,plain,
    ( k3_xboole_0(k3_xboole_0(X0,X1),X0) = k3_xboole_0(X0,X1) ),
    inference(demodulation,[status(thm)],[c_49,c_2])).

cnf(c_64,plain,
    ( k3_xboole_0(k3_xboole_0(X0,X1),X1) = k3_xboole_0(X1,X0) ),
    inference(superposition,[status(thm)],[c_0,c_58])).

cnf(c_26,plain,
    ( k3_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(X1,k3_xboole_0(X0,X2)) ),
    inference(superposition,[status(thm)],[c_3,c_0])).

cnf(c_164,plain,
    ( k3_xboole_0(X0,k3_xboole_0(X1,X0)) = k3_xboole_0(X1,X0) ),
    inference(superposition,[status(thm)],[c_2,c_26])).

cnf(c_210,plain,
    ( k3_xboole_0(k3_xboole_0(X0,X1),X1) = k3_xboole_0(X1,k3_xboole_0(X1,X0)) ),
    inference(superposition,[status(thm)],[c_64,c_164])).

cnf(c_213,plain,
    ( k3_xboole_0(k3_xboole_0(X0,X1),X1) = k3_xboole_0(X1,k3_xboole_0(X0,X1)) ),
    inference(superposition,[status(thm)],[c_164,c_58])).

cnf(c_214,plain,
    ( k3_xboole_0(X0,k3_xboole_0(k3_xboole_0(X1,X0),X2)) = k3_xboole_0(k3_xboole_0(X1,X0),X2) ),
    inference(superposition,[status(thm)],[c_164,c_3])).

cnf(c_52,plain,
    ( k3_xboole_0(X0,k3_xboole_0(k3_xboole_0(X1,X0),X2)) = k3_xboole_0(k3_xboole_0(X0,X1),X2) ),
    inference(superposition,[status(thm)],[c_37,c_3])).

cnf(c_56,plain,
    ( k3_xboole_0(X0,k3_xboole_0(k3_xboole_0(X1,X0),X2)) = k3_xboole_0(X0,k3_xboole_0(X1,X2)) ),
    inference(light_normalisation,[status(thm)],[c_52,c_3])).

cnf(c_237,plain,
    ( k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X1,k3_xboole_0(X0,X2)) ),
    inference(light_normalisation,[status(thm)],[c_214,c_56])).

cnf(c_238,plain,
    ( k3_xboole_0(k3_xboole_0(X0,X1),X1) = k3_xboole_0(X0,X1) ),
    inference(demodulation,[status(thm)],[c_213,c_164,c_237])).

cnf(c_242,plain,
    ( k3_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_xboole_0(X1,X0) ),
    inference(demodulation,[status(thm)],[c_210,c_238])).

cnf(c_4,plain,
    ( k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(k3_xboole_0(X0,X1),X2)) = k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) ),
    inference(cnf_transformation,[],[f22])).

cnf(c_5,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f20])).

cnf(c_1,plain,
    ( k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f15])).

cnf(c_18,plain,
    ( k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,k3_xboole_0(X1,X2))) = k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) ),
    inference(theory_normalisation,[status(thm)],[c_4,c_5,c_1,c_3,c_0])).

cnf(c_311,plain,
    ( k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X1,k3_xboole_0(k3_xboole_0(X1,X0),X2))) = k3_xboole_0(X1,k5_xboole_0(k3_xboole_0(X1,X0),k3_xboole_0(k3_xboole_0(X1,X0),X2))) ),
    inference(superposition,[status(thm)],[c_242,c_18])).

cnf(c_90,plain,
    ( k5_xboole_0(k3_xboole_0(k3_xboole_0(X0,X1),X2),k3_xboole_0(X0,k3_xboole_0(X1,k3_xboole_0(X2,X3)))) = k3_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X2,k3_xboole_0(X2,X3))) ),
    inference(superposition,[status(thm)],[c_3,c_18])).

cnf(c_112,plain,
    ( k5_xboole_0(k3_xboole_0(X0,k3_xboole_0(X1,X2)),k3_xboole_0(X0,k3_xboole_0(X1,k3_xboole_0(X2,X3)))) = k3_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X2,k3_xboole_0(X2,X3))) ),
    inference(light_normalisation,[status(thm)],[c_90,c_3])).

cnf(c_97,plain,
    ( k5_xboole_0(k3_xboole_0(X0,k3_xboole_0(X1,X2)),k3_xboole_0(X0,k3_xboole_0(X1,k3_xboole_0(X2,X3)))) = k3_xboole_0(X0,k5_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(k3_xboole_0(X1,X2),X3))) ),
    inference(superposition,[status(thm)],[c_3,c_18])).

cnf(c_113,plain,
    ( k3_xboole_0(X0,k5_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(k3_xboole_0(X1,X2),X3))) = k3_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X2,k3_xboole_0(X2,X3))) ),
    inference(demodulation,[status(thm)],[c_112,c_97])).

cnf(c_183,plain,
    ( k3_xboole_0(X0,k3_xboole_0(X1,k3_xboole_0(X0,X2))) = k3_xboole_0(X0,k3_xboole_0(X1,X2)) ),
    inference(superposition,[status(thm)],[c_26,c_33])).

cnf(c_187,plain,
    ( k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X1,k3_xboole_0(X0,X2))) = k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) ),
    inference(superposition,[status(thm)],[c_26,c_18])).

cnf(c_338,plain,
    ( k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) = k3_xboole_0(X1,k5_xboole_0(X0,k3_xboole_0(X0,X2))) ),
    inference(demodulation,[status(thm)],[c_311,c_2,c_113,c_183,c_187,c_237])).

cnf(c_94,plain,
    ( k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,k3_xboole_0(X2,X1))) = k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) ),
    inference(superposition,[status(thm)],[c_0,c_18])).

cnf(c_6,negated_conjecture,
    ( k3_xboole_0(k5_xboole_0(sK0,k3_xboole_0(sK0,sK2)),sK1) != k5_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK2,sK1))) ),
    inference(cnf_transformation,[],[f23])).

cnf(c_17,negated_conjecture,
    ( k5_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK0,k3_xboole_0(sK2,k3_xboole_0(sK1,sK1)))) != k3_xboole_0(sK1,k5_xboole_0(sK0,k3_xboole_0(sK0,sK2))) ),
    inference(theory_normalisation,[status(thm)],[c_6,c_5,c_1,c_3,c_0])).

cnf(c_25,plain,
    ( k5_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK0,k3_xboole_0(sK2,sK1))) != k3_xboole_0(sK1,k5_xboole_0(sK0,k3_xboole_0(sK0,sK2))) ),
    inference(demodulation,[status(thm)],[c_17,c_2])).

cnf(c_24580,plain,
    ( k3_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK2))) != k3_xboole_0(sK1,k5_xboole_0(sK0,k3_xboole_0(sK0,sK2))) ),
    inference(demodulation,[status(thm)],[c_94,c_25])).

cnf(c_35617,plain,
    ( k3_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK2))) != k3_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK2))) ),
    inference(demodulation,[status(thm)],[c_338,c_24580])).

cnf(c_35618,plain,
    ( $false ),
    inference(theory_normalisation,[status(thm)],[c_35617])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 19:04:42 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 9.50/1.99  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 9.50/1.99  
% 9.50/1.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 9.50/1.99  
% 9.50/1.99  ------  iProver source info
% 9.50/1.99  
% 9.50/1.99  git: date: 2020-06-30 10:37:57 +0100
% 9.50/1.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 9.50/1.99  git: non_committed_changes: false
% 9.50/1.99  git: last_make_outside_of_git: false
% 9.50/1.99  
% 9.50/1.99  ------ 
% 9.50/1.99  
% 9.50/1.99  ------ Input Options
% 9.50/1.99  
% 9.50/1.99  --out_options                           all
% 9.50/1.99  --tptp_safe_out                         true
% 9.50/1.99  --problem_path                          ""
% 9.50/1.99  --include_path                          ""
% 9.50/1.99  --clausifier                            res/vclausify_rel
% 9.50/1.99  --clausifier_options                    --mode clausify
% 9.50/1.99  --stdin                                 false
% 9.50/1.99  --stats_out                             all
% 9.50/1.99  
% 9.50/1.99  ------ General Options
% 9.50/1.99  
% 9.50/1.99  --fof                                   false
% 9.50/1.99  --time_out_real                         305.
% 9.50/1.99  --time_out_virtual                      -1.
% 9.50/1.99  --symbol_type_check                     false
% 9.50/1.99  --clausify_out                          false
% 9.50/1.99  --sig_cnt_out                           false
% 9.50/1.99  --trig_cnt_out                          false
% 9.50/1.99  --trig_cnt_out_tolerance                1.
% 9.50/1.99  --trig_cnt_out_sk_spl                   false
% 9.50/1.99  --abstr_cl_out                          false
% 9.50/1.99  
% 9.50/1.99  ------ Global Options
% 9.50/1.99  
% 9.50/1.99  --schedule                              default
% 9.50/1.99  --add_important_lit                     false
% 9.50/1.99  --prop_solver_per_cl                    1000
% 9.50/1.99  --min_unsat_core                        false
% 9.50/1.99  --soft_assumptions                      false
% 9.50/1.99  --soft_lemma_size                       3
% 9.50/1.99  --prop_impl_unit_size                   0
% 9.50/1.99  --prop_impl_unit                        []
% 9.50/1.99  --share_sel_clauses                     true
% 9.50/1.99  --reset_solvers                         false
% 9.50/1.99  --bc_imp_inh                            [conj_cone]
% 9.50/1.99  --conj_cone_tolerance                   3.
% 9.50/1.99  --extra_neg_conj                        none
% 9.50/1.99  --large_theory_mode                     true
% 9.50/1.99  --prolific_symb_bound                   200
% 9.50/1.99  --lt_threshold                          2000
% 9.50/1.99  --clause_weak_htbl                      true
% 9.50/1.99  --gc_record_bc_elim                     false
% 9.50/1.99  
% 9.50/1.99  ------ Preprocessing Options
% 9.50/1.99  
% 9.50/1.99  --preprocessing_flag                    true
% 9.50/1.99  --time_out_prep_mult                    0.1
% 9.50/1.99  --splitting_mode                        input
% 9.50/1.99  --splitting_grd                         true
% 9.50/1.99  --splitting_cvd                         false
% 9.50/1.99  --splitting_cvd_svl                     false
% 9.50/1.99  --splitting_nvd                         32
% 9.50/1.99  --sub_typing                            true
% 9.50/1.99  --prep_gs_sim                           true
% 9.50/1.99  --prep_unflatten                        true
% 9.50/1.99  --prep_res_sim                          true
% 9.50/1.99  --prep_upred                            true
% 9.50/1.99  --prep_sem_filter                       exhaustive
% 9.50/1.99  --prep_sem_filter_out                   false
% 9.50/1.99  --pred_elim                             true
% 9.50/1.99  --res_sim_input                         true
% 9.50/1.99  --eq_ax_congr_red                       true
% 9.50/1.99  --pure_diseq_elim                       true
% 9.50/1.99  --brand_transform                       false
% 9.50/1.99  --non_eq_to_eq                          false
% 9.50/1.99  --prep_def_merge                        true
% 9.50/1.99  --prep_def_merge_prop_impl              false
% 9.50/1.99  --prep_def_merge_mbd                    true
% 9.50/1.99  --prep_def_merge_tr_red                 false
% 9.50/1.99  --prep_def_merge_tr_cl                  false
% 9.50/1.99  --smt_preprocessing                     true
% 9.50/1.99  --smt_ac_axioms                         fast
% 9.50/1.99  --preprocessed_out                      false
% 9.50/1.99  --preprocessed_stats                    false
% 9.50/1.99  
% 9.50/1.99  ------ Abstraction refinement Options
% 9.50/1.99  
% 9.50/1.99  --abstr_ref                             []
% 9.50/1.99  --abstr_ref_prep                        false
% 9.50/1.99  --abstr_ref_until_sat                   false
% 9.50/1.99  --abstr_ref_sig_restrict                funpre
% 9.50/1.99  --abstr_ref_af_restrict_to_split_sk     false
% 9.50/1.99  --abstr_ref_under                       []
% 9.50/1.99  
% 9.50/1.99  ------ SAT Options
% 9.50/1.99  
% 9.50/1.99  --sat_mode                              false
% 9.50/1.99  --sat_fm_restart_options                ""
% 9.50/1.99  --sat_gr_def                            false
% 9.50/1.99  --sat_epr_types                         true
% 9.50/1.99  --sat_non_cyclic_types                  false
% 9.50/1.99  --sat_finite_models                     false
% 9.50/1.99  --sat_fm_lemmas                         false
% 9.50/1.99  --sat_fm_prep                           false
% 9.50/1.99  --sat_fm_uc_incr                        true
% 9.50/1.99  --sat_out_model                         small
% 9.50/1.99  --sat_out_clauses                       false
% 9.50/1.99  
% 9.50/1.99  ------ QBF Options
% 9.50/1.99  
% 9.50/1.99  --qbf_mode                              false
% 9.50/1.99  --qbf_elim_univ                         false
% 9.50/1.99  --qbf_dom_inst                          none
% 9.50/1.99  --qbf_dom_pre_inst                      false
% 9.50/1.99  --qbf_sk_in                             false
% 9.50/1.99  --qbf_pred_elim                         true
% 9.50/1.99  --qbf_split                             512
% 9.50/1.99  
% 9.50/1.99  ------ BMC1 Options
% 9.50/1.99  
% 9.50/1.99  --bmc1_incremental                      false
% 9.50/1.99  --bmc1_axioms                           reachable_all
% 9.50/1.99  --bmc1_min_bound                        0
% 9.50/1.99  --bmc1_max_bound                        -1
% 9.50/1.99  --bmc1_max_bound_default                -1
% 9.50/1.99  --bmc1_symbol_reachability              true
% 9.50/1.99  --bmc1_property_lemmas                  false
% 9.50/1.99  --bmc1_k_induction                      false
% 9.50/1.99  --bmc1_non_equiv_states                 false
% 9.50/1.99  --bmc1_deadlock                         false
% 9.50/1.99  --bmc1_ucm                              false
% 9.50/1.99  --bmc1_add_unsat_core                   none
% 9.50/1.99  --bmc1_unsat_core_children              false
% 9.50/1.99  --bmc1_unsat_core_extrapolate_axioms    false
% 9.50/1.99  --bmc1_out_stat                         full
% 9.50/1.99  --bmc1_ground_init                      false
% 9.50/1.99  --bmc1_pre_inst_next_state              false
% 9.50/1.99  --bmc1_pre_inst_state                   false
% 9.50/1.99  --bmc1_pre_inst_reach_state             false
% 9.50/1.99  --bmc1_out_unsat_core                   false
% 9.50/1.99  --bmc1_aig_witness_out                  false
% 9.50/1.99  --bmc1_verbose                          false
% 9.50/1.99  --bmc1_dump_clauses_tptp                false
% 9.50/1.99  --bmc1_dump_unsat_core_tptp             false
% 9.50/1.99  --bmc1_dump_file                        -
% 9.50/1.99  --bmc1_ucm_expand_uc_limit              128
% 9.50/1.99  --bmc1_ucm_n_expand_iterations          6
% 9.50/1.99  --bmc1_ucm_extend_mode                  1
% 9.50/1.99  --bmc1_ucm_init_mode                    2
% 9.50/1.99  --bmc1_ucm_cone_mode                    none
% 9.50/1.99  --bmc1_ucm_reduced_relation_type        0
% 9.50/1.99  --bmc1_ucm_relax_model                  4
% 9.50/1.99  --bmc1_ucm_full_tr_after_sat            true
% 9.50/1.99  --bmc1_ucm_expand_neg_assumptions       false
% 9.50/1.99  --bmc1_ucm_layered_model                none
% 9.50/1.99  --bmc1_ucm_max_lemma_size               10
% 9.50/1.99  
% 9.50/1.99  ------ AIG Options
% 9.50/1.99  
% 9.50/1.99  --aig_mode                              false
% 9.50/1.99  
% 9.50/1.99  ------ Instantiation Options
% 9.50/1.99  
% 9.50/1.99  --instantiation_flag                    true
% 9.50/1.99  --inst_sos_flag                         false
% 9.50/1.99  --inst_sos_phase                        true
% 9.50/1.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 9.50/1.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 9.50/1.99  --inst_lit_sel_side                     num_symb
% 9.50/1.99  --inst_solver_per_active                1400
% 9.50/1.99  --inst_solver_calls_frac                1.
% 9.50/1.99  --inst_passive_queue_type               priority_queues
% 9.50/1.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 9.50/1.99  --inst_passive_queues_freq              [25;2]
% 9.50/1.99  --inst_dismatching                      true
% 9.50/1.99  --inst_eager_unprocessed_to_passive     true
% 9.50/1.99  --inst_prop_sim_given                   true
% 9.50/1.99  --inst_prop_sim_new                     false
% 9.50/1.99  --inst_subs_new                         false
% 9.50/1.99  --inst_eq_res_simp                      false
% 9.50/1.99  --inst_subs_given                       false
% 9.50/1.99  --inst_orphan_elimination               true
% 9.50/1.99  --inst_learning_loop_flag               true
% 9.50/1.99  --inst_learning_start                   3000
% 9.50/1.99  --inst_learning_factor                  2
% 9.50/1.99  --inst_start_prop_sim_after_learn       3
% 9.50/1.99  --inst_sel_renew                        solver
% 9.50/1.99  --inst_lit_activity_flag                true
% 9.50/1.99  --inst_restr_to_given                   false
% 9.50/1.99  --inst_activity_threshold               500
% 9.50/1.99  --inst_out_proof                        true
% 9.50/1.99  
% 9.50/1.99  ------ Resolution Options
% 9.50/1.99  
% 9.50/1.99  --resolution_flag                       true
% 9.50/1.99  --res_lit_sel                           adaptive
% 9.50/1.99  --res_lit_sel_side                      none
% 9.50/1.99  --res_ordering                          kbo
% 9.50/1.99  --res_to_prop_solver                    active
% 9.50/1.99  --res_prop_simpl_new                    false
% 9.50/1.99  --res_prop_simpl_given                  true
% 9.50/1.99  --res_passive_queue_type                priority_queues
% 9.50/1.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 9.50/1.99  --res_passive_queues_freq               [15;5]
% 9.50/1.99  --res_forward_subs                      full
% 9.50/1.99  --res_backward_subs                     full
% 9.50/1.99  --res_forward_subs_resolution           true
% 9.50/1.99  --res_backward_subs_resolution          true
% 9.50/1.99  --res_orphan_elimination                true
% 9.50/1.99  --res_time_limit                        2.
% 9.50/1.99  --res_out_proof                         true
% 9.50/1.99  
% 9.50/1.99  ------ Superposition Options
% 9.50/1.99  
% 9.50/1.99  --superposition_flag                    true
% 9.50/1.99  --sup_passive_queue_type                priority_queues
% 9.50/1.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 9.50/1.99  --sup_passive_queues_freq               [8;1;4]
% 9.50/1.99  --demod_completeness_check              fast
% 9.50/1.99  --demod_use_ground                      true
% 9.50/1.99  --sup_to_prop_solver                    passive
% 9.50/1.99  --sup_prop_simpl_new                    true
% 9.50/1.99  --sup_prop_simpl_given                  true
% 9.50/1.99  --sup_fun_splitting                     false
% 9.50/1.99  --sup_smt_interval                      50000
% 9.50/1.99  
% 9.50/1.99  ------ Superposition Simplification Setup
% 9.50/1.99  
% 9.50/1.99  --sup_indices_passive                   []
% 9.50/1.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 9.50/1.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 9.50/1.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 9.50/1.99  --sup_full_triv                         [TrivRules;PropSubs]
% 9.50/1.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 9.50/1.99  --sup_full_bw                           [BwDemod]
% 9.50/1.99  --sup_immed_triv                        [TrivRules]
% 9.50/1.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 9.50/1.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 9.50/1.99  --sup_immed_bw_main                     []
% 9.50/1.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 9.50/1.99  --sup_input_triv                        [Unflattening;TrivRules]
% 9.50/1.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 9.50/1.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 9.50/1.99  
% 9.50/1.99  ------ Combination Options
% 9.50/1.99  
% 9.50/1.99  --comb_res_mult                         3
% 9.50/1.99  --comb_sup_mult                         2
% 9.50/1.99  --comb_inst_mult                        10
% 9.50/1.99  
% 9.50/1.99  ------ Debug Options
% 9.50/1.99  
% 9.50/1.99  --dbg_backtrace                         false
% 9.50/1.99  --dbg_dump_prop_clauses                 false
% 9.50/1.99  --dbg_dump_prop_clauses_file            -
% 9.50/1.99  --dbg_out_stat                          false
% 9.50/1.99  ------ Parsing...
% 9.50/1.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 9.50/1.99  
% 9.50/1.99  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  pe_s  pe_e 
% 9.50/1.99  
% 9.50/1.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 9.50/1.99  
% 9.50/1.99  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 9.50/1.99  ------ Proving...
% 9.50/1.99  ------ Problem Properties 
% 9.50/1.99  
% 9.50/1.99  
% 9.50/1.99  clauses                                 7
% 9.50/1.99  conjectures                             1
% 9.50/1.99  EPR                                     0
% 9.50/1.99  Horn                                    7
% 9.50/1.99  unary                                   7
% 9.50/1.99  binary                                  0
% 9.50/1.99  lits                                    7
% 9.50/1.99  lits eq                                 7
% 9.50/1.99  fd_pure                                 0
% 9.50/1.99  fd_pseudo                               0
% 9.50/1.99  fd_cond                                 0
% 9.50/1.99  fd_pseudo_cond                          0
% 9.50/1.99  AC symbols                              2
% 9.50/1.99  
% 9.50/1.99  ------ Schedule UEQ
% 9.50/1.99  
% 9.50/1.99  ------ pure equality problem: resolution off 
% 9.50/1.99  
% 9.50/1.99  ------ Option_UEQ Time Limit: Unbounded
% 9.50/1.99  
% 9.50/1.99  
% 9.50/1.99  ------ 
% 9.50/1.99  Current options:
% 9.50/1.99  ------ 
% 9.50/1.99  
% 9.50/1.99  ------ Input Options
% 9.50/1.99  
% 9.50/1.99  --out_options                           all
% 9.50/1.99  --tptp_safe_out                         true
% 9.50/1.99  --problem_path                          ""
% 9.50/1.99  --include_path                          ""
% 9.50/1.99  --clausifier                            res/vclausify_rel
% 9.50/1.99  --clausifier_options                    --mode clausify
% 9.50/1.99  --stdin                                 false
% 9.50/1.99  --stats_out                             all
% 9.50/1.99  
% 9.50/1.99  ------ General Options
% 9.50/1.99  
% 9.50/1.99  --fof                                   false
% 9.50/1.99  --time_out_real                         305.
% 9.50/1.99  --time_out_virtual                      -1.
% 9.50/1.99  --symbol_type_check                     false
% 9.50/1.99  --clausify_out                          false
% 9.50/1.99  --sig_cnt_out                           false
% 9.50/1.99  --trig_cnt_out                          false
% 9.50/1.99  --trig_cnt_out_tolerance                1.
% 9.50/1.99  --trig_cnt_out_sk_spl                   false
% 9.50/1.99  --abstr_cl_out                          false
% 9.50/1.99  
% 9.50/1.99  ------ Global Options
% 9.50/1.99  
% 9.50/1.99  --schedule                              default
% 9.50/1.99  --add_important_lit                     false
% 9.50/1.99  --prop_solver_per_cl                    1000
% 9.50/1.99  --min_unsat_core                        false
% 9.50/1.99  --soft_assumptions                      false
% 9.50/1.99  --soft_lemma_size                       3
% 9.50/1.99  --prop_impl_unit_size                   0
% 9.50/1.99  --prop_impl_unit                        []
% 9.50/1.99  --share_sel_clauses                     true
% 9.50/1.99  --reset_solvers                         false
% 9.50/1.99  --bc_imp_inh                            [conj_cone]
% 9.50/1.99  --conj_cone_tolerance                   3.
% 9.50/1.99  --extra_neg_conj                        none
% 9.50/1.99  --large_theory_mode                     true
% 9.50/1.99  --prolific_symb_bound                   200
% 9.50/1.99  --lt_threshold                          2000
% 9.50/1.99  --clause_weak_htbl                      true
% 9.50/1.99  --gc_record_bc_elim                     false
% 9.50/1.99  
% 9.50/1.99  ------ Preprocessing Options
% 9.50/1.99  
% 9.50/1.99  --preprocessing_flag                    true
% 9.50/1.99  --time_out_prep_mult                    0.1
% 9.50/1.99  --splitting_mode                        input
% 9.50/1.99  --splitting_grd                         true
% 9.50/1.99  --splitting_cvd                         false
% 9.50/1.99  --splitting_cvd_svl                     false
% 9.50/1.99  --splitting_nvd                         32
% 9.50/1.99  --sub_typing                            true
% 9.50/1.99  --prep_gs_sim                           true
% 9.50/1.99  --prep_unflatten                        true
% 9.50/1.99  --prep_res_sim                          true
% 9.50/1.99  --prep_upred                            true
% 9.50/1.99  --prep_sem_filter                       exhaustive
% 9.50/1.99  --prep_sem_filter_out                   false
% 9.50/1.99  --pred_elim                             true
% 9.50/1.99  --res_sim_input                         true
% 9.50/1.99  --eq_ax_congr_red                       true
% 9.50/1.99  --pure_diseq_elim                       true
% 9.50/1.99  --brand_transform                       false
% 9.50/1.99  --non_eq_to_eq                          false
% 9.50/1.99  --prep_def_merge                        true
% 9.50/1.99  --prep_def_merge_prop_impl              false
% 9.50/1.99  --prep_def_merge_mbd                    true
% 9.50/1.99  --prep_def_merge_tr_red                 false
% 9.50/1.99  --prep_def_merge_tr_cl                  false
% 9.50/1.99  --smt_preprocessing                     true
% 9.50/1.99  --smt_ac_axioms                         fast
% 9.50/1.99  --preprocessed_out                      false
% 9.50/1.99  --preprocessed_stats                    false
% 9.50/1.99  
% 9.50/1.99  ------ Abstraction refinement Options
% 9.50/1.99  
% 9.50/1.99  --abstr_ref                             []
% 9.50/1.99  --abstr_ref_prep                        false
% 9.50/1.99  --abstr_ref_until_sat                   false
% 9.50/1.99  --abstr_ref_sig_restrict                funpre
% 9.50/1.99  --abstr_ref_af_restrict_to_split_sk     false
% 9.50/1.99  --abstr_ref_under                       []
% 9.50/1.99  
% 9.50/1.99  ------ SAT Options
% 9.50/1.99  
% 9.50/1.99  --sat_mode                              false
% 9.50/1.99  --sat_fm_restart_options                ""
% 9.50/1.99  --sat_gr_def                            false
% 9.50/1.99  --sat_epr_types                         true
% 9.50/1.99  --sat_non_cyclic_types                  false
% 9.50/1.99  --sat_finite_models                     false
% 9.50/1.99  --sat_fm_lemmas                         false
% 9.50/1.99  --sat_fm_prep                           false
% 9.50/1.99  --sat_fm_uc_incr                        true
% 9.50/1.99  --sat_out_model                         small
% 9.50/1.99  --sat_out_clauses                       false
% 9.50/1.99  
% 9.50/1.99  ------ QBF Options
% 9.50/1.99  
% 9.50/1.99  --qbf_mode                              false
% 9.50/1.99  --qbf_elim_univ                         false
% 9.50/1.99  --qbf_dom_inst                          none
% 9.50/1.99  --qbf_dom_pre_inst                      false
% 9.50/1.99  --qbf_sk_in                             false
% 9.50/1.99  --qbf_pred_elim                         true
% 9.50/1.99  --qbf_split                             512
% 9.50/1.99  
% 9.50/1.99  ------ BMC1 Options
% 9.50/1.99  
% 9.50/1.99  --bmc1_incremental                      false
% 9.50/1.99  --bmc1_axioms                           reachable_all
% 9.50/1.99  --bmc1_min_bound                        0
% 9.50/1.99  --bmc1_max_bound                        -1
% 9.50/1.99  --bmc1_max_bound_default                -1
% 9.50/1.99  --bmc1_symbol_reachability              true
% 9.50/1.99  --bmc1_property_lemmas                  false
% 9.50/1.99  --bmc1_k_induction                      false
% 9.50/1.99  --bmc1_non_equiv_states                 false
% 9.50/1.99  --bmc1_deadlock                         false
% 9.50/1.99  --bmc1_ucm                              false
% 9.50/1.99  --bmc1_add_unsat_core                   none
% 9.50/1.99  --bmc1_unsat_core_children              false
% 9.50/1.99  --bmc1_unsat_core_extrapolate_axioms    false
% 9.50/1.99  --bmc1_out_stat                         full
% 9.50/1.99  --bmc1_ground_init                      false
% 9.50/1.99  --bmc1_pre_inst_next_state              false
% 9.50/1.99  --bmc1_pre_inst_state                   false
% 9.50/1.99  --bmc1_pre_inst_reach_state             false
% 9.50/1.99  --bmc1_out_unsat_core                   false
% 9.50/1.99  --bmc1_aig_witness_out                  false
% 9.50/1.99  --bmc1_verbose                          false
% 9.50/1.99  --bmc1_dump_clauses_tptp                false
% 9.50/1.99  --bmc1_dump_unsat_core_tptp             false
% 9.50/1.99  --bmc1_dump_file                        -
% 9.50/1.99  --bmc1_ucm_expand_uc_limit              128
% 9.50/1.99  --bmc1_ucm_n_expand_iterations          6
% 9.50/1.99  --bmc1_ucm_extend_mode                  1
% 9.50/1.99  --bmc1_ucm_init_mode                    2
% 9.50/1.99  --bmc1_ucm_cone_mode                    none
% 9.50/1.99  --bmc1_ucm_reduced_relation_type        0
% 9.50/1.99  --bmc1_ucm_relax_model                  4
% 9.50/1.99  --bmc1_ucm_full_tr_after_sat            true
% 9.50/1.99  --bmc1_ucm_expand_neg_assumptions       false
% 9.50/1.99  --bmc1_ucm_layered_model                none
% 9.50/1.99  --bmc1_ucm_max_lemma_size               10
% 9.50/1.99  
% 9.50/1.99  ------ AIG Options
% 9.50/1.99  
% 9.50/1.99  --aig_mode                              false
% 9.50/1.99  
% 9.50/1.99  ------ Instantiation Options
% 9.50/1.99  
% 9.50/1.99  --instantiation_flag                    false
% 9.50/1.99  --inst_sos_flag                         false
% 9.50/1.99  --inst_sos_phase                        true
% 9.50/1.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 9.50/1.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 9.50/1.99  --inst_lit_sel_side                     num_symb
% 9.50/1.99  --inst_solver_per_active                1400
% 9.50/1.99  --inst_solver_calls_frac                1.
% 9.50/1.99  --inst_passive_queue_type               priority_queues
% 9.50/1.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 9.50/1.99  --inst_passive_queues_freq              [25;2]
% 9.50/1.99  --inst_dismatching                      true
% 9.50/1.99  --inst_eager_unprocessed_to_passive     true
% 9.50/1.99  --inst_prop_sim_given                   true
% 9.50/1.99  --inst_prop_sim_new                     false
% 9.50/1.99  --inst_subs_new                         false
% 9.50/1.99  --inst_eq_res_simp                      false
% 9.50/1.99  --inst_subs_given                       false
% 9.50/1.99  --inst_orphan_elimination               true
% 9.50/1.99  --inst_learning_loop_flag               true
% 9.50/1.99  --inst_learning_start                   3000
% 9.50/1.99  --inst_learning_factor                  2
% 9.50/1.99  --inst_start_prop_sim_after_learn       3
% 9.50/1.99  --inst_sel_renew                        solver
% 9.50/1.99  --inst_lit_activity_flag                true
% 9.50/1.99  --inst_restr_to_given                   false
% 9.50/1.99  --inst_activity_threshold               500
% 9.50/1.99  --inst_out_proof                        true
% 9.50/1.99  
% 9.50/1.99  ------ Resolution Options
% 9.50/1.99  
% 9.50/1.99  --resolution_flag                       false
% 9.50/1.99  --res_lit_sel                           adaptive
% 9.50/1.99  --res_lit_sel_side                      none
% 9.50/1.99  --res_ordering                          kbo
% 9.50/1.99  --res_to_prop_solver                    active
% 9.50/1.99  --res_prop_simpl_new                    false
% 9.50/1.99  --res_prop_simpl_given                  true
% 9.50/1.99  --res_passive_queue_type                priority_queues
% 9.50/1.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 9.50/1.99  --res_passive_queues_freq               [15;5]
% 9.50/1.99  --res_forward_subs                      full
% 9.50/1.99  --res_backward_subs                     full
% 9.50/1.99  --res_forward_subs_resolution           true
% 9.50/1.99  --res_backward_subs_resolution          true
% 9.50/1.99  --res_orphan_elimination                true
% 9.50/1.99  --res_time_limit                        2.
% 9.50/1.99  --res_out_proof                         true
% 9.50/1.99  
% 9.50/1.99  ------ Superposition Options
% 9.50/1.99  
% 9.50/1.99  --superposition_flag                    true
% 9.50/1.99  --sup_passive_queue_type                priority_queues
% 9.50/1.99  --sup_passive_queues                    [[-conj_dist;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 9.50/1.99  --sup_passive_queues_freq               [8;1;4]
% 9.50/1.99  --demod_completeness_check              fast
% 9.50/1.99  --demod_use_ground                      true
% 9.50/1.99  --sup_to_prop_solver                    active
% 9.50/1.99  --sup_prop_simpl_new                    false
% 9.50/1.99  --sup_prop_simpl_given                  false
% 9.50/1.99  --sup_fun_splitting                     true
% 9.50/1.99  --sup_smt_interval                      10000
% 9.50/1.99  
% 9.50/1.99  ------ Superposition Simplification Setup
% 9.50/1.99  
% 9.50/1.99  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 9.50/1.99  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 9.50/1.99  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 9.50/1.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 9.50/1.99  --sup_full_triv                         [TrivRules]
% 9.50/1.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 9.50/1.99  --sup_full_bw                           [BwDemod;BwSubsumption]
% 9.50/1.99  --sup_immed_triv                        [TrivRules]
% 9.50/1.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 9.50/1.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 9.50/1.99  --sup_immed_bw_main                     []
% 9.50/1.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 9.50/1.99  --sup_input_triv                        [Unflattening;TrivRules]
% 9.50/1.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 9.50/1.99  --sup_input_bw                          [BwDemod;BwSubsumption]
% 9.50/1.99  
% 9.50/1.99  ------ Combination Options
% 9.50/1.99  
% 9.50/1.99  --comb_res_mult                         1
% 9.50/1.99  --comb_sup_mult                         1
% 9.50/1.99  --comb_inst_mult                        1000000
% 9.50/1.99  
% 9.50/1.99  ------ Debug Options
% 9.50/1.99  
% 9.50/1.99  --dbg_backtrace                         false
% 9.50/1.99  --dbg_dump_prop_clauses                 false
% 9.50/1.99  --dbg_dump_prop_clauses_file            -
% 9.50/1.99  --dbg_out_stat                          false
% 9.50/1.99  
% 9.50/1.99  
% 9.50/1.99  
% 9.50/1.99  
% 9.50/1.99  ------ Proving...
% 9.50/1.99  
% 9.50/1.99  
% 9.50/1.99  % SZS status Theorem for theBenchmark.p
% 9.50/1.99  
% 9.50/1.99   Resolution empty clause
% 9.50/1.99  
% 9.50/1.99  % SZS output start CNFRefutation for theBenchmark.p
% 9.50/1.99  
% 9.50/1.99  fof(f1,axiom,(
% 9.50/1.99    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 9.50/1.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 9.50/1.99  
% 9.50/1.99  fof(f14,plain,(
% 9.50/1.99    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 9.50/1.99    inference(cnf_transformation,[],[f1])).
% 9.50/1.99  
% 9.50/1.99  fof(f3,axiom,(
% 9.50/1.99    ! [X0,X1] : k3_xboole_0(X0,X0) = X0),
% 9.50/1.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 9.50/1.99  
% 9.50/1.99  fof(f10,plain,(
% 9.50/1.99    ! [X0] : k3_xboole_0(X0,X0) = X0),
% 9.50/1.99    inference(rectify,[],[f3])).
% 9.50/1.99  
% 9.50/1.99  fof(f16,plain,(
% 9.50/1.99    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 9.50/1.99    inference(cnf_transformation,[],[f10])).
% 9.50/1.99  
% 9.50/1.99  fof(f5,axiom,(
% 9.50/1.99    ! [X0,X1,X2] : k3_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(k3_xboole_0(X0,X1),X2)),
% 9.50/1.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 9.50/1.99  
% 9.50/1.99  fof(f18,plain,(
% 9.50/1.99    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(k3_xboole_0(X0,X1),X2)) )),
% 9.50/1.99    inference(cnf_transformation,[],[f5])).
% 9.50/1.99  
% 9.50/1.99  fof(f6,axiom,(
% 9.50/1.99    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)),
% 9.50/1.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 9.50/1.99  
% 9.50/1.99  fof(f19,plain,(
% 9.50/1.99    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)) )),
% 9.50/1.99    inference(cnf_transformation,[],[f6])).
% 9.50/1.99  
% 9.50/1.99  fof(f4,axiom,(
% 9.50/1.99    ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1)),
% 9.50/1.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 9.50/1.99  
% 9.50/1.99  fof(f17,plain,(
% 9.50/1.99    ( ! [X0,X1] : (k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1)) )),
% 9.50/1.99    inference(cnf_transformation,[],[f4])).
% 9.50/1.99  
% 9.50/1.99  fof(f22,plain,(
% 9.50/1.99    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) = k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(k3_xboole_0(X0,X1),X2))) )),
% 9.50/1.99    inference(definition_unfolding,[],[f19,f17,f17])).
% 9.50/1.99  
% 9.50/1.99  fof(f7,axiom,(
% 9.50/1.99    ! [X0,X1,X2] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2)),
% 9.50/1.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 9.50/1.99  
% 9.50/1.99  fof(f20,plain,(
% 9.50/1.99    ( ! [X2,X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2)) )),
% 9.50/1.99    inference(cnf_transformation,[],[f7])).
% 9.50/1.99  
% 9.50/1.99  fof(f2,axiom,(
% 9.50/1.99    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)),
% 9.50/1.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 9.50/1.99  
% 9.50/1.99  fof(f15,plain,(
% 9.50/1.99    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)) )),
% 9.50/1.99    inference(cnf_transformation,[],[f2])).
% 9.50/1.99  
% 9.50/1.99  fof(f8,conjecture,(
% 9.50/1.99    ! [X0,X1,X2] : k3_xboole_0(k4_xboole_0(X0,X2),X1) = k4_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X2,X1))),
% 9.50/1.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 9.50/1.99  
% 9.50/1.99  fof(f9,negated_conjecture,(
% 9.50/1.99    ~! [X0,X1,X2] : k3_xboole_0(k4_xboole_0(X0,X2),X1) = k4_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X2,X1))),
% 9.50/1.99    inference(negated_conjecture,[],[f8])).
% 9.50/1.99  
% 9.50/1.99  fof(f11,plain,(
% 9.50/1.99    ? [X0,X1,X2] : k3_xboole_0(k4_xboole_0(X0,X2),X1) != k4_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X2,X1))),
% 9.50/1.99    inference(ennf_transformation,[],[f9])).
% 9.50/1.99  
% 9.50/1.99  fof(f12,plain,(
% 9.50/1.99    ? [X0,X1,X2] : k3_xboole_0(k4_xboole_0(X0,X2),X1) != k4_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X2,X1)) => k3_xboole_0(k4_xboole_0(sK0,sK2),sK1) != k4_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK2,sK1))),
% 9.50/1.99    introduced(choice_axiom,[])).
% 9.50/1.99  
% 9.50/1.99  fof(f13,plain,(
% 9.50/1.99    k3_xboole_0(k4_xboole_0(sK0,sK2),sK1) != k4_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK2,sK1))),
% 9.50/1.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f11,f12])).
% 9.50/1.99  
% 9.50/1.99  fof(f21,plain,(
% 9.50/1.99    k3_xboole_0(k4_xboole_0(sK0,sK2),sK1) != k4_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK2,sK1))),
% 9.50/1.99    inference(cnf_transformation,[],[f13])).
% 9.50/1.99  
% 9.50/1.99  fof(f23,plain,(
% 9.50/1.99    k3_xboole_0(k5_xboole_0(sK0,k3_xboole_0(sK0,sK2)),sK1) != k5_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK2,sK1)))),
% 9.50/1.99    inference(definition_unfolding,[],[f21,f17,f17])).
% 9.50/1.99  
% 9.50/1.99  cnf(c_0,plain,
% 9.50/1.99      ( k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
% 9.50/1.99      inference(cnf_transformation,[],[f14]) ).
% 9.50/1.99  
% 9.50/1.99  cnf(c_2,plain,
% 9.50/1.99      ( k3_xboole_0(X0,X0) = X0 ),
% 9.50/1.99      inference(cnf_transformation,[],[f16]) ).
% 9.50/1.99  
% 9.50/1.99  cnf(c_3,plain,
% 9.50/1.99      ( k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2)) ),
% 9.50/1.99      inference(cnf_transformation,[],[f18]) ).
% 9.50/1.99  
% 9.50/1.99  cnf(c_33,plain,
% 9.50/1.99      ( k3_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
% 9.50/1.99      inference(superposition,[status(thm)],[c_2,c_3]) ).
% 9.50/1.99  
% 9.50/1.99  cnf(c_37,plain,
% 9.50/1.99      ( k3_xboole_0(X0,k3_xboole_0(X1,X0)) = k3_xboole_0(X0,X1) ),
% 9.50/1.99      inference(superposition,[status(thm)],[c_0,c_33]) ).
% 9.50/1.99  
% 9.50/1.99  cnf(c_49,plain,
% 9.50/1.99      ( k3_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k3_xboole_0(k3_xboole_0(X0,X1),X0) ),
% 9.50/1.99      inference(superposition,[status(thm)],[c_33,c_37]) ).
% 9.50/1.99  
% 9.50/1.99  cnf(c_58,plain,
% 9.50/1.99      ( k3_xboole_0(k3_xboole_0(X0,X1),X0) = k3_xboole_0(X0,X1) ),
% 9.50/1.99      inference(demodulation,[status(thm)],[c_49,c_2]) ).
% 9.50/1.99  
% 9.50/1.99  cnf(c_64,plain,
% 9.50/1.99      ( k3_xboole_0(k3_xboole_0(X0,X1),X1) = k3_xboole_0(X1,X0) ),
% 9.50/1.99      inference(superposition,[status(thm)],[c_0,c_58]) ).
% 9.50/1.99  
% 9.50/1.99  cnf(c_26,plain,
% 9.50/1.99      ( k3_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(X1,k3_xboole_0(X0,X2)) ),
% 9.50/1.99      inference(superposition,[status(thm)],[c_3,c_0]) ).
% 9.50/1.99  
% 9.50/1.99  cnf(c_164,plain,
% 9.50/1.99      ( k3_xboole_0(X0,k3_xboole_0(X1,X0)) = k3_xboole_0(X1,X0) ),
% 9.50/1.99      inference(superposition,[status(thm)],[c_2,c_26]) ).
% 9.50/1.99  
% 9.50/1.99  cnf(c_210,plain,
% 9.50/1.99      ( k3_xboole_0(k3_xboole_0(X0,X1),X1) = k3_xboole_0(X1,k3_xboole_0(X1,X0)) ),
% 9.50/1.99      inference(superposition,[status(thm)],[c_64,c_164]) ).
% 9.50/1.99  
% 9.50/1.99  cnf(c_213,plain,
% 9.50/1.99      ( k3_xboole_0(k3_xboole_0(X0,X1),X1) = k3_xboole_0(X1,k3_xboole_0(X0,X1)) ),
% 9.50/1.99      inference(superposition,[status(thm)],[c_164,c_58]) ).
% 9.50/1.99  
% 9.50/1.99  cnf(c_214,plain,
% 9.50/1.99      ( k3_xboole_0(X0,k3_xboole_0(k3_xboole_0(X1,X0),X2)) = k3_xboole_0(k3_xboole_0(X1,X0),X2) ),
% 9.50/1.99      inference(superposition,[status(thm)],[c_164,c_3]) ).
% 9.50/1.99  
% 9.50/1.99  cnf(c_52,plain,
% 9.50/1.99      ( k3_xboole_0(X0,k3_xboole_0(k3_xboole_0(X1,X0),X2)) = k3_xboole_0(k3_xboole_0(X0,X1),X2) ),
% 9.50/1.99      inference(superposition,[status(thm)],[c_37,c_3]) ).
% 9.50/1.99  
% 9.50/1.99  cnf(c_56,plain,
% 9.50/1.99      ( k3_xboole_0(X0,k3_xboole_0(k3_xboole_0(X1,X0),X2)) = k3_xboole_0(X0,k3_xboole_0(X1,X2)) ),
% 9.50/1.99      inference(light_normalisation,[status(thm)],[c_52,c_3]) ).
% 9.50/1.99  
% 9.50/1.99  cnf(c_237,plain,
% 9.50/1.99      ( k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X1,k3_xboole_0(X0,X2)) ),
% 9.50/1.99      inference(light_normalisation,[status(thm)],[c_214,c_56]) ).
% 9.50/1.99  
% 9.50/1.99  cnf(c_238,plain,
% 9.50/1.99      ( k3_xboole_0(k3_xboole_0(X0,X1),X1) = k3_xboole_0(X0,X1) ),
% 9.50/1.99      inference(demodulation,[status(thm)],[c_213,c_164,c_237]) ).
% 9.50/1.99  
% 9.50/1.99  cnf(c_242,plain,
% 9.50/1.99      ( k3_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_xboole_0(X1,X0) ),
% 9.50/1.99      inference(demodulation,[status(thm)],[c_210,c_238]) ).
% 9.50/1.99  
% 9.50/1.99  cnf(c_4,plain,
% 9.50/1.99      ( k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(k3_xboole_0(X0,X1),X2)) = k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) ),
% 9.50/1.99      inference(cnf_transformation,[],[f22]) ).
% 9.50/1.99  
% 9.50/1.99  cnf(c_5,plain,
% 9.50/1.99      ( k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
% 9.50/1.99      inference(cnf_transformation,[],[f20]) ).
% 9.50/1.99  
% 9.50/1.99  cnf(c_1,plain,
% 9.50/1.99      ( k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
% 9.50/1.99      inference(cnf_transformation,[],[f15]) ).
% 9.50/1.99  
% 9.50/1.99  cnf(c_18,plain,
% 9.50/1.99      ( k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,k3_xboole_0(X1,X2))) = k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) ),
% 9.50/1.99      inference(theory_normalisation,[status(thm)],[c_4,c_5,c_1,c_3,c_0]) ).
% 9.50/1.99  
% 9.50/1.99  cnf(c_311,plain,
% 9.50/1.99      ( k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X1,k3_xboole_0(k3_xboole_0(X1,X0),X2))) = k3_xboole_0(X1,k5_xboole_0(k3_xboole_0(X1,X0),k3_xboole_0(k3_xboole_0(X1,X0),X2))) ),
% 9.50/1.99      inference(superposition,[status(thm)],[c_242,c_18]) ).
% 9.50/1.99  
% 9.50/1.99  cnf(c_90,plain,
% 9.50/1.99      ( k5_xboole_0(k3_xboole_0(k3_xboole_0(X0,X1),X2),k3_xboole_0(X0,k3_xboole_0(X1,k3_xboole_0(X2,X3)))) = k3_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X2,k3_xboole_0(X2,X3))) ),
% 9.50/1.99      inference(superposition,[status(thm)],[c_3,c_18]) ).
% 9.50/1.99  
% 9.50/1.99  cnf(c_112,plain,
% 9.50/1.99      ( k5_xboole_0(k3_xboole_0(X0,k3_xboole_0(X1,X2)),k3_xboole_0(X0,k3_xboole_0(X1,k3_xboole_0(X2,X3)))) = k3_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X2,k3_xboole_0(X2,X3))) ),
% 9.50/1.99      inference(light_normalisation,[status(thm)],[c_90,c_3]) ).
% 9.50/1.99  
% 9.50/1.99  cnf(c_97,plain,
% 9.50/1.99      ( k5_xboole_0(k3_xboole_0(X0,k3_xboole_0(X1,X2)),k3_xboole_0(X0,k3_xboole_0(X1,k3_xboole_0(X2,X3)))) = k3_xboole_0(X0,k5_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(k3_xboole_0(X1,X2),X3))) ),
% 9.50/1.99      inference(superposition,[status(thm)],[c_3,c_18]) ).
% 9.50/1.99  
% 9.50/1.99  cnf(c_113,plain,
% 9.50/1.99      ( k3_xboole_0(X0,k5_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(k3_xboole_0(X1,X2),X3))) = k3_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X2,k3_xboole_0(X2,X3))) ),
% 9.50/1.99      inference(demodulation,[status(thm)],[c_112,c_97]) ).
% 9.50/1.99  
% 9.50/1.99  cnf(c_183,plain,
% 9.50/1.99      ( k3_xboole_0(X0,k3_xboole_0(X1,k3_xboole_0(X0,X2))) = k3_xboole_0(X0,k3_xboole_0(X1,X2)) ),
% 9.50/1.99      inference(superposition,[status(thm)],[c_26,c_33]) ).
% 9.50/1.99  
% 9.50/1.99  cnf(c_187,plain,
% 9.50/1.99      ( k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X1,k3_xboole_0(X0,X2))) = k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) ),
% 9.50/1.99      inference(superposition,[status(thm)],[c_26,c_18]) ).
% 9.50/1.99  
% 9.50/1.99  cnf(c_338,plain,
% 9.50/1.99      ( k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) = k3_xboole_0(X1,k5_xboole_0(X0,k3_xboole_0(X0,X2))) ),
% 9.50/1.99      inference(demodulation,[status(thm)],[c_311,c_2,c_113,c_183,c_187,c_237]) ).
% 9.50/1.99  
% 9.50/1.99  cnf(c_94,plain,
% 9.50/1.99      ( k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,k3_xboole_0(X2,X1))) = k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) ),
% 9.50/1.99      inference(superposition,[status(thm)],[c_0,c_18]) ).
% 9.50/1.99  
% 9.50/1.99  cnf(c_6,negated_conjecture,
% 9.50/1.99      ( k3_xboole_0(k5_xboole_0(sK0,k3_xboole_0(sK0,sK2)),sK1) != k5_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK2,sK1))) ),
% 9.50/1.99      inference(cnf_transformation,[],[f23]) ).
% 9.50/1.99  
% 9.50/1.99  cnf(c_17,negated_conjecture,
% 9.50/1.99      ( k5_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK0,k3_xboole_0(sK2,k3_xboole_0(sK1,sK1)))) != k3_xboole_0(sK1,k5_xboole_0(sK0,k3_xboole_0(sK0,sK2))) ),
% 9.50/1.99      inference(theory_normalisation,[status(thm)],[c_6,c_5,c_1,c_3,c_0]) ).
% 9.50/1.99  
% 9.50/1.99  cnf(c_25,plain,
% 9.50/1.99      ( k5_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK0,k3_xboole_0(sK2,sK1))) != k3_xboole_0(sK1,k5_xboole_0(sK0,k3_xboole_0(sK0,sK2))) ),
% 9.50/1.99      inference(demodulation,[status(thm)],[c_17,c_2]) ).
% 9.50/1.99  
% 9.50/1.99  cnf(c_24580,plain,
% 9.50/1.99      ( k3_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK2))) != k3_xboole_0(sK1,k5_xboole_0(sK0,k3_xboole_0(sK0,sK2))) ),
% 9.50/1.99      inference(demodulation,[status(thm)],[c_94,c_25]) ).
% 9.50/1.99  
% 9.50/1.99  cnf(c_35617,plain,
% 9.50/1.99      ( k3_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK2))) != k3_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK2))) ),
% 9.50/1.99      inference(demodulation,[status(thm)],[c_338,c_24580]) ).
% 9.50/1.99  
% 9.50/1.99  cnf(c_35618,plain,
% 9.50/1.99      ( $false ),
% 9.50/1.99      inference(theory_normalisation,[status(thm)],[c_35617]) ).
% 9.50/1.99  
% 9.50/1.99  
% 9.50/1.99  % SZS output end CNFRefutation for theBenchmark.p
% 9.50/1.99  
% 9.50/1.99  ------                               Statistics
% 9.50/1.99  
% 9.50/1.99  ------ General
% 9.50/1.99  
% 9.50/1.99  abstr_ref_over_cycles:                  0
% 9.50/1.99  abstr_ref_under_cycles:                 0
% 9.50/1.99  gc_basic_clause_elim:                   0
% 9.50/1.99  forced_gc_time:                         0
% 9.50/1.99  parsing_time:                           0.008
% 9.50/1.99  unif_index_cands_time:                  0.
% 9.50/1.99  unif_index_add_time:                    0.
% 9.50/1.99  orderings_time:                         0.
% 9.50/1.99  out_proof_time:                         0.008
% 9.50/1.99  total_time:                             1.086
% 9.50/1.99  num_of_symbols:                         36
% 9.50/1.99  num_of_terms:                           43254
% 9.50/1.99  
% 9.50/1.99  ------ Preprocessing
% 9.50/1.99  
% 9.50/1.99  num_of_splits:                          0
% 9.50/1.99  num_of_split_atoms:                     0
% 9.50/1.99  num_of_reused_defs:                     0
% 9.50/1.99  num_eq_ax_congr_red:                    0
% 9.50/1.99  num_of_sem_filtered_clauses:            0
% 9.50/1.99  num_of_subtypes:                        0
% 9.50/1.99  monotx_restored_types:                  0
% 9.50/1.99  sat_num_of_epr_types:                   0
% 9.50/1.99  sat_num_of_non_cyclic_types:            0
% 9.50/1.99  sat_guarded_non_collapsed_types:        0
% 9.50/1.99  num_pure_diseq_elim:                    0
% 9.50/1.99  simp_replaced_by:                       0
% 9.50/1.99  res_preprocessed:                       18
% 9.50/1.99  prep_upred:                             0
% 9.50/1.99  prep_unflattend:                        0
% 9.50/1.99  smt_new_axioms:                         0
% 9.50/1.99  pred_elim_cands:                        0
% 9.50/1.99  pred_elim:                              0
% 9.50/1.99  pred_elim_cl:                           0
% 9.50/1.99  pred_elim_cycles:                       0
% 9.50/1.99  merged_defs:                            0
% 9.50/1.99  merged_defs_ncl:                        0
% 9.50/1.99  bin_hyper_res:                          0
% 9.50/1.99  prep_cycles:                            2
% 9.50/1.99  pred_elim_time:                         0.
% 9.50/1.99  splitting_time:                         0.
% 9.50/1.99  sem_filter_time:                        0.
% 9.50/1.99  monotx_time:                            0.
% 9.50/1.99  subtype_inf_time:                       0.
% 9.50/1.99  
% 9.50/1.99  ------ Problem properties
% 9.50/1.99  
% 9.50/1.99  clauses:                                7
% 9.50/1.99  conjectures:                            1
% 9.50/1.99  epr:                                    0
% 9.50/1.99  horn:                                   7
% 9.50/1.99  ground:                                 1
% 9.50/1.99  unary:                                  7
% 9.50/1.99  binary:                                 0
% 9.50/1.99  lits:                                   7
% 9.50/1.99  lits_eq:                                7
% 9.50/1.99  fd_pure:                                0
% 9.50/1.99  fd_pseudo:                              0
% 9.50/1.99  fd_cond:                                0
% 9.50/1.99  fd_pseudo_cond:                         0
% 9.50/1.99  ac_symbols:                             2
% 9.50/1.99  
% 9.50/1.99  ------ Propositional Solver
% 9.50/1.99  
% 9.50/1.99  prop_solver_calls:                      13
% 9.50/1.99  prop_fast_solver_calls:                 48
% 9.50/1.99  smt_solver_calls:                       0
% 9.50/1.99  smt_fast_solver_calls:                  0
% 9.50/1.99  prop_num_of_clauses:                    167
% 9.50/1.99  prop_preprocess_simplified:             312
% 9.50/1.99  prop_fo_subsumed:                       0
% 9.50/1.99  prop_solver_time:                       0.
% 9.50/1.99  smt_solver_time:                        0.
% 9.50/1.99  smt_fast_solver_time:                   0.
% 9.50/1.99  prop_fast_solver_time:                  0.
% 9.50/1.99  prop_unsat_core_time:                   0.
% 9.50/1.99  
% 9.50/1.99  ------ QBF
% 9.50/1.99  
% 9.50/1.99  qbf_q_res:                              0
% 9.50/1.99  qbf_num_tautologies:                    0
% 9.50/1.99  qbf_prep_cycles:                        0
% 9.50/1.99  
% 9.50/1.99  ------ BMC1
% 9.50/1.99  
% 9.50/1.99  bmc1_current_bound:                     -1
% 9.50/1.99  bmc1_last_solved_bound:                 -1
% 9.50/1.99  bmc1_unsat_core_size:                   -1
% 9.50/1.99  bmc1_unsat_core_parents_size:           -1
% 9.50/1.99  bmc1_merge_next_fun:                    0
% 9.50/1.99  bmc1_unsat_core_clauses_time:           0.
% 9.50/1.99  
% 9.50/1.99  ------ Instantiation
% 9.50/1.99  
% 9.50/1.99  inst_num_of_clauses:                    0
% 9.50/1.99  inst_num_in_passive:                    0
% 9.50/1.99  inst_num_in_active:                     0
% 9.50/1.99  inst_num_in_unprocessed:                0
% 9.50/1.99  inst_num_of_loops:                      0
% 9.50/1.99  inst_num_of_learning_restarts:          0
% 9.50/1.99  inst_num_moves_active_passive:          0
% 9.50/1.99  inst_lit_activity:                      0
% 9.50/1.99  inst_lit_activity_moves:                0
% 9.50/1.99  inst_num_tautologies:                   0
% 9.50/1.99  inst_num_prop_implied:                  0
% 9.50/1.99  inst_num_existing_simplified:           0
% 9.50/1.99  inst_num_eq_res_simplified:             0
% 9.50/1.99  inst_num_child_elim:                    0
% 9.50/1.99  inst_num_of_dismatching_blockings:      0
% 9.50/1.99  inst_num_of_non_proper_insts:           0
% 9.50/1.99  inst_num_of_duplicates:                 0
% 9.50/1.99  inst_inst_num_from_inst_to_res:         0
% 9.50/1.99  inst_dismatching_checking_time:         0.
% 9.50/1.99  
% 9.50/1.99  ------ Resolution
% 9.50/1.99  
% 9.50/1.99  res_num_of_clauses:                     0
% 9.50/1.99  res_num_in_passive:                     0
% 9.50/1.99  res_num_in_active:                      0
% 9.50/1.99  res_num_of_loops:                       20
% 9.50/1.99  res_forward_subset_subsumed:            0
% 9.50/1.99  res_backward_subset_subsumed:           0
% 9.50/1.99  res_forward_subsumed:                   0
% 9.50/1.99  res_backward_subsumed:                  0
% 9.50/1.99  res_forward_subsumption_resolution:     0
% 9.50/1.99  res_backward_subsumption_resolution:    0
% 9.50/1.99  res_clause_to_clause_subsumption:       161533
% 9.50/1.99  res_orphan_elimination:                 0
% 9.50/1.99  res_tautology_del:                      0
% 9.50/1.99  res_num_eq_res_simplified:              0
% 9.50/1.99  res_num_sel_changes:                    0
% 9.50/1.99  res_moves_from_active_to_pass:          0
% 9.50/1.99  
% 9.50/1.99  ------ Superposition
% 9.50/1.99  
% 9.50/1.99  sup_time_total:                         0.
% 9.50/1.99  sup_time_generating:                    0.
% 9.50/1.99  sup_time_sim_full:                      0.
% 9.50/1.99  sup_time_sim_immed:                     0.
% 9.50/1.99  
% 9.50/1.99  sup_num_of_clauses:                     2802
% 9.50/1.99  sup_num_in_active:                      113
% 9.50/1.99  sup_num_in_passive:                     2689
% 9.50/1.99  sup_num_of_loops:                       115
% 9.50/1.99  sup_fw_superposition:                   10322
% 9.50/1.99  sup_bw_superposition:                   11086
% 9.50/1.99  sup_immediate_simplified:               12346
% 9.50/1.99  sup_given_eliminated:                   0
% 9.50/1.99  comparisons_done:                       0
% 9.50/1.99  comparisons_avoided:                    0
% 9.50/1.99  
% 9.50/1.99  ------ Simplifications
% 9.50/1.99  
% 9.50/1.99  
% 9.50/1.99  sim_fw_subset_subsumed:                 0
% 9.50/1.99  sim_bw_subset_subsumed:                 0
% 9.50/1.99  sim_fw_subsumed:                        606
% 9.50/1.99  sim_bw_subsumed:                        3
% 9.50/1.99  sim_fw_subsumption_res:                 0
% 9.50/1.99  sim_bw_subsumption_res:                 0
% 9.50/1.99  sim_tautology_del:                      0
% 9.50/1.99  sim_eq_tautology_del:                   967
% 9.50/1.99  sim_eq_res_simp:                        0
% 9.50/1.99  sim_fw_demodulated:                     9160
% 9.50/1.99  sim_bw_demodulated:                     26
% 9.50/1.99  sim_light_normalised:                   4914
% 9.50/1.99  sim_joinable_taut:                      743
% 9.50/1.99  sim_joinable_simp:                      1
% 9.50/1.99  sim_ac_normalised:                      0
% 9.50/1.99  sim_smt_subsumption:                    0
% 9.50/1.99  
%------------------------------------------------------------------------------
