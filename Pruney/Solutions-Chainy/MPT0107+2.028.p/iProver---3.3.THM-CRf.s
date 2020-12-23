%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:25:23 EST 2020

% Result     : Theorem 2.35s
% Output     : CNFRefutation 2.35s
% Verified   : 
% Statistics : Number of formulae       :   68 (2050 expanded)
%              Number of clauses        :   40 ( 666 expanded)
%              Number of leaves         :   10 ( 603 expanded)
%              Depth                    :   23
%              Number of atoms          :   69 (2051 expanded)
%              Number of equality atoms :   68 (2050 expanded)
%              Maximal formula depth    :    5 (   2 average)
%              Maximal clause size      :    2 (   1 average)
%              Maximal term depth       :    6 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f4,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f4])).

fof(f7,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f7])).

fof(f6,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f38,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2) ),
    inference(definition_unfolding,[],[f31,f30,f30])).

fof(f5,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f37,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f29,f30])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f36,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(definition_unfolding,[],[f20,f30,f30])).

fof(f8,axiom,(
    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f8])).

fof(f39,plain,(
    ! [X0,X1] : k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1)) = X0 ),
    inference(definition_unfolding,[],[f32,f30])).

fof(f9,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f9])).

fof(f3,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f3])).

fof(f35,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(k4_xboole_0(X1,X0),X0)) ),
    inference(definition_unfolding,[],[f33,f27])).

fof(f10,conjecture,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f11,negated_conjecture,(
    ~ ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(negated_conjecture,[],[f10])).

fof(f12,plain,(
    ? [X0,X1] : k4_xboole_0(X0,X1) != k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(ennf_transformation,[],[f11])).

fof(f18,plain,
    ( ? [X0,X1] : k4_xboole_0(X0,X1) != k5_xboole_0(X0,k3_xboole_0(X0,X1))
   => k4_xboole_0(sK1,sK2) != k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
    k4_xboole_0(sK1,sK2) != k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f12,f18])).

fof(f34,plain,(
    k4_xboole_0(sK1,sK2) != k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)) ),
    inference(cnf_transformation,[],[f19])).

fof(f40,plain,(
    k4_xboole_0(sK1,sK2) != k2_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))),k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),sK1)) ),
    inference(definition_unfolding,[],[f34,f27,f30])).

cnf(c_8,plain,
    ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f28])).

cnf(c_10,plain,
    ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_856,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(k1_xboole_0,X1))) = k4_xboole_0(k4_xboole_0(X0,X0),X1) ),
    inference(superposition,[status(thm)],[c_8,c_10])).

cnf(c_9,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_377,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X0)) = k4_xboole_0(X0,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_8,c_9])).

cnf(c_385,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X0)) = X0 ),
    inference(light_normalisation,[status(thm)],[c_377,c_8])).

cnf(c_3899,plain,
    ( k4_xboole_0(k4_xboole_0(k4_xboole_0(k1_xboole_0,X0),k4_xboole_0(k1_xboole_0,X0)),X0) = k4_xboole_0(k1_xboole_0,X0) ),
    inference(superposition,[status(thm)],[c_856,c_385])).

cnf(c_1,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_290,plain,
    ( k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0)) = k4_xboole_0(X0,X0) ),
    inference(superposition,[status(thm)],[c_8,c_1])).

cnf(c_401,plain,
    ( k4_xboole_0(X0,k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0))) = X0 ),
    inference(superposition,[status(thm)],[c_290,c_385])).

cnf(c_502,plain,
    ( k4_xboole_0(k4_xboole_0(k1_xboole_0,X0),k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,X0))) = k4_xboole_0(k1_xboole_0,X0) ),
    inference(superposition,[status(thm)],[c_290,c_401])).

cnf(c_374,plain,
    ( k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,X0)) = k4_xboole_0(k1_xboole_0,X0) ),
    inference(superposition,[status(thm)],[c_290,c_9])).

cnf(c_522,plain,
    ( k4_xboole_0(k4_xboole_0(k1_xboole_0,X0),k4_xboole_0(k1_xboole_0,X0)) = k4_xboole_0(k1_xboole_0,X0) ),
    inference(light_normalisation,[status(thm)],[c_502,c_374])).

cnf(c_3917,plain,
    ( k4_xboole_0(k4_xboole_0(k1_xboole_0,X0),X0) = k4_xboole_0(k1_xboole_0,X0) ),
    inference(light_normalisation,[status(thm)],[c_3899,c_522])).

cnf(c_11,plain,
    ( k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f39])).

cnf(c_654,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) = X0 ),
    inference(superposition,[status(thm)],[c_9,c_11])).

cnf(c_2230,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,k4_xboole_0(X1,X0))) = X0 ),
    inference(superposition,[status(thm)],[c_1,c_654])).

cnf(c_4370,plain,
    ( k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(k1_xboole_0,X0)),k4_xboole_0(k4_xboole_0(k1_xboole_0,X0),k4_xboole_0(k1_xboole_0,X0))) = X0 ),
    inference(superposition,[status(thm)],[c_3917,c_2230])).

cnf(c_4421,plain,
    ( k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(k1_xboole_0,X0)),k4_xboole_0(k1_xboole_0,X0)) = X0 ),
    inference(light_normalisation,[status(thm)],[c_4370,c_522])).

cnf(c_0,plain,
    ( k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(k4_xboole_0(X1,X0),X0)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_4376,plain,
    ( k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(k1_xboole_0,X0)),k4_xboole_0(k1_xboole_0,X0)) = k2_xboole_0(X0,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_3917,c_0])).

cnf(c_4422,plain,
    ( k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(demodulation,[status(thm)],[c_4421,c_4376])).

cnf(c_4373,plain,
    ( k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(k1_xboole_0,X0)),k4_xboole_0(k4_xboole_0(k1_xboole_0,X0),X0)) = k2_xboole_0(X0,k4_xboole_0(k1_xboole_0,X0)) ),
    inference(superposition,[status(thm)],[c_3917,c_0])).

cnf(c_4414,plain,
    ( k2_xboole_0(X0,k4_xboole_0(k1_xboole_0,X0)) = k2_xboole_0(X0,k1_xboole_0) ),
    inference(light_normalisation,[status(thm)],[c_4373,c_3917,c_4376])).

cnf(c_4425,plain,
    ( k2_xboole_0(X0,k4_xboole_0(k1_xboole_0,X0)) = X0 ),
    inference(demodulation,[status(thm)],[c_4422,c_4414])).

cnf(c_4595,plain,
    ( k4_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_4425,c_654])).

cnf(c_4618,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X0),X1) = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) ),
    inference(demodulation,[status(thm)],[c_4595,c_856])).

cnf(c_850,plain,
    ( k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,X1))) = k4_xboole_0(k4_xboole_0(X0,X0),X1) ),
    inference(superposition,[status(thm)],[c_290,c_10])).

cnf(c_4620,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X0),X1) = k4_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(demodulation,[status(thm)],[c_4595,c_850])).

cnf(c_4622,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X0),X1) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_4620,c_4595])).

cnf(c_4624,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_4618,c_4622])).

cnf(c_4626,plain,
    ( k4_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_4624,c_8])).

cnf(c_4856,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X0,k4_xboole_0(X0,X1))))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_4626,c_10])).

cnf(c_372,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0))) = k4_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_1,c_9])).

cnf(c_4858,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X0))) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_4856,c_372])).

cnf(c_12,negated_conjecture,
    ( k4_xboole_0(sK1,sK2) != k2_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))),k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),sK1)) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_219,plain,
    ( k2_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK2,sK1)))) != k4_xboole_0(sK1,sK2) ),
    inference(demodulation,[status(thm)],[c_12,c_9,c_10])).

cnf(c_5160,plain,
    ( k2_xboole_0(k4_xboole_0(sK1,sK2),k1_xboole_0) != k4_xboole_0(sK1,sK2) ),
    inference(demodulation,[status(thm)],[c_4858,c_219])).

cnf(c_5161,plain,
    ( k4_xboole_0(sK1,sK2) != k4_xboole_0(sK1,sK2) ),
    inference(demodulation,[status(thm)],[c_5160,c_4422])).

cnf(c_5162,plain,
    ( $false ),
    inference(equality_resolution_simp,[status(thm)],[c_5161])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : iproveropt_run.sh %d %s
% 0.13/0.33  % Computer   : n015.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 13:00:53 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 2.35/0.99  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.35/0.99  
% 2.35/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.35/0.99  
% 2.35/0.99  ------  iProver source info
% 2.35/0.99  
% 2.35/0.99  git: date: 2020-06-30 10:37:57 +0100
% 2.35/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.35/0.99  git: non_committed_changes: false
% 2.35/0.99  git: last_make_outside_of_git: false
% 2.35/0.99  
% 2.35/0.99  ------ 
% 2.35/0.99  
% 2.35/0.99  ------ Input Options
% 2.35/0.99  
% 2.35/0.99  --out_options                           all
% 2.35/0.99  --tptp_safe_out                         true
% 2.35/0.99  --problem_path                          ""
% 2.35/0.99  --include_path                          ""
% 2.35/0.99  --clausifier                            res/vclausify_rel
% 2.35/0.99  --clausifier_options                    --mode clausify
% 2.35/0.99  --stdin                                 false
% 2.35/0.99  --stats_out                             all
% 2.35/0.99  
% 2.35/0.99  ------ General Options
% 2.35/0.99  
% 2.35/0.99  --fof                                   false
% 2.35/0.99  --time_out_real                         305.
% 2.35/0.99  --time_out_virtual                      -1.
% 2.35/0.99  --symbol_type_check                     false
% 2.35/0.99  --clausify_out                          false
% 2.35/0.99  --sig_cnt_out                           false
% 2.35/0.99  --trig_cnt_out                          false
% 2.35/0.99  --trig_cnt_out_tolerance                1.
% 2.35/0.99  --trig_cnt_out_sk_spl                   false
% 2.35/0.99  --abstr_cl_out                          false
% 2.35/0.99  
% 2.35/0.99  ------ Global Options
% 2.35/0.99  
% 2.35/0.99  --schedule                              default
% 2.35/0.99  --add_important_lit                     false
% 2.35/0.99  --prop_solver_per_cl                    1000
% 2.35/0.99  --min_unsat_core                        false
% 2.35/0.99  --soft_assumptions                      false
% 2.35/0.99  --soft_lemma_size                       3
% 2.35/0.99  --prop_impl_unit_size                   0
% 2.35/0.99  --prop_impl_unit                        []
% 2.35/0.99  --share_sel_clauses                     true
% 2.35/0.99  --reset_solvers                         false
% 2.35/0.99  --bc_imp_inh                            [conj_cone]
% 2.35/0.99  --conj_cone_tolerance                   3.
% 2.35/0.99  --extra_neg_conj                        none
% 2.35/0.99  --large_theory_mode                     true
% 2.35/0.99  --prolific_symb_bound                   200
% 2.35/0.99  --lt_threshold                          2000
% 2.35/0.99  --clause_weak_htbl                      true
% 2.35/0.99  --gc_record_bc_elim                     false
% 2.35/0.99  
% 2.35/0.99  ------ Preprocessing Options
% 2.35/0.99  
% 2.35/0.99  --preprocessing_flag                    true
% 2.35/0.99  --time_out_prep_mult                    0.1
% 2.35/0.99  --splitting_mode                        input
% 2.35/0.99  --splitting_grd                         true
% 2.35/0.99  --splitting_cvd                         false
% 2.35/0.99  --splitting_cvd_svl                     false
% 2.35/0.99  --splitting_nvd                         32
% 2.35/0.99  --sub_typing                            true
% 2.35/0.99  --prep_gs_sim                           true
% 2.35/0.99  --prep_unflatten                        true
% 2.35/0.99  --prep_res_sim                          true
% 2.35/0.99  --prep_upred                            true
% 2.35/0.99  --prep_sem_filter                       exhaustive
% 2.35/0.99  --prep_sem_filter_out                   false
% 2.35/0.99  --pred_elim                             true
% 2.35/0.99  --res_sim_input                         true
% 2.35/0.99  --eq_ax_congr_red                       true
% 2.35/0.99  --pure_diseq_elim                       true
% 2.35/0.99  --brand_transform                       false
% 2.35/0.99  --non_eq_to_eq                          false
% 2.35/0.99  --prep_def_merge                        true
% 2.35/0.99  --prep_def_merge_prop_impl              false
% 2.35/0.99  --prep_def_merge_mbd                    true
% 2.35/0.99  --prep_def_merge_tr_red                 false
% 2.35/0.99  --prep_def_merge_tr_cl                  false
% 2.35/0.99  --smt_preprocessing                     true
% 2.35/0.99  --smt_ac_axioms                         fast
% 2.35/0.99  --preprocessed_out                      false
% 2.35/0.99  --preprocessed_stats                    false
% 2.35/0.99  
% 2.35/0.99  ------ Abstraction refinement Options
% 2.35/0.99  
% 2.35/0.99  --abstr_ref                             []
% 2.35/0.99  --abstr_ref_prep                        false
% 2.35/0.99  --abstr_ref_until_sat                   false
% 2.35/0.99  --abstr_ref_sig_restrict                funpre
% 2.35/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 2.35/0.99  --abstr_ref_under                       []
% 2.35/0.99  
% 2.35/0.99  ------ SAT Options
% 2.35/0.99  
% 2.35/0.99  --sat_mode                              false
% 2.35/0.99  --sat_fm_restart_options                ""
% 2.35/0.99  --sat_gr_def                            false
% 2.35/0.99  --sat_epr_types                         true
% 2.35/0.99  --sat_non_cyclic_types                  false
% 2.35/0.99  --sat_finite_models                     false
% 2.35/0.99  --sat_fm_lemmas                         false
% 2.35/0.99  --sat_fm_prep                           false
% 2.35/0.99  --sat_fm_uc_incr                        true
% 2.35/0.99  --sat_out_model                         small
% 2.35/0.99  --sat_out_clauses                       false
% 2.35/0.99  
% 2.35/0.99  ------ QBF Options
% 2.35/0.99  
% 2.35/0.99  --qbf_mode                              false
% 2.35/0.99  --qbf_elim_univ                         false
% 2.35/0.99  --qbf_dom_inst                          none
% 2.35/0.99  --qbf_dom_pre_inst                      false
% 2.35/0.99  --qbf_sk_in                             false
% 2.35/0.99  --qbf_pred_elim                         true
% 2.35/0.99  --qbf_split                             512
% 2.35/0.99  
% 2.35/0.99  ------ BMC1 Options
% 2.35/0.99  
% 2.35/0.99  --bmc1_incremental                      false
% 2.35/0.99  --bmc1_axioms                           reachable_all
% 2.35/0.99  --bmc1_min_bound                        0
% 2.35/0.99  --bmc1_max_bound                        -1
% 2.35/0.99  --bmc1_max_bound_default                -1
% 2.35/0.99  --bmc1_symbol_reachability              true
% 2.35/0.99  --bmc1_property_lemmas                  false
% 2.35/0.99  --bmc1_k_induction                      false
% 2.35/0.99  --bmc1_non_equiv_states                 false
% 2.35/0.99  --bmc1_deadlock                         false
% 2.35/0.99  --bmc1_ucm                              false
% 2.35/0.99  --bmc1_add_unsat_core                   none
% 2.35/0.99  --bmc1_unsat_core_children              false
% 2.35/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 2.35/0.99  --bmc1_out_stat                         full
% 2.35/0.99  --bmc1_ground_init                      false
% 2.35/0.99  --bmc1_pre_inst_next_state              false
% 2.35/0.99  --bmc1_pre_inst_state                   false
% 2.35/0.99  --bmc1_pre_inst_reach_state             false
% 2.35/0.99  --bmc1_out_unsat_core                   false
% 2.35/0.99  --bmc1_aig_witness_out                  false
% 2.35/0.99  --bmc1_verbose                          false
% 2.35/0.99  --bmc1_dump_clauses_tptp                false
% 2.35/0.99  --bmc1_dump_unsat_core_tptp             false
% 2.35/0.99  --bmc1_dump_file                        -
% 2.35/0.99  --bmc1_ucm_expand_uc_limit              128
% 2.35/0.99  --bmc1_ucm_n_expand_iterations          6
% 2.35/0.99  --bmc1_ucm_extend_mode                  1
% 2.35/0.99  --bmc1_ucm_init_mode                    2
% 2.35/0.99  --bmc1_ucm_cone_mode                    none
% 2.35/0.99  --bmc1_ucm_reduced_relation_type        0
% 2.35/0.99  --bmc1_ucm_relax_model                  4
% 2.35/0.99  --bmc1_ucm_full_tr_after_sat            true
% 2.35/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 2.35/0.99  --bmc1_ucm_layered_model                none
% 2.35/0.99  --bmc1_ucm_max_lemma_size               10
% 2.35/0.99  
% 2.35/0.99  ------ AIG Options
% 2.35/0.99  
% 2.35/0.99  --aig_mode                              false
% 2.35/0.99  
% 2.35/0.99  ------ Instantiation Options
% 2.35/0.99  
% 2.35/0.99  --instantiation_flag                    true
% 2.35/0.99  --inst_sos_flag                         false
% 2.35/0.99  --inst_sos_phase                        true
% 2.35/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.35/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.35/0.99  --inst_lit_sel_side                     num_symb
% 2.35/0.99  --inst_solver_per_active                1400
% 2.35/0.99  --inst_solver_calls_frac                1.
% 2.35/0.99  --inst_passive_queue_type               priority_queues
% 2.35/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.35/0.99  --inst_passive_queues_freq              [25;2]
% 2.35/0.99  --inst_dismatching                      true
% 2.35/0.99  --inst_eager_unprocessed_to_passive     true
% 2.35/0.99  --inst_prop_sim_given                   true
% 2.35/0.99  --inst_prop_sim_new                     false
% 2.35/0.99  --inst_subs_new                         false
% 2.35/0.99  --inst_eq_res_simp                      false
% 2.35/0.99  --inst_subs_given                       false
% 2.35/0.99  --inst_orphan_elimination               true
% 2.35/0.99  --inst_learning_loop_flag               true
% 2.35/0.99  --inst_learning_start                   3000
% 2.35/0.99  --inst_learning_factor                  2
% 2.35/0.99  --inst_start_prop_sim_after_learn       3
% 2.35/0.99  --inst_sel_renew                        solver
% 2.35/0.99  --inst_lit_activity_flag                true
% 2.35/0.99  --inst_restr_to_given                   false
% 2.35/0.99  --inst_activity_threshold               500
% 2.35/0.99  --inst_out_proof                        true
% 2.35/0.99  
% 2.35/0.99  ------ Resolution Options
% 2.35/0.99  
% 2.35/0.99  --resolution_flag                       true
% 2.35/0.99  --res_lit_sel                           adaptive
% 2.35/0.99  --res_lit_sel_side                      none
% 2.35/0.99  --res_ordering                          kbo
% 2.35/0.99  --res_to_prop_solver                    active
% 2.35/0.99  --res_prop_simpl_new                    false
% 2.35/0.99  --res_prop_simpl_given                  true
% 2.35/0.99  --res_passive_queue_type                priority_queues
% 2.35/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.35/0.99  --res_passive_queues_freq               [15;5]
% 2.35/0.99  --res_forward_subs                      full
% 2.35/0.99  --res_backward_subs                     full
% 2.35/0.99  --res_forward_subs_resolution           true
% 2.35/0.99  --res_backward_subs_resolution          true
% 2.35/0.99  --res_orphan_elimination                true
% 2.35/0.99  --res_time_limit                        2.
% 2.35/0.99  --res_out_proof                         true
% 2.35/0.99  
% 2.35/0.99  ------ Superposition Options
% 2.35/0.99  
% 2.35/0.99  --superposition_flag                    true
% 2.35/0.99  --sup_passive_queue_type                priority_queues
% 2.35/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.35/0.99  --sup_passive_queues_freq               [8;1;4]
% 2.35/0.99  --demod_completeness_check              fast
% 2.35/0.99  --demod_use_ground                      true
% 2.35/0.99  --sup_to_prop_solver                    passive
% 2.35/0.99  --sup_prop_simpl_new                    true
% 2.35/0.99  --sup_prop_simpl_given                  true
% 2.35/0.99  --sup_fun_splitting                     false
% 2.35/0.99  --sup_smt_interval                      50000
% 2.35/0.99  
% 2.35/0.99  ------ Superposition Simplification Setup
% 2.35/0.99  
% 2.35/0.99  --sup_indices_passive                   []
% 2.35/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.35/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.35/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.35/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 2.35/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.35/0.99  --sup_full_bw                           [BwDemod]
% 2.35/0.99  --sup_immed_triv                        [TrivRules]
% 2.35/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.35/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.35/0.99  --sup_immed_bw_main                     []
% 2.35/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.35/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 2.35/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.35/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.35/0.99  
% 2.35/0.99  ------ Combination Options
% 2.35/0.99  
% 2.35/0.99  --comb_res_mult                         3
% 2.35/0.99  --comb_sup_mult                         2
% 2.35/0.99  --comb_inst_mult                        10
% 2.35/0.99  
% 2.35/0.99  ------ Debug Options
% 2.35/0.99  
% 2.35/0.99  --dbg_backtrace                         false
% 2.35/0.99  --dbg_dump_prop_clauses                 false
% 2.35/0.99  --dbg_dump_prop_clauses_file            -
% 2.35/0.99  --dbg_out_stat                          false
% 2.35/0.99  ------ Parsing...
% 2.35/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.35/0.99  
% 2.35/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 2.35/0.99  
% 2.35/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.35/0.99  
% 2.35/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.35/0.99  ------ Proving...
% 2.35/0.99  ------ Problem Properties 
% 2.35/0.99  
% 2.35/0.99  
% 2.35/0.99  clauses                                 13
% 2.35/0.99  conjectures                             1
% 2.35/0.99  EPR                                     0
% 2.35/0.99  Horn                                    9
% 2.35/0.99  unary                                   7
% 2.35/0.99  binary                                  2
% 2.35/0.99  lits                                    24
% 2.35/0.99  lits eq                                 10
% 2.35/0.99  fd_pure                                 0
% 2.35/0.99  fd_pseudo                               0
% 2.35/0.99  fd_cond                                 0
% 2.35/0.99  fd_pseudo_cond                          3
% 2.35/0.99  AC symbols                              0
% 2.35/0.99  
% 2.35/0.99  ------ Schedule dynamic 5 is on 
% 2.35/0.99  
% 2.35/0.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.35/0.99  
% 2.35/0.99  
% 2.35/0.99  ------ 
% 2.35/0.99  Current options:
% 2.35/0.99  ------ 
% 2.35/0.99  
% 2.35/0.99  ------ Input Options
% 2.35/0.99  
% 2.35/0.99  --out_options                           all
% 2.35/0.99  --tptp_safe_out                         true
% 2.35/0.99  --problem_path                          ""
% 2.35/0.99  --include_path                          ""
% 2.35/0.99  --clausifier                            res/vclausify_rel
% 2.35/0.99  --clausifier_options                    --mode clausify
% 2.35/0.99  --stdin                                 false
% 2.35/0.99  --stats_out                             all
% 2.35/0.99  
% 2.35/0.99  ------ General Options
% 2.35/0.99  
% 2.35/0.99  --fof                                   false
% 2.35/0.99  --time_out_real                         305.
% 2.35/0.99  --time_out_virtual                      -1.
% 2.35/0.99  --symbol_type_check                     false
% 2.35/0.99  --clausify_out                          false
% 2.35/0.99  --sig_cnt_out                           false
% 2.35/0.99  --trig_cnt_out                          false
% 2.35/0.99  --trig_cnt_out_tolerance                1.
% 2.35/0.99  --trig_cnt_out_sk_spl                   false
% 2.35/0.99  --abstr_cl_out                          false
% 2.35/0.99  
% 2.35/0.99  ------ Global Options
% 2.35/0.99  
% 2.35/0.99  --schedule                              default
% 2.35/0.99  --add_important_lit                     false
% 2.35/0.99  --prop_solver_per_cl                    1000
% 2.35/0.99  --min_unsat_core                        false
% 2.35/0.99  --soft_assumptions                      false
% 2.35/0.99  --soft_lemma_size                       3
% 2.35/0.99  --prop_impl_unit_size                   0
% 2.35/0.99  --prop_impl_unit                        []
% 2.35/0.99  --share_sel_clauses                     true
% 2.35/0.99  --reset_solvers                         false
% 2.35/0.99  --bc_imp_inh                            [conj_cone]
% 2.35/0.99  --conj_cone_tolerance                   3.
% 2.35/0.99  --extra_neg_conj                        none
% 2.35/0.99  --large_theory_mode                     true
% 2.35/0.99  --prolific_symb_bound                   200
% 2.35/0.99  --lt_threshold                          2000
% 2.35/0.99  --clause_weak_htbl                      true
% 2.35/0.99  --gc_record_bc_elim                     false
% 2.35/0.99  
% 2.35/0.99  ------ Preprocessing Options
% 2.35/0.99  
% 2.35/0.99  --preprocessing_flag                    true
% 2.35/0.99  --time_out_prep_mult                    0.1
% 2.35/0.99  --splitting_mode                        input
% 2.35/0.99  --splitting_grd                         true
% 2.35/0.99  --splitting_cvd                         false
% 2.35/0.99  --splitting_cvd_svl                     false
% 2.35/0.99  --splitting_nvd                         32
% 2.35/0.99  --sub_typing                            true
% 2.35/0.99  --prep_gs_sim                           true
% 2.35/0.99  --prep_unflatten                        true
% 2.35/0.99  --prep_res_sim                          true
% 2.35/0.99  --prep_upred                            true
% 2.35/0.99  --prep_sem_filter                       exhaustive
% 2.35/0.99  --prep_sem_filter_out                   false
% 2.35/0.99  --pred_elim                             true
% 2.35/0.99  --res_sim_input                         true
% 2.35/0.99  --eq_ax_congr_red                       true
% 2.35/0.99  --pure_diseq_elim                       true
% 2.35/0.99  --brand_transform                       false
% 2.35/0.99  --non_eq_to_eq                          false
% 2.35/0.99  --prep_def_merge                        true
% 2.35/0.99  --prep_def_merge_prop_impl              false
% 2.35/0.99  --prep_def_merge_mbd                    true
% 2.35/0.99  --prep_def_merge_tr_red                 false
% 2.35/0.99  --prep_def_merge_tr_cl                  false
% 2.35/0.99  --smt_preprocessing                     true
% 2.35/0.99  --smt_ac_axioms                         fast
% 2.35/0.99  --preprocessed_out                      false
% 2.35/0.99  --preprocessed_stats                    false
% 2.35/0.99  
% 2.35/0.99  ------ Abstraction refinement Options
% 2.35/0.99  
% 2.35/0.99  --abstr_ref                             []
% 2.35/0.99  --abstr_ref_prep                        false
% 2.35/0.99  --abstr_ref_until_sat                   false
% 2.35/0.99  --abstr_ref_sig_restrict                funpre
% 2.35/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 2.35/0.99  --abstr_ref_under                       []
% 2.35/0.99  
% 2.35/0.99  ------ SAT Options
% 2.35/0.99  
% 2.35/0.99  --sat_mode                              false
% 2.35/0.99  --sat_fm_restart_options                ""
% 2.35/0.99  --sat_gr_def                            false
% 2.35/0.99  --sat_epr_types                         true
% 2.35/0.99  --sat_non_cyclic_types                  false
% 2.35/0.99  --sat_finite_models                     false
% 2.35/0.99  --sat_fm_lemmas                         false
% 2.35/0.99  --sat_fm_prep                           false
% 2.35/0.99  --sat_fm_uc_incr                        true
% 2.35/0.99  --sat_out_model                         small
% 2.35/0.99  --sat_out_clauses                       false
% 2.35/0.99  
% 2.35/0.99  ------ QBF Options
% 2.35/0.99  
% 2.35/0.99  --qbf_mode                              false
% 2.35/0.99  --qbf_elim_univ                         false
% 2.35/0.99  --qbf_dom_inst                          none
% 2.35/0.99  --qbf_dom_pre_inst                      false
% 2.35/0.99  --qbf_sk_in                             false
% 2.35/0.99  --qbf_pred_elim                         true
% 2.35/0.99  --qbf_split                             512
% 2.35/0.99  
% 2.35/0.99  ------ BMC1 Options
% 2.35/0.99  
% 2.35/0.99  --bmc1_incremental                      false
% 2.35/0.99  --bmc1_axioms                           reachable_all
% 2.35/0.99  --bmc1_min_bound                        0
% 2.35/0.99  --bmc1_max_bound                        -1
% 2.35/0.99  --bmc1_max_bound_default                -1
% 2.35/0.99  --bmc1_symbol_reachability              true
% 2.35/0.99  --bmc1_property_lemmas                  false
% 2.35/0.99  --bmc1_k_induction                      false
% 2.35/0.99  --bmc1_non_equiv_states                 false
% 2.35/0.99  --bmc1_deadlock                         false
% 2.35/0.99  --bmc1_ucm                              false
% 2.35/0.99  --bmc1_add_unsat_core                   none
% 2.35/0.99  --bmc1_unsat_core_children              false
% 2.35/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 2.35/0.99  --bmc1_out_stat                         full
% 2.35/0.99  --bmc1_ground_init                      false
% 2.35/0.99  --bmc1_pre_inst_next_state              false
% 2.35/0.99  --bmc1_pre_inst_state                   false
% 2.35/0.99  --bmc1_pre_inst_reach_state             false
% 2.35/0.99  --bmc1_out_unsat_core                   false
% 2.35/0.99  --bmc1_aig_witness_out                  false
% 2.35/0.99  --bmc1_verbose                          false
% 2.35/0.99  --bmc1_dump_clauses_tptp                false
% 2.35/0.99  --bmc1_dump_unsat_core_tptp             false
% 2.35/0.99  --bmc1_dump_file                        -
% 2.35/0.99  --bmc1_ucm_expand_uc_limit              128
% 2.35/0.99  --bmc1_ucm_n_expand_iterations          6
% 2.35/0.99  --bmc1_ucm_extend_mode                  1
% 2.35/0.99  --bmc1_ucm_init_mode                    2
% 2.35/0.99  --bmc1_ucm_cone_mode                    none
% 2.35/0.99  --bmc1_ucm_reduced_relation_type        0
% 2.35/0.99  --bmc1_ucm_relax_model                  4
% 2.35/0.99  --bmc1_ucm_full_tr_after_sat            true
% 2.35/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 2.35/0.99  --bmc1_ucm_layered_model                none
% 2.35/0.99  --bmc1_ucm_max_lemma_size               10
% 2.35/0.99  
% 2.35/0.99  ------ AIG Options
% 2.35/0.99  
% 2.35/0.99  --aig_mode                              false
% 2.35/0.99  
% 2.35/0.99  ------ Instantiation Options
% 2.35/0.99  
% 2.35/0.99  --instantiation_flag                    true
% 2.35/0.99  --inst_sos_flag                         false
% 2.35/0.99  --inst_sos_phase                        true
% 2.35/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.35/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.35/0.99  --inst_lit_sel_side                     none
% 2.35/0.99  --inst_solver_per_active                1400
% 2.35/0.99  --inst_solver_calls_frac                1.
% 2.35/0.99  --inst_passive_queue_type               priority_queues
% 2.35/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.35/0.99  --inst_passive_queues_freq              [25;2]
% 2.35/0.99  --inst_dismatching                      true
% 2.35/0.99  --inst_eager_unprocessed_to_passive     true
% 2.35/0.99  --inst_prop_sim_given                   true
% 2.35/0.99  --inst_prop_sim_new                     false
% 2.35/0.99  --inst_subs_new                         false
% 2.35/0.99  --inst_eq_res_simp                      false
% 2.35/0.99  --inst_subs_given                       false
% 2.35/0.99  --inst_orphan_elimination               true
% 2.35/0.99  --inst_learning_loop_flag               true
% 2.35/0.99  --inst_learning_start                   3000
% 2.35/0.99  --inst_learning_factor                  2
% 2.35/0.99  --inst_start_prop_sim_after_learn       3
% 2.35/0.99  --inst_sel_renew                        solver
% 2.35/0.99  --inst_lit_activity_flag                true
% 2.35/0.99  --inst_restr_to_given                   false
% 2.35/0.99  --inst_activity_threshold               500
% 2.35/0.99  --inst_out_proof                        true
% 2.35/0.99  
% 2.35/0.99  ------ Resolution Options
% 2.35/0.99  
% 2.35/0.99  --resolution_flag                       false
% 2.35/0.99  --res_lit_sel                           adaptive
% 2.35/0.99  --res_lit_sel_side                      none
% 2.35/0.99  --res_ordering                          kbo
% 2.35/0.99  --res_to_prop_solver                    active
% 2.35/0.99  --res_prop_simpl_new                    false
% 2.35/0.99  --res_prop_simpl_given                  true
% 2.35/0.99  --res_passive_queue_type                priority_queues
% 2.35/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.35/0.99  --res_passive_queues_freq               [15;5]
% 2.35/0.99  --res_forward_subs                      full
% 2.35/0.99  --res_backward_subs                     full
% 2.35/0.99  --res_forward_subs_resolution           true
% 2.35/0.99  --res_backward_subs_resolution          true
% 2.35/0.99  --res_orphan_elimination                true
% 2.35/0.99  --res_time_limit                        2.
% 2.35/0.99  --res_out_proof                         true
% 2.35/0.99  
% 2.35/0.99  ------ Superposition Options
% 2.35/0.99  
% 2.35/0.99  --superposition_flag                    true
% 2.35/0.99  --sup_passive_queue_type                priority_queues
% 2.35/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.35/0.99  --sup_passive_queues_freq               [8;1;4]
% 2.35/0.99  --demod_completeness_check              fast
% 2.35/0.99  --demod_use_ground                      true
% 2.35/0.99  --sup_to_prop_solver                    passive
% 2.35/0.99  --sup_prop_simpl_new                    true
% 2.35/0.99  --sup_prop_simpl_given                  true
% 2.35/0.99  --sup_fun_splitting                     false
% 2.35/0.99  --sup_smt_interval                      50000
% 2.35/0.99  
% 2.35/0.99  ------ Superposition Simplification Setup
% 2.35/0.99  
% 2.35/0.99  --sup_indices_passive                   []
% 2.35/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.35/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.35/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.35/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 2.35/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.35/0.99  --sup_full_bw                           [BwDemod]
% 2.35/0.99  --sup_immed_triv                        [TrivRules]
% 2.35/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.35/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.35/0.99  --sup_immed_bw_main                     []
% 2.35/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.35/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 2.35/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.35/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.35/0.99  
% 2.35/0.99  ------ Combination Options
% 2.35/0.99  
% 2.35/0.99  --comb_res_mult                         3
% 2.35/0.99  --comb_sup_mult                         2
% 2.35/0.99  --comb_inst_mult                        10
% 2.35/0.99  
% 2.35/0.99  ------ Debug Options
% 2.35/0.99  
% 2.35/0.99  --dbg_backtrace                         false
% 2.35/0.99  --dbg_dump_prop_clauses                 false
% 2.35/0.99  --dbg_dump_prop_clauses_file            -
% 2.35/0.99  --dbg_out_stat                          false
% 2.35/0.99  
% 2.35/0.99  
% 2.35/0.99  
% 2.35/0.99  
% 2.35/0.99  ------ Proving...
% 2.35/0.99  
% 2.35/0.99  
% 2.35/0.99  % SZS status Theorem for theBenchmark.p
% 2.35/0.99  
% 2.35/0.99   Resolution empty clause
% 2.35/0.99  
% 2.35/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 2.35/0.99  
% 2.35/0.99  fof(f4,axiom,(
% 2.35/0.99    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 2.35/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.35/0.99  
% 2.35/0.99  fof(f28,plain,(
% 2.35/0.99    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 2.35/0.99    inference(cnf_transformation,[],[f4])).
% 2.35/0.99  
% 2.35/0.99  fof(f7,axiom,(
% 2.35/0.99    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)),
% 2.35/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.35/0.99  
% 2.35/0.99  fof(f31,plain,(
% 2.35/0.99    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)) )),
% 2.35/0.99    inference(cnf_transformation,[],[f7])).
% 2.35/0.99  
% 2.35/0.99  fof(f6,axiom,(
% 2.35/0.99    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 2.35/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.35/0.99  
% 2.35/0.99  fof(f30,plain,(
% 2.35/0.99    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 2.35/0.99    inference(cnf_transformation,[],[f6])).
% 2.35/0.99  
% 2.35/0.99  fof(f38,plain,(
% 2.35/0.99    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2)) )),
% 2.35/0.99    inference(definition_unfolding,[],[f31,f30,f30])).
% 2.35/0.99  
% 2.35/0.99  fof(f5,axiom,(
% 2.35/0.99    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))),
% 2.35/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.35/0.99  
% 2.35/0.99  fof(f29,plain,(
% 2.35/0.99    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 2.35/0.99    inference(cnf_transformation,[],[f5])).
% 2.35/0.99  
% 2.35/0.99  fof(f37,plain,(
% 2.35/0.99    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 2.35/0.99    inference(definition_unfolding,[],[f29,f30])).
% 2.35/0.99  
% 2.35/0.99  fof(f1,axiom,(
% 2.35/0.99    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 2.35/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.35/0.99  
% 2.35/0.99  fof(f20,plain,(
% 2.35/0.99    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 2.35/0.99    inference(cnf_transformation,[],[f1])).
% 2.35/0.99  
% 2.35/0.99  fof(f36,plain,(
% 2.35/0.99    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0))) )),
% 2.35/0.99    inference(definition_unfolding,[],[f20,f30,f30])).
% 2.35/0.99  
% 2.35/0.99  fof(f8,axiom,(
% 2.35/0.99    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0),
% 2.35/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.35/0.99  
% 2.35/0.99  fof(f32,plain,(
% 2.35/0.99    ( ! [X0,X1] : (k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0) )),
% 2.35/0.99    inference(cnf_transformation,[],[f8])).
% 2.35/0.99  
% 2.35/0.99  fof(f39,plain,(
% 2.35/0.99    ( ! [X0,X1] : (k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1)) = X0) )),
% 2.35/0.99    inference(definition_unfolding,[],[f32,f30])).
% 2.35/0.99  
% 2.35/0.99  fof(f9,axiom,(
% 2.35/0.99    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)),
% 2.35/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.35/0.99  
% 2.35/0.99  fof(f33,plain,(
% 2.35/0.99    ( ! [X0,X1] : (k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)) )),
% 2.35/0.99    inference(cnf_transformation,[],[f9])).
% 2.35/0.99  
% 2.35/0.99  fof(f3,axiom,(
% 2.35/0.99    ! [X0,X1] : k5_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0))),
% 2.35/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.35/0.99  
% 2.35/0.99  fof(f27,plain,(
% 2.35/0.99    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0))) )),
% 2.35/0.99    inference(cnf_transformation,[],[f3])).
% 2.35/0.99  
% 2.35/0.99  fof(f35,plain,(
% 2.35/0.99    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(k4_xboole_0(X1,X0),X0))) )),
% 2.35/0.99    inference(definition_unfolding,[],[f33,f27])).
% 2.35/0.99  
% 2.35/0.99  fof(f10,conjecture,(
% 2.35/0.99    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 2.35/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.35/0.99  
% 2.35/0.99  fof(f11,negated_conjecture,(
% 2.35/0.99    ~! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 2.35/0.99    inference(negated_conjecture,[],[f10])).
% 2.35/0.99  
% 2.35/0.99  fof(f12,plain,(
% 2.35/0.99    ? [X0,X1] : k4_xboole_0(X0,X1) != k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 2.35/0.99    inference(ennf_transformation,[],[f11])).
% 2.35/0.99  
% 2.35/0.99  fof(f18,plain,(
% 2.35/0.99    ? [X0,X1] : k4_xboole_0(X0,X1) != k5_xboole_0(X0,k3_xboole_0(X0,X1)) => k4_xboole_0(sK1,sK2) != k5_xboole_0(sK1,k3_xboole_0(sK1,sK2))),
% 2.35/0.99    introduced(choice_axiom,[])).
% 2.35/0.99  
% 2.35/0.99  fof(f19,plain,(
% 2.35/0.99    k4_xboole_0(sK1,sK2) != k5_xboole_0(sK1,k3_xboole_0(sK1,sK2))),
% 2.35/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f12,f18])).
% 2.35/0.99  
% 2.35/0.99  fof(f34,plain,(
% 2.35/0.99    k4_xboole_0(sK1,sK2) != k5_xboole_0(sK1,k3_xboole_0(sK1,sK2))),
% 2.35/0.99    inference(cnf_transformation,[],[f19])).
% 2.35/0.99  
% 2.35/0.99  fof(f40,plain,(
% 2.35/0.99    k4_xboole_0(sK1,sK2) != k2_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))),k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),sK1))),
% 2.35/0.99    inference(definition_unfolding,[],[f34,f27,f30])).
% 2.35/0.99  
% 2.35/0.99  cnf(c_8,plain,
% 2.35/0.99      ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
% 2.35/0.99      inference(cnf_transformation,[],[f28]) ).
% 2.35/0.99  
% 2.35/0.99  cnf(c_10,plain,
% 2.35/0.99      ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) ),
% 2.35/0.99      inference(cnf_transformation,[],[f38]) ).
% 2.35/0.99  
% 2.35/0.99  cnf(c_856,plain,
% 2.35/0.99      ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(k1_xboole_0,X1))) = k4_xboole_0(k4_xboole_0(X0,X0),X1) ),
% 2.35/0.99      inference(superposition,[status(thm)],[c_8,c_10]) ).
% 2.35/0.99  
% 2.35/0.99  cnf(c_9,plain,
% 2.35/0.99      ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,X1) ),
% 2.35/0.99      inference(cnf_transformation,[],[f37]) ).
% 2.35/0.99  
% 2.35/0.99  cnf(c_377,plain,
% 2.35/0.99      ( k4_xboole_0(X0,k4_xboole_0(X0,X0)) = k4_xboole_0(X0,k1_xboole_0) ),
% 2.35/0.99      inference(superposition,[status(thm)],[c_8,c_9]) ).
% 2.35/0.99  
% 2.35/0.99  cnf(c_385,plain,
% 2.35/0.99      ( k4_xboole_0(X0,k4_xboole_0(X0,X0)) = X0 ),
% 2.35/0.99      inference(light_normalisation,[status(thm)],[c_377,c_8]) ).
% 2.35/0.99  
% 2.35/0.99  cnf(c_3899,plain,
% 2.35/0.99      ( k4_xboole_0(k4_xboole_0(k4_xboole_0(k1_xboole_0,X0),k4_xboole_0(k1_xboole_0,X0)),X0) = k4_xboole_0(k1_xboole_0,X0) ),
% 2.35/0.99      inference(superposition,[status(thm)],[c_856,c_385]) ).
% 2.35/0.99  
% 2.35/0.99  cnf(c_1,plain,
% 2.35/0.99      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
% 2.35/0.99      inference(cnf_transformation,[],[f36]) ).
% 2.35/0.99  
% 2.35/0.99  cnf(c_290,plain,
% 2.35/0.99      ( k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0)) = k4_xboole_0(X0,X0) ),
% 2.35/0.99      inference(superposition,[status(thm)],[c_8,c_1]) ).
% 2.35/0.99  
% 2.35/0.99  cnf(c_401,plain,
% 2.35/0.99      ( k4_xboole_0(X0,k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0))) = X0 ),
% 2.35/0.99      inference(superposition,[status(thm)],[c_290,c_385]) ).
% 2.35/0.99  
% 2.35/0.99  cnf(c_502,plain,
% 2.35/0.99      ( k4_xboole_0(k4_xboole_0(k1_xboole_0,X0),k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,X0))) = k4_xboole_0(k1_xboole_0,X0) ),
% 2.35/0.99      inference(superposition,[status(thm)],[c_290,c_401]) ).
% 2.35/0.99  
% 2.35/0.99  cnf(c_374,plain,
% 2.35/0.99      ( k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,X0)) = k4_xboole_0(k1_xboole_0,X0) ),
% 2.35/0.99      inference(superposition,[status(thm)],[c_290,c_9]) ).
% 2.35/0.99  
% 2.35/0.99  cnf(c_522,plain,
% 2.35/0.99      ( k4_xboole_0(k4_xboole_0(k1_xboole_0,X0),k4_xboole_0(k1_xboole_0,X0)) = k4_xboole_0(k1_xboole_0,X0) ),
% 2.35/0.99      inference(light_normalisation,[status(thm)],[c_502,c_374]) ).
% 2.35/0.99  
% 2.35/0.99  cnf(c_3917,plain,
% 2.35/0.99      ( k4_xboole_0(k4_xboole_0(k1_xboole_0,X0),X0) = k4_xboole_0(k1_xboole_0,X0) ),
% 2.35/0.99      inference(light_normalisation,[status(thm)],[c_3899,c_522]) ).
% 2.35/0.99  
% 2.35/0.99  cnf(c_11,plain,
% 2.35/0.99      ( k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1)) = X0 ),
% 2.35/0.99      inference(cnf_transformation,[],[f39]) ).
% 2.35/0.99  
% 2.35/0.99  cnf(c_654,plain,
% 2.35/0.99      ( k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) = X0 ),
% 2.35/0.99      inference(superposition,[status(thm)],[c_9,c_11]) ).
% 2.35/0.99  
% 2.35/0.99  cnf(c_2230,plain,
% 2.35/0.99      ( k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,k4_xboole_0(X1,X0))) = X0 ),
% 2.35/0.99      inference(superposition,[status(thm)],[c_1,c_654]) ).
% 2.35/0.99  
% 2.35/0.99  cnf(c_4370,plain,
% 2.35/0.99      ( k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(k1_xboole_0,X0)),k4_xboole_0(k4_xboole_0(k1_xboole_0,X0),k4_xboole_0(k1_xboole_0,X0))) = X0 ),
% 2.35/0.99      inference(superposition,[status(thm)],[c_3917,c_2230]) ).
% 2.35/0.99  
% 2.35/0.99  cnf(c_4421,plain,
% 2.35/0.99      ( k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(k1_xboole_0,X0)),k4_xboole_0(k1_xboole_0,X0)) = X0 ),
% 2.35/0.99      inference(light_normalisation,[status(thm)],[c_4370,c_522]) ).
% 2.35/0.99  
% 2.35/0.99  cnf(c_0,plain,
% 2.35/0.99      ( k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(k4_xboole_0(X1,X0),X0)) = k2_xboole_0(X0,X1) ),
% 2.35/0.99      inference(cnf_transformation,[],[f35]) ).
% 2.35/0.99  
% 2.35/0.99  cnf(c_4376,plain,
% 2.35/0.99      ( k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(k1_xboole_0,X0)),k4_xboole_0(k1_xboole_0,X0)) = k2_xboole_0(X0,k1_xboole_0) ),
% 2.35/0.99      inference(superposition,[status(thm)],[c_3917,c_0]) ).
% 2.35/0.99  
% 2.35/0.99  cnf(c_4422,plain,
% 2.35/0.99      ( k2_xboole_0(X0,k1_xboole_0) = X0 ),
% 2.35/0.99      inference(demodulation,[status(thm)],[c_4421,c_4376]) ).
% 2.35/0.99  
% 2.35/0.99  cnf(c_4373,plain,
% 2.35/0.99      ( k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(k1_xboole_0,X0)),k4_xboole_0(k4_xboole_0(k1_xboole_0,X0),X0)) = k2_xboole_0(X0,k4_xboole_0(k1_xboole_0,X0)) ),
% 2.35/0.99      inference(superposition,[status(thm)],[c_3917,c_0]) ).
% 2.35/0.99  
% 2.35/0.99  cnf(c_4414,plain,
% 2.35/0.99      ( k2_xboole_0(X0,k4_xboole_0(k1_xboole_0,X0)) = k2_xboole_0(X0,k1_xboole_0) ),
% 2.35/0.99      inference(light_normalisation,[status(thm)],[c_4373,c_3917,c_4376]) ).
% 2.35/0.99  
% 2.35/0.99  cnf(c_4425,plain,
% 2.35/0.99      ( k2_xboole_0(X0,k4_xboole_0(k1_xboole_0,X0)) = X0 ),
% 2.35/0.99      inference(demodulation,[status(thm)],[c_4422,c_4414]) ).
% 2.35/0.99  
% 2.35/0.99  cnf(c_4595,plain,
% 2.35/0.99      ( k4_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
% 2.35/0.99      inference(superposition,[status(thm)],[c_4425,c_654]) ).
% 2.35/0.99  
% 2.35/0.99  cnf(c_4618,plain,
% 2.35/0.99      ( k4_xboole_0(k4_xboole_0(X0,X0),X1) = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) ),
% 2.35/0.99      inference(demodulation,[status(thm)],[c_4595,c_856]) ).
% 2.35/0.99  
% 2.35/0.99  cnf(c_850,plain,
% 2.35/0.99      ( k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,X1))) = k4_xboole_0(k4_xboole_0(X0,X0),X1) ),
% 2.35/0.99      inference(superposition,[status(thm)],[c_290,c_10]) ).
% 2.35/0.99  
% 2.35/0.99  cnf(c_4620,plain,
% 2.35/0.99      ( k4_xboole_0(k4_xboole_0(X0,X0),X1) = k4_xboole_0(k1_xboole_0,k1_xboole_0) ),
% 2.35/0.99      inference(demodulation,[status(thm)],[c_4595,c_850]) ).
% 2.35/0.99  
% 2.35/0.99  cnf(c_4622,plain,
% 2.35/0.99      ( k4_xboole_0(k4_xboole_0(X0,X0),X1) = k1_xboole_0 ),
% 2.35/0.99      inference(demodulation,[status(thm)],[c_4620,c_4595]) ).
% 2.35/0.99  
% 2.35/0.99  cnf(c_4624,plain,
% 2.35/0.99      ( k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) = k1_xboole_0 ),
% 2.35/0.99      inference(light_normalisation,[status(thm)],[c_4618,c_4622]) ).
% 2.35/0.99  
% 2.35/0.99  cnf(c_4626,plain,
% 2.35/0.99      ( k4_xboole_0(X0,X0) = k1_xboole_0 ),
% 2.35/0.99      inference(light_normalisation,[status(thm)],[c_4624,c_8]) ).
% 2.35/0.99  
% 2.35/0.99  cnf(c_4856,plain,
% 2.35/0.99      ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X0,k4_xboole_0(X0,X1))))) = k1_xboole_0 ),
% 2.35/0.99      inference(superposition,[status(thm)],[c_4626,c_10]) ).
% 2.35/0.99  
% 2.35/0.99  cnf(c_372,plain,
% 2.35/0.99      ( k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0))) = k4_xboole_0(X0,X1) ),
% 2.35/0.99      inference(superposition,[status(thm)],[c_1,c_9]) ).
% 2.35/0.99  
% 2.35/0.99  cnf(c_4858,plain,
% 2.35/0.99      ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X0))) = k1_xboole_0 ),
% 2.35/0.99      inference(demodulation,[status(thm)],[c_4856,c_372]) ).
% 2.35/0.99  
% 2.35/0.99  cnf(c_12,negated_conjecture,
% 2.35/0.99      ( k4_xboole_0(sK1,sK2) != k2_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))),k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),sK1)) ),
% 2.35/0.99      inference(cnf_transformation,[],[f40]) ).
% 2.35/0.99  
% 2.35/0.99  cnf(c_219,plain,
% 2.35/0.99      ( k2_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK2,sK1)))) != k4_xboole_0(sK1,sK2) ),
% 2.35/0.99      inference(demodulation,[status(thm)],[c_12,c_9,c_10]) ).
% 2.35/0.99  
% 2.35/0.99  cnf(c_5160,plain,
% 2.35/0.99      ( k2_xboole_0(k4_xboole_0(sK1,sK2),k1_xboole_0) != k4_xboole_0(sK1,sK2) ),
% 2.35/0.99      inference(demodulation,[status(thm)],[c_4858,c_219]) ).
% 2.35/0.99  
% 2.35/0.99  cnf(c_5161,plain,
% 2.35/0.99      ( k4_xboole_0(sK1,sK2) != k4_xboole_0(sK1,sK2) ),
% 2.35/0.99      inference(demodulation,[status(thm)],[c_5160,c_4422]) ).
% 2.35/0.99  
% 2.35/0.99  cnf(c_5162,plain,
% 2.35/0.99      ( $false ),
% 2.35/0.99      inference(equality_resolution_simp,[status(thm)],[c_5161]) ).
% 2.35/0.99  
% 2.35/0.99  
% 2.35/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 2.35/0.99  
% 2.35/0.99  ------                               Statistics
% 2.35/0.99  
% 2.35/0.99  ------ General
% 2.35/0.99  
% 2.35/0.99  abstr_ref_over_cycles:                  0
% 2.35/0.99  abstr_ref_under_cycles:                 0
% 2.35/0.99  gc_basic_clause_elim:                   0
% 2.35/0.99  forced_gc_time:                         0
% 2.35/0.99  parsing_time:                           0.008
% 2.35/0.99  unif_index_cands_time:                  0.
% 2.35/0.99  unif_index_add_time:                    0.
% 2.35/0.99  orderings_time:                         0.
% 2.35/0.99  out_proof_time:                         0.008
% 2.35/0.99  total_time:                             0.185
% 2.35/0.99  num_of_symbols:                         38
% 2.35/0.99  num_of_terms:                           5809
% 2.35/0.99  
% 2.35/0.99  ------ Preprocessing
% 2.35/0.99  
% 2.35/0.99  num_of_splits:                          0
% 2.35/0.99  num_of_split_atoms:                     0
% 2.35/0.99  num_of_reused_defs:                     0
% 2.35/0.99  num_eq_ax_congr_red:                    6
% 2.35/0.99  num_of_sem_filtered_clauses:            1
% 2.35/0.99  num_of_subtypes:                        0
% 2.35/0.99  monotx_restored_types:                  0
% 2.35/0.99  sat_num_of_epr_types:                   0
% 2.35/0.99  sat_num_of_non_cyclic_types:            0
% 2.35/0.99  sat_guarded_non_collapsed_types:        0
% 2.35/0.99  num_pure_diseq_elim:                    0
% 2.35/0.99  simp_replaced_by:                       0
% 2.35/0.99  res_preprocessed:                       50
% 2.35/0.99  prep_upred:                             0
% 2.35/0.99  prep_unflattend:                        0
% 2.35/0.99  smt_new_axioms:                         0
% 2.35/0.99  pred_elim_cands:                        1
% 2.35/0.99  pred_elim:                              0
% 2.35/0.99  pred_elim_cl:                           0
% 2.35/0.99  pred_elim_cycles:                       1
% 2.35/0.99  merged_defs:                            0
% 2.35/0.99  merged_defs_ncl:                        0
% 2.35/0.99  bin_hyper_res:                          0
% 2.35/0.99  prep_cycles:                            3
% 2.35/0.99  pred_elim_time:                         0.
% 2.35/0.99  splitting_time:                         0.
% 2.35/0.99  sem_filter_time:                        0.
% 2.35/0.99  monotx_time:                            0.
% 2.35/0.99  subtype_inf_time:                       0.
% 2.35/0.99  
% 2.35/0.99  ------ Problem properties
% 2.35/0.99  
% 2.35/0.99  clauses:                                13
% 2.35/0.99  conjectures:                            1
% 2.35/0.99  epr:                                    0
% 2.35/0.99  horn:                                   9
% 2.35/0.99  ground:                                 1
% 2.35/0.99  unary:                                  7
% 2.35/0.99  binary:                                 2
% 2.35/0.99  lits:                                   24
% 2.35/0.99  lits_eq:                                10
% 2.35/0.99  fd_pure:                                0
% 2.35/0.99  fd_pseudo:                              0
% 2.35/0.99  fd_cond:                                0
% 2.35/0.99  fd_pseudo_cond:                         3
% 2.35/0.99  ac_symbols:                             0
% 2.35/0.99  
% 2.35/0.99  ------ Propositional Solver
% 2.35/0.99  
% 2.35/0.99  prop_solver_calls:                      24
% 2.35/0.99  prop_fast_solver_calls:                 264
% 2.35/0.99  smt_solver_calls:                       0
% 2.35/0.99  smt_fast_solver_calls:                  0
% 2.35/0.99  prop_num_of_clauses:                    1565
% 2.35/0.99  prop_preprocess_simplified:             3257
% 2.35/0.99  prop_fo_subsumed:                       1
% 2.35/0.99  prop_solver_time:                       0.
% 2.35/0.99  smt_solver_time:                        0.
% 2.35/0.99  smt_fast_solver_time:                   0.
% 2.35/0.99  prop_fast_solver_time:                  0.
% 2.35/0.99  prop_unsat_core_time:                   0.
% 2.35/0.99  
% 2.35/0.99  ------ QBF
% 2.35/0.99  
% 2.35/0.99  qbf_q_res:                              0
% 2.35/0.99  qbf_num_tautologies:                    0
% 2.35/0.99  qbf_prep_cycles:                        0
% 2.35/0.99  
% 2.35/0.99  ------ BMC1
% 2.35/0.99  
% 2.35/0.99  bmc1_current_bound:                     -1
% 2.35/0.99  bmc1_last_solved_bound:                 -1
% 2.35/0.99  bmc1_unsat_core_size:                   -1
% 2.35/0.99  bmc1_unsat_core_parents_size:           -1
% 2.35/0.99  bmc1_merge_next_fun:                    0
% 2.35/0.99  bmc1_unsat_core_clauses_time:           0.
% 2.35/0.99  
% 2.35/0.99  ------ Instantiation
% 2.35/0.99  
% 2.35/0.99  inst_num_of_clauses:                    425
% 2.35/0.99  inst_num_in_passive:                    164
% 2.35/0.99  inst_num_in_active:                     173
% 2.35/0.99  inst_num_in_unprocessed:                88
% 2.35/0.99  inst_num_of_loops:                      240
% 2.35/0.99  inst_num_of_learning_restarts:          0
% 2.35/0.99  inst_num_moves_active_passive:          65
% 2.35/0.99  inst_lit_activity:                      0
% 2.35/0.99  inst_lit_activity_moves:                0
% 2.35/0.99  inst_num_tautologies:                   0
% 2.35/0.99  inst_num_prop_implied:                  0
% 2.35/0.99  inst_num_existing_simplified:           0
% 2.35/0.99  inst_num_eq_res_simplified:             0
% 2.35/0.99  inst_num_child_elim:                    0
% 2.35/0.99  inst_num_of_dismatching_blockings:      258
% 2.35/0.99  inst_num_of_non_proper_insts:           353
% 2.35/0.99  inst_num_of_duplicates:                 0
% 2.35/0.99  inst_inst_num_from_inst_to_res:         0
% 2.35/0.99  inst_dismatching_checking_time:         0.
% 2.35/0.99  
% 2.35/0.99  ------ Resolution
% 2.35/0.99  
% 2.35/0.99  res_num_of_clauses:                     0
% 2.35/0.99  res_num_in_passive:                     0
% 2.35/0.99  res_num_in_active:                      0
% 2.35/0.99  res_num_of_loops:                       53
% 2.35/0.99  res_forward_subset_subsumed:            40
% 2.35/0.99  res_backward_subset_subsumed:           0
% 2.35/0.99  res_forward_subsumed:                   0
% 2.35/0.99  res_backward_subsumed:                  0
% 2.35/0.99  res_forward_subsumption_resolution:     0
% 2.35/0.99  res_backward_subsumption_resolution:    0
% 2.35/0.99  res_clause_to_clause_subsumption:       2393
% 2.35/0.99  res_orphan_elimination:                 0
% 2.35/0.99  res_tautology_del:                      26
% 2.35/0.99  res_num_eq_res_simplified:              0
% 2.35/0.99  res_num_sel_changes:                    0
% 2.35/0.99  res_moves_from_active_to_pass:          0
% 2.35/0.99  
% 2.35/0.99  ------ Superposition
% 2.35/0.99  
% 2.35/0.99  sup_time_total:                         0.
% 2.35/0.99  sup_time_generating:                    0.
% 2.35/0.99  sup_time_sim_full:                      0.
% 2.35/0.99  sup_time_sim_immed:                     0.
% 2.35/0.99  
% 2.35/0.99  sup_num_of_clauses:                     199
% 2.35/0.99  sup_num_in_active:                      21
% 2.35/0.99  sup_num_in_passive:                     178
% 2.35/0.99  sup_num_of_loops:                       47
% 2.35/0.99  sup_fw_superposition:                   520
% 2.35/0.99  sup_bw_superposition:                   359
% 2.35/0.99  sup_immediate_simplified:               415
% 2.35/0.99  sup_given_eliminated:                   1
% 2.35/0.99  comparisons_done:                       0
% 2.35/0.99  comparisons_avoided:                    0
% 2.35/0.99  
% 2.35/0.99  ------ Simplifications
% 2.35/0.99  
% 2.35/0.99  
% 2.35/0.99  sim_fw_subset_subsumed:                 11
% 2.35/0.99  sim_bw_subset_subsumed:                 2
% 2.35/0.99  sim_fw_subsumed:                        53
% 2.35/0.99  sim_bw_subsumed:                        6
% 2.35/0.99  sim_fw_subsumption_res:                 0
% 2.35/0.99  sim_bw_subsumption_res:                 0
% 2.35/0.99  sim_tautology_del:                      17
% 2.35/0.99  sim_eq_tautology_del:                   109
% 2.35/0.99  sim_eq_res_simp:                        1
% 2.35/0.99  sim_fw_demodulated:                     175
% 2.35/0.99  sim_bw_demodulated:                     36
% 2.35/0.99  sim_light_normalised:                   224
% 2.35/0.99  sim_joinable_taut:                      0
% 2.35/0.99  sim_joinable_simp:                      0
% 2.35/0.99  sim_ac_normalised:                      0
% 2.35/0.99  sim_smt_subsumption:                    0
% 2.35/0.99  
%------------------------------------------------------------------------------
