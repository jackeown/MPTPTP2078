%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:24:34 EST 2020

% Result     : Theorem 3.85s
% Output     : CNFRefutation 3.85s
% Verified   : 
% Statistics : Number of formulae       :   70 ( 252 expanded)
%              Number of clauses        :   37 (  82 expanded)
%              Number of leaves         :   11 (  68 expanded)
%              Depth                    :   17
%              Number of atoms          :   93 ( 320 expanded)
%              Number of equality atoms :   65 ( 235 expanded)
%              Maximal formula depth    :    7 (   2 average)
%              Maximal clause size      :    4 (   1 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k3_xboole_0(X0,X1) != k1_xboole_0 )
      & ( k3_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f17,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f7,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f30,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,X1))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(definition_unfolding,[],[f17,f23])).

fof(f10,conjecture,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,k4_xboole_0(X1,X2))
     => r1_xboole_0(X1,k4_xboole_0(X0,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f11,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( r1_xboole_0(X0,k4_xboole_0(X1,X2))
       => r1_xboole_0(X1,k4_xboole_0(X0,X2)) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f12,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_xboole_0(X1,k4_xboole_0(X0,X2))
      & r1_xboole_0(X0,k4_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f14,plain,
    ( ? [X0,X1,X2] :
        ( ~ r1_xboole_0(X1,k4_xboole_0(X0,X2))
        & r1_xboole_0(X0,k4_xboole_0(X1,X2)) )
   => ( ~ r1_xboole_0(sK1,k4_xboole_0(sK0,sK2))
      & r1_xboole_0(sK0,k4_xboole_0(sK1,sK2)) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,
    ( ~ r1_xboole_0(sK1,k4_xboole_0(sK0,sK2))
    & r1_xboole_0(sK0,k4_xboole_0(sK1,sK2)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f12,f14])).

fof(f26,plain,(
    r1_xboole_0(sK0,k4_xboole_0(sK1,sK2)) ),
    inference(cnf_transformation,[],[f15])).

fof(f9,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(X0,k4_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k4_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X2)) ),
    inference(cnf_transformation,[],[f9])).

fof(f33,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k4_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X2))) ),
    inference(definition_unfolding,[],[f25,f23])).

fof(f3,axiom,(
    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f3])).

fof(f31,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) ),
    inference(definition_unfolding,[],[f19,f23])).

fof(f5,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f8,axiom,(
    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f8])).

fof(f32,plain,(
    ! [X0,X1] : k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1)) = X0 ),
    inference(definition_unfolding,[],[f24,f23])).

fof(f6,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f6])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f28,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(definition_unfolding,[],[f16,f23,f23])).

fof(f4,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f4])).

fof(f18,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k3_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f13])).

fof(f29,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k1_xboole_0 != k4_xboole_0(X0,k4_xboole_0(X0,X1)) ) ),
    inference(definition_unfolding,[],[f18,f23])).

fof(f27,plain,(
    ~ r1_xboole_0(sK1,k4_xboole_0(sK0,sK2)) ),
    inference(cnf_transformation,[],[f15])).

cnf(c_2,plain,
    ( ~ r1_xboole_0(X0,X1)
    | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f30])).

cnf(c_44,plain,
    ( ~ r1_xboole_0(X0,X1)
    | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_xboole_0 ),
    inference(prop_impl,[status(thm)],[c_2])).

cnf(c_10,negated_conjecture,
    ( r1_xboole_0(sK0,k4_xboole_0(sK1,sK2)) ),
    inference(cnf_transformation,[],[f26])).

cnf(c_85,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_xboole_0
    | k4_xboole_0(sK1,sK2) != X1
    | sK0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_44,c_10])).

cnf(c_86,plain,
    ( k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK1,sK2))) = k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_85])).

cnf(c_8,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X2))) = k4_xboole_0(X0,k4_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_415,plain,
    ( k4_xboole_0(sK0,k4_xboole_0(X0,k4_xboole_0(sK1,sK2))) = k2_xboole_0(k4_xboole_0(sK0,X0),k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_86,c_8])).

cnf(c_3,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f31])).

cnf(c_5,plain,
    ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f21])).

cnf(c_112,plain,
    ( k4_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_3,c_5])).

cnf(c_7,plain,
    ( k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f32])).

cnf(c_394,plain,
    ( k2_xboole_0(k4_xboole_0(X0,k1_xboole_0),k1_xboole_0) = X0 ),
    inference(superposition,[status(thm)],[c_112,c_7])).

cnf(c_395,plain,
    ( k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(light_normalisation,[status(thm)],[c_394,c_5])).

cnf(c_434,plain,
    ( k4_xboole_0(sK0,k4_xboole_0(X0,k4_xboole_0(sK1,sK2))) = k4_xboole_0(sK0,X0) ),
    inference(demodulation,[status(thm)],[c_415,c_395])).

cnf(c_555,plain,
    ( k2_xboole_0(k4_xboole_0(sK0,X0),k4_xboole_0(sK0,k4_xboole_0(sK0,X1))) = k4_xboole_0(sK0,k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(sK1,sK2)),X1)) ),
    inference(superposition,[status(thm)],[c_434,c_8])).

cnf(c_6,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f22])).

cnf(c_569,plain,
    ( k4_xboole_0(sK0,k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(sK1,sK2),X1))) = k4_xboole_0(sK0,k4_xboole_0(X0,X1)) ),
    inference(demodulation,[status(thm)],[c_555,c_6,c_8])).

cnf(c_0,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f28])).

cnf(c_304,plain,
    ( k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,X1),X2)) = k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X2) ),
    inference(superposition,[status(thm)],[c_0,c_6])).

cnf(c_2005,plain,
    ( k4_xboole_0(sK0,k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(sK1,sK2)))) = k4_xboole_0(sK0,k4_xboole_0(X1,k4_xboole_0(X1,X0))) ),
    inference(superposition,[status(thm)],[c_304,c_434])).

cnf(c_5709,plain,
    ( k4_xboole_0(sK0,k4_xboole_0(sK2,k4_xboole_0(sK2,sK1))) = k4_xboole_0(sK0,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))) ),
    inference(superposition,[status(thm)],[c_569,c_2005])).

cnf(c_5710,plain,
    ( k4_xboole_0(sK0,k4_xboole_0(sK2,k4_xboole_0(sK2,sK1))) = k4_xboole_0(sK0,sK1) ),
    inference(demodulation,[status(thm)],[c_5709,c_434])).

cnf(c_317,plain,
    ( k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X0,X1))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_6,c_112])).

cnf(c_4,plain,
    ( k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f20])).

cnf(c_318,plain,
    ( k4_xboole_0(X0,k2_xboole_0(X1,X0)) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_317,c_4])).

cnf(c_999,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),X0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_7,c_318])).

cnf(c_1478,plain,
    ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_0,c_999])).

cnf(c_5778,plain,
    ( k4_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(sK2,k4_xboole_0(sK2,sK1))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_5710,c_1478])).

cnf(c_6068,plain,
    ( k4_xboole_0(sK1,k2_xboole_0(k4_xboole_0(sK1,sK0),k4_xboole_0(sK2,k4_xboole_0(sK2,sK1)))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_5778,c_304])).

cnf(c_412,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X2,k4_xboole_0(X2,X0))) = k4_xboole_0(X0,k4_xboole_0(X1,X2)) ),
    inference(superposition,[status(thm)],[c_0,c_8])).

cnf(c_6069,plain,
    ( k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK0,sK2))) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_6068,c_412])).

cnf(c_1,plain,
    ( r1_xboole_0(X0,X1)
    | k4_xboole_0(X0,k4_xboole_0(X0,X1)) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f29])).

cnf(c_42,plain,
    ( r1_xboole_0(X0,X1)
    | k4_xboole_0(X0,k4_xboole_0(X0,X1)) != k1_xboole_0 ),
    inference(prop_impl,[status(thm)],[c_1])).

cnf(c_9,negated_conjecture,
    ( ~ r1_xboole_0(sK1,k4_xboole_0(sK0,sK2)) ),
    inference(cnf_transformation,[],[f27])).

cnf(c_80,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) != k1_xboole_0
    | k4_xboole_0(sK0,sK2) != X1
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_42,c_9])).

cnf(c_81,plain,
    ( k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK0,sK2))) != k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_80])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_6069,c_81])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : iproveropt_run.sh %d %s
% 0.13/0.33  % Computer   : n020.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 09:17:52 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 3.85/1.00  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.85/1.00  
% 3.85/1.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.85/1.00  
% 3.85/1.00  ------  iProver source info
% 3.85/1.00  
% 3.85/1.00  git: date: 2020-06-30 10:37:57 +0100
% 3.85/1.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.85/1.00  git: non_committed_changes: false
% 3.85/1.00  git: last_make_outside_of_git: false
% 3.85/1.00  
% 3.85/1.00  ------ 
% 3.85/1.00  
% 3.85/1.00  ------ Input Options
% 3.85/1.00  
% 3.85/1.00  --out_options                           all
% 3.85/1.00  --tptp_safe_out                         true
% 3.85/1.00  --problem_path                          ""
% 3.85/1.00  --include_path                          ""
% 3.85/1.00  --clausifier                            res/vclausify_rel
% 3.85/1.00  --clausifier_options                    ""
% 3.85/1.00  --stdin                                 false
% 3.85/1.00  --stats_out                             all
% 3.85/1.00  
% 3.85/1.00  ------ General Options
% 3.85/1.00  
% 3.85/1.00  --fof                                   false
% 3.85/1.00  --time_out_real                         305.
% 3.85/1.00  --time_out_virtual                      -1.
% 3.85/1.00  --symbol_type_check                     false
% 3.85/1.00  --clausify_out                          false
% 3.85/1.00  --sig_cnt_out                           false
% 3.85/1.00  --trig_cnt_out                          false
% 3.85/1.00  --trig_cnt_out_tolerance                1.
% 3.85/1.00  --trig_cnt_out_sk_spl                   false
% 3.85/1.00  --abstr_cl_out                          false
% 3.85/1.00  
% 3.85/1.00  ------ Global Options
% 3.85/1.00  
% 3.85/1.00  --schedule                              default
% 3.85/1.00  --add_important_lit                     false
% 3.85/1.00  --prop_solver_per_cl                    1000
% 3.85/1.00  --min_unsat_core                        false
% 3.85/1.00  --soft_assumptions                      false
% 3.85/1.00  --soft_lemma_size                       3
% 3.85/1.00  --prop_impl_unit_size                   0
% 3.85/1.00  --prop_impl_unit                        []
% 3.85/1.00  --share_sel_clauses                     true
% 3.85/1.00  --reset_solvers                         false
% 3.85/1.00  --bc_imp_inh                            [conj_cone]
% 3.85/1.00  --conj_cone_tolerance                   3.
% 3.85/1.00  --extra_neg_conj                        none
% 3.85/1.00  --large_theory_mode                     true
% 3.85/1.00  --prolific_symb_bound                   200
% 3.85/1.00  --lt_threshold                          2000
% 3.85/1.00  --clause_weak_htbl                      true
% 3.85/1.00  --gc_record_bc_elim                     false
% 3.85/1.00  
% 3.85/1.00  ------ Preprocessing Options
% 3.85/1.00  
% 3.85/1.00  --preprocessing_flag                    true
% 3.85/1.00  --time_out_prep_mult                    0.1
% 3.85/1.00  --splitting_mode                        input
% 3.85/1.00  --splitting_grd                         true
% 3.85/1.00  --splitting_cvd                         false
% 3.85/1.00  --splitting_cvd_svl                     false
% 3.85/1.00  --splitting_nvd                         32
% 3.85/1.00  --sub_typing                            true
% 3.85/1.00  --prep_gs_sim                           true
% 3.85/1.00  --prep_unflatten                        true
% 3.85/1.00  --prep_res_sim                          true
% 3.85/1.00  --prep_upred                            true
% 3.85/1.00  --prep_sem_filter                       exhaustive
% 3.85/1.00  --prep_sem_filter_out                   false
% 3.85/1.00  --pred_elim                             true
% 3.85/1.00  --res_sim_input                         true
% 3.85/1.00  --eq_ax_congr_red                       true
% 3.85/1.00  --pure_diseq_elim                       true
% 3.85/1.00  --brand_transform                       false
% 3.85/1.00  --non_eq_to_eq                          false
% 3.85/1.00  --prep_def_merge                        true
% 3.85/1.00  --prep_def_merge_prop_impl              false
% 3.85/1.00  --prep_def_merge_mbd                    true
% 3.85/1.00  --prep_def_merge_tr_red                 false
% 3.85/1.00  --prep_def_merge_tr_cl                  false
% 3.85/1.00  --smt_preprocessing                     true
% 3.85/1.00  --smt_ac_axioms                         fast
% 3.85/1.00  --preprocessed_out                      false
% 3.85/1.00  --preprocessed_stats                    false
% 3.85/1.00  
% 3.85/1.00  ------ Abstraction refinement Options
% 3.85/1.00  
% 3.85/1.00  --abstr_ref                             []
% 3.85/1.00  --abstr_ref_prep                        false
% 3.85/1.00  --abstr_ref_until_sat                   false
% 3.85/1.00  --abstr_ref_sig_restrict                funpre
% 3.85/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 3.85/1.00  --abstr_ref_under                       []
% 3.85/1.00  
% 3.85/1.00  ------ SAT Options
% 3.85/1.00  
% 3.85/1.00  --sat_mode                              false
% 3.85/1.00  --sat_fm_restart_options                ""
% 3.85/1.00  --sat_gr_def                            false
% 3.85/1.00  --sat_epr_types                         true
% 3.85/1.00  --sat_non_cyclic_types                  false
% 3.85/1.00  --sat_finite_models                     false
% 3.85/1.00  --sat_fm_lemmas                         false
% 3.85/1.00  --sat_fm_prep                           false
% 3.85/1.00  --sat_fm_uc_incr                        true
% 3.85/1.00  --sat_out_model                         small
% 3.85/1.00  --sat_out_clauses                       false
% 3.85/1.00  
% 3.85/1.00  ------ QBF Options
% 3.85/1.00  
% 3.85/1.00  --qbf_mode                              false
% 3.85/1.00  --qbf_elim_univ                         false
% 3.85/1.00  --qbf_dom_inst                          none
% 3.85/1.00  --qbf_dom_pre_inst                      false
% 3.85/1.00  --qbf_sk_in                             false
% 3.85/1.00  --qbf_pred_elim                         true
% 3.85/1.00  --qbf_split                             512
% 3.85/1.00  
% 3.85/1.00  ------ BMC1 Options
% 3.85/1.00  
% 3.85/1.00  --bmc1_incremental                      false
% 3.85/1.00  --bmc1_axioms                           reachable_all
% 3.85/1.00  --bmc1_min_bound                        0
% 3.85/1.00  --bmc1_max_bound                        -1
% 3.85/1.00  --bmc1_max_bound_default                -1
% 3.85/1.00  --bmc1_symbol_reachability              true
% 3.85/1.00  --bmc1_property_lemmas                  false
% 3.85/1.00  --bmc1_k_induction                      false
% 3.85/1.00  --bmc1_non_equiv_states                 false
% 3.85/1.00  --bmc1_deadlock                         false
% 3.85/1.00  --bmc1_ucm                              false
% 3.85/1.00  --bmc1_add_unsat_core                   none
% 3.85/1.00  --bmc1_unsat_core_children              false
% 3.85/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 3.85/1.00  --bmc1_out_stat                         full
% 3.85/1.00  --bmc1_ground_init                      false
% 3.85/1.00  --bmc1_pre_inst_next_state              false
% 3.85/1.00  --bmc1_pre_inst_state                   false
% 3.85/1.00  --bmc1_pre_inst_reach_state             false
% 3.85/1.00  --bmc1_out_unsat_core                   false
% 3.85/1.00  --bmc1_aig_witness_out                  false
% 3.85/1.00  --bmc1_verbose                          false
% 3.85/1.00  --bmc1_dump_clauses_tptp                false
% 3.85/1.00  --bmc1_dump_unsat_core_tptp             false
% 3.85/1.00  --bmc1_dump_file                        -
% 3.85/1.00  --bmc1_ucm_expand_uc_limit              128
% 3.85/1.00  --bmc1_ucm_n_expand_iterations          6
% 3.85/1.00  --bmc1_ucm_extend_mode                  1
% 3.85/1.00  --bmc1_ucm_init_mode                    2
% 3.85/1.00  --bmc1_ucm_cone_mode                    none
% 3.85/1.00  --bmc1_ucm_reduced_relation_type        0
% 3.85/1.00  --bmc1_ucm_relax_model                  4
% 3.85/1.00  --bmc1_ucm_full_tr_after_sat            true
% 3.85/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 3.85/1.00  --bmc1_ucm_layered_model                none
% 3.85/1.00  --bmc1_ucm_max_lemma_size               10
% 3.85/1.00  
% 3.85/1.00  ------ AIG Options
% 3.85/1.00  
% 3.85/1.00  --aig_mode                              false
% 3.85/1.00  
% 3.85/1.00  ------ Instantiation Options
% 3.85/1.00  
% 3.85/1.00  --instantiation_flag                    true
% 3.85/1.00  --inst_sos_flag                         true
% 3.85/1.00  --inst_sos_phase                        true
% 3.85/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.85/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.85/1.00  --inst_lit_sel_side                     num_symb
% 3.85/1.00  --inst_solver_per_active                1400
% 3.85/1.00  --inst_solver_calls_frac                1.
% 3.85/1.00  --inst_passive_queue_type               priority_queues
% 3.85/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.85/1.00  --inst_passive_queues_freq              [25;2]
% 3.85/1.00  --inst_dismatching                      true
% 3.85/1.00  --inst_eager_unprocessed_to_passive     true
% 3.85/1.00  --inst_prop_sim_given                   true
% 3.85/1.00  --inst_prop_sim_new                     false
% 3.85/1.00  --inst_subs_new                         false
% 3.85/1.00  --inst_eq_res_simp                      false
% 3.85/1.00  --inst_subs_given                       false
% 3.85/1.00  --inst_orphan_elimination               true
% 3.85/1.00  --inst_learning_loop_flag               true
% 3.85/1.00  --inst_learning_start                   3000
% 3.85/1.00  --inst_learning_factor                  2
% 3.85/1.00  --inst_start_prop_sim_after_learn       3
% 3.85/1.00  --inst_sel_renew                        solver
% 3.85/1.00  --inst_lit_activity_flag                true
% 3.85/1.00  --inst_restr_to_given                   false
% 3.85/1.00  --inst_activity_threshold               500
% 3.85/1.00  --inst_out_proof                        true
% 3.85/1.00  
% 3.85/1.00  ------ Resolution Options
% 3.85/1.00  
% 3.85/1.00  --resolution_flag                       true
% 3.85/1.00  --res_lit_sel                           adaptive
% 3.85/1.00  --res_lit_sel_side                      none
% 3.85/1.00  --res_ordering                          kbo
% 3.85/1.00  --res_to_prop_solver                    active
% 3.85/1.00  --res_prop_simpl_new                    false
% 3.85/1.00  --res_prop_simpl_given                  true
% 3.85/1.00  --res_passive_queue_type                priority_queues
% 3.85/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.85/1.00  --res_passive_queues_freq               [15;5]
% 3.85/1.00  --res_forward_subs                      full
% 3.85/1.00  --res_backward_subs                     full
% 3.85/1.00  --res_forward_subs_resolution           true
% 3.85/1.00  --res_backward_subs_resolution          true
% 3.85/1.00  --res_orphan_elimination                true
% 3.85/1.00  --res_time_limit                        2.
% 3.85/1.00  --res_out_proof                         true
% 3.85/1.00  
% 3.85/1.00  ------ Superposition Options
% 3.85/1.00  
% 3.85/1.00  --superposition_flag                    true
% 3.85/1.00  --sup_passive_queue_type                priority_queues
% 3.85/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.85/1.00  --sup_passive_queues_freq               [8;1;4]
% 3.85/1.00  --demod_completeness_check              fast
% 3.85/1.00  --demod_use_ground                      true
% 3.85/1.00  --sup_to_prop_solver                    passive
% 3.85/1.00  --sup_prop_simpl_new                    true
% 3.85/1.00  --sup_prop_simpl_given                  true
% 3.85/1.00  --sup_fun_splitting                     true
% 3.85/1.00  --sup_smt_interval                      50000
% 3.85/1.00  
% 3.85/1.00  ------ Superposition Simplification Setup
% 3.85/1.00  
% 3.85/1.00  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 3.85/1.00  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 3.85/1.00  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 3.85/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 3.85/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 3.85/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 3.85/1.00  --sup_full_bw                           [BwDemod;BwSubsumption]
% 3.85/1.00  --sup_immed_triv                        [TrivRules]
% 3.85/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.85/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.85/1.00  --sup_immed_bw_main                     []
% 3.85/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 3.85/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 3.85/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.85/1.00  --sup_input_bw                          []
% 3.85/1.00  
% 3.85/1.00  ------ Combination Options
% 3.85/1.00  
% 3.85/1.00  --comb_res_mult                         3
% 3.85/1.00  --comb_sup_mult                         2
% 3.85/1.00  --comb_inst_mult                        10
% 3.85/1.00  
% 3.85/1.00  ------ Debug Options
% 3.85/1.00  
% 3.85/1.00  --dbg_backtrace                         false
% 3.85/1.00  --dbg_dump_prop_clauses                 false
% 3.85/1.00  --dbg_dump_prop_clauses_file            -
% 3.85/1.00  --dbg_out_stat                          false
% 3.85/1.00  ------ Parsing...
% 3.85/1.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.85/1.00  
% 3.85/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 3.85/1.00  
% 3.85/1.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.85/1.00  
% 3.85/1.00  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 3.85/1.00  ------ Proving...
% 3.85/1.00  ------ Problem Properties 
% 3.85/1.00  
% 3.85/1.00  
% 3.85/1.00  clauses                                 10
% 3.85/1.00  conjectures                             0
% 3.85/1.00  EPR                                     0
% 3.85/1.00  Horn                                    10
% 3.85/1.00  unary                                   9
% 3.85/1.00  binary                                  1
% 3.85/1.00  lits                                    11
% 3.85/1.00  lits eq                                 11
% 3.85/1.00  fd_pure                                 0
% 3.85/1.00  fd_pseudo                               0
% 3.85/1.00  fd_cond                                 0
% 3.85/1.00  fd_pseudo_cond                          0
% 3.85/1.00  AC symbols                              0
% 3.85/1.00  
% 3.85/1.00  ------ Schedule dynamic 5 is on 
% 3.85/1.00  
% 3.85/1.00  ------ no conjectures: strip conj schedule 
% 3.85/1.00  
% 3.85/1.00  ------ pure equality problem: resolution off 
% 3.85/1.00  
% 3.85/1.00  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" stripped conjectures Time Limit: 10.
% 3.85/1.00  
% 3.85/1.00  
% 3.85/1.00  ------ 
% 3.85/1.00  Current options:
% 3.85/1.00  ------ 
% 3.85/1.00  
% 3.85/1.00  ------ Input Options
% 3.85/1.00  
% 3.85/1.00  --out_options                           all
% 3.85/1.00  --tptp_safe_out                         true
% 3.85/1.00  --problem_path                          ""
% 3.85/1.00  --include_path                          ""
% 3.85/1.00  --clausifier                            res/vclausify_rel
% 3.85/1.00  --clausifier_options                    ""
% 3.85/1.00  --stdin                                 false
% 3.85/1.00  --stats_out                             all
% 3.85/1.00  
% 3.85/1.00  ------ General Options
% 3.85/1.00  
% 3.85/1.00  --fof                                   false
% 3.85/1.00  --time_out_real                         305.
% 3.85/1.00  --time_out_virtual                      -1.
% 3.85/1.00  --symbol_type_check                     false
% 3.85/1.00  --clausify_out                          false
% 3.85/1.00  --sig_cnt_out                           false
% 3.85/1.00  --trig_cnt_out                          false
% 3.85/1.00  --trig_cnt_out_tolerance                1.
% 3.85/1.00  --trig_cnt_out_sk_spl                   false
% 3.85/1.00  --abstr_cl_out                          false
% 3.85/1.00  
% 3.85/1.00  ------ Global Options
% 3.85/1.00  
% 3.85/1.00  --schedule                              default
% 3.85/1.00  --add_important_lit                     false
% 3.85/1.00  --prop_solver_per_cl                    1000
% 3.85/1.00  --min_unsat_core                        false
% 3.85/1.00  --soft_assumptions                      false
% 3.85/1.00  --soft_lemma_size                       3
% 3.85/1.00  --prop_impl_unit_size                   0
% 3.85/1.00  --prop_impl_unit                        []
% 3.85/1.00  --share_sel_clauses                     true
% 3.85/1.00  --reset_solvers                         false
% 3.85/1.00  --bc_imp_inh                            [conj_cone]
% 3.85/1.00  --conj_cone_tolerance                   3.
% 3.85/1.00  --extra_neg_conj                        none
% 3.85/1.00  --large_theory_mode                     true
% 3.85/1.00  --prolific_symb_bound                   200
% 3.85/1.00  --lt_threshold                          2000
% 3.85/1.00  --clause_weak_htbl                      true
% 3.85/1.00  --gc_record_bc_elim                     false
% 3.85/1.00  
% 3.85/1.00  ------ Preprocessing Options
% 3.85/1.00  
% 3.85/1.00  --preprocessing_flag                    true
% 3.85/1.00  --time_out_prep_mult                    0.1
% 3.85/1.00  --splitting_mode                        input
% 3.85/1.00  --splitting_grd                         true
% 3.85/1.00  --splitting_cvd                         false
% 3.85/1.00  --splitting_cvd_svl                     false
% 3.85/1.00  --splitting_nvd                         32
% 3.85/1.00  --sub_typing                            true
% 3.85/1.00  --prep_gs_sim                           true
% 3.85/1.00  --prep_unflatten                        true
% 3.85/1.00  --prep_res_sim                          true
% 3.85/1.00  --prep_upred                            true
% 3.85/1.00  --prep_sem_filter                       exhaustive
% 3.85/1.00  --prep_sem_filter_out                   false
% 3.85/1.00  --pred_elim                             true
% 3.85/1.00  --res_sim_input                         true
% 3.85/1.00  --eq_ax_congr_red                       true
% 3.85/1.00  --pure_diseq_elim                       true
% 3.85/1.00  --brand_transform                       false
% 3.85/1.00  --non_eq_to_eq                          false
% 3.85/1.00  --prep_def_merge                        true
% 3.85/1.00  --prep_def_merge_prop_impl              false
% 3.85/1.00  --prep_def_merge_mbd                    true
% 3.85/1.00  --prep_def_merge_tr_red                 false
% 3.85/1.00  --prep_def_merge_tr_cl                  false
% 3.85/1.00  --smt_preprocessing                     true
% 3.85/1.00  --smt_ac_axioms                         fast
% 3.85/1.00  --preprocessed_out                      false
% 3.85/1.00  --preprocessed_stats                    false
% 3.85/1.00  
% 3.85/1.00  ------ Abstraction refinement Options
% 3.85/1.00  
% 3.85/1.00  --abstr_ref                             []
% 3.85/1.00  --abstr_ref_prep                        false
% 3.85/1.00  --abstr_ref_until_sat                   false
% 3.85/1.00  --abstr_ref_sig_restrict                funpre
% 3.85/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 3.85/1.00  --abstr_ref_under                       []
% 3.85/1.00  
% 3.85/1.00  ------ SAT Options
% 3.85/1.00  
% 3.85/1.00  --sat_mode                              false
% 3.85/1.00  --sat_fm_restart_options                ""
% 3.85/1.00  --sat_gr_def                            false
% 3.85/1.00  --sat_epr_types                         true
% 3.85/1.00  --sat_non_cyclic_types                  false
% 3.85/1.00  --sat_finite_models                     false
% 3.85/1.00  --sat_fm_lemmas                         false
% 3.85/1.00  --sat_fm_prep                           false
% 3.85/1.00  --sat_fm_uc_incr                        true
% 3.85/1.00  --sat_out_model                         small
% 3.85/1.00  --sat_out_clauses                       false
% 3.85/1.00  
% 3.85/1.00  ------ QBF Options
% 3.85/1.00  
% 3.85/1.00  --qbf_mode                              false
% 3.85/1.00  --qbf_elim_univ                         false
% 3.85/1.00  --qbf_dom_inst                          none
% 3.85/1.00  --qbf_dom_pre_inst                      false
% 3.85/1.00  --qbf_sk_in                             false
% 3.85/1.00  --qbf_pred_elim                         true
% 3.85/1.00  --qbf_split                             512
% 3.85/1.00  
% 3.85/1.00  ------ BMC1 Options
% 3.85/1.00  
% 3.85/1.00  --bmc1_incremental                      false
% 3.85/1.00  --bmc1_axioms                           reachable_all
% 3.85/1.00  --bmc1_min_bound                        0
% 3.85/1.00  --bmc1_max_bound                        -1
% 3.85/1.00  --bmc1_max_bound_default                -1
% 3.85/1.00  --bmc1_symbol_reachability              true
% 3.85/1.00  --bmc1_property_lemmas                  false
% 3.85/1.00  --bmc1_k_induction                      false
% 3.85/1.00  --bmc1_non_equiv_states                 false
% 3.85/1.00  --bmc1_deadlock                         false
% 3.85/1.00  --bmc1_ucm                              false
% 3.85/1.00  --bmc1_add_unsat_core                   none
% 3.85/1.00  --bmc1_unsat_core_children              false
% 3.85/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 3.85/1.00  --bmc1_out_stat                         full
% 3.85/1.00  --bmc1_ground_init                      false
% 3.85/1.00  --bmc1_pre_inst_next_state              false
% 3.85/1.00  --bmc1_pre_inst_state                   false
% 3.85/1.00  --bmc1_pre_inst_reach_state             false
% 3.85/1.00  --bmc1_out_unsat_core                   false
% 3.85/1.00  --bmc1_aig_witness_out                  false
% 3.85/1.00  --bmc1_verbose                          false
% 3.85/1.00  --bmc1_dump_clauses_tptp                false
% 3.85/1.00  --bmc1_dump_unsat_core_tptp             false
% 3.85/1.00  --bmc1_dump_file                        -
% 3.85/1.00  --bmc1_ucm_expand_uc_limit              128
% 3.85/1.00  --bmc1_ucm_n_expand_iterations          6
% 3.85/1.00  --bmc1_ucm_extend_mode                  1
% 3.85/1.00  --bmc1_ucm_init_mode                    2
% 3.85/1.00  --bmc1_ucm_cone_mode                    none
% 3.85/1.00  --bmc1_ucm_reduced_relation_type        0
% 3.85/1.00  --bmc1_ucm_relax_model                  4
% 3.85/1.00  --bmc1_ucm_full_tr_after_sat            true
% 3.85/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 3.85/1.00  --bmc1_ucm_layered_model                none
% 3.85/1.00  --bmc1_ucm_max_lemma_size               10
% 3.85/1.00  
% 3.85/1.00  ------ AIG Options
% 3.85/1.00  
% 3.85/1.00  --aig_mode                              false
% 3.85/1.00  
% 3.85/1.00  ------ Instantiation Options
% 3.85/1.00  
% 3.85/1.00  --instantiation_flag                    true
% 3.85/1.00  --inst_sos_flag                         true
% 3.85/1.00  --inst_sos_phase                        true
% 3.85/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.85/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.85/1.00  --inst_lit_sel_side                     none
% 3.85/1.00  --inst_solver_per_active                1400
% 3.85/1.00  --inst_solver_calls_frac                1.
% 3.85/1.00  --inst_passive_queue_type               priority_queues
% 3.85/1.00  --inst_passive_queues                   [[-num_var];[+age;-num_symb]]
% 3.85/1.00  --inst_passive_queues_freq              [25;2]
% 3.85/1.00  --inst_dismatching                      true
% 3.85/1.00  --inst_eager_unprocessed_to_passive     true
% 3.85/1.00  --inst_prop_sim_given                   true
% 3.85/1.00  --inst_prop_sim_new                     false
% 3.85/1.00  --inst_subs_new                         false
% 3.85/1.00  --inst_eq_res_simp                      false
% 3.85/1.00  --inst_subs_given                       false
% 3.85/1.00  --inst_orphan_elimination               true
% 3.85/1.00  --inst_learning_loop_flag               true
% 3.85/1.00  --inst_learning_start                   3000
% 3.85/1.00  --inst_learning_factor                  2
% 3.85/1.00  --inst_start_prop_sim_after_learn       3
% 3.85/1.00  --inst_sel_renew                        solver
% 3.85/1.00  --inst_lit_activity_flag                true
% 3.85/1.00  --inst_restr_to_given                   false
% 3.85/1.00  --inst_activity_threshold               500
% 3.85/1.00  --inst_out_proof                        true
% 3.85/1.00  
% 3.85/1.00  ------ Resolution Options
% 3.85/1.00  
% 3.85/1.00  --resolution_flag                       false
% 3.85/1.00  --res_lit_sel                           adaptive
% 3.85/1.00  --res_lit_sel_side                      none
% 3.85/1.00  --res_ordering                          kbo
% 3.85/1.00  --res_to_prop_solver                    active
% 3.85/1.00  --res_prop_simpl_new                    false
% 3.85/1.00  --res_prop_simpl_given                  true
% 3.85/1.00  --res_passive_queue_type                priority_queues
% 3.85/1.00  --res_passive_queues                    [[-num_symb];[+age;-num_symb]]
% 3.85/1.00  --res_passive_queues_freq               [15;5]
% 3.85/1.00  --res_forward_subs                      full
% 3.85/1.00  --res_backward_subs                     full
% 3.85/1.00  --res_forward_subs_resolution           true
% 3.85/1.00  --res_backward_subs_resolution          true
% 3.85/1.00  --res_orphan_elimination                true
% 3.85/1.00  --res_time_limit                        2.
% 3.85/1.00  --res_out_proof                         true
% 3.85/1.00  
% 3.85/1.00  ------ Superposition Options
% 3.85/1.00  
% 3.85/1.00  --superposition_flag                    true
% 3.85/1.00  --sup_passive_queue_type                priority_queues
% 3.85/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.85/1.00  --sup_passive_queues_freq               [8;1;4]
% 3.85/1.00  --demod_completeness_check              fast
% 3.85/1.00  --demod_use_ground                      true
% 3.85/1.00  --sup_to_prop_solver                    passive
% 3.85/1.00  --sup_prop_simpl_new                    true
% 3.85/1.00  --sup_prop_simpl_given                  true
% 3.85/1.00  --sup_fun_splitting                     true
% 3.85/1.00  --sup_smt_interval                      50000
% 3.85/1.00  
% 3.85/1.00  ------ Superposition Simplification Setup
% 3.85/1.00  
% 3.85/1.00  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 3.85/1.00  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 3.85/1.00  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 3.85/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 3.85/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 3.85/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 3.85/1.00  --sup_full_bw                           [BwDemod;BwSubsumption]
% 3.85/1.00  --sup_immed_triv                        [TrivRules]
% 3.85/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.85/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.85/1.00  --sup_immed_bw_main                     []
% 3.85/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 3.85/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 3.85/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.85/1.00  --sup_input_bw                          []
% 3.85/1.00  
% 3.85/1.00  ------ Combination Options
% 3.85/1.00  
% 3.85/1.00  --comb_res_mult                         3
% 3.85/1.00  --comb_sup_mult                         2
% 3.85/1.00  --comb_inst_mult                        10
% 3.85/1.00  
% 3.85/1.00  ------ Debug Options
% 3.85/1.00  
% 3.85/1.00  --dbg_backtrace                         false
% 3.85/1.00  --dbg_dump_prop_clauses                 false
% 3.85/1.00  --dbg_dump_prop_clauses_file            -
% 3.85/1.00  --dbg_out_stat                          false
% 3.85/1.00  
% 3.85/1.00  
% 3.85/1.00  
% 3.85/1.00  
% 3.85/1.00  ------ Proving...
% 3.85/1.00  
% 3.85/1.00  
% 3.85/1.00  % SZS status Theorem for theBenchmark.p
% 3.85/1.00  
% 3.85/1.00  % SZS output start CNFRefutation for theBenchmark.p
% 3.85/1.00  
% 3.85/1.00  fof(f2,axiom,(
% 3.85/1.00    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 3.85/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.85/1.00  
% 3.85/1.00  fof(f13,plain,(
% 3.85/1.00    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) & (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)))),
% 3.85/1.00    inference(nnf_transformation,[],[f2])).
% 3.85/1.00  
% 3.85/1.00  fof(f17,plain,(
% 3.85/1.00    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)) )),
% 3.85/1.00    inference(cnf_transformation,[],[f13])).
% 3.85/1.00  
% 3.85/1.00  fof(f7,axiom,(
% 3.85/1.00    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 3.85/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.85/1.00  
% 3.85/1.00  fof(f23,plain,(
% 3.85/1.00    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 3.85/1.00    inference(cnf_transformation,[],[f7])).
% 3.85/1.00  
% 3.85/1.00  fof(f30,plain,(
% 3.85/1.00    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,X1)) | ~r1_xboole_0(X0,X1)) )),
% 3.85/1.00    inference(definition_unfolding,[],[f17,f23])).
% 3.85/1.00  
% 3.85/1.00  fof(f10,conjecture,(
% 3.85/1.00    ! [X0,X1,X2] : (r1_xboole_0(X0,k4_xboole_0(X1,X2)) => r1_xboole_0(X1,k4_xboole_0(X0,X2)))),
% 3.85/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.85/1.00  
% 3.85/1.00  fof(f11,negated_conjecture,(
% 3.85/1.00    ~! [X0,X1,X2] : (r1_xboole_0(X0,k4_xboole_0(X1,X2)) => r1_xboole_0(X1,k4_xboole_0(X0,X2)))),
% 3.85/1.00    inference(negated_conjecture,[],[f10])).
% 3.85/1.00  
% 3.85/1.00  fof(f12,plain,(
% 3.85/1.00    ? [X0,X1,X2] : (~r1_xboole_0(X1,k4_xboole_0(X0,X2)) & r1_xboole_0(X0,k4_xboole_0(X1,X2)))),
% 3.85/1.00    inference(ennf_transformation,[],[f11])).
% 3.85/1.00  
% 3.85/1.00  fof(f14,plain,(
% 3.85/1.00    ? [X0,X1,X2] : (~r1_xboole_0(X1,k4_xboole_0(X0,X2)) & r1_xboole_0(X0,k4_xboole_0(X1,X2))) => (~r1_xboole_0(sK1,k4_xboole_0(sK0,sK2)) & r1_xboole_0(sK0,k4_xboole_0(sK1,sK2)))),
% 3.85/1.00    introduced(choice_axiom,[])).
% 3.85/1.00  
% 3.85/1.00  fof(f15,plain,(
% 3.85/1.00    ~r1_xboole_0(sK1,k4_xboole_0(sK0,sK2)) & r1_xboole_0(sK0,k4_xboole_0(sK1,sK2))),
% 3.85/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f12,f14])).
% 3.85/1.00  
% 3.85/1.00  fof(f26,plain,(
% 3.85/1.00    r1_xboole_0(sK0,k4_xboole_0(sK1,sK2))),
% 3.85/1.00    inference(cnf_transformation,[],[f15])).
% 3.85/1.00  
% 3.85/1.00  fof(f9,axiom,(
% 3.85/1.00    ! [X0,X1,X2] : k4_xboole_0(X0,k4_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X2))),
% 3.85/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.85/1.00  
% 3.85/1.00  fof(f25,plain,(
% 3.85/1.00    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X2))) )),
% 3.85/1.00    inference(cnf_transformation,[],[f9])).
% 3.85/1.00  
% 3.85/1.00  fof(f33,plain,(
% 3.85/1.00    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X2)))) )),
% 3.85/1.00    inference(definition_unfolding,[],[f25,f23])).
% 3.85/1.00  
% 3.85/1.00  fof(f3,axiom,(
% 3.85/1.00    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0),
% 3.85/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.85/1.00  
% 3.85/1.00  fof(f19,plain,(
% 3.85/1.00    ( ! [X0] : (k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0) )),
% 3.85/1.00    inference(cnf_transformation,[],[f3])).
% 3.85/1.00  
% 3.85/1.00  fof(f31,plain,(
% 3.85/1.00    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0))) )),
% 3.85/1.00    inference(definition_unfolding,[],[f19,f23])).
% 3.85/1.00  
% 3.85/1.00  fof(f5,axiom,(
% 3.85/1.00    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 3.85/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.85/1.00  
% 3.85/1.00  fof(f21,plain,(
% 3.85/1.00    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 3.85/1.00    inference(cnf_transformation,[],[f5])).
% 3.85/1.00  
% 3.85/1.00  fof(f8,axiom,(
% 3.85/1.00    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0),
% 3.85/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.85/1.00  
% 3.85/1.00  fof(f24,plain,(
% 3.85/1.00    ( ! [X0,X1] : (k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0) )),
% 3.85/1.00    inference(cnf_transformation,[],[f8])).
% 3.85/1.00  
% 3.85/1.00  fof(f32,plain,(
% 3.85/1.00    ( ! [X0,X1] : (k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1)) = X0) )),
% 3.85/1.00    inference(definition_unfolding,[],[f24,f23])).
% 3.85/1.00  
% 3.85/1.00  fof(f6,axiom,(
% 3.85/1.00    ! [X0,X1,X2] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2)),
% 3.85/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.85/1.00  
% 3.85/1.00  fof(f22,plain,(
% 3.85/1.00    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2)) )),
% 3.85/1.00    inference(cnf_transformation,[],[f6])).
% 3.85/1.00  
% 3.85/1.00  fof(f1,axiom,(
% 3.85/1.00    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 3.85/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.85/1.00  
% 3.85/1.00  fof(f16,plain,(
% 3.85/1.00    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 3.85/1.00    inference(cnf_transformation,[],[f1])).
% 3.85/1.00  
% 3.85/1.00  fof(f28,plain,(
% 3.85/1.00    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0))) )),
% 3.85/1.00    inference(definition_unfolding,[],[f16,f23,f23])).
% 3.85/1.00  
% 3.85/1.00  fof(f4,axiom,(
% 3.85/1.00    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))),
% 3.85/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.85/1.00  
% 3.85/1.00  fof(f20,plain,(
% 3.85/1.00    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 3.85/1.00    inference(cnf_transformation,[],[f4])).
% 3.85/1.00  
% 3.85/1.00  fof(f18,plain,(
% 3.85/1.00    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) )),
% 3.85/1.00    inference(cnf_transformation,[],[f13])).
% 3.85/1.00  
% 3.85/1.00  fof(f29,plain,(
% 3.85/1.00    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k1_xboole_0 != k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 3.85/1.00    inference(definition_unfolding,[],[f18,f23])).
% 3.85/1.00  
% 3.85/1.00  fof(f27,plain,(
% 3.85/1.00    ~r1_xboole_0(sK1,k4_xboole_0(sK0,sK2))),
% 3.85/1.00    inference(cnf_transformation,[],[f15])).
% 3.85/1.00  
% 3.85/1.00  cnf(c_2,plain,
% 3.85/1.00      ( ~ r1_xboole_0(X0,X1)
% 3.85/1.00      | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_xboole_0 ),
% 3.85/1.00      inference(cnf_transformation,[],[f30]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_44,plain,
% 3.85/1.00      ( ~ r1_xboole_0(X0,X1)
% 3.85/1.00      | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_xboole_0 ),
% 3.85/1.00      inference(prop_impl,[status(thm)],[c_2]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_10,negated_conjecture,
% 3.85/1.00      ( r1_xboole_0(sK0,k4_xboole_0(sK1,sK2)) ),
% 3.85/1.00      inference(cnf_transformation,[],[f26]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_85,plain,
% 3.85/1.00      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_xboole_0
% 3.85/1.00      | k4_xboole_0(sK1,sK2) != X1
% 3.85/1.00      | sK0 != X0 ),
% 3.85/1.00      inference(resolution_lifted,[status(thm)],[c_44,c_10]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_86,plain,
% 3.85/1.00      ( k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK1,sK2))) = k1_xboole_0 ),
% 3.85/1.00      inference(unflattening,[status(thm)],[c_85]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_8,plain,
% 3.85/1.00      ( k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X2))) = k4_xboole_0(X0,k4_xboole_0(X1,X2)) ),
% 3.85/1.00      inference(cnf_transformation,[],[f33]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_415,plain,
% 3.85/1.00      ( k4_xboole_0(sK0,k4_xboole_0(X0,k4_xboole_0(sK1,sK2))) = k2_xboole_0(k4_xboole_0(sK0,X0),k1_xboole_0) ),
% 3.85/1.00      inference(superposition,[status(thm)],[c_86,c_8]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_3,plain,
% 3.85/1.00      ( k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) = k1_xboole_0 ),
% 3.85/1.00      inference(cnf_transformation,[],[f31]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_5,plain,
% 3.85/1.00      ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
% 3.85/1.00      inference(cnf_transformation,[],[f21]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_112,plain,
% 3.85/1.00      ( k4_xboole_0(X0,X0) = k1_xboole_0 ),
% 3.85/1.00      inference(light_normalisation,[status(thm)],[c_3,c_5]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_7,plain,
% 3.85/1.00      ( k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1)) = X0 ),
% 3.85/1.00      inference(cnf_transformation,[],[f32]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_394,plain,
% 3.85/1.00      ( k2_xboole_0(k4_xboole_0(X0,k1_xboole_0),k1_xboole_0) = X0 ),
% 3.85/1.00      inference(superposition,[status(thm)],[c_112,c_7]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_395,plain,
% 3.85/1.00      ( k2_xboole_0(X0,k1_xboole_0) = X0 ),
% 3.85/1.00      inference(light_normalisation,[status(thm)],[c_394,c_5]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_434,plain,
% 3.85/1.00      ( k4_xboole_0(sK0,k4_xboole_0(X0,k4_xboole_0(sK1,sK2))) = k4_xboole_0(sK0,X0) ),
% 3.85/1.00      inference(demodulation,[status(thm)],[c_415,c_395]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_555,plain,
% 3.85/1.00      ( k2_xboole_0(k4_xboole_0(sK0,X0),k4_xboole_0(sK0,k4_xboole_0(sK0,X1))) = k4_xboole_0(sK0,k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(sK1,sK2)),X1)) ),
% 3.85/1.00      inference(superposition,[status(thm)],[c_434,c_8]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_6,plain,
% 3.85/1.00      ( k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
% 3.85/1.00      inference(cnf_transformation,[],[f22]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_569,plain,
% 3.85/1.00      ( k4_xboole_0(sK0,k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(sK1,sK2),X1))) = k4_xboole_0(sK0,k4_xboole_0(X0,X1)) ),
% 3.85/1.00      inference(demodulation,[status(thm)],[c_555,c_6,c_8]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_0,plain,
% 3.85/1.00      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
% 3.85/1.00      inference(cnf_transformation,[],[f28]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_304,plain,
% 3.85/1.00      ( k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,X1),X2)) = k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X2) ),
% 3.85/1.00      inference(superposition,[status(thm)],[c_0,c_6]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_2005,plain,
% 3.85/1.00      ( k4_xboole_0(sK0,k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(sK1,sK2)))) = k4_xboole_0(sK0,k4_xboole_0(X1,k4_xboole_0(X1,X0))) ),
% 3.85/1.00      inference(superposition,[status(thm)],[c_304,c_434]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_5709,plain,
% 3.85/1.00      ( k4_xboole_0(sK0,k4_xboole_0(sK2,k4_xboole_0(sK2,sK1))) = k4_xboole_0(sK0,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))) ),
% 3.85/1.00      inference(superposition,[status(thm)],[c_569,c_2005]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_5710,plain,
% 3.85/1.00      ( k4_xboole_0(sK0,k4_xboole_0(sK2,k4_xboole_0(sK2,sK1))) = k4_xboole_0(sK0,sK1) ),
% 3.85/1.00      inference(demodulation,[status(thm)],[c_5709,c_434]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_317,plain,
% 3.85/1.00      ( k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X0,X1))) = k1_xboole_0 ),
% 3.85/1.00      inference(superposition,[status(thm)],[c_6,c_112]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_4,plain,
% 3.85/1.00      ( k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
% 3.85/1.00      inference(cnf_transformation,[],[f20]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_318,plain,
% 3.85/1.00      ( k4_xboole_0(X0,k2_xboole_0(X1,X0)) = k1_xboole_0 ),
% 3.85/1.00      inference(demodulation,[status(thm)],[c_317,c_4]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_999,plain,
% 3.85/1.00      ( k4_xboole_0(k4_xboole_0(X0,X1),X0) = k1_xboole_0 ),
% 3.85/1.00      inference(superposition,[status(thm)],[c_7,c_318]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_1478,plain,
% 3.85/1.00      ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1) = k1_xboole_0 ),
% 3.85/1.00      inference(superposition,[status(thm)],[c_0,c_999]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_5778,plain,
% 3.85/1.00      ( k4_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(sK2,k4_xboole_0(sK2,sK1))) = k1_xboole_0 ),
% 3.85/1.00      inference(superposition,[status(thm)],[c_5710,c_1478]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_6068,plain,
% 3.85/1.00      ( k4_xboole_0(sK1,k2_xboole_0(k4_xboole_0(sK1,sK0),k4_xboole_0(sK2,k4_xboole_0(sK2,sK1)))) = k1_xboole_0 ),
% 3.85/1.00      inference(superposition,[status(thm)],[c_5778,c_304]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_412,plain,
% 3.85/1.00      ( k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X2,k4_xboole_0(X2,X0))) = k4_xboole_0(X0,k4_xboole_0(X1,X2)) ),
% 3.85/1.00      inference(superposition,[status(thm)],[c_0,c_8]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_6069,plain,
% 3.85/1.00      ( k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK0,sK2))) = k1_xboole_0 ),
% 3.85/1.00      inference(demodulation,[status(thm)],[c_6068,c_412]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_1,plain,
% 3.85/1.00      ( r1_xboole_0(X0,X1)
% 3.85/1.00      | k4_xboole_0(X0,k4_xboole_0(X0,X1)) != k1_xboole_0 ),
% 3.85/1.00      inference(cnf_transformation,[],[f29]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_42,plain,
% 3.85/1.00      ( r1_xboole_0(X0,X1)
% 3.85/1.00      | k4_xboole_0(X0,k4_xboole_0(X0,X1)) != k1_xboole_0 ),
% 3.85/1.00      inference(prop_impl,[status(thm)],[c_1]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_9,negated_conjecture,
% 3.85/1.00      ( ~ r1_xboole_0(sK1,k4_xboole_0(sK0,sK2)) ),
% 3.85/1.00      inference(cnf_transformation,[],[f27]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_80,plain,
% 3.85/1.00      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) != k1_xboole_0
% 3.85/1.00      | k4_xboole_0(sK0,sK2) != X1
% 3.85/1.00      | sK1 != X0 ),
% 3.85/1.00      inference(resolution_lifted,[status(thm)],[c_42,c_9]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_81,plain,
% 3.85/1.00      ( k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK0,sK2))) != k1_xboole_0 ),
% 3.85/1.00      inference(unflattening,[status(thm)],[c_80]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(contradiction,plain,
% 3.85/1.00      ( $false ),
% 3.85/1.00      inference(minisat,[status(thm)],[c_6069,c_81]) ).
% 3.85/1.00  
% 3.85/1.00  
% 3.85/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 3.85/1.00  
% 3.85/1.00  ------                               Statistics
% 3.85/1.00  
% 3.85/1.00  ------ General
% 3.85/1.00  
% 3.85/1.00  abstr_ref_over_cycles:                  0
% 3.85/1.00  abstr_ref_under_cycles:                 0
% 3.85/1.00  gc_basic_clause_elim:                   0
% 3.85/1.00  forced_gc_time:                         0
% 3.85/1.00  parsing_time:                           0.007
% 3.85/1.00  unif_index_cands_time:                  0.
% 3.85/1.00  unif_index_add_time:                    0.
% 3.85/1.00  orderings_time:                         0.
% 3.85/1.00  out_proof_time:                         0.02
% 3.85/1.00  total_time:                             0.362
% 3.85/1.00  num_of_symbols:                         38
% 3.85/1.00  num_of_terms:                           13303
% 3.85/1.00  
% 3.85/1.00  ------ Preprocessing
% 3.85/1.00  
% 3.85/1.00  num_of_splits:                          0
% 3.85/1.00  num_of_split_atoms:                     0
% 3.85/1.00  num_of_reused_defs:                     0
% 3.85/1.00  num_eq_ax_congr_red:                    0
% 3.85/1.00  num_of_sem_filtered_clauses:            0
% 3.85/1.00  num_of_subtypes:                        0
% 3.85/1.00  monotx_restored_types:                  0
% 3.85/1.00  sat_num_of_epr_types:                   0
% 3.85/1.00  sat_num_of_non_cyclic_types:            0
% 3.85/1.00  sat_guarded_non_collapsed_types:        0
% 3.85/1.00  num_pure_diseq_elim:                    0
% 3.85/1.00  simp_replaced_by:                       0
% 3.85/1.00  res_preprocessed:                       35
% 3.85/1.00  prep_upred:                             0
% 3.85/1.00  prep_unflattend:                        4
% 3.85/1.00  smt_new_axioms:                         0
% 3.85/1.00  pred_elim_cands:                        0
% 3.85/1.00  pred_elim:                              1
% 3.85/1.00  pred_elim_cl:                           1
% 3.85/1.00  pred_elim_cycles:                       2
% 3.85/1.00  merged_defs:                            2
% 3.85/1.00  merged_defs_ncl:                        0
% 3.85/1.00  bin_hyper_res:                          2
% 3.85/1.00  prep_cycles:                            3
% 3.85/1.00  pred_elim_time:                         0.
% 3.85/1.00  splitting_time:                         0.
% 3.85/1.00  sem_filter_time:                        0.
% 3.85/1.00  monotx_time:                            0.
% 3.85/1.00  subtype_inf_time:                       0.
% 3.85/1.00  
% 3.85/1.00  ------ Problem properties
% 3.85/1.00  
% 3.85/1.00  clauses:                                10
% 3.85/1.00  conjectures:                            0
% 3.85/1.00  epr:                                    0
% 3.85/1.00  horn:                                   10
% 3.85/1.00  ground:                                 3
% 3.85/1.00  unary:                                  9
% 3.85/1.00  binary:                                 1
% 3.85/1.00  lits:                                   11
% 3.85/1.00  lits_eq:                                11
% 3.85/1.00  fd_pure:                                0
% 3.85/1.00  fd_pseudo:                              0
% 3.85/1.00  fd_cond:                                0
% 3.85/1.00  fd_pseudo_cond:                         0
% 3.85/1.00  ac_symbols:                             0
% 3.85/1.00  
% 3.85/1.00  ------ Propositional Solver
% 3.85/1.00  
% 3.85/1.00  prop_solver_calls:                      28
% 3.85/1.00  prop_fast_solver_calls:                 190
% 3.85/1.00  smt_solver_calls:                       0
% 3.85/1.00  smt_fast_solver_calls:                  0
% 3.85/1.00  prop_num_of_clauses:                    2032
% 3.85/1.00  prop_preprocess_simplified:             2111
% 3.85/1.00  prop_fo_subsumed:                       0
% 3.85/1.00  prop_solver_time:                       0.
% 3.85/1.00  smt_solver_time:                        0.
% 3.85/1.00  smt_fast_solver_time:                   0.
% 3.85/1.00  prop_fast_solver_time:                  0.
% 3.85/1.00  prop_unsat_core_time:                   0.
% 3.85/1.00  
% 3.85/1.00  ------ QBF
% 3.85/1.00  
% 3.85/1.00  qbf_q_res:                              0
% 3.85/1.00  qbf_num_tautologies:                    0
% 3.85/1.00  qbf_prep_cycles:                        0
% 3.85/1.00  
% 3.85/1.00  ------ BMC1
% 3.85/1.00  
% 3.85/1.00  bmc1_current_bound:                     -1
% 3.85/1.00  bmc1_last_solved_bound:                 -1
% 3.85/1.00  bmc1_unsat_core_size:                   -1
% 3.85/1.00  bmc1_unsat_core_parents_size:           -1
% 3.85/1.00  bmc1_merge_next_fun:                    0
% 3.85/1.00  bmc1_unsat_core_clauses_time:           0.
% 3.85/1.00  
% 3.85/1.00  ------ Instantiation
% 3.85/1.00  
% 3.85/1.00  inst_num_of_clauses:                    630
% 3.85/1.00  inst_num_in_passive:                    117
% 3.85/1.00  inst_num_in_active:                     297
% 3.85/1.00  inst_num_in_unprocessed:                216
% 3.85/1.00  inst_num_of_loops:                      350
% 3.85/1.00  inst_num_of_learning_restarts:          0
% 3.85/1.00  inst_num_moves_active_passive:          48
% 3.85/1.00  inst_lit_activity:                      0
% 3.85/1.00  inst_lit_activity_moves:                0
% 3.85/1.00  inst_num_tautologies:                   0
% 3.85/1.00  inst_num_prop_implied:                  0
% 3.85/1.00  inst_num_existing_simplified:           0
% 3.85/1.00  inst_num_eq_res_simplified:             0
% 3.85/1.00  inst_num_child_elim:                    0
% 3.85/1.00  inst_num_of_dismatching_blockings:      157
% 3.85/1.00  inst_num_of_non_proper_insts:           828
% 3.85/1.00  inst_num_of_duplicates:                 0
% 3.85/1.00  inst_inst_num_from_inst_to_res:         0
% 3.85/1.00  inst_dismatching_checking_time:         0.
% 3.85/1.00  
% 3.85/1.00  ------ Resolution
% 3.85/1.00  
% 3.85/1.00  res_num_of_clauses:                     0
% 3.85/1.00  res_num_in_passive:                     0
% 3.85/1.00  res_num_in_active:                      0
% 3.85/1.00  res_num_of_loops:                       38
% 3.85/1.00  res_forward_subset_subsumed:            288
% 3.85/1.00  res_backward_subset_subsumed:           0
% 3.85/1.00  res_forward_subsumed:                   0
% 3.85/1.00  res_backward_subsumed:                  0
% 3.85/1.00  res_forward_subsumption_resolution:     0
% 3.85/1.00  res_backward_subsumption_resolution:    0
% 3.85/1.00  res_clause_to_clause_subsumption:       3397
% 3.85/1.00  res_orphan_elimination:                 0
% 3.85/1.00  res_tautology_del:                      76
% 3.85/1.00  res_num_eq_res_simplified:              0
% 3.85/1.00  res_num_sel_changes:                    0
% 3.85/1.00  res_moves_from_active_to_pass:          0
% 3.85/1.00  
% 3.85/1.00  ------ Superposition
% 3.85/1.00  
% 3.85/1.00  sup_time_total:                         0.
% 3.85/1.00  sup_time_generating:                    0.
% 3.85/1.00  sup_time_sim_full:                      0.
% 3.85/1.00  sup_time_sim_immed:                     0.
% 3.85/1.00  
% 3.85/1.00  sup_num_of_clauses:                     592
% 3.85/1.00  sup_num_in_active:                      60
% 3.85/1.00  sup_num_in_passive:                     532
% 3.85/1.00  sup_num_of_loops:                       69
% 3.85/1.00  sup_fw_superposition:                   984
% 3.85/1.00  sup_bw_superposition:                   999
% 3.85/1.00  sup_immediate_simplified:               1246
% 3.85/1.00  sup_given_eliminated:                   0
% 3.85/1.00  comparisons_done:                       0
% 3.85/1.00  comparisons_avoided:                    0
% 3.85/1.00  
% 3.85/1.00  ------ Simplifications
% 3.85/1.00  
% 3.85/1.00  
% 3.85/1.00  sim_fw_subset_subsumed:                 0
% 3.85/1.00  sim_bw_subset_subsumed:                 0
% 3.85/1.00  sim_fw_subsumed:                        187
% 3.85/1.00  sim_bw_subsumed:                        11
% 3.85/1.00  sim_fw_subsumption_res:                 0
% 3.85/1.00  sim_bw_subsumption_res:                 0
% 3.85/1.00  sim_tautology_del:                      0
% 3.85/1.00  sim_eq_tautology_del:                   408
% 3.85/1.00  sim_eq_res_simp:                        0
% 3.85/1.00  sim_fw_demodulated:                     1120
% 3.85/1.00  sim_bw_demodulated:                     11
% 3.85/1.00  sim_light_normalised:                   390
% 3.85/1.00  sim_joinable_taut:                      0
% 3.85/1.00  sim_joinable_simp:                      0
% 3.85/1.00  sim_ac_normalised:                      0
% 3.85/1.00  sim_smt_subsumption:                    0
% 3.85/1.00  
%------------------------------------------------------------------------------
